//! Runs rustfmt on the repository.

use crate::builder::Builder;
use crate::util::{output, t};
use ignore::WalkBuilder;
use std::collections::VecDeque;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc::SyncSender;

fn rustfmt(src: &Path, rustfmt: &Path, paths: &[PathBuf], check: bool) -> impl FnMut() {
    let mut cmd = Command::new(&rustfmt);
    // avoid the submodule config paths from coming into play,
    // we only allow a single global config for the workspace for now
    cmd.arg("--config-path").arg(&src.canonicalize().unwrap());
    cmd.arg("--edition").arg("2021");
    cmd.arg("--unstable-features");
    cmd.arg("--skip-children");
    if check {
        cmd.arg("--check");
    }
    cmd.args(paths);
    let cmd_debug = format!("{:?}", cmd);
    let mut cmd = cmd.spawn().expect("running rustfmt");
    // poor man's async: return a closure that'll wait for rustfmt's completion
    move || {
        let status = cmd.wait().unwrap();
        if !status.success() {
            eprintln!(
                "Running `{}` failed.\nIf you're running `tidy`, \
                        try again with `--bless`. Or, if you just want to format \
                        code, run `./x.py fmt` instead.",
                cmd_debug,
            );
            crate::detail_exit(1);
        }
    }
}

#[derive(serde::Deserialize)]
struct RustfmtConfig {
    ignore: Vec<String>,
}

pub fn format(build: &Builder<'_>, check: bool, paths: &[PathBuf]) {
    if build.config.dry_run {
        return;
    }
    let mut builder = ignore::types::TypesBuilder::new();
    builder.add_defaults();
    builder.select("rust");
    let matcher = builder.build().unwrap();
    let rustfmt_config = build.src.join("rustfmt.toml");
    if !rustfmt_config.exists() {
        eprintln!("Not running formatting checks; rustfmt.toml does not exist.");
        eprintln!("This may happen in distributed tarballs.");
        return;
    }
    let rustfmt_config = t!(std::fs::read_to_string(&rustfmt_config));
    let rustfmt_config: RustfmtConfig = t!(toml::from_str(&rustfmt_config));
    let mut ignore_fmt = ignore::overrides::OverrideBuilder::new(&build.src);
    for ignore in rustfmt_config.ignore {
        ignore_fmt.add(&format!("!{}", ignore)).expect(&ignore);
    }
    let git_available = match Command::new("git")
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
    {
        Ok(status) => status.success(),
        Err(_) => false,
    };
    if git_available {
        let in_working_tree = match build
            .config
            .git()
            .arg("rev-parse")
            .arg("--is-inside-work-tree")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
        {
            Ok(status) => status.success(),
            Err(_) => false,
        };
        if in_working_tree {
            let untracked_paths_output = output(
                build.config.git().arg("status").arg("--porcelain").arg("--untracked-files=normal"),
            );
            let untracked_paths = untracked_paths_output
                .lines()
                .filter(|entry| entry.starts_with("??"))
                .map(|entry| {
                    entry.split(' ').nth(1).expect("every git status entry should list a path")
                });
            for untracked_path in untracked_paths {
                println!("skip untracked path {} during rustfmt invocations", untracked_path);
                // The leading `/` makes it an exact match against the
                // repository root, rather than a glob. Without that, if you
                // have `foo.rs` in the repository root it will also match
                // against anything like `compiler/rustc_foo/src/foo.rs`,
                // preventing the latter from being formatted.
                ignore_fmt.add(&format!("!/{}", untracked_path)).expect(&untracked_path);
            }
        } else {
            println!("Not in git tree. Skipping git-aware format checks");
        }
    } else {
        println!("Could not find usable git. Skipping git-aware format checks");
    }
    let ignore_fmt = ignore_fmt.build().unwrap();

    let rustfmt_path = build.initial_rustfmt().unwrap_or_else(|| {
        eprintln!("./x.py fmt is not supported on this channel");
        crate::detail_exit(1);
    });
    assert!(rustfmt_path.exists(), "{}", rustfmt_path.display());
    let src = build.src.clone();
    let (tx, rx): (SyncSender<PathBuf>, _) = std::sync::mpsc::sync_channel(128);
    let walker = match paths.get(0) {
        Some(first) => {
            let mut walker = WalkBuilder::new(first);
            for path in &paths[1..] {
                walker.add(path);
            }
            walker
        }
        None => WalkBuilder::new(src.clone()),
    }
    .types(matcher)
    .overrides(ignore_fmt)
    .build_parallel();

    // there is a lot of blocking involved in spawning a child process and reading files to format.
    // spawn more processes than available concurrency to keep the CPU busy
    let max_processes = build.jobs() as usize * 2;

    // spawn child processes on a separate thread so we can batch entries we have received from ignore
    let thread = std::thread::spawn(move || {
        let mut children = VecDeque::new();
        while let Ok(path) = rx.recv() {
            // try getting a few more paths from the channel to amortize the overhead of spawning processes
            let paths: Vec<_> = rx.try_iter().take(7).chain(std::iter::once(path)).collect();

            let child = rustfmt(&src, &rustfmt_path, paths.as_slice(), check);
            children.push_back(child);

            if children.len() >= max_processes {
                // await oldest child
                children.pop_front().unwrap()();
            }
        }

        // await remaining children
        for mut child in children {
            child();
        }
    });

    walker.run(|| {
        let tx = tx.clone();
        Box::new(move |entry| {
            let entry = t!(entry);
            if entry.file_type().map_or(false, |t| t.is_file()) {
                t!(tx.send(entry.into_path()));
            }
            ignore::WalkState::Continue
        })
    });

    drop(tx);

    thread.join().unwrap();
}
