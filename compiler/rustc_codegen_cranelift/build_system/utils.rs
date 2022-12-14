use std::env;
use std::fs;
use std::io::Write;
use std::path::Path;
use std::process::{self, Command, Stdio};

pub(crate) fn cargo_command(
    cargo: impl AsRef<Path>,
    subcommand: &str,
    triple: Option<&str>,
    source_dir: &Path,
) -> Command {
    let mut cmd = Command::new(cargo.as_ref());
    cmd.arg(subcommand)
        .arg("--manifest-path")
        .arg(source_dir.join("Cargo.toml"))
        .arg("--target-dir")
        .arg(source_dir.join("target"));

    if let Some(triple) = triple {
        cmd.arg("--target").arg(triple);
    }

    cmd
}

pub(crate) fn hyperfine_command(
    warmup: u64,
    runs: u64,
    prepare: Option<Command>,
    a: Command,
    b: Command,
) -> Command {
    let mut bench = Command::new("hyperfine");

    if warmup != 0 {
        bench.arg("--warmup").arg(warmup.to_string());
    }

    if runs != 0 {
        bench.arg("--runs").arg(runs.to_string());
    }

    if let Some(prepare) = prepare {
        bench.arg("--prepare").arg(format!("{:?}", prepare));
    }

    bench.arg(format!("{:?}", a)).arg(format!("{:?}", b));

    bench
}

#[track_caller]
pub(crate) fn try_hard_link(src: impl AsRef<Path>, dst: impl AsRef<Path>) {
    let src = src.as_ref();
    let dst = dst.as_ref();
    if let Err(_) = fs::hard_link(src, dst) {
        fs::copy(src, dst).unwrap(); // Fallback to copying if hardlinking failed
    }
}

#[track_caller]
pub(crate) fn spawn_and_wait(mut cmd: Command) {
    if !cmd.spawn().unwrap().wait().unwrap().success() {
        process::exit(1);
    }
}

#[track_caller]
pub(crate) fn spawn_and_wait_with_input(mut cmd: Command, input: String) -> String {
    let mut child = cmd
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("Failed to spawn child process");

    let mut stdin = child.stdin.take().expect("Failed to open stdin");
    std::thread::spawn(move || {
        stdin.write_all(input.as_bytes()).expect("Failed to write to stdin");
    });

    let output = child.wait_with_output().expect("Failed to read stdout");
    if !output.status.success() {
        process::exit(1);
    }

    String::from_utf8(output.stdout).unwrap()
}

pub(crate) fn copy_dir_recursively(from: &Path, to: &Path) {
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let filename = entry.file_name();
        if filename == "." || filename == ".." {
            continue;
        }
        if entry.metadata().unwrap().is_dir() {
            fs::create_dir(to.join(&filename)).unwrap();
            copy_dir_recursively(&from.join(&filename), &to.join(&filename));
        } else {
            fs::copy(from.join(&filename), to.join(&filename)).unwrap();
        }
    }
}

pub(crate) fn is_ci() -> bool {
    env::var("CI").as_ref().map(|val| &**val) == Ok("true")
}
