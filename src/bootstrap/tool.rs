use std::collections::HashSet;
use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::{exit, Command};

use build_helper::t;

use crate::builder::{Builder, Cargo as CargoCommand, RunConfig, ShouldRun, Step};
use crate::cache::Interned;
use crate::channel;
use crate::channel::GitInfo;
use crate::compile;
use crate::toolstate::ToolState;
use crate::util::{add_dylib_path, exe};
use crate::Compiler;
use crate::Mode;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum SourceType {
    InTree,
    Submodule,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct ToolBuild {
    compiler: Compiler,
    target: Interned<String>,
    tool: &'static str,
    path: &'static str,
    mode: Mode,
    is_optional_tool: bool,
    source_type: SourceType,
    extra_features: Vec<String>,
}

impl Step for ToolBuild {
    type Output = Option<PathBuf>;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.never()
    }

    /// Builds a tool in `src/tools`
    ///
    /// This will build the specified tool with the specified `host` compiler in
    /// `stage` into the normal cargo output directory.
    fn run(self, builder: &Builder<'_>) -> Option<PathBuf> {
        let compiler = self.compiler;
        let target = self.target;
        let tool = self.tool;
        let path = self.path;
        let is_optional_tool = self.is_optional_tool;

        match self.mode {
            Mode::ToolRustc => builder.ensure(compile::Rustc { compiler, target }),
            Mode::ToolStd => builder.ensure(compile::Std { compiler, target }),
            Mode::ToolBootstrap => {} // uses downloaded stage0 compiler libs
            _ => panic!("unexpected Mode for tool build"),
        }

        let cargo = prepare_tool_cargo(
            builder,
            compiler,
            self.mode,
            target,
            "build",
            path,
            self.source_type,
            &self.extra_features,
        );

        builder.info(&format!("Building stage{} tool {} ({})", compiler.stage, tool, target));
        let mut duplicates = Vec::new();
        let is_expected = compile::stream_cargo(builder, cargo, vec![], &mut |msg| {
            // Only care about big things like the RLS/Cargo for now
            match tool {
                "rls" | "cargo" | "clippy-driver" | "miri" | "rustfmt" => {}

                _ => return,
            }
            let (id, features, filenames) = match msg {
                compile::CargoMessage::CompilerArtifact {
                    package_id,
                    features,
                    filenames,
                    target: _,
                } => (package_id, features, filenames),
                _ => return,
            };
            let features = features.iter().map(|s| s.to_string()).collect::<Vec<_>>();

            for path in filenames {
                let val = (tool, PathBuf::from(&*path), features.clone());
                // we're only interested in deduplicating rlibs for now
                if val.1.extension().and_then(|s| s.to_str()) != Some("rlib") {
                    continue;
                }

                // Don't worry about compiles that turn out to be host
                // dependencies or build scripts. To skip these we look for
                // anything that goes in `.../release/deps` but *doesn't* go in
                // `$target/release/deps`. This ensure that outputs in
                // `$target/release` are still considered candidates for
                // deduplication.
                if let Some(parent) = val.1.parent() {
                    if parent.ends_with("release/deps") {
                        let maybe_target = parent
                            .parent()
                            .and_then(|p| p.parent())
                            .and_then(|p| p.file_name())
                            .and_then(|p| p.to_str())
                            .unwrap();
                        if maybe_target != &*target {
                            continue;
                        }
                    }
                }

                // Record that we've built an artifact for `id`, and if one was
                // already listed then we need to see if we reused the same
                // artifact or produced a duplicate.
                let mut artifacts = builder.tool_artifacts.borrow_mut();
                let prev_artifacts = artifacts.entry(target).or_default();
                let prev = match prev_artifacts.get(&*id) {
                    Some(prev) => prev,
                    None => {
                        prev_artifacts.insert(id.to_string(), val);
                        continue;
                    }
                };
                if prev.1 == val.1 {
                    return; // same path, same artifact
                }

                // If the paths are different and one of them *isn't* inside of
                // `release/deps`, then it means it's probably in
                // `$target/release`, or it's some final artifact like
                // `libcargo.rlib`. In these situations Cargo probably just
                // copied it up from `$target/release/deps/libcargo-xxxx.rlib`,
                // so if the features are equal we can just skip it.
                let prev_no_hash = prev.1.parent().unwrap().ends_with("release/deps");
                let val_no_hash = val.1.parent().unwrap().ends_with("release/deps");
                if prev.2 == val.2 || !prev_no_hash || !val_no_hash {
                    return;
                }

                // ... and otherwise this looks like we duplicated some sort of
                // compilation, so record it to generate an error later.
                duplicates.push((id.to_string(), val, prev.clone()));
            }
        });

        if is_expected && !duplicates.is_empty() {
            println!(
                "duplicate artifacts found when compiling a tool, this \
                      typically means that something was recompiled because \
                      a transitive dependency has different features activated \
                      than in a previous build:\n"
            );
            println!(
                "the following dependencies are duplicated although they \
                      have the same features enabled:"
            );
            for (id, cur, prev) in duplicates.drain_filter(|(_, cur, prev)| cur.2 == prev.2) {
                println!("  {}", id);
                // same features
                println!("    `{}` ({:?})\n    `{}` ({:?})", cur.0, cur.1, prev.0, prev.1);
            }
            println!("the following dependencies have different features:");
            for (id, cur, prev) in duplicates {
                println!("  {}", id);
                let cur_features: HashSet<_> = cur.2.into_iter().collect();
                let prev_features: HashSet<_> = prev.2.into_iter().collect();
                println!(
                    "    `{}` additionally enabled features {:?} at {:?}",
                    cur.0,
                    &cur_features - &prev_features,
                    cur.1
                );
                println!(
                    "    `{}` additionally enabled features {:?} at {:?}",
                    prev.0,
                    &prev_features - &cur_features,
                    prev.1
                );
            }
            println!();
            println!(
                "to fix this you will probably want to edit the local \
                      src/tools/rustc-workspace-hack/Cargo.toml crate, as \
                      that will update the dependency graph to ensure that \
                      these crates all share the same feature set"
            );
            panic!("tools should not compile multiple copies of the same crate");
        }

        builder.save_toolstate(
            tool,
            if is_expected { ToolState::TestFail } else { ToolState::BuildFail },
        );

        if !is_expected {
            if !is_optional_tool {
                exit(1);
            } else {
                None
            }
        } else {
            let cargo_out =
                builder.cargo_out(compiler, self.mode, target).join(exe(tool, &compiler.host));
            let bin = builder.tools_dir(compiler).join(exe(tool, &compiler.host));
            builder.copy(&cargo_out, &bin);
            Some(bin)
        }
    }
}

pub fn prepare_tool_cargo(
    builder: &Builder<'_>,
    compiler: Compiler,
    mode: Mode,
    target: Interned<String>,
    command: &'static str,
    path: &'static str,
    source_type: SourceType,
    extra_features: &[String],
) -> CargoCommand {
    let mut cargo = builder.cargo(compiler, mode, source_type, target, command);
    let dir = builder.src.join(path);
    cargo.arg("--manifest-path").arg(dir.join("Cargo.toml"));

    let mut features = extra_features.to_vec();
    if builder.build.config.cargo_native_static {
        if path.ends_with("cargo")
            || path.ends_with("rls")
            || path.ends_with("clippy")
            || path.ends_with("miri")
            || path.ends_with("rustfmt")
        {
            cargo.env("LIBZ_SYS_STATIC", "1");
            features.push("rustc-workspace-hack/all-static".to_string());
        }
    }

    // if tools are using lzma we want to force the build script to build its
    // own copy
    cargo.env("LZMA_API_STATIC", "1");

    // CFG_RELEASE is needed by rustfmt (and possibly other tools) which
    // import rustc-ap-rustc_attr which requires this to be set for the
    // `#[cfg(version(...))]` attribute.
    cargo.env("CFG_RELEASE", builder.rust_release());
    cargo.env("CFG_RELEASE_CHANNEL", &builder.config.channel);
    cargo.env("CFG_VERSION", builder.rust_version());
    cargo.env("CFG_RELEASE_NUM", channel::CFG_RELEASE_NUM);

    let info = GitInfo::new(builder.config.ignore_git, &dir);
    if let Some(sha) = info.sha() {
        cargo.env("CFG_COMMIT_HASH", sha);
    }
    if let Some(sha_short) = info.sha_short() {
        cargo.env("CFG_SHORT_COMMIT_HASH", sha_short);
    }
    if let Some(date) = info.commit_date() {
        cargo.env("CFG_COMMIT_DATE", date);
    }
    if !features.is_empty() {
        cargo.arg("--features").arg(&features.join(", "));
    }
    cargo
}

macro_rules! bootstrap_tool {
    ($(
        $name:ident, $path:expr, $tool_name:expr
        $(,is_external_tool = $external:expr)*
        $(,is_unstable_tool = $unstable:expr)*
        $(,features = $features:expr)*
        ;
    )+) => {
        #[derive(Copy, PartialEq, Eq, Clone)]
        pub enum Tool {
            $(
                $name,
            )+
        }

        impl<'a> Builder<'a> {
            pub fn tool_exe(&self, tool: Tool) -> PathBuf {
                match tool {
                    $(Tool::$name =>
                        self.ensure($name {
                            compiler: self.compiler(0, self.config.build),
                            target: self.config.build,
                        }),
                    )+
                }
            }
        }

        $(
            #[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
        pub struct $name {
            pub compiler: Compiler,
            pub target: Interned<String>,
        }

        impl Step for $name {
            type Output = PathBuf;

            fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
                run.path($path)
            }

            fn make_run(run: RunConfig<'_>) {
                run.builder.ensure($name {
                    // snapshot compiler
                    compiler: run.builder.compiler(0, run.builder.config.build),
                    target: run.target,
                });
            }

            fn run(self, builder: &Builder<'_>) -> PathBuf {
                builder.ensure(ToolBuild {
                    compiler: self.compiler,
                    target: self.target,
                    tool: $tool_name,
                    mode: if false $(|| $unstable)* {
                        // use in-tree libraries for unstable features
                        Mode::ToolStd
                    } else {
                        Mode::ToolBootstrap
                    },
                    path: $path,
                    is_optional_tool: false,
                    source_type: if false $(|| $external)* {
                        SourceType::Submodule
                    } else {
                        SourceType::InTree
                    },
                    extra_features: {
                        // FIXME(#60643): avoid this lint by using `_`
                        let mut _tmp = Vec::new();
                        $(_tmp.extend($features);)*
                        _tmp
                    },
                }).expect("expected to build -- essential tool")
            }
        }
        )+
    }
}

bootstrap_tool!(
    Rustbook, "src/tools/rustbook", "rustbook";
    UnstableBookGen, "src/tools/unstable-book-gen", "unstable-book-gen";
    Tidy, "src/tools/tidy", "tidy";
    Linkchecker, "src/tools/linkchecker", "linkchecker";
    CargoTest, "src/tools/cargotest", "cargotest";
    Compiletest, "src/tools/compiletest", "compiletest", is_unstable_tool = true;
    BuildManifest, "src/tools/build-manifest", "build-manifest";
    RemoteTestClient, "src/tools/remote-test-client", "remote-test-client";
    RustInstaller, "src/tools/rust-installer", "fabricate", is_external_tool = true;
    RustdocTheme, "src/tools/rustdoc-themes", "rustdoc-themes";
    ExpandYamlAnchors, "src/tools/expand-yaml-anchors", "expand-yaml-anchors";
);

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, Ord, PartialOrd)]
pub struct ErrorIndex {
    pub compiler: Compiler,
}

impl ErrorIndex {
    pub fn command(builder: &Builder<'_>, compiler: Compiler) -> Command {
        let mut cmd = Command::new(builder.ensure(ErrorIndex { compiler }));
        add_dylib_path(
            vec![PathBuf::from(&builder.sysroot_libdir(compiler, compiler.host))],
            &mut cmd,
        );
        cmd
    }
}

impl Step for ErrorIndex {
    type Output = PathBuf;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/error_index_generator")
    }

    fn make_run(run: RunConfig<'_>) {
        // Compile the error-index in the same stage as rustdoc to avoid
        // recompiling rustdoc twice if we can.
        let host = run.builder.config.build;
        let compiler = run.builder.compiler_for(run.builder.top_stage, host, host);
        run.builder.ensure(ErrorIndex { compiler });
    }

    fn run(self, builder: &Builder<'_>) -> PathBuf {
        builder
            .ensure(ToolBuild {
                compiler: self.compiler,
                target: self.compiler.host,
                tool: "error_index_generator",
                mode: Mode::ToolRustc,
                path: "src/tools/error_index_generator",
                is_optional_tool: false,
                source_type: SourceType::InTree,
                extra_features: Vec::new(),
            })
            .expect("expected to build -- essential tool")
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct RemoteTestServer {
    pub compiler: Compiler,
    pub target: Interned<String>,
}

impl Step for RemoteTestServer {
    type Output = PathBuf;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/remote-test-server")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(RemoteTestServer {
            compiler: run.builder.compiler(run.builder.top_stage, run.builder.config.build),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> PathBuf {
        builder
            .ensure(ToolBuild {
                compiler: self.compiler,
                target: self.target,
                tool: "remote-test-server",
                mode: Mode::ToolStd,
                path: "src/tools/remote-test-server",
                is_optional_tool: false,
                source_type: SourceType::InTree,
                extra_features: Vec::new(),
            })
            .expect("expected to build -- essential tool")
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, Ord, PartialOrd)]
pub struct Rustdoc {
    /// This should only ever be 0 or 2.
    /// We sometimes want to reference the "bootstrap" rustdoc, which is why this option is here.
    pub compiler: Compiler,
}

impl Step for Rustdoc {
    type Output = PathBuf;
    const DEFAULT: bool = true;
    const ONLY_HOSTS: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/rustdoc").path("src/librustdoc")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder
            .ensure(Rustdoc { compiler: run.builder.compiler(run.builder.top_stage, run.host) });
    }

    fn run(self, builder: &Builder<'_>) -> PathBuf {
        let target_compiler = self.compiler;
        if target_compiler.stage == 0 {
            if !target_compiler.is_snapshot(builder) {
                panic!("rustdoc in stage 0 must be snapshot rustdoc");
            }
            return builder.initial_rustc.with_file_name(exe("rustdoc", &target_compiler.host));
        }
        let target = target_compiler.host;
        // Similar to `compile::Assemble`, build with the previous stage's compiler. Otherwise
        // we'd have stageN/bin/rustc and stageN/bin/rustdoc be effectively different stage
        // compilers, which isn't what we want. Rustdoc should be linked in the same way as the
        // rustc compiler it's paired with, so it must be built with the previous stage compiler.
        let build_compiler = builder.compiler(target_compiler.stage - 1, builder.config.build);

        // The presence of `target_compiler` ensures that the necessary libraries (codegen backends,
        // compiler libraries, ...) are built. Rustdoc does not require the presence of any
        // libraries within sysroot_libdir (i.e., rustlib), though doctests may want it (since
        // they'll be linked to those libraries). As such, don't explicitly `ensure` any additional
        // libraries here. The intuition here is that If we've built a compiler, we should be able
        // to build rustdoc.

        let cargo = prepare_tool_cargo(
            builder,
            build_compiler,
            Mode::ToolRustc,
            target,
            "build",
            "src/tools/rustdoc",
            SourceType::InTree,
            &[],
        );

        builder.info(&format!(
            "Building rustdoc for stage{} ({})",
            target_compiler.stage, target_compiler.host
        ));
        builder.run(&mut cargo.into());

        // Cargo adds a number of paths to the dylib search path on windows, which results in
        // the wrong rustdoc being executed. To avoid the conflicting rustdocs, we name the "tool"
        // rustdoc a different name.
        let tool_rustdoc = builder
            .cargo_out(build_compiler, Mode::ToolRustc, target)
            .join(exe("rustdoc_tool_binary", &target_compiler.host));

        // don't create a stage0-sysroot/bin directory.
        if target_compiler.stage > 0 {
            let sysroot = builder.sysroot(target_compiler);
            let bindir = sysroot.join("bin");
            t!(fs::create_dir_all(&bindir));
            let bin_rustdoc = bindir.join(exe("rustdoc", &*target_compiler.host));
            let _ = fs::remove_file(&bin_rustdoc);
            builder.copy(&tool_rustdoc, &bin_rustdoc);
            bin_rustdoc
        } else {
            tool_rustdoc
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, Ord, PartialOrd)]
pub struct FuzzTargetGenerator {
    pub compiler: Compiler,
}

impl Step for FuzzTargetGenerator {
    type Output = PathBuf;
    const DEFAULT: bool = true;
    const ONLY_HOSTS: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/fuzz-target-generator").path("src/librustdoc")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(FuzzTargetGenerator {
            compiler: run.builder.compiler(run.builder.top_stage, run.host),
        });
    }

    fn run(self, builder: &Builder<'_>) -> PathBuf {
        let target_compiler = self.compiler;
        if target_compiler.stage == 0 {
            if !target_compiler.is_snapshot(builder) {
                panic!("rustdoc in stage 0 must be snapshot rustdoc");
            }
            return builder.initial_rustc.with_file_name(exe("rustdoc", &target_compiler.host));
        }
        let target = target_compiler.host;
        // Similar to `compile::Assemble`, build with the previous stage's compiler. Otherwise
        // we'd have stageN/bin/rustc and stageN/bin/rustdoc be effectively different stage
        // compilers, which isn't what we want. Rustdoc should be linked in the same way as the
        // rustc compiler it's paired with, so it must be built with the previous stage compiler.
        let build_compiler = builder.compiler(target_compiler.stage - 1, builder.config.build);

        // The presence of `target_compiler` ensures that the necessary libraries (codegen backends,
        // compiler libraries, ...) are built. Rustdoc does not require the presence of any
        // libraries within sysroot_libdir (i.e., rustlib), though doctests may want it (since
        // they'll be linked to those libraries). As such, don't explicitly `ensure` any additional
        // libraries here. The intuition here is that If we've built a compiler, we should be able
        // to build rustdoc.

        let cargo = prepare_tool_cargo(
            builder,
            build_compiler,
            Mode::ToolRustc,
            target,
            "build",
            "src/tools/fuzz-target-generator",
            SourceType::InTree,
            &[],
        );

        builder.info(&format!(
            "Building rustdoc for stage{} ({})",
            target_compiler.stage, target_compiler.host
        ));
        builder.run(&mut cargo.into());

        // Cargo adds a number of paths to the dylib search path on windows, which results in
        // the wrong rustdoc being executed. To avoid the conflicting rustdocs, we name the "tool"
        // rustdoc a different name.
        let tool_rustdoc = builder
            .cargo_out(build_compiler, Mode::ToolRustc, target)
            .join(exe("fuzz-target-generator", &target_compiler.host));

        // don't create a stage0-sysroot/bin directory.
        if target_compiler.stage > 0 {
            let sysroot = builder.sysroot(target_compiler);
            let bindir = sysroot.join("bin");
            t!(fs::create_dir_all(&bindir));
            let bin_rustdoc = bindir.join(exe("fuzz-target-generator", &*target_compiler.host));
            let _ = fs::remove_file(&bin_rustdoc);
            builder.copy(&tool_rustdoc, &bin_rustdoc);
            bin_rustdoc
        } else {
            tool_rustdoc
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Cargo {
    pub compiler: Compiler,
    pub target: Interned<String>,
}

impl Step for Cargo {
    type Output = PathBuf;
    const DEFAULT: bool = true;
    const ONLY_HOSTS: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        let builder = run.builder;
        run.path("src/tools/cargo").default_condition(builder.config.extended)
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Cargo {
            compiler: run.builder.compiler(run.builder.top_stage, run.builder.config.build),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> PathBuf {
        builder
            .ensure(ToolBuild {
                compiler: self.compiler,
                target: self.target,
                tool: "cargo",
                mode: Mode::ToolRustc,
                path: "src/tools/cargo",
                is_optional_tool: false,
                source_type: SourceType::Submodule,
                extra_features: Vec::new(),
            })
            .expect("expected to build -- essential tool")
    }
}

macro_rules! tool_extended {
    (($sel:ident, $builder:ident),
       $($name:ident,
       $toolstate:ident,
       $path:expr,
       $tool_name:expr,
       stable = $stable:expr,
       $(in_tree = $in_tree:expr,)*
       $extra_deps:block;)+) => {
        $(
            #[derive(Debug, Clone, Hash, PartialEq, Eq)]
        pub struct $name {
            pub compiler: Compiler,
            pub target: Interned<String>,
            pub extra_features: Vec<String>,
        }

        impl Step for $name {
            type Output = Option<PathBuf>;
            const DEFAULT: bool = true; // Overwritten below
            const ONLY_HOSTS: bool = true;

            fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
                let builder = run.builder;
                run.path($path).default_condition(
                    builder.config.extended
                        && builder.config.tools.as_ref().map_or(
                            // By default, on nightly/dev enable all tools, else only
                            // build stable tools.
                            $stable || builder.build.unstable_features(),
                            // If `tools` is set, search list for this tool.
                            |tools| {
                                tools.iter().any(|tool| match tool.as_ref() {
                                    "clippy" => $tool_name == "clippy-driver",
                                    x => $tool_name == x,
                            })
                        }),
                )
            }

            fn make_run(run: RunConfig<'_>) {
                run.builder.ensure($name {
                    compiler: run.builder.compiler(run.builder.top_stage, run.builder.config.build),
                    target: run.target,
                    extra_features: Vec::new(),
                });
            }

            #[allow(unused_mut)]
            fn run(mut $sel, $builder: &Builder<'_>) -> Option<PathBuf> {
                $extra_deps
                $builder.ensure(ToolBuild {
                    compiler: $sel.compiler,
                    target: $sel.target,
                    tool: $tool_name,
                    mode: Mode::ToolRustc,
                    path: $path,
                    extra_features: $sel.extra_features,
                    is_optional_tool: true,
                    source_type: if false $(|| $in_tree)* {
                        SourceType::InTree
                    } else {
                        SourceType::Submodule
                    },
                })
            }
        }
        )+
    }
}

// Note: tools need to be also added to `Builder::get_step_descriptions` in `builder.rs`
// to make `./x.py build <tool>` work.
tool_extended!((self, builder),
    Cargofmt, rustfmt, "src/tools/rustfmt", "cargo-fmt", stable=true, {};
    CargoClippy, clippy, "src/tools/clippy", "cargo-clippy", stable=true, in_tree=true, {};
    Clippy, clippy, "src/tools/clippy", "clippy-driver", stable=true, in_tree=true, {};
    Miri, miri, "src/tools/miri", "miri", stable=false, {};
    CargoMiri, miri, "src/tools/miri/cargo-miri", "cargo-miri", stable=false, {};
    Rls, rls, "src/tools/rls", "rls", stable=true, {
        builder.ensure(Clippy {
            compiler: self.compiler,
            target: self.target,
            extra_features: Vec::new(),
        });
        self.extra_features.push("clippy".to_owned());
    };
    Rustfmt, rustfmt, "src/tools/rustfmt", "rustfmt", stable=true, {};
    RustAnalyzer, rust_analyzer, "src/tools/rust-analyzer/crates/rust-analyzer", "rust-analyzer", stable=false, {};
);

impl<'a> Builder<'a> {
    /// Gets a `Command` which is ready to run `tool` in `stage` built for
    /// `host`.
    pub fn tool_cmd(&self, tool: Tool) -> Command {
        let mut cmd = Command::new(self.tool_exe(tool));
        let compiler = self.compiler(0, self.config.build);
        let host = &compiler.host;
        // Prepares the `cmd` provided to be able to run the `compiler` provided.
        //
        // Notably this munges the dynamic library lookup path to point to the
        // right location to run `compiler`.
        let mut lib_paths: Vec<PathBuf> = vec![
            self.build.rustc_snapshot_libdir(),
            self.cargo_out(compiler, Mode::ToolBootstrap, *host).join("deps"),
        ];

        // On MSVC a tool may invoke a C compiler (e.g., compiletest in run-make
        // mode) and that C compiler may need some extra PATH modification. Do
        // so here.
        if compiler.host.contains("msvc") {
            let curpaths = env::var_os("PATH").unwrap_or_default();
            let curpaths = env::split_paths(&curpaths).collect::<Vec<_>>();
            for &(ref k, ref v) in self.cc[&compiler.host].env() {
                if k != "PATH" {
                    continue;
                }
                for path in env::split_paths(v) {
                    if !curpaths.contains(&path) {
                        lib_paths.push(path);
                    }
                }
            }
        }

        add_dylib_path(lib_paths, &mut cmd);
        cmd
    }
}
