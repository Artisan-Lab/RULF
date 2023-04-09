//! rustbuild, the Rust build system
//!
//! This is the entry point for the build system used to compile the `rustc`
//! compiler. Lots of documentation can be found in the `README.md` file in the
//! parent directory, and otherwise documentation can be found throughout the `build`
//! directory in each respective module.

use std::env;

use bootstrap::{t, Build, Config, Subcommand, VERSION};

fn main() {
    let args = env::args().skip(1).collect::<Vec<_>>();
    let config = Config::parse(&args);

    let mut build_lock;
    let _build_lock_guard;
    if cfg!(any(unix, windows)) {
        build_lock = fd_lock::RwLock::new(t!(std::fs::File::create(config.out.join("lock"))));
        _build_lock_guard = match build_lock.try_write() {
            Ok(lock) => lock,
            err => {
                println!("warning: build directory locked, waiting for lock");
                drop(err);
                t!(build_lock.write())
            }
        };
    } else {
        println!("warning: file locking not supported for target, not locking build directory");
    }

    // check_version warnings are not printed during setup
    let changelog_suggestion =
        if matches!(config.cmd, Subcommand::Setup { .. }) { None } else { check_version(&config) };

    // NOTE: Since `./configure` generates a `config.toml`, distro maintainers will see the
    // changelog warning, not the `x.py setup` message.
    let suggest_setup = !config.config.exists() && !matches!(config.cmd, Subcommand::Setup { .. });
    if suggest_setup {
        println!("warning: you have not made a `config.toml`");
        println!(
            "help: consider running `./x.py setup` or copying `config.toml.example` by running \
            `cp config.toml.example config.toml`"
        );
    } else if let Some(suggestion) = &changelog_suggestion {
        println!("{}", suggestion);
    }

    let pre_commit = config.src.join(".git").join("hooks").join("pre-commit");
    Build::new(config).build();

    if suggest_setup {
        println!("warning: you have not made a `config.toml`");
        println!(
            "help: consider running `./x.py setup` or copying `config.toml.example` by running \
            `cp config.toml.example config.toml`"
        );
    } else if let Some(suggestion) = &changelog_suggestion {
        println!("{}", suggestion);
    }

    // Give a warning if the pre-commit script is in pre-commit and not pre-push.
    // HACK: Since the commit script uses hard links, we can't actually tell if it was installed by x.py setup or not.
    // We could see if it's identical to src/etc/pre-push.sh, but pre-push may have been modified in the meantime.
    // Instead, look for this comment, which is almost certainly not in any custom hook.
    if std::fs::read_to_string(pre_commit).map_or(false, |contents| {
        contents.contains("https://github.com/rust-lang/rust/issues/77620#issuecomment-705144570")
    }) {
        println!(
            "warning: You have the pre-push script installed to .git/hooks/pre-commit. \
                  Consider moving it to .git/hooks/pre-push instead, which runs less often."
        );
    }

    if suggest_setup || changelog_suggestion.is_some() {
        println!("note: this message was printed twice to make it more likely to be seen");
    }
}

fn check_version(config: &Config) -> Option<String> {
    let mut msg = String::new();

    let suggestion = if let Some(seen) = config.changelog_seen {
        if seen != VERSION {
            msg.push_str("warning: there have been changes to x.py since you last updated.\n");
            format!("update `config.toml` to use `changelog-seen = {}` instead", VERSION)
        } else {
            return None;
        }
    } else {
        msg.push_str("warning: x.py has made several changes recently you may want to look at\n");
        format!("add `changelog-seen = {}` at the top of `config.toml`", VERSION)
    };

    msg.push_str("help: consider looking at the changes in `src/bootstrap/CHANGELOG.md`\n");
    msg.push_str("note: to silence this warning, ");
    msg.push_str(&suggestion);

    Some(msg)
}
