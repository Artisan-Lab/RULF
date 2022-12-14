use std::path::Path;
use std::process::Command;

/// Uses the `llvm-bolt` binary to instrument the binary/library at the given `path` with BOLT.
/// When the instrumented artifact is executed, it will generate BOLT profiles into
/// `/tmp/prof.fdata.<pid>.fdata`.
pub fn instrument_with_bolt_inplace(path: &Path) {
    let dir = std::env::temp_dir();
    let instrumented_path = dir.join("instrumented.so");

    let status = Command::new("llvm-bolt")
        .arg("-instrument")
        .arg(&path)
        // Make sure that each process will write its profiles into a separate file
        .arg("--instrumentation-file-append-pid")
        .arg("-o")
        .arg(&instrumented_path)
        .status()
        .expect("Could not instrument artifact using BOLT");

    if !status.success() {
        panic!("Could not instrument {} with BOLT, exit code {:?}", path.display(), status.code());
    }

    std::fs::copy(&instrumented_path, path).expect("Cannot copy instrumented artifact");
    std::fs::remove_file(instrumented_path).expect("Cannot delete instrumented artifact");
}

/// Uses the `llvm-bolt` binary to optimize the binary/library at the given `path` with BOLT,
/// using merged profiles from `profile_path`.
///
/// The recorded profiles have to be merged using the `merge-fdata` tool from LLVM and the merged
/// profile path should be then passed to this function.
pub fn optimize_library_with_bolt_inplace(path: &Path, profile_path: &Path) {
    let dir = std::env::temp_dir();
    let optimized_path = dir.join("optimized.so");

    let status = Command::new("llvm-bolt")
        .arg(&path)
        .arg("-data")
        .arg(&profile_path)
        .arg("-o")
        .arg(&optimized_path)
        // Reorder basic blocks within functions
        .arg("-reorder-blocks=ext-tsp")
        // Reorder functions within the binary
        .arg("-reorder-functions=hfsort+")
        // Split function code into hot and code regions
        .arg("-split-functions=2")
        // Split as many basic blocks as possible
        .arg("-split-all-cold")
        // Move jump tables to a separate section
        .arg("-jump-tables=move")
        // Use GNU_STACK program header for new segment (workaround for issues with strip/objcopy)
        .arg("-use-gnu-stack")
        // Fold functions with identical code
        .arg("-icf=1")
        // Update DWARF debug info in the final binary
        .arg("-update-debug-sections")
        // Print optimization statistics
        .arg("-dyno-stats")
        .status()
        .expect("Could not optimize artifact using BOLT");

    if !status.success() {
        panic!("Could not optimize {} with BOLT, exit code {:?}", path.display(), status.code());
    }

    std::fs::copy(&optimized_path, path).expect("Cannot copy optimized artifact");
    std::fs::remove_file(optimized_path).expect("Cannot delete optimized artifact");
}
