use std::process::Command;

/// Run a single Lean script via `lake env lean --run` and return the content of its output file.
///
/// `extra_args` are passed between the script name and the output path (e.g. a step count).
pub fn run_lean_script(script: &str, extra_args: &[&str], output_path: &str) -> String {
    let backend_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let tests_dir = backend_dir.join("tests").join("fixtures");
    let clean_root = backend_dir.parent().unwrap().parent().unwrap();
    std::fs::create_dir_all(tests_dir.join("output")).unwrap();
    let _ = std::fs::remove_file(tests_dir.join(output_path));

    let lean_file = tests_dir.join(script);
    let output_file = tests_dir.join(output_path);

    let mut cmd = Command::new("lake");
    cmd.args(["env", "lean", "--run"]);
    cmd.arg(&lean_file);
    for arg in extra_args {
        cmd.arg(arg);
    }
    cmd.arg(&output_file);
    cmd.current_dir(clean_root);

    let result = cmd.output().expect("Failed to run lake");
    assert!(
        result.status.success(),
        "Lean script '{}' failed\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
        script,
        result.status,
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );

    std::fs::read_to_string(&output_file)
        .unwrap_or_else(|e| panic!("Failed to read output '{}': {}", output_path, e))
}
