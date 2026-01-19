//! Test CLI commands
#[cfg(test)]
use serial_test::serial;

#[cfg(test)]
#[serial]
mod test_cli {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };

    #[test]
    fn test_help() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("--help")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_cli_simple_ta() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_cli_simple_eta() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple_reset.eta")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_cli_simple_tla() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.tla")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_cli_simple_debug() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("--debug")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_cli_log_config() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("--logger-config-file")
            .arg("./tests/resources/log_config.yaml")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
        assert!(std::fs::remove_file("./target/file.log").is_ok());
    }

    #[test]
    #[cfg(feature = "oxidd")]
    #[ignore = "Non-deterministically fails on CI"]
    fn test_oxidd() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--features")
            .arg("oxidd")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .arg("--bdd")
            .arg("oxidd")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_z3() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .arg("--smt-solver")
            .arg("z3")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_cli_acs_mc() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .arg("acs")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_cli_smt_mc() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .arg("smt")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_cli_symbolic_mc() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .arg("zcs")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_cli_short_output() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .arg("-o")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );

        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .arg("--compact-out")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_cli_abort_on_violation() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .arg("-a")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );

        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .arg("--abort-on-violation")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_cvc5() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .arg("--smt-solver")
            .arg("cvc5")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    #[cfg(feature = "cudd")]
    fn test_custom_config() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--features")
            .arg("cudd")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .arg("--config-file")
            .arg("./tests/resources/config.yaml")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    #[cfg(feature = "dot")]
    fn test_visualize_ta_dot_format() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--features")
            .arg("dot")
            .arg("--")
            .arg("visualize")
            .arg("./tests/resources/simple.ta")
            .arg("./test_ta.dot")
            .arg("--output-format")
            .arg("dot")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
        assert!(std::fs::remove_file("./test_ta.dot").is_ok());
    }

    #[test]
    #[cfg(feature = "dot")]
    fn test_visualize_ta_png_format() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--features")
            .arg("dot")
            .arg("--")
            .arg("visualize")
            .arg("./tests/resources/simple.ta")
            .arg("./test_ta.png")
            .arg("--output-format")
            .arg("png")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
        assert!(std::fs::remove_file("./test_ta.png").is_ok());
    }

    #[test]
    #[cfg(feature = "dot")]
    fn test_visualize_ta_svg_format() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--features")
            .arg("dot")
            .arg("--")
            .arg("visualize")
            .arg("./tests/resources/simple.ta")
            .arg("./test_ta.svg")
            .arg("--output-format")
            .arg("svg")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
        assert!(std::fs::remove_file("./test_ta.svg").is_ok());
    }

    #[test]
    fn test_cli_coverability_input() {
        let mut child = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .arg("--mode")
            .arg("coverability")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("Failed to spawn");

        child
            .stdin
            .as_mut()
            .expect("Failed to open stdin")
            // First input nonsense, then input a valid location to be covered, finally no manual initial configuration is given.
            .write_all(b"l\nloc0\nno\n")
            .expect("Write failed.");
        let output = child.wait_with_output().expect("Failed to wait on child");

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_cli_reachability_input() {
        let mut child = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("check")
            .arg("./tests/resources/simple.ta")
            .arg("--mode")
            .arg("reachability")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("Failed to spawn");

        child
            .stdin
            .as_mut()
            .expect("Failed to open stdin")
            // First input nonsense, then input a valid location , then again the same one, then another one
            // Finally also manually input the initial configuration (7 integers: 5 for number of procs in the different locations and two for the variable valuations)
            // Also inject a letter and a negative number when a number >= 0 is required
            .write_all(b"l\nlocEC\nlocEC\nlocAC\n\nyes\n3\n3\n0\n0\n0\n-2\n2\n2\nbad input\n")
            .expect("Write failed.");
        let output = child.wait_with_output().expect("Failed to wait on child");

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
    }

    #[test]
    fn test_translate_to_bymc() {
        let output = Command::new("cargo")
            .arg("run")
            .arg("--")
            .arg("translate")
            .arg("./tests/resources/simple.tla")
            .arg("./test_ta.ta")
            .arg("--output-format")
            .arg("bymc")
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute: {err}"));

        assert!(
            output.status.success(),
            "Failed to execute command: stdout: {}; stderr: {}",
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap()
        );
        assert!(std::fs::remove_file("./test_ta.ta").is_ok());
    }
}
