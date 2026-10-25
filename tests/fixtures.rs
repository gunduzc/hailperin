//! Runs the binary on every example. `examples/*.hai` must pass, printing only `success`;
//! `examples/neg/*.hai` must fail, printing exactly its sibling `.err`.

use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

/// Long enough for the slowest example in a debug build; a hang fails instead of stalling.
const LIMIT: Duration = Duration::from_secs(60);

struct Run {
    code: Option<i32>,
    stdout: String,
    stderr: String,
}

fn run(args: &[&str]) -> Run {
    let mut child = Command::new(env!("CARGO_BIN_EXE_hailperin"))
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    // Read on other threads so a full pipe can't block the child.
    let read = |mut r: Box<dyn Read + Send>| {
        thread::spawn(move || {
            let mut s = String::new();
            r.read_to_string(&mut s).unwrap();
            s
        })
    };
    let out = read(Box::new(child.stdout.take().unwrap()));
    let err = read(Box::new(child.stderr.take().unwrap()));
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if start.elapsed() > LIMIT {
            child.kill().unwrap();
            panic!("{args:?}: still running after {LIMIT:?}");
        }
        thread::sleep(Duration::from_millis(20));
    };
    Run { code: status.code(), stdout: out.join().unwrap(), stderr: err.join().unwrap() }
}

/// The `.hai` files in `dir`, each with what it must print: its sibling of extension `pinned`,
/// or else `success`. Anything else there (other than subdirectories) is an error.
fn cases(dir: &str, pinned: Option<&str>) -> Vec<(PathBuf, String)> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join(dir);
    let mut cases = Vec::new();
    for entry in fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            continue;
        }
        match path.extension().and_then(|e| e.to_str()) {
            Some("hai") => {
                let expected = match pinned {
                    Some(p) => fs::read_to_string(path.with_extension(p))
                        .unwrap_or_else(|_| panic!("{}: no sibling .{p}", path.display())),
                    None => "success\n".to_string(),
                };
                cases.push((path, expected));
            }
            Some(e) if Some(e) == pinned => {
                assert!(path.with_extension("hai").exists(), "{}: no sibling .hai", path.display());
            }
            _ => panic!("{}: unexpected file", path.display()),
        }
    }
    assert!(!cases.is_empty(), "no cases in {}", dir.display());
    cases.sort();
    cases
}

/// Runs every case in `dir`, which must exit with `code` and print what it's pinned to.
fn check_dir(dir: &str, pinned: Option<&str>, code: i32) {
    for (path, expected) in cases(dir, pinned) {
        let r = run(&[path.to_str().unwrap()]);
        assert_eq!(r.code, Some(code), "{}: should exit with {code}, printed:\n{}", path.display(), r.stdout);
        assert_eq!(r.stdout, expected, "{}: output differs", path.display());
        assert!(r.stderr.is_empty(), "{}: wrote to stderr", path.display());
    }
}

#[test]
fn every_example_passes() {
    check_dir("examples", None, 0);
}

#[test]
fn every_negative_fails_as_pinned() {
    check_dir("examples/neg", Some("err"), 1);
}

/// `fmt` output checks like the original, and formatting it again changes nothing.
#[test]
fn fmt_is_stable_and_preserves_meaning() {
    for (path, _) in cases("examples", None) {
        let once = run(&["fmt", path.to_str().unwrap()]);
        assert_eq!(once.code, Some(0), "{}: fmt failed:\n{}", path.display(), once.stdout);
        let tmp = std::env::temp_dir().join(format!("hailperin-fmt-{}", path.file_name().unwrap().to_str().unwrap()));
        fs::write(&tmp, &once.stdout).unwrap();
        // Imports are found next to the file, so check the formatted text from the examples directory.
        let dir = path.parent().unwrap();
        let checked = Command::new(env!("CARGO_BIN_EXE_hailperin"))
            .current_dir(dir)
            .arg("-")
            .stdin(fs::File::open(&tmp).unwrap())
            .output()
            .unwrap();
        assert_eq!(String::from_utf8_lossy(&checked.stdout), "success\n", "{}: formatted text doesn't check", path.display());
        let twice = run(&["fmt", tmp.to_str().unwrap()]);
        assert_eq!(twice.stdout, once.stdout, "{}: fmt is not idempotent", path.display());
        fs::remove_file(&tmp).unwrap();
    }
}

#[test]
fn bad_usage_exits_2() {
    let r = run(&["a.hai", "b.hai"]);
    assert_eq!(r.code, Some(2));
    assert!(r.stderr.starts_with("usage: hailperin [FILE]"), "{}", r.stderr);
    assert!(r.stdout.is_empty());
    let r = run(&["no/such/file.hai"]);
    assert_eq!(r.code, Some(2));
    assert!(r.stderr.starts_with("hailperin: "), "{}", r.stderr);
    assert!(r.stdout.is_empty());
}
