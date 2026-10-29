//! Runs the binary on every example: `examples/*.hai` must pass, printing only `success`, and
//! so must the files in each directory under `examples`, checked through those nothing imports.
//! Also the command line, files that import each other, and what must agree with the code: the
//! examples and words in SPEC.md, and the editor syntax. What must fail is in `rejections.rs`,
//! as source text.

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

/// What nano's formatter and linter need: `fmt --write` rewrites the file, `--lint` gives
/// `file:line:col: message` and says nothing when the file checks.
#[test]
fn fmt_write_and_lint_serve_an_editor() {
    let dir = std::env::temp_dir();
    let flat = dir.join(format!("hailperin-write-{}.hai", std::process::id()));
    let canonical = fs::read_to_string("examples/socrates.hai").unwrap();
    let unindented: String = canonical.lines().map(|l| format!("{}\n", l.trim_start())).collect();
    fs::write(&flat, &unindented).unwrap();
    let out = run(&["fmt", "--write", flat.to_str().unwrap()]);
    assert_eq!((out.code, out.stdout.as_str()), (Some(0), ""));
    assert_eq!(fs::read_to_string(&flat).unwrap(), run(&["fmt", "examples/socrates.hai"]).stdout);
    assert_eq!(run(&["--lint", flat.to_str().unwrap()]).stdout, "");

    fs::write(&flat, "theorem t:\n  oops\n").unwrap();
    let out = run(&["--lint", flat.to_str().unwrap()]);
    assert_eq!(out.code, Some(1));
    assert!(out.stdout.starts_with(&format!("{}:", flat.display())) && out.stdout.contains(":1: "), "{}", out.stdout);
    // A file that doesn't parse is left as it was.
    let before = fs::read_to_string(&flat).unwrap();
    let out = run(&["fmt", "--write", flat.to_str().unwrap()]);
    if out.code != Some(0) {
        assert_eq!(fs::read_to_string(&flat).unwrap(), before);
    }
    fs::remove_file(&flat).unwrap();
    assert_eq!(run(&["fmt", "--write", "-"]).code, Some(2));
}

#[test]
fn help_is_an_answer() {
    for flag in ["--help", "-h"] {
        let r = run(&[flag]);
        assert_eq!(r.code, Some(0));
        assert!(r.stdout.starts_with("usage: hailperin [FILE]"), "{}", r.stdout);
        assert!(r.stderr.is_empty());
    }
}

#[test]
fn a_missing_file_is_named() {
    let r = run(&["no_such_file.hai"]);
    assert_eq!(r.code, Some(2));
    assert_eq!(r.stderr, "hailperin: `no_such_file.hai` doesn't exist\n");
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

/// Writes `files` into a fresh directory and runs the binary on `main` there.
fn run_files(name: &str, files: &[(&str, &str)], main: &str) -> String {
    let dir = std::env::temp_dir().join(format!("hailperin-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    for (path, src) in files {
        let path = dir.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, src).unwrap();
    }
    let out = run(&[dir.join(main).to_str().unwrap()]).stdout;
    fs::remove_dir_all(&dir).unwrap();
    out
}

#[test]
fn a_file_sees_only_what_it_imports() {
    // `b` uses `X` from `a` without importing it: refused alike alone and after `a` is loaded.
    let files = [
        ("a.hai", "predicate P x\ndefine X x = P x and P x\n"),
        ("b.hai", "theorem tb:\n  variable y\n  assume h: X y\n  therefore forall y. X y -> X y\n"),
        ("c.hai", "import a\nimport b\n"),
    ];
    assert!(run_files("sees", &files, "b.hai").contains("`X` is not declared"));
    assert_eq!(run_files("sees", &files, "c.hai"), "failure: b.hai: line 3: tb: `X` is from a.hai, which this file doesn't import\n");
    // A theorem's predicate may share a name with a predicate it doesn't see, but two globals
    // never share one, and the clash names the other file.
    let files = [
        ("a.hai", "predicate P x\n"),
        ("b.hai", "theorem tb:\n  predicate P x\n  variable y\n  assume h: P y\n  therefore forall y. P y -> P y\n"),
        ("c.hai", "import a\nimport b\n"),
        ("d.hai", "predicate P\n"),
        ("e.hai", "import a\nimport d\n"),
    ];
    assert_eq!(run_files("sees", &files, "c.hai"), "success\n");
    assert_eq!(run_files("sees", &files, "e.hai"), "failure: d.hai: line 1: `P` is already declared in a.hai\n");
}

#[test]
fn messages_fold_only_what_the_file_sees() {
    // `fb` never imports `fa`, so its messages never print `Two`, whoever loads `fa` first.
    let files = [
        ("p.hai", "predicate P x\n"),
        ("fa.hai", "import p\ndefine Two x = P x and P x\n"),
        ("fb.hai", "import p\ntheorem tb:\n  variable y\n  assume h: P y and P y\n  k: P y by reit h\n  therefore forall y. (P y and P y) -> P y\n"),
        ("fc.hai", "import fa\nimport fb\n"),
    ];
    assert_eq!(run_files("folds", &files, "fb.hai"), "failure: line 5: tb: this gives P y and P y, not P y\n");
    assert_eq!(run_files("folds", &files, "fc.hai"), "failure: fb.hai: line 5: tb: this gives P y and P y, not P y\n");
}

#[test]
fn an_imported_file_is_named_from_the_checked_file() {
    // `sub/s` imports `a` as `../a`, but from `top` it is `a.hai`.
    let files = [
        ("a.hai", "predicate P x\ntheorem bad:\n  variable y\n  assume h: P y\n  k: P y by reit q\n  therefore forall y. P y -> P y\n"),
        ("sub/s.hai", "import ../a\n"),
        ("top.hai", "import sub/s\n"),
    ];
    assert_eq!(run_files("names", &files, "top.hai"), "failure: a.hai: line 5: bad: `q` is not a line or a theorem here\n");
}

/// The `.hai` files in each directory under `examples`, with those no other file there imports.
fn subdirectories() -> Vec<(Vec<PathBuf>, Vec<PathBuf>)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut out = Vec::new();
    for entry in fs::read_dir(&root).unwrap() {
        let dir = entry.unwrap().path();
        if !dir.is_dir() {
            continue;
        }
        let mut files: Vec<PathBuf> = fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|e| e == "hai")).collect();
        files.sort();
        let imported: Vec<String> = files
            .iter()
            .flat_map(|f| fs::read_to_string(f).unwrap().lines().filter_map(|l| l.strip_prefix("import ").map(|p| p.trim().rsplit('/').next().unwrap().to_string())).collect::<Vec<_>>())
            .collect();
        let leaves = files.iter().filter(|f| !imported.contains(&f.file_stem().unwrap().to_string_lossy().into_owned())).cloned().collect();
        out.push((files, leaves));
    }
    out
}

/// A file in a subdirectory is checked as an import of the files nothing there imports, and
/// formatting it twice gives the same text.
#[test]
fn every_example_in_a_subdirectory_passes() {
    for (files, leaves) in subdirectories() {
        assert!(!leaves.is_empty(), "every file in {} is imported by another", files[0].parent().unwrap().display());
        for leaf in &leaves {
            let r = run(&[leaf.to_str().unwrap()]);
            assert_eq!(r.stdout, "success\n", "{}", leaf.display());
        }
        for f in &files {
            let once = run(&["fmt", f.to_str().unwrap()]);
            let tmp = std::env::temp_dir().join(format!("hailperin-sub-{}", f.file_name().unwrap().to_str().unwrap()));
            fs::write(&tmp, &once.stdout).unwrap();
            assert_eq!(run(&["fmt", tmp.to_str().unwrap()]).stdout, once.stdout, "{}: fmt is not idempotent", f.display());
            fs::remove_file(&tmp).unwrap();
        }
    }
}

/// The editor syntax highlights every keyword and rule of the language, and nothing else.
#[test]
fn the_editor_syntax_knows_the_words() {
    let syntax = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("editors/hailperin.sublime-syntax")).unwrap();
    let mut listed: Vec<&str> = syntax.split("\\b(").skip(1).flat_map(|s| s.split(")\\b").next().unwrap().split('|')).collect();
    let mut words: Vec<&str> = hailperin::lexer::KEYWORDS.iter().map(|(w, _)| *w).chain(hailperin::check::RULES.iter().copied()).collect();
    listed.sort_unstable();
    words.sort_unstable();
    assert_eq!(listed, words);
}

/// Every editor's highlighting knows every keyword and rule.
#[test]
fn every_editor_knows_the_words() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("editors");
    let files = ["vim/syntax/hailperin.vim", "hailperin.nanorc", "vscode/syntaxes/hailperin.tmLanguage.json", "tree-sitter-hailperin/grammar.js"];
    let words: Vec<&str> = hailperin::lexer::KEYWORDS.iter().map(|(w, _)| *w).chain(hailperin::check::RULES.iter().copied()).collect();
    for file in files {
        let text = fs::read_to_string(dir.join(file)).unwrap();
        let found: Vec<&str> = text.split(|c: char| !c.is_ascii_alphanumeric() && c != '_').collect();
        for word in &words {
            assert!(found.contains(word), "{file} doesn't know `{word}`");
        }
    }
}

/// `explain` shows the lines that checked before a failure, then the failure.
#[test]
fn explain_shows_what_checked_before_a_failure() {
    let src = "predicate A\npredicate B\ntheorem t:\n  assume a: A\n  k: A by reit a\n  j: B by reit a\n  therefore A -> B\n";
    let tmp = std::env::temp_dir().join(format!("hailperin-explain-{}.hai", std::process::id()));
    fs::write(&tmp, src).unwrap();
    let r = run(&["explain", tmp.to_str().unwrap()]);
    fs::remove_file(&tmp).unwrap();
    assert_eq!(r.code, Some(1));
    assert_eq!(r.stdout, "theorem t\n  a: [ | a] A\n  k: [ | a] A\nfailure: line 6: t: this gives A, not B\n");
}

/// Every complete example in SPEC.md checks: a block that starts like a file, has a theorem,
/// and leaves nothing out with `...`.
#[test]
fn spec_examples_check() {
    let spec = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("SPEC.md")).unwrap();
    let mut checked = 0;
    for block in spec.split("```").skip(1).step_by(2) {
        let code = block.split_once('\n').map_or("", |(_, c)| c);
        let starts = ["predicate ", "define ", "import ", "theorem ", "--"].iter().any(|k| code.starts_with(k));
        if !starts || !code.lines().any(|l| l.starts_with("theorem ")) || code.contains("...") {
            continue;
        }
        if let Err(e) = hailperin::verify(code) {
            panic!("a SPEC.md example fails: {e}\n{code}");
        }
        checked += 1;
    }
    assert!(checked >= 2, "only {checked} complete examples found in SPEC.md");
}

/// SPEC.md has a row for every rule and mentions every flag `--help` lists.
#[test]
fn spec_knows_every_rule_and_flag() {
    let spec = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("SPEC.md")).unwrap();
    for rule in hailperin::check::RULES {
        assert!(spec.contains(&format!("| `{rule}")), "SPEC.md has no row for `{rule}`");
    }
    let help = run(&["--help"]).stdout;
    for flag in help.split_whitespace().filter(|w| w.starts_with("--")) {
        assert!(spec.contains(&format!("`{flag}")), "SPEC.md doesn't mention `{flag}`");
    }
}
