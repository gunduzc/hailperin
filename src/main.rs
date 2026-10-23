use std::io::Read;
use std::path::Path;
use std::process::exit;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (src, path) = match args.as_slice() {
        [_] => (read_stdin(), None),
        [_, path] if path == "-" => (read_stdin(), None),
        [_, path] => (std::fs::read_to_string(path), Some(Path::new(path))),
        _ => {
            eprintln!("usage: hailperin [FILE]");
            exit(2);
        }
    };
    let src = src.unwrap_or_else(|e| {
        eprintln!("hailperin: {e}");
        exit(2);
    });

    // Imports are found next to the file, or in the current directory for standard input.
    let dir = path.and_then(Path::parent).filter(|d| !d.as_os_str().is_empty()).unwrap_or(Path::new("."));
    match hailperin::verify_in(&src, dir, path, &mut |_, _| {}) {
        Ok(()) => println!("success"),
        Err(e) => {
            println!("failure: {e}");
            exit(1);
        }
    }
}

fn read_stdin() -> std::io::Result<String> {
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).map(|_| s)
}
