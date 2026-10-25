use std::io::Read;
use std::path::Path;
use std::process::exit;

const USAGE: &str = "usage: hailperin [FILE]          check a file (`-` or nothing: standard input)
       hailperin fmt FILE        print the file with one indentation level per block
       hailperin explain FILE    print each line's scope and formula, and what each theorem rests on";

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (mode, file) = match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        [_] => ("check", None),
        [_, "fmt", f] => ("fmt", Some(*f)),
        [_, "explain", f] => ("explain", Some(*f)),
        [_, f] if !matches!(*f, "fmt" | "explain" | "--help" | "-h") => ("check", Some(*f)),
        _ => {
            eprintln!("{USAGE}");
            exit(2);
        }
    };
    let path = file.filter(|f| *f != "-").map(Path::new);
    let src = match path {
        Some(p) => std::fs::read_to_string(p),
        None => read_stdin(),
    };
    let src = src.unwrap_or_else(|e| {
        eprintln!("hailperin: {e}");
        exit(2);
    });
    // Imports are found next to the file, or in the current directory for standard input.
    let dir = path.and_then(Path::parent).filter(|d| !d.as_os_str().is_empty()).unwrap_or(Path::new("."));
    let result = match mode {
        "fmt" => hailperin::fmt::format(&src).map(|out| print!("{out}")),
        "explain" => hailperin::explain_in(&src, dir, path).map(|lines| {
            for l in lines {
                println!("{l}");
            }
        }),
        _ => hailperin::verify_in(&src, dir, path, &mut |_, _| {}).map(|()| println!("success")),
    };
    if let Err(e) = result {
        println!("failure: {e}");
        exit(1);
    }
}

fn read_stdin() -> std::io::Result<String> {
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).map(|_| s)
}
