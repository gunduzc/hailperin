use std::io::Read;
use std::path::Path;
use std::process::exit;

const USAGE: &str = "usage: hailperin [FILE]          check a file (`-` or nothing: standard input)
       hailperin --lint FILE     check a file, a failure as `FILE:LINE:1: message` and silence on success
       hailperin fmt [OPTIONS] FILE
                                 print the file in its canonical layout
           --write               rewrite the file instead, unless it fails
           --indent N            spaces per level (2)
           --continue N          spaces a continued line goes past its item (4)
           --width N             break lines longer than N (never)
           --by pad|space        `by` and `=` in one column per group, or after one space (pad)
           --scope segment|theorem
                                 a column per run of steps, or per theorem (segment)
       hailperin explain FILE    print each line's scope and formula";

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let argv: Vec<&str> = args.iter().map(String::as_str).collect();
    let mut opts = hailperin::fmt::Options::default();
    let mut write = false;
    let (mode, file) = match argv.as_slice() {
        [_] => ("check", None),
        // Asked for, the usage is the answer: on standard output, and no error.
        [_, "--help" | "-h"] => {
            println!("{USAGE}");
            return;
        }
        [_, "fmt", rest @ ..] => {
            let mut file = None;
            let mut i = 0;
            while i < rest.len() {
                if rest[i] == "--write" {
                    write = true;
                    i += 1;
                    continue;
                }
                let value = rest.get(i + 1).copied();
                match (rest[i], value) {
                    ("--indent", Some(n)) => match n.parse() {
                        Ok(n) => opts.indent = n,
                        Err(_) => usage(),
                    },
                    ("--continue", Some(n)) => match n.parse() {
                        Ok(n) => opts.continuation = n,
                        Err(_) => usage(),
                    },
                    ("--width", Some(n)) => match n.parse() {
                        Ok(n) => opts.width = Some(n),
                        Err(_) => usage(),
                    },
                    ("--by", Some("pad")) => opts.pad = true,
                    ("--by", Some("space")) => opts.pad = false,
                    ("--scope", Some("segment")) => opts.theorem_wide = false,
                    ("--scope", Some("theorem")) => opts.theorem_wide = true,
                    (f, _) if !f.starts_with("--") && file.is_none() => {
                        file = Some(f);
                        i += 1;
                        continue;
                    }
                    _ => usage(),
                }
                i += 2;
            }
            match file {
                Some(f) if !(write && f == "-") => ("fmt", Some(f)),
                _ => usage(),
            }
        }
        [_, "explain", f] => ("explain", Some(*f)),
        [_, "--lint", f] => ("lint", Some(*f)),
        [_, f] if !matches!(*f, "fmt" | "explain") => ("check", Some(*f)),
        _ => usage(),
    };
    let path = file.filter(|f| *f != "-").map(Path::new);
    let src = match path {
        Some(p) => std::fs::read_to_string(p),
        None => read_stdin(),
    };
    let src = src.unwrap_or_else(|e| {
        match (path, e.kind()) {
            (Some(p), std::io::ErrorKind::NotFound) => eprintln!("hailperin: `{}` doesn't exist", p.display()),
            (Some(p), _) => eprintln!("hailperin: can't read `{}`: {e}", p.display()),
            (None, _) => eprintln!("hailperin: can't read standard input: {e}"),
        }
        exit(2);
    });
    // Imports are found next to the file, or in the current directory for standard input.
    let dir = path.and_then(Path::parent).filter(|d| !d.as_os_str().is_empty()).unwrap_or(Path::new("."));
    let result = match mode {
        "fmt" => hailperin::fmt::format(&src, &opts).map(|out| match path {
            Some(p) if write => {
                if out != src {
                    std::fs::write(p, out).unwrap_or_else(|e| {
                        eprintln!("hailperin: can't write `{}`: {e}", p.display());
                        exit(2);
                    });
                }
            }
            _ => print!("{out}"),
        }),
        // The lines that checked, even when a later one fails.
        "explain" => {
            let (lines, checked) = hailperin::explain_in(&src, dir, path);
            for l in lines {
                println!("{l}");
            }
            checked
        }
        "lint" => hailperin::verify_in(&src, dir, path, &mut |_, _| {}),
        _ => hailperin::verify_in(&src, dir, path, &mut |_, _| {}).map(|()| println!("success")),
    };
    if let (Err(e), "lint") = (&result, mode) {
        // The line is that of the checked file; an error in an import is put at the top, with its own line in the message.
        let (line, msg) = match &e.file {
            None => (e.line, e.msg.clone()),
            Some(_) => (1, e.to_string()),
        };
        println!("{}:{line}:1: {msg}", path.map_or("-".into(), |p| p.display().to_string()));
        exit(1);
    }
    if mode == "lint" {
        return;
    }
    if let Err(e) = result {
        println!("failure: {e}");
        exit(1);
    }
}

fn usage() -> ! {
    eprintln!("{USAGE}");
    exit(2);
}

fn read_stdin() -> std::io::Result<String> {
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).map(|_| s)
}
