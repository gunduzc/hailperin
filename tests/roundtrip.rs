//! What messages print is the formula they mean: random formulas, printed by `explain`, restate
//! the original by `reit`, which compares with definitions unfolded.

use std::path::Path;

const DECLARATIONS: &str = "predicate P x\npredicate Q\npredicate R x y\n\
                            define Sw x y = R y x and P x\ndefine Alt A x = A or P x\n\
                            define Both A B = A and not B\ndefine Mix x A y = (A -> R x y) and P y\n";

/// A formula of depth at most `d` over the variables `bound`, from the generator's state.
fn formula(d: usize, bound: &mut Vec<String>, next: &mut impl FnMut(usize) -> usize) -> String {
    let var = |next: &mut dyn FnMut(usize) -> usize, bound: &[String]| bound[next(bound.len())].clone();
    if d == 0 || next(4) == 0 {
        if bound.is_empty() {
            return ["Q", "absurd"][next(2)].to_string();
        }
        return match next(if d == 0 { 3 } else { 6 }) {
            0 => format!("P {}", var(next, bound)),
            1 => format!("R {} {}", var(next, bound), var(next, bound)),
            2 => format!("Sw {} {}", var(next, bound), var(next, bound)),
            3 => format!("Alt ({}) {}", formula(d - 1, bound, next), var(next, bound)),
            4 => format!("Both ({}) ({})", formula(d - 1, bound, next), formula(d - 1, bound, next)),
            _ => format!("Mix {} ({}) {}", var(next, bound), formula(d - 1, bound, next), var(next, bound)),
        };
    }
    match next(6) {
        0 => format!("not ({})", formula(d - 1, bound, next)),
        k @ (1 | 2) => {
            let v = format!("v{}", bound.len() + 1);
            bound.push(v.clone());
            let body = formula(d - 1, bound, next);
            bound.pop();
            format!("({} {v}. {body})", if k == 1 { "forall" } else { "exists" })
        }
        k => format!("({}) {} ({})", formula(d - 1, bound, next), ["and", "or", "->"][k - 3], formula(d - 1, bound, next)),
    }
}

#[test]
fn printed_formulas_mean_what_they_print() {
    let mut state: u64 = 1;
    let mut next = |n: usize| {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        ((state >> 33) as usize) % n
    };
    for _ in 0..300 {
        let depth = 2 + next(4);
        let f = formula(depth, &mut Vec::new(), &mut next);
        let src = format!("{DECLARATIONS}theorem t:\n  assume h: {f}\n  therefore ({f}) -> ({f})\n");
        let (lines, checked) = hailperin::explain_in(&src, Path::new("."), None);
        checked.unwrap_or_else(|e| panic!("{f}: {e}"));
        let printed = lines.iter().find_map(|l| l.strip_prefix("  h: ")).and_then(|l| l.split_once("] ")).map(|(_, p)| p.to_string()).unwrap();
        let again = format!("{DECLARATIONS}theorem t:\n  assume h: {f}\n  k: {printed} by reit h\n  therefore ({f}) -> ({printed})\n");
        if let Err(e) = hailperin::verify(&again) {
            panic!("{f}\nprinted as {printed}\n{e}");
        }
    }
}
