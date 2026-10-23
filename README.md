# msfol.rs

A small proof assistant. FOL is the metatheory, infinite axiomatization, maybe MSFOL.

The Dark Souls approach to writing proofs, i.e. "git gud". No goals. No tactics. No unification. Not even models or standard axioms. You write a string of FOL/MSFOL inference rules, and the checker either says success or failure. Nothing more.

The fact that it happily proves a contradiction from a false premise means it's working correctly.

Self-contained Rust, without much in the way of external crates. Comparatively short.
