# unico-lean-proofs

Machine-verified Lean 4 proofs produced by the **UNICO / NOUS** project — an
autonomous discovery-and-certification pipeline (statement selection → numeric
falsification → multi-engine proof search → local kernel verification) run by
Solarys431.

Every file in this repository compiles with the Lean 4 kernel: no `sorry`,
no additional axioms. Trust level is stated per file (pure kernel vs
kernel + compiler for `native_decide`).

## Proofs

| File | Statement | Status | Author of proof |
|------|-----------|--------|-----------------|
| [`UnicoProofs/Erdos1064K2.lean`](UnicoProofs/Erdos1064K2.lean) | **Erdős Problem 1064, variant k2** — there are infinitely many `n` with `φ(n) < φ(n − φ(n))` (solved informally by Grytczuk–Luca–Wójtowicz, 2001; no `formal_proof` recorded in [formal-conjectures](https://github.com/google-deepmind/formal-conjectures); an equivalent independent proof appeared in [rjwalters/lean-genius](https://github.com/rjwalters/lean-genius) on July 8, 2026 — see the prior-art note in the file) | ✅ pure kernel | Aristotle (Harmonic AI) — see disclosure in file |

## How to verify

```bash
# requires elan (https://leanprover-community.github.io/get_started.html)
lake exe cache get   # downloads precompiled mathlib
lake build           # kernel-checks every proof — should end with no errors
```

Toolchain: `leanprover/lean4:v4.32.0-rc1` · mathlib `v4.32.0-rc1`.
CI runs the same build on every push.

## AI disclosure

Proofs in this repository are produced with AI assistance (Aristotle by
Harmonic, Codex by OpenAI, Claude by Anthropic) and are labeled
**LLM-generated**, with per-file provenance notes. The Lean kernel is the
sole arbiter of correctness: nothing is published here unless it compiles.

## License

Apache 2.0 — see [LICENSE](LICENSE).
