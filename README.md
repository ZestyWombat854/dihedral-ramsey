# Dihedral Ramsey numbers of the alternating 3-path

This repository records a proof and evidence package for

> R_dih(P3alt, K_b) = R_cyc(P3alt, K_b) = 2b − 1 for all b,

the a = 3 slice of Conjecture 4.9 (Damnjanovic–Dordevic,
arXiv:2607.06817) and Conjecture 4.23 (Basic–Damnjanovic–Stevanovic–
Stosic, arXiv:2604.16188).

## Status

- The proof resolves both conjectures at a = 3 only. The full
  conjectures (a >= 4) remain open.
- The lower bound and Dih(3) = Sym(3) are formally verified in Lean 4.
- The upper bound rests on a citation chain through Chvatal 1977 and is
  not formalized.
- No human peer review has been obtained.

## Contents

| File | Description |
|---|---|
| `theorem-b-preprint.pdf` | Typeset preprint (LaTeX-compiled, 6 pages). |
| `theorem-b-preprint.tex` | LaTeX source for the preprint. |
| `theorem-b-preprint.md` | Markdown version of the same preprint. |
| `TheoremB.lean` | Lean 4 proof (core only, no mathlib, no imports) of the lower bound for every b >= 1, plus Dih(3) = Sym(3). |
| `verify_theorem_b.py` | Python checker (stdlib only): lower bounds for b = 2..8, both bounds at b = 3, plus Corollary 5's orbit-equality premise. |
| `verify_theorem_b_result.json` | The Python checker's full output. |
| `VERIFICATION_MAP.md` | Claim-by-claim map: which preprint claims are Lean-proved, Python-verified, or citation-only. Includes SHA-256 hashes, trust boundaries, and what is not verified. |
| `lean-toolchain` | Toolchain pin (`leanprover/lean4:v4.12.0`) so `elan` auto-selects the right Lean in a clone. |
| `LICENSE` | MIT. |

## Verification

See `VERIFICATION_MAP.md` for the full claim-by-claim breakdown.

In summary: the lower bound is machine-verified for every b (Lean) and
for b = 2..8 (Python). At b = 3, both bounds are machine-verified
(Python, all 1,024 colorings of K_5). The upper bound for general b is a
citation, not a computation — it rests on Chvatal 1977 via
arXiv:2607.06817's Theorem 4.13.

## Usage

Python checker:

    python3 verify_theorem_b.py [output.json]

Exits 0 iff every check passes. No dependencies beyond Python 3.

Lean proof:

    lean TheoremB.lean

Requires Lean 4 toolchain v4.12.0 — with `elan` installed, the repo's
`lean-toolchain` file resolves it automatically when run from a clone.
Clean exit = every theorem kernel-checked. Expected output: five
`#print axioms` lines listing only the three standard axioms.

## AI assistance

Claude (Anthropic) produced the proof, the verification scripts, and the
Lean formalization autonomously. Human direction was limited to
initiation and operational supervision.
