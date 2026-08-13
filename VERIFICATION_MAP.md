# Verification map

How each claim in the preprint is checked, and by what.

Source: `theorem-b-preprint.tex` (LaTeX, compiled to PDF), SHA-256
`677ca6a75811de47092cd32170a06934da21fd3850c599212eb6537438ded9bb`.
Markdown version: `theorem-b-preprint.md`, SHA-256
`01fe1655ab4e4fb0c03ecace41ef90cbcc62c14f7b582cea4b94929d474a9b36`.

Statuses: **Lean-proved** = kernel-checked theorem in `TheoremB.lean`;
**Python-verified** = checked by `verify_theorem_b.py` for finite b;
**citation** = rests on a referenced result, not on a computation or
formal proof in this package.

## Core claims

| Preprint section | Claim | Verification | Status |
|---|---|---|---|
| §4, Lemma 1 | K_b-embeddability is group-independent | Lean: `noMonoCopy_completeGraph_reduce` | **Lean-proved** |
| §5, Lemma 2 | Block-partition lower bound R >= 1 + (a-1)(b-1) | Lean: `lemma2_blockWitness` (the a = 3 specialization, arbitrary groups on both sides); Python: b=2..8 | **Lean-proved** (a = 3, all b) + **Python-verified** (b=2..8); the general-a statement is paper-only |
| §6, Lemma 3 | Dih(3) = Sym(3) | Lean: `lemma3_dih3_eq_sym3`; Python: generator closure | **Lean-proved** + **Python-verified** |
| §7, Theorem 4 | R_dih(P3alt, K_b) = 2b-1 | Upper bound: **citation** (Chvatal 1977 via DD26 Thm 4.13). Lower bound: **Lean-proved** (`theoremB_lowerBound`, every b >= 1) |
| §8, Corollary 5 | R_cyc(P3alt, K_b) = 2b-1 | Orbit equality: **Python-verified** (`corollary5_orbit_check`: Cyc(3)-orbit = Sym(3)-orbit = the 3 center-labelings; K_b orbits singleton). Proposition 2.4 application: **citation** |
| §9, SAT table | 2b-1 matches for b=2..7 | DRAT-certified (external, not in this package) | **externally verified** |
| §9, b=3 exact | R_dih(P3alt, K_3) = 5 | Python: all 1,024 colorings of K_5 | **Python-verified** (both bounds) |

## What is not verified in this package

- **The upper bound for general b.** It rests on Chvatal's 1977
  tree-complete-graph theorem, cited second-hand via DD26's Theorem 4.13.
  The 1977 original was not consulted.
- **Proposition 2.1 and 2.4 from DD26.** Used in the Sym-collapse step
  (Theorem 4) and the cyclic corollary (Corollary 5). Cited, not
  reproved.
- **The SAT/DRAT certificates.** Produced during adversarial review of
  the internal write-up. Not included in this package; the Python checker
  independently covers b=2..8 lower bounds and b=3 both bounds.

## Lean trust boundary

Axioms (printed by the file's own `#print axioms` calls):
`propext`, `Classical.choice`, `Quot.sound` — the three standard
Lean 4 / Mathlib foundational axioms.

Prohibited and confirmed absent: `sorry`, `admit`, custom `axiom`
declarations, `native_decide`, unsafe proof construction.

File: `TheoremB.lean` (standalone, no mathlib, no imports), SHA-256
`39dc7cadf7487aee1beb60d487ddf69023ccc865646f5cb625dfc36765de2edc`.

## Python checker trust boundary

File: `verify_theorem_b.py` (stdlib only, no dependencies), SHA-256
`1ddc3ae7863252934538e0fb70e3258a295365412495d7827e35b63c7599088d`.

The script builds Dih(3) by generator closure from sigma and rho — it
does not assume the collapse it is checking. Five self-tests confirm the
detector fires on planted patterns and respects ordered semantics
(increasing-injection definition from DD26 §2). It also verifies
Corollary 5's orbit-equality premise from definitions (Cyc(3) built by
closure from sigma alone); the Proposition 2.4 application itself remains
a citation.
