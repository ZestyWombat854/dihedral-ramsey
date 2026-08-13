# SAT/DRAT certificates for b = 2..7 (regenerated)

Machine-checkable evidence for the preprint's §9 claim: direct SAT
computation on the **raw** dihedral encoding — Dih(3) and Dih(b) encoded
as-is, no Sym-collapse — gives SAT at n = 2b−2 and UNSAT at n = 2b−1 for
every b = 2..7, matching R_dih(P3alt, K_b) = 2b−1 exactly.

## Provenance, stated plainly

These are **regenerated** certificates (fresh solver runs, 2026-08-13),
not the originals. The producing run's disk-discipline policy deleted its
proof files after verification, so the original certificates no longer
exist. Same instances, same encoding, same tooling (kissat 4.0.4,
drat-trim); a DRAT certificate is checkable on its own terms regardless of
when it was produced.

## Files, per b in 2..7

| File | What it is |
|---|---|
| `b{b}_n{2b-2}.cnf` | DIMACS instance at the witness size (SAT expected) |
| `b{b}_n{2b-2}.witness.txt` | Decoded 2-coloring + raw solver model; header records the independent embedding re-check |
| `b{b}_n{2b-1}.cnf` | DIMACS instance at the Ramsey size (UNSAT expected) |
| `b{b}_n{2b-1}.drat` | DRAT proof of unsatisfiability (ASCII) |
| `b{b}_n{*}.kissat.log`, `b{b}_n{*}.drat-trim.log` | Full solver and checker outputs |
| `results.json` | Summary of all twelve legs |

## Encoding

One Boolean variable x_{u,v} per edge {u,v} of K_n (u < v), true iff the
edge has colour 2 ([DD26] §2.3, eqs. (1)–(2)). For every increasing
injection ψ and every φ ∈ Dih(3): a clause of positive literals over the
image edges of P3alt (forbids an all-colour-1 copy). For every increasing
injection ψ and every φ ∈ Dih(b): a clause of negative literals over the
image edges of K_b (forbids an all-colour-2 copy). Group elements are the
distinct permutations of each dihedral group, built by generator closure —
2b of them for b ≥ 3; for b = 2 the four closed-form words collapse to the
2 distinct permutations of a 2-element set, so the b = 2 instances carry
C(n,2)·2 clauses on that side rather than the duplicate-counting
C(n,2)·4.

## Re-checking

Each UNSAT leg, with any drat-trim build:

    drat-trim b7_n13.cnf b7_n13.drat

Expected: `s VERIFIED`. Each SAT leg's `witness.txt` states the decoded
coloring; the independent re-check (no Dih(3)-embedded P3alt in colour 1,
no Dih(b)-embedded K_b in colour 2) is reproducible with
`verify_theorem_b.py`'s `gamma_embedded` on the decoded edge sets.

## Regenerating from scratch

    python3 make_theorem_b_certificates.py sat-out/

(from the repository root; needs `kissat` and `drat-trim` on PATH, or
`KISSAT`/`DRATTRIM` environment variables pointing at the binaries).
The generator asserts the clause count C(n,3)·|Dih(3)| + C(n,b)·|Dih(b)|
for every instance before writing it.
