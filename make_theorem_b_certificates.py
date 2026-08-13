#!/usr/bin/env python3
"""
make_theorem_b_certificates.py — regenerate the b = 2..7 SAT/DRAT
certificates for Theorem B on the RAW dihedral encoding.

Context: the entry's numeric-corroboration claim ("direct SAT recomputation
on the raw Dih(3)/Dih(b) encoding for b = 2..7, DRAT-certified both
directions") was originally verified during the producing run, whose
disk-discipline policy then deleted the proof files. These are FRESH runs
of the same instances, regenerated 2026-08-13 for the evidence repository.

Encoding ([DD26] arXiv:2607.06817, §2.3, eqs. (1)-(2), raw — no
Sym-collapse): one Boolean variable x_{u,v} per edge {u,v} of K_n (u < v),
true iff the edge has colour 2. For every increasing injection
psi : {0,1,2} -> {0..n-1} and every phi in Dih(3), a clause with one
POSITIVE literal per image edge of P3alt (forbids an all-colour-1 copy);
for every increasing injection psi : {0..b-1} -> {0..n-1} and every
phi in Dih(b), a clause with one NEGATIVE literal per image edge of K_b
(forbids an all-colour-2 copy). Group elements are the distinct
permutations of the dihedral group, built by generator closure (for
b >= 3 that is exactly 2b elements; for b = 2 the closed form's four
words collapse to the 2 distinct permutations of a 2-element set).

For each b in 2..7:
  n = 2b-2:  expect SAT; the model is decoded and checked by the
             INDEPENDENT embedding checker from verify_theorem_b.py
             (no Dih(3)-embedded P3alt in colour 1, no Dih(b)-embedded
             K_b in colour 2).
  n = 2b-1:  expect UNSAT; kissat emits a DRAT proof, checked by
             drat-trim (verdict searched in full output — the producing
             run documented a carriage-return trap on this line).

Artifacts per instance, written to the output directory:
  b{b}_n{n}.cnf            the DIMACS instance
  b{b}_n{n}.kissat.log     full solver output
  b{b}_n{n}.witness.txt    (SAT legs) decoded colouring + raw v-lines
  b{b}_n{n}.drat           (UNSAT legs) DRAT proof, ASCII
  b{b}_n{n}.drat-trim.log  (UNSAT legs) checker output
plus results.json summarising all twelve legs.

Usage: python3 make_theorem_b_certificates.py [outdir]
Exits 0 iff all six witnesses validate and all six proofs verify.
"""

import itertools
import json
import math
import os
import shutil
import subprocess
import sys
from datetime import datetime, timezone

from verify_theorem_b import P3ALT_EDGES, dihedral_group, edge, gamma_embedded

_TASK = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KISSAT = (os.environ.get("KISSAT") or shutil.which("kissat")
          or os.path.join(_TASK, "code/vendor/kissat/build/kissat"))
DRATTRIM = (os.environ.get("DRATTRIM") or shutil.which("drat-trim")
            or os.path.join(_TASK, "code/vendor/drat-trim/drat-trim"))


def var_map(n):
    pairs = list(itertools.combinations(range(n), 2))
    return {p: i + 1 for i, p in enumerate(pairs)}, pairs


def encode(b, n):
    """Raw [DD26] eqs.(1)-(2) clause set for (P3alt, Dih(3)) vs (K_b, Dih(b))."""
    vm, pairs = var_map(n)
    dih3 = dihedral_group(3)
    dihb = dihedral_group(b)
    kb_edges = list(itertools.combinations(range(b), 2))
    clauses = []
    for psi in itertools.combinations(range(n), 3):
        for phi in dih3:
            clauses.append([vm[edge(psi[phi[u]], psi[phi[v]])]
                            for (u, v) in P3ALT_EDGES])
    for psi in itertools.combinations(range(n), b):
        for phi in dihb:
            clauses.append([-vm[edge(psi[phi[u]], psi[phi[v]])]
                            for (u, v) in kb_edges])
    expected = (math.comb(n, 3) * len(dih3)
                + math.comb(n, b) * len(dihb))
    assert len(clauses) == expected, (len(clauses), expected)
    return vm, pairs, clauses


def write_cnf(path, nvars, clauses, comment):
    with open(path, "w") as f:
        f.write(f"c {comment}\n")
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")


def parse_model(output):
    lits = []
    for line in output.splitlines():
        if line.startswith("v "):
            lits.extend(int(x) for x in line[2:].split())
    return {abs(l): l > 0 for l in lits if l != 0}


def run(cmd):
    proc = subprocess.run(cmd, capture_output=True, text=True)
    return proc.returncode, proc.stdout + proc.stderr


def main():
    outdir = sys.argv[1] if len(sys.argv) > 1 else "sat-certificates"
    os.makedirs(outdir, exist_ok=True)
    results = []
    ok = True

    for b in range(2, 8):
        row = {"b": b, "predicted_R": 2 * b - 1}

        # --- SAT leg: n = 2b-2 --------------------------------------------
        n = 2 * b - 2
        vm, pairs, clauses = encode(b, n)
        base = os.path.join(outdir, f"b{b}_n{n}")
        write_cnf(base + ".cnf", len(pairs), clauses,
                  f"Theorem B raw encoding: (P3alt,Dih(3)) vs (K_{b},Dih({b})), "
                  f"n={n}; SAT expected (witness leg); regenerated 2026-08-13")
        rc, out = run([KISSAT, "--no-binary", base + ".cnf"])
        open(base + ".kissat.log", "w").write(out)
        model = parse_model(out)
        blue = {p for p in pairs if model.get(vm[p], False)}
        red = set(pairs) - blue
        kb_edges = list(itertools.combinations(range(b), 2))
        red_hit = gamma_embedded(P3ALT_EDGES, 3, dihedral_group(3), red, n)
        blue_hit = gamma_embedded(kb_edges, b, dihedral_group(b), blue, n)
        witness_valid = rc == 10 and not red_hit and not blue_hit
        with open(base + ".witness.txt", "w") as f:
            f.write(f"c decoded witness for n={n} (colour1=red, colour2=blue)\n")
            f.write(f"c red  (colour 1): {sorted(red)}\n")
            f.write(f"c blue (colour 2): {sorted(blue)}\n")
            f.write("c independent check: no Dih(3)-embedded P3alt in red: "
                    f"{not red_hit}; no Dih({b})-embedded K_{b} in blue: "
                    f"{not blue_hit}\n")
            for line in out.splitlines():
                if line.startswith("v "):
                    f.write(line + "\n")
        row["sat_leg"] = {"n": n, "clauses": len(clauses),
                          "kissat_exit": rc, "witness_valid": witness_valid,
                          "conclusion": f"R_dih(P3alt,K_{b}) >= {2*b-1}"}
        ok &= witness_valid

        # --- UNSAT leg: n = 2b-1 ------------------------------------------
        n = 2 * b - 1
        vm, pairs, clauses = encode(b, n)
        base = os.path.join(outdir, f"b{b}_n{n}")
        write_cnf(base + ".cnf", len(pairs), clauses,
                  f"Theorem B raw encoding: (P3alt,Dih(3)) vs (K_{b},Dih({b})), "
                  f"n={n}; UNSAT expected (proof leg); regenerated 2026-08-13")
        rc, out = run([KISSAT, "--no-binary", base + ".cnf", base + ".drat"])
        open(base + ".kissat.log", "w").write(out)
        rc2, out2 = run([DRATTRIM, base + ".cnf", base + ".drat"])
        open(base + ".drat-trim.log", "w").write(out2)
        verified = rc == 20 and "VERIFIED" in out2
        row["unsat_leg"] = {"n": n, "clauses": len(clauses),
                            "kissat_exit": rc, "drat_trim_verified": verified,
                            "conclusion": f"R_dih(P3alt,K_{b}) <= {2*b-1}"}
        ok &= verified

        row["exact"] = (f"R_dih(P3alt,K_{b}) = {2*b-1}"
                        if row["sat_leg"]["witness_valid"]
                        and row["unsat_leg"]["drat_trim_verified"]
                        else "INCOMPLETE")
        results.append(row)
        print(f"b={b}: SAT@{2*b-2} witness_valid={row['sat_leg']['witness_valid']}"
              f" | UNSAT@{2*b-1} drat-trim={row['unsat_leg']['drat_trim_verified']}"
              f" -> {row['exact']}")

    summary = {
        "script": "make_theorem_b_certificates.py",
        "run_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "provenance": "REGENERATED certificates (fresh solver runs, "
                      "2026-08-13). The producing run's originals were "
                      "deleted after verification under its disk-discipline "
                      "policy; same instances, same encoding, same tooling.",
        "tools": {"solver": "kissat 4.0.4", "checker": "drat-trim"},
        "results": results,
        "all_ok": ok,
        "verdict": ("6/6 exact: witnesses independently validated, proofs "
                    "drat-trim VERIFIED") if ok else "FAILURE — see rows",
    }
    with open(os.path.join(outdir, "results.json"), "w") as f:
        json.dump(summary, f, indent=2)
    print(f"VERDICT: {summary['verdict']}")
    print(f"Artifacts in {outdir}/")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
