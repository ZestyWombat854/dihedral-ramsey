#!/usr/bin/env python3
"""
verify_theorem_b.py — standalone checker for the claim

    R_dih(P3alt, K_b) = 2b - 1  for all b
    (the a = 3 slice of Damnjanovic-Dordevic, arXiv:2607.06817, Conjecture 4.9)

===========================================================================
WHAT THIS SCRIPT VERIFIES — AND WHAT IT DOES NOT
===========================================================================
VERIFIES, for each b in 2..8: the LOWER bound R_dih(P3alt, K_b) >= 2b-1,
by constructing the block-partition witness coloring of K_{2b-2} (Lemma 2
of the accompanying note) and exhaustively checking that it contains no
Dih(3)-embedded P3alt in red and no K_b in blue.

VERIFIES, for b = 3 only: BOTH bounds. It additionally enumerates all
2^10 = 1024 red/blue colorings of K_5 and confirms every one contains a
red Dih(3)-embedded P3alt or a blue triangle. So R_dih(P3alt, K_3) = 5 is
machine-verified end-to-end by this script alone.

ALSO VERIFIES: the orbit-equality premise of the cyclic corollary
(Corollary 5 of the note): the Cyc(3)-orbit of P3alt equals its
Sym(3)-orbit — both are exactly the three labeled 3-paths, one per choice
of center — and the orbit of K_b is a singleton (under Dih(b) for b=2..8,
under all of Sym(b) for b=2..5). The APPLICATION of [DD26]'s
Proposition 2.4 to these facts remains a citation, not a computation.

DOES NOT VERIFY: the upper bound R_dih(P3alt, K_b) <= 2b-1 for general b.
That half of the theorem rests on a citation chain — Dih(3) = Sym(3),
then Chvatal 1977 via [DD26, Theorem 4.13] — i.e., on a proof, not on a
computation this script could reproduce.
===========================================================================

Definitions are implemented directly from arXiv:2607.06817 (Section 2):
H is Gamma-embeddable in G iff some homomorphism psi . phi maps H into G,
with phi in Gamma and psi an INCREASING injection into G's ordered vertex
set. The dihedral group is built by closure from its two generators — the
script does NOT assume Dih(3) = Sym(3); it re-derives it and reports it.

Usage:  python3 verify_theorem_b.py [output.json]
        (stdlib only; writes verify_theorem_b_result.json by default,
        exits 0 iff every check passes)
"""

import itertools
import json
import math
import sys
from datetime import datetime, timezone

P3ALT_EDGES = [(0, 2), (1, 2)]  # vertex sequence (0, 2, 1): the path 0-2-1


def compose(p, q):
    """Permutation composition p . q (apply q first)."""
    return tuple(p[q[i]] for i in range(len(p)))


def dihedral_group(m):
    """Dih(m) on {0..m-1} by BFS closure of sigma: i->i+1 (mod m), rho: i->m-1-i."""
    sigma = tuple((i + 1) % m for i in range(m))
    rho = tuple(m - 1 - i for i in range(m))
    identity = tuple(range(m))
    group = {identity}
    frontier = [identity]
    while frontier:
        g = frontier.pop()
        for h in (sigma, rho):
            ng = compose(h, g)
            if ng not in group:
                group.add(ng)
                frontier.append(ng)
    return sorted(group)


def edge(u, v):
    return (u, v) if u < v else (v, u)


def gamma_embedded(pattern_edges, pattern_order, group, edge_set, n):
    """Is the pattern Gamma-embeddable in the graph (edge_set, n)?

    Tries every phi in the group and every increasing injection psi
    (= every sorted pattern_order-subset of range(n)); the embedding maps
    pattern vertex v to psi[phi[v]].
    """
    for phi in group:
        permuted = [edge(phi[u], phi[v]) for (u, v) in pattern_edges]
        for psi in itertools.combinations(range(n), pattern_order):
            if all(edge(psi[pu], psi[pv]) in edge_set for (pu, pv) in permuted):
                return True
    return False


def has_clique(edge_set, n, b):
    """Does the graph contain K_b? (For a complete pattern, Gamma-embeddability
    is clique containment for ANY group — every relabeling fixes K_b.)"""
    if b <= 1:
        return n >= b
    for sub in itertools.combinations(range(n), b):
        if all(edge(u, v) in edge_set for u, v in itertools.combinations(sub, 2)):
            return True
    return False


def witness_coloring(b):
    """Lemma 2 witness for a=3: n = 2(b-1) vertices, b-1 blocks of size 2;
    same-block pairs red, cross-block pairs blue."""
    n = 2 * (b - 1)
    blocks = [(2 * i, 2 * i + 1) for i in range(b - 1)]
    red = {edge(u, v) for (u, v) in blocks}
    blue = {edge(u, v) for u, v in itertools.combinations(range(n), 2)} - red
    return n, blocks, red, blue


def run_controls(dih3):
    """Self-tests: the detectors must FIRE on planted patterns and must
    respect the increasing-injection (ordered) semantics."""
    controls = []

    def record(name, expected, observed):
        controls.append({"name": name, "expected": expected,
                         "observed": observed, "pass": expected == observed})

    all_k4 = {edge(u, v) for u, v in itertools.combinations(range(4), 2)}
    record("all-red K_4 contains a red Dih(3)-embedded P3alt",
           True, gamma_embedded(P3ALT_EDGES, 3, dih3, all_k4, 4))
    record("all-blue K_4 contains a blue K_4",
           True, has_clique(all_k4, 4, 4))

    # Mutation test: plant one red cross-block edge in the b=4 witness;
    # vertices 0,1,2 then span red edges {0,1},{1,2} — a P3alt copy the
    # detector must catch (via a non-identity relabeling).
    _, _, red4, _ = witness_coloring(4)
    mutated = set(red4) | {edge(1, 2)}
    record("b=4 witness + planted red edge {1,2} contains the pattern",
           True, gamma_embedded(P3ALT_EDGES, 3, dih3, mutated, 6))

    # Ordered-semantics test: red path 0-1-2 (center 1). Under the TRIVIAL
    # group the only increasing placement demands center 2 — no embedding;
    # under Dih(3) a relabeling reaches it — embedding exists. This
    # distinguishes the groups, confirming the encoder respects the
    # increasing-injection definition.
    center1 = {edge(0, 1), edge(1, 2)}
    trivial = [tuple(range(3))]
    record("path 0-1-2: NOT {id}-embeddable (ordered semantics)",
           False, gamma_embedded(P3ALT_EDGES, 3, trivial, center1, 3))
    record("path 0-1-2: Dih(3)-embeddable",
           True, gamma_embedded(P3ALT_EDGES, 3, dih3, center1, 3))

    return controls


def cyclic_orbit_check():
    """Corollary 5's orbit-equality premise, checked from definitions.

    Builds Cyc(3) by generator closure from sigma alone (nothing assumes
    the equality being checked), computes the Cyc(3)- and Sym(3)-orbits of
    P3alt as sets of labeled edge sets, and confirms both equal the three
    center-labelings. Also confirms K_b's orbit is the singleton {K_b}
    under Dih(b) for b = 2..8 and under all of Sym(b) for b = 2..5."""
    def image(edges, phi):
        return frozenset(edge(phi[u], phi[v]) for (u, v) in edges)

    sigma = tuple((i + 1) % 3 for i in range(3))
    identity = tuple(range(3))
    cyc3 = {identity}
    frontier = [identity]
    while frontier:
        g = frontier.pop()
        ng = compose(sigma, g)
        if ng not in cyc3:
            cyc3.add(ng)
            frontier.append(ng)

    cyc_orbit = {image(P3ALT_EDGES, phi) for phi in cyc3}
    sym_orbit = {image(P3ALT_EDGES, phi)
                 for phi in itertools.permutations(range(3))}
    centers = {frozenset({(0, 2), (1, 2)}),   # center 2 (P3alt itself)
               frozenset({(0, 1), (0, 2)}),   # center 0
               frozenset({(0, 1), (1, 2)})}   # center 1
    kb_rows = []
    for b in range(2, 9):
        kb = {edge(u, v) for u, v in itertools.combinations(range(b), 2)}
        dih_singleton = {image(kb, phi)
                         for phi in dihedral_group(b)} == {frozenset(kb)}
        sym_singleton = True
        if b <= 5:
            sym_singleton = {image(kb, phi)
                             for phi in itertools.permutations(range(b))} \
                == {frozenset(kb)}
        kb_rows.append({"b": b,
                        "dih_orbit_is_singleton": dih_singleton,
                        "sym_orbit_is_singleton_checked_b_le_5": sym_singleton})
    return {
        "cyc3_order": len(cyc3),
        "cyc3_orbit_size": len(cyc_orbit),
        "sym3_orbit_size": len(sym_orbit),
        "orbits_equal": cyc_orbit == sym_orbit,
        "orbit_is_the_three_center_labelings":
            cyc_orbit == centers and sym_orbit == centers,
        "kb_orbit_singleton": kb_rows,
        "conclusion": "Cyc(3)-orbit of P3alt = Sym(3)-orbit (the 3 labeled "
                      "3-paths); K_b orbits are singletons — the premise "
                      "Corollary 5 feeds to [DD26] Proposition 2.4. The "
                      "Proposition 2.4 application itself is a citation.",
    }


def main():
    out_path = sys.argv[1] if len(sys.argv) > 1 else "verify_theorem_b_result.json"

    # --- Group facts (Lemma 3 is CHECKED here, not assumed) ---------------
    dih3 = dihedral_group(3)
    sym3 = sorted(itertools.permutations(range(3)))
    dih4 = dihedral_group(4)
    group_facts = {
        "dih3_order": len(dih3),
        "sym3_order": len(sym3),
        "dih3_equals_sym3": dih3 == sym3,
        "dih3_elements": [list(p) for p in dih3],
        "dih4_order": len(dih4),
        "sym4_order": math.factorial(4),
        "dih4_equals_sym4": len(dih4) == math.factorial(4),
    }

    # --- Checker self-tests ------------------------------------------------
    controls = run_controls(dih3)

    # --- Lower bounds, b = 2..8 ---------------------------------------------
    lower_bounds = []
    for b in range(2, 9):
        n, blocks, red, blue = witness_coloring(b)
        red_hit = gamma_embedded(P3ALT_EDGES, 3, dih3, red, n)
        blue_hit = has_clique(blue, n, b)
        lower_bounds.append({
            "b": b,
            "n_witness": n,
            "blocks": blocks,
            "red_contains_dih3_P3alt": red_hit,
            "blue_contains_Kb": blue_hit,
            "witness_valid": not red_hit and not blue_hit,
            "conclusion": f"R_dih(P3alt, K_{b}) >= {2 * b - 1}",
        })

    # --- b = 3, exhaustive upper bound at n = 5 ------------------------------
    edges5 = list(itertools.combinations(range(5), 2))
    assert len(edges5) == 10
    bad = 0
    for mask in range(1 << 10):
        red = {edges5[i] for i in range(10) if mask >> i & 1}
        blue = set(edges5) - red
        if not (gamma_embedded(P3ALT_EDGES, 3, dih3, red, 5)
                or has_clique(blue, 5, 3)):
            bad += 1
    b3_exhaustive = {
        "n": 5,
        "colorings_checked": 1 << 10,
        "colorings_avoiding_both": bad,
        "all_contain_red_P3alt_or_blue_K3": bad == 0,
        "conclusion": "R_dih(P3alt, K_3) <= 5",
    }

    # --- Corollary 5's orbit-equality premise --------------------------------
    orbit = cyclic_orbit_check()

    # --- Verdict -------------------------------------------------------------
    all_pass = (
        group_facts["dih3_equals_sym3"]
        and all(c["pass"] for c in controls)
        and all(r["witness_valid"] for r in lower_bounds)
        and b3_exhaustive["all_contain_red_P3alt_or_blue_K3"]
        and orbit["orbits_equal"]
        and orbit["orbit_is_the_three_center_labelings"]
        and all(r["dih_orbit_is_singleton"]
                and r["sym_orbit_is_singleton_checked_b_le_5"]
                for r in orbit["kb_orbit_singleton"])
    )
    result = {
        "script": "verify_theorem_b.py",
        "run_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "claim": "R_dih(P3alt, K_b) = 2b-1 for all b "
                 "(arXiv:2607.06817 Conjecture 4.9 at a=3)",
        "scope": "LOWER bound verified for b=2..8; BOTH bounds verified at "
                 "b=3 only; Corollary 5's orbit-equality premise verified "
                 "(the Proposition 2.4 application is a citation). The "
                 "general upper bound is NOT verified here — it rests on "
                 "Dih(3)=Sym(3) plus Chvatal 1977 via [DD26, Theorem 4.13], "
                 "a proof, not a computation.",
        "group_facts": group_facts,
        "checker_controls": controls,
        "lower_bounds": lower_bounds,
        "b3_exhaustive": b3_exhaustive,
        "corollary5_orbit_check": orbit,
        "b3_exact": "R_dih(P3alt, K_3) = 5 "
                    "(valid witness at n=4 + exhaustive check at n=5)",
        "summary": {
            "all_checks_pass": all_pass,
            "verdict": ("LOWER BOUNDS VERIFIED for b=2..8; b=3 EXACT (both "
                        "bounds); COROLLARY-5 ORBIT PREMISE VERIFIED")
                       if all_pass else "FAILURE — see fields above",
        },
    }

    with open(out_path, "w") as f:
        json.dump(result, f, indent=2)

    print(f"Dih(3) built by generator closure: order {len(dih3)}, "
          f"equals Sym(3): {group_facts['dih3_equals_sym3']} "
          f"(contrast Dih(4): order {len(dih4)} of {math.factorial(4)})")
    print(f"Checker controls: {sum(c['pass'] for c in controls)}/{len(controls)} pass")
    for r in lower_bounds:
        print(f"  b={r['b']}: witness on n={r['n_witness']} valid={r['witness_valid']}"
              f" -> {r['conclusion']}")
    print(f"b=3 exhaustive at n=5: {b3_exhaustive['colorings_checked']} colorings, "
          f"{b3_exhaustive['colorings_avoiding_both']} avoid both -> "
          f"{b3_exhaustive['conclusion']}")
    print(f"Corollary-5 orbit premise: Cyc(3)-orbit size "
          f"{orbit['cyc3_orbit_size']} == Sym(3)-orbit size "
          f"{orbit['sym3_orbit_size']}, equal={orbit['orbits_equal']}, "
          f"K_b singletons OK")
    print(f"VERDICT: {result['summary']['verdict']}")
    print(f"JSON written to {out_path}")
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
