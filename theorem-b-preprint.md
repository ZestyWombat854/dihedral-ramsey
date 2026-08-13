# The a = 3 slice of two permutational Ramsey conjectures: R_dih(P3alt, K_b) = R_cyc(P3alt, K_b) = 2b − 1 for all b

**DRAFT v1 (2026-08-12) — for human review before any posting. Extracted from
§6.6 of a larger internal write-up; see §11 for provenance and verification
status.**

## Abstract

For b ∈ ℕ let R_dih(P3alt, K_b) denote the dihedral Ramsey number, in the
sense of Damnjanović–Đorđević [DD26], of the alternating path of order 3
against the complete graph K_b. We prove R_dih(P3alt, K_b) = 2b − 1 for all b
— the a = 3 slice of [DD26, Conjecture 4.9] — and R_cyc(P3alt, K_b) = 2b − 1
for all b — the a = 3 slice of [Baš+26, Conjecture 4.23]. The dihedral case
rests on an order argument special to three vertices: Dih(3) = Sym(3), so
rotations and reflections already exhaust all relabelings, dihedral
embeddability collapses to ordinary subgraph containment, and Chvátal's 1977
tree–complete-graph theorem applies. The cyclic case does not follow from the
reflection-symmetry reduction of [DD26, Corollary 2.5] — P3alt lacks
reflection symmetry — but does follow from an orbit-equality argument via
[DD26, Proposition 2.4]. A block-partition construction, valid for every
connected pattern and every permutation group, gives the matching lower bound.
The identity was corroborated by direct SAT computation on the raw dihedral
encoding for b = 2..7, and b = 3 is fully machine-verified by the accompanying
standalone script; the lower bound for every b, and the Dih(3) = Sym(3)
collapse, are additionally machine-verified in Lean 4 (the upper bound is
the citation). The upper bound for patterns of order a ≥ 4 remains open.

## 1. History and the two conjectures

Damnjanović and Đorđević [DD26] compute small *reflective* and *dihedral*
Ramsey numbers — permutational Ramsey numbers under reflection or dihedral
symmetry groups — by SAT encoding under fixed solver budgets, and state
several closed-form conjectures that their own tables support only as
computed cells or unproved lower bounds. The one this note closes at a = 3
reads, verbatim:

> **Conjecture 4.9** [DD26]. For any a, b ∈ ℕ, we have
> R_dih(P_a^alt, K_b) = 1 + (a − 1)(b − 1).

For the *cyclic* variant of the same pairing, [DD26]'s Table 2 records the
matching conjecture from the companion paper of Bašić, Damnjanović,
Stevanović, and Stošić, citing it as [Baš+26, Conjecture 4.23]:

> **Conjecture 4.23** [Baš+26, as cited in DD26, Table 2].
> R_cyc(P_a^alt, K_b) = 1 + (a − 1)(b − 1) for a, b ∈ ℕ.

At a = 3 both right-hand sides equal 2b − 1.

**What is and is not new here.** [Baš+26]'s companion repository already
tabulates cyclic values matching 2b − 1 for b = 3..8 as ordinary computed SAT
cells (we traced them to the underlying solver logs, not just the summary
table), without stating a closed form. The new content of this note is
therefore: the closed form itself (all b, not six data points), its proof (a
citation chain plus two group-theoretic facts, not a search), and — for the
*dihedral* value, which [Baš+26] never tabulates directly — a new all-b
closed form. The b = 3..8 cyclic arithmetic is not new.

## 2. Definitions

All definitions are restated from [DD26, §§1–2].

**Permutational Ramsey numbers.** For graphs H_1, ..., H_k on vertex sets
{0, ..., |H_j| − 1} and permutation groups Γ_j on V(H_j), the graph H_j is
**Γ_j-embeddable** in a graph G (on a totally ordered vertex set) if there is
a homomorphism H_j → G of the form ψ ∘ φ, where φ ∈ Γ_j and
ψ : V(H_j) → V(G) is an **increasing** injection. Only the pattern's own
vertices may be permuted (by φ); the placement ψ into the host's fixed vertex
order must be order-preserving. The **permutational Ramsey number**
R(H_1^Γ1, ..., H_k^Γk) is the least n such that every k-edge-coloring of K_n
contains, for some color j, a Γ_j-embedded copy of H_j in color j.

The increasing-injection requirement is the substance of the definition:
arbitrary relabelings of the host K_n are *not* a symmetry of the problem —
only the pattern's own group Γ_j is. This is exactly why the choice of group
matters and why the theorem below is not vacuous.

**The groups.** For a pattern of order m on {0, ..., m−1}, the **dihedral
group** Dih(m) = ⟨σ, ρ⟩ where σ(i) = i + 1 (mod m) is the rotation and
ρ(i) = m − 1 − i the reflection; |Dih(m)| = 2m. The **cyclic group**
Cyc(m) = ⟨σ⟩ has order m. R_dih (resp. R_cyc) denotes the permutational
Ramsey number in which every Γ_j is the dihedral (resp. cyclic) group of its
own pattern H_j. Taking every Γ_j to be the full symmetric group Sym(|H_j|)
recovers the classical Ramsey number [DD26, §1]: with all relabelings
available, any ordinary subgraph copy can be pre-permuted so that its
placement is increasing.

**Γ-isomorphism.** F ≅_Γ H iff some isomorphism from F to H is an element of
Γ [DD26, §2]; its equivalence classes are the Γ-orbits of labeled patterns.
Two facts from [DD26] are used below, quoted in full (modulo notation):

> **Proposition 2.1** [DD26]. Let H_1, H_2, ..., H_k be graphs and let
> Γ_1, Γ_2, ..., Γ_k be permutation groups on their respective vertex sets.
> Suppose that F_1, F_2, ..., F_k are graphs such that F_j ≅_Γj H_j for each
> j ∈ {1, 2, ..., k}. Then R(F_1^Γ1, F_2^Γ2, ..., F_k^Γk) =
> R(H_1^Γ1, H_2^Γ2, ..., H_k^Γk).

> **Proposition 2.4** [DD26]. Let H_1, H_2, ..., H_k be graphs, and let
> Γ_1, Γ_2, ..., Γ_k and Λ_1, Λ_2, ..., Λ_k be permutation groups on their
> respective vertex sets. Suppose that, for each j ∈ {1, 2, ..., k}, H_j
> lies in the same equivalence class under both ≅_Γj and ≅_Λj. Then
> R(H_1^Λ1, H_2^Λ2, ..., H_k^Λk) = R(H_1^Γ1, H_2^Γ2, ..., H_k^Γk).

**The pattern.** The alternating path P_a^alt is the path on {0, ..., a−1}
whose vertex sequence is (0, a−1, 1, a−2, ...), with edges between
consecutive terms. For a = 3 the sequence is (0, 2, 1), so

    P3alt = the path 0 — 2 — 1,  edges {0,2} and {1,2},  center vertex 2.

## 3. Dih(3), concretely

Dih(3) is generated by σ = (0 → 1 → 2 → 0) and ρ = (0 ↔ 2, fixing 1). Its six
elements, as permutations (images of 0, 1, 2 in order):

| element | 0 ↦ | 1 ↦ | 2 ↦ |
|---|---|---|---|
| id      | 0 | 1 | 2 |
| σ       | 1 | 2 | 0 |
| σ²      | 2 | 0 | 1 |
| ρ       | 2 | 1 | 0 |
| σρ      | 0 | 2 | 1 |
| σ²ρ     | 1 | 0 | 2 |

These are six distinct permutations of a three-element set, and Sym(3) has
3! = 6 elements in total. That observation is Lemma 3 below; the point of
listing the elements is that nothing is hidden — for three vertices,
rotations and reflections already produce every relabeling.

## 4. Lemma 1: K_b-embeddability is group-independent

**Lemma 1.** For any b ∈ ℕ, n ≥ b, any graph G on {0, ..., n−1}, and *any*
permutation group Γ on {0, ..., b−1}: K_b is Γ-embeddable in G if and only if
G contains a clique of size b.

*Proof.* (⇐) Let v_0 < v_1 < ... < v_{b−1} be the vertices of a b-clique of
G. Take ψ(i) = v_i and φ = id ∈ Γ. Every pair of K_b's vertices is an edge,
and every image pair is a clique edge. (⇒) ψ ∘ φ is injective (φ is a
bijection, ψ an injection), and every pair of K_b's vertices is an edge, so
the b image vertices are pairwise adjacent in G — a clique. ∎

## 5. Lemma 2: the block-partition lower bound

**Lemma 2.** Let a, b ≥ 1 and n = (a − 1)(b − 1). Fix *any* partition of
{0, ..., n−1} into b − 1 blocks of size a − 1 (contiguous or not), *any*
connected graph H of order a, and *any* permutation groups Γ (on V(H)) and Λ
(on V(K_b)). Color every same-block pair with color 1 and every cross-block
pair with color 2. Then color 1 contains no Γ-embedded H and color 2 contains
no Λ-embedded K_b; consequently

    R(H^Γ, K_b^Λ) ≥ 1 + (a − 1)(b − 1).

*Proof.* Color 1's graph is a disjoint union of b − 1 cliques K_{a−1}. The
image of H under the injective homomorphism ψ ∘ φ is a connected subgraph on
a vertices, hence lies inside a single component — but each component has
only a − 1 < a vertices. So color 1 has no Γ-embedded H. Color 2's graph is
the complete (b−1)-partite complement; by Lemma 1 a Λ-embedded K_b requires a
color-2 clique of size b, but any b vertices distributed among b − 1 blocks
share a block by pigeonhole, and that pair has color 1. ∎

Specializing H = P_a^alt (connected, order a) and Γ = Dih(a), Λ = Dih(b):
R_dih(P_a^alt, K_b) ≥ 1 + (a − 1)(b − 1) for all a, b ∈ ℕ — the lower-bound
half of [DD26, Conjecture 4.9] in full generality. For a = 3 the witness is
b − 1 disjoint "dominoes" (red blocks of size 2) on 2b − 2 vertices; the
accompanying script constructs and checks it exhaustively for b = 2..8.

## 6. Lemma 3: Dih(3) = Sym(3)

**Lemma 3.** As sets of permutations of {0, 1, 2}, Dih(3) = Sym(3).

*Proof.* Dih(3)'s generators are permutations of {0, 1, 2}, so
Dih(3) ≤ Sym(3). |Dih(3)| = 2·3 = 6 = 3! = |Sym(3)|, and a subgroup with the
same order as its ambient finite group equals it. ∎ (Equivalently: a 3-cycle
and a transposition already generate all of Sym(3).)

This collapse is unique to a = 3: for every a ≥ 4, |Dih(a)| = 2a < a!, and
indeed Dih(a) ≠ Sym(a) (checked explicitly for a = 3..12 during review).

## 7. The theorem

**Theorem 4.** R_dih(P3alt, K_b) = 2b − 1 for all b ∈ ℕ.

*Proof.* By Lemma 3, (P3alt)^Dih(3)-embeddability *is*
(P3alt)^Sym(3)-embeddability — the same group, hence literally the same
relation. By Lemma 1, the group attached to the K_b argument is irrelevant,
so Dih(b) may be replaced by Sym(b) without changing any embeddability
predicate. With every group now the full symmetric group, the permutational
Ramsey number is the classical one [DD26, §1]:

    R_dih(P3alt, K_b) = R((P3alt)^Sym(3), K_b^Sym(b)) = R(P3, K_b),

where P3 denotes the (unlabeled) path of order 3 — as an unlabeled graph,
P3alt is the unique tree on 3 vertices, and Proposition 2.1 (with symmetric
groups, whose orbits are exactly unlabeled-isomorphism classes) makes the
choice of labeled representative irrelevant. Chvátal's tree–complete-graph
theorem, as restated verbatim in [DD26]:

> **Theorem 4.13** [DD26, quoting Chv77]. For any a, b ∈ ℕ and tree T of
> order a, we have R(T, K_b) = 1 + (a − 1)(b − 1).

With a = 3: R(P3, K_b) = 1 + 2(b − 1) = 2b − 1. ∎

Note the division of labor: the *lower* bound is also proved directly and
independently by Lemma 2, so the only step of this note that rests on a
citation rather than a self-contained argument is the upper bound
R(P3, K_b) ≤ 2b − 1 inside Theorem 4.13.

## 8. The cyclic corollary — and why it is not the reflection-symmetry route

A natural first guess is [DD26, Corollary 2.5]: for graphs with *reflection
symmetry* (the map φ(x) = |H| − 1 − x is an automorphism),
R_dih = R_cyc. That corollary **does not apply** to P3alt: under
φ(x) = 2 − x, the edge {0,2} is fixed, but {1,2} ↦ {1,0} = {0,1}, which is
not an edge of P3alt. P3alt lacks reflection symmetry. ([DD26]'s own text
corroborates this reading: it treats dihedral alternating paths as a
genuinely separate class precisely because Corollaries 2.5/2.6 do not
collapse them to the cyclic case.)

The mechanism that does work is Proposition 2.4, an orbit-equality condition
strictly weaker than an automorphism requirement.

**Orbit computation.** The Cyc(3)-orbit of P3alt: applying σ to the edge set
{{0,2},{1,2}} gives {{1,0},{2,0}} (center 0); applying σ² gives
{{2,1},{0,1}} (center 1). So the orbit is the three labeled 3-paths with
center 2, 0, 1 respectively. The Sym(3)-orbit of P3alt is the set of *all*
labeled copies of the 3-path on {0,1,2} — and a labeled 3-path is determined
by its center, so that orbit is the same three graphs. The two orbits are
equal: a coincidence of a 3-vertex tree having only 3 labeled shapes at all,
each reachable by rotation alone — nothing to do with reflection. On the
other side, the orbit of K_b under *any* permutation group is the singleton
{K_b}.

**Corollary 5.** R_cyc(P3alt, K_b) = 2b − 1 for all b ∈ ℕ — the a = 3 slice
of [Baš+26, Conjecture 4.23].

*Proof.* Proposition 2.4, applied coordinate-wise with (Γ_1, Λ_1) =
(Cyc(3), Sym(3)) on P3alt (orbits equal, as computed) and (Γ_2, Λ_2) =
(Cyc(b), Sym(b)) on K_b (orbits trivially equal), gives
R_cyc(P3alt, K_b) = R((P3alt)^Sym(3), K_b^Sym(b)) = R(P3, K_b) — the same
classical anchor as in Theorem 4, hence the same value 2b − 1. ∎

The cyclic and dihedral values are thus equal, but by two different
mechanisms meeting at a shared classical anchor — not by one being a
one-line consequence of the other.

## 9. Numeric corroboration

The following computations corroborate the theorem; they are **corroboration,
not proof** (the proof is §§4–8).

**Direct SAT recomputation on the raw dihedral encoding** (i.e., encoding
Dih(3) and Dih(b) as-is, *not* using the Sym-collapse — an independent check
of the conclusion, not just the proof steps), carried out during adversarial
review of the internal write-up:

| b | predicted 2b−1 | SAT at 2b−2 (witness checked) | UNSAT at 2b−1 (DRAT) | match |
|---|---|---|---|---|
| 2 | 3  | yes, brute-force verified | drat-trim VERIFIED | YES |
| 3 | 5  | yes, brute-force verified | drat-trim VERIFIED | YES |
| 4 | 7  | yes, brute-force verified | drat-trim VERIFIED | YES |
| 5 | 9  | yes, brute-force verified | drat-trim VERIFIED | YES |
| 6 | 11 | yes, brute-force verified | drat-trim VERIFIED | YES |
| 7 | 13 | yes, brute-force verified | drat-trim VERIFIED | YES |

6/6 exact matches. A bonus check swapped K_5's group from Dih(5) (order 10)
to Sym(5) (order 120) inside the actual encoding and reproduced an identical
SAT@8/UNSAT@9 boundary — a direct in-chain exercise of Lemma 1. A
from-scratch exhaustive enumeration of all 2^10 colorings of K_5 at b = 3
independently confirms R_dih(P3alt, K_3) = 5 with no SAT solver in the loop.

**Independent tabulation.** [Baš+26]'s companion repository tabulates the
cyclic value 2b − 1 for b = 3..8 as computed cells (traced during review down
to the raw solver logs and their SAT/UNSAT exit codes).

**Accompanying script.** `verify_theorem_b.py` (in this evidence package) is
a standalone stdlib-Python checker that (i) builds Dih(3) by generator
closure — it does *not* assume Lemma 3 — and re-derives |Dih(3)| = 6 =
|Sym(3)|; (ii) constructs Lemma 2's witness coloring and exhaustively
verifies the lower bound R_dih(P3alt, K_b) ≥ 2b − 1 for b = 2..8; and (iii)
at b = 3 exhaustively checks all 1,024 colorings of K_5, so
R_dih(P3alt, K_3) = 5 is machine-verified in both directions by the script
alone. It also checks Corollary 5's orbit-equality premise explicitly: the
Cyc(3)-orbit of P3alt equals the Sym(3)-orbit — the three center-labelings —
and K_b's orbit is a singleton (Dih(b) for b = 2..8, all of Sym(b) for
b = 2..5); the Proposition 2.4 application itself remains a citation. The
script cannot and does not verify the upper bound for general b — that is
the citation chain through Theorem 4.13.

**Accompanying Lean proof.** `TheoremB.lean` (in this evidence package) is a
standalone Lean 4 file — core only, no mathlib, no imports — whose main
theorem, `theoremB_lowerBound`, machine-checks the lower-bound half of
Theorem 4 *for every b ≥ 1 at once*: R_dih(P3alt, K_b) ≥ 2b − 1, via
Lemma 2's block witness, proved in full group generality (any permutation
family on either side, not only the dihedral groups). It also proves
Lemma 3 (Dih(3) = Sym(3), both inclusions, with the dihedral group built
from the paper's closed form), and it includes — and builds on the
definitions of — the run's earlier Lean proof of a Lemma-1 parallel (the
K_b group-invariance lemma), whose axiom audit it prints alongside its
own. These are genuine
∀b arguments — a hand-rolled pigeonhole and a max-degree-1 argument — not
per-instance kernel enumeration. Axiom audit (printed by the file itself):
`propext, Classical.choice, Quot.sound` only; no `native_decide`, no
`sorry`. The upper bound is deliberately not formalized — see §11.

## 10. What remains open

The general upper bound (a ≥ 4) resists the two standard strategies — a
diagnosis, not a hardness proof. (1) Mirroring [DD26]'s own
pigeonhole-induction (their Theorem 4.1 mechanism, which proves the
monotone-path column for any group): growing K_b against a fixed dihedral
pattern only shows *some* embedding of P_a^alt exists, with no control over
*which* of Dih(a)'s admissible shapes it is. (2) The classical Chvátal
degree-split induction: its greedy tree-embedding lemma has the identical
defect. Quantifying the gap: the Dih(a)-orbit of P_a^alt has exactly a
distinct "zigzag" shapes out of a!/2 labeled paths (checked for every
a = 3..14); both standard mechanisms certify "some shape, unrestricted," and
neither supplies leverage on which. For a ≥ 4 the Lemma 3 collapse is
unavailable (|Dih(a)| = 2a < a!), so the a = 3 route does not extend. No
counterexample to Conjecture 4.9 was found anywhere checked (every published
exact cell of [DD26]'s Table 13 and every cell closed during the wider run);
the obstruction is proof technique, not evidence against the conjecture.

## 11. Provenance, verification status, and scope

This work was carried out autonomously by an AI system (Claude, Anthropic)
on 2026-08-11/12, as one lane of a larger Ramsey-theory research run on a
single laptop; this note extracts the theorem's self-contained mathematical
content from the run's internal write-up (its §6.6, where Lemmas 1–3,
Theorem 4, and Corollary 5 appear as L1–L3, Theorem B, and its corollary).
Human direction was limited to initiation and operational supervision.

**Verification status, stated precisely:**

- **Adversarial review** was performed by *AI saboteur agents within the
  same pipeline* — independent re-derivation of all three lemmas; direct SAT
  recomputation of b = 2..7 on the raw dihedral encoding with DRAT
  certificates checked by drat-trim (§9); a verbatim citation audit of every
  [DD26] statement used, read off rendered PDF pages; for Corollary 5, an
  independent orbit recomputation plus exhaustive both-boundary brute force
  at b = 2, 3, 4 bypassing both Proposition 2.4 and Theorem 4, with b = 5, 6
  corroborated against [Baš+26]'s committed solver logs. Zero refutations;
  one immaterial tally slip in motivational text was found and corrected.
  **No human mathematician has reviewed these claims.**
- **Partially formally verified (Lean 4).** The lower bound
  R_dih(P3alt, K_b) ≥ 2b − 1 for every b ≥ 1 — Lemma 2's witness argument,
  in full group generality — and Lemma 3 (Dih(3) = Sym(3)) are
  machine-checked in Lean 4 core (no mathlib; axioms `propext`,
  `Classical.choice`, `Quot.sound`; no `native_decide`) in this package's
  standalone `TheoremB.lean`, which also contains the run's Lean-proved
  parallel of Lemma 1 and builds on its definitions. **The upper bound is
  not formalized** —
  neither Chvátal's theorem nor the reduction steps that reach it
  (Proposition 2.1/2.4's application, the Sym-collapse-to-classical step);
  those remain citations. The exact-value claim is therefore Lean-verified
  from below and citation-anchored from above.
- **Chvátal 1977 is cited second-hand**, via its verbatim restatement as
  [DD26, Theorem 4.13]; the restatement was checked against [DD26]'s PDF,
  but the 1977 original was not consulted.
- **A disclosed reproducibility gap:** the producing lane's original scratch
  scripts were never committed to disk. Every reported numeric outcome that
  the adversarial reviewer re-ran reproduced exactly, and the accompanying
  script re-verifies the lower bounds and the b = 3 cell from scratch.
- **Novelty:** same-day arXiv version checks, targeted arXiv phrase
  searches, general web searches, and Semantic Scholar citation checks
  (2026-08-12) found no prior statement or proof of the closed form or of
  the Dih(3) = Sym(3) mechanism applied to this pairing. The final Semantic
  Scholar pass was rate-limited and relied on three same-day zero-citation
  fetches earlier that day.

```diff
- ===== NOT DONE =====
- I did NOT include the ordered and reflective variants of the same a=3
- pairing (treated separately in the run's internal write-up); this note's
- scope is exactly the dihedral and cyclic cases, and it makes no claim,
- in either direction, about the other variants' status.
- I did NOT prove anything about a >= 4; Conjecture 4.9 remains open there
- (see Section 10 for exactly where the standard techniques stop).
- I did NOT formalize the upper bound: the Lean file verifies the lower
- bound (every b), Lemma 3, and a Lemma-1 parallel, and nothing else — the
- upper bound rests on the citation chain through [DD26, Theorem 4.13].
- I did NOT obtain human peer review; adversarial review was AI-internal
- (Section 11).
- WHAT IT WOULD CHANGE: a gap in the upper bound's citation chain (the
- Sym-collapse-to-classical step, Proposition 2.1/2.4's application, or
- the Chvatal statement) would invalidate the UPPER bounds beyond the
- SAT-verified range (b = 2..7 dihedral, b = 3..8 cyclic); the LOWER
- bounds now stand on kernel-checked proof for every b regardless. A
- prior publication of either closed form would change this note's
- contribution from new-result to rediscovery.
```

## References

- [DD26] I. Damnjanović, I. Đorđević, "Computation of small reflective and
  dihedral Ramsey numbers," arXiv:2607.06817v2 [math.CO], 12 Jul 2026.
- [Baš+26] N. Bašić, I. Damnjanović, D. Stevanović, I. Stošić, "Some results
  on small ordered and cyclic Ramsey numbers," arXiv:2604.16188v1 [math.CO],
  17 Apr 2026 — [DD26]'s reference [4], with companion repository
  `ord-ram-num`.
- [Chv77] V. Chvátal, "Tree-complete graph Ramsey numbers," J. Graph Theory
  1 (1977), 93. Cited via its verbatim restatement as [DD26, Theorem 4.13].
