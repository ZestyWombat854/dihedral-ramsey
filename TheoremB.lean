/-
TheoremB.lean — STANDALONE single-file version for the evidence gist.

Machine-checked lower bound of Theorem B (R_dih(P3alt, K_b) >= 2b-1 for
every b >= 1) plus Lemma 3 (Dih(3) = Sym(3)), in Lean 4 core — no mathlib,
no lake project, no imports. Check it with a bare Lean 4 (v4.12.0):

    lean TheoremB.lean

A clean exit (no output, exit code 0) means every theorem in this file is
kernel-checked. The `#print axioms` lines at the very end display the
axiom dependencies of the main theorems; the expected output is
`[propext, Classical.choice, Quot.sound]` — Lean's three standard axioms —
with NO `Lean.ofReduceBool` (i.e. no `native_decide`: the ∀b theorems are
genuine proofs, not compiled enumeration, and the small `decide` examples
are kernel-reduced).

This file is a verbatim concatenation of three files from the research
run's Lean project (canonical copies, in order):
  code/lean/RamseyFormal/Defs.lean         (pod L2 — definitions)
  code/lean/RamseyFormal/KbReduction.lean  (pod L2 — the Lemma-1 parallel)
  code/lean/RamseyFormal/TheoremB.lean     (this submission — the theorems)
with only the `import RamseyFormal.*` lines removed (they become no-ops in
a single file) and this header plus the trailing `#print axioms` block
added. What each theorem states, and what is deliberately NOT formalized
(the Chvátal upper bound), is documented in the third part's own header.
-/

/-
STAGING FILE — written by pod L2, 2026-08-11.

`notes/lean/README.md` (L0's coordination file) did not exist yet when this
was written, so per the L2 dispatch instructions ("if the README/definitions
aren't up yet, draft against the paper's definitions in a clearly-marked
staging file and reconcile when L0 lands") these definitions are drafted
directly against the source paper and the run's own independently-checked
Python reference implementations, NOT against any L0 output. If/when
`notes/lean/README.md` lands with canonical definitions, this file should be
reconciled against it (replace with `import`s of L0's file, keep only what
L0 doesn't cover) — see `notes/lean/L2-log.md` for the reconciliation note.

Source paper: Damnjanović & Đorđević, "Computation of small reflective and
dihedral Ramsey numbers," arXiv:2607.06817v2 [DD26]. Page cites below refer
to this paper (local copy: `artifacts/web/arxiv-2607.06817v2.pdf`). All
constructions here were cross-checked at definition time against two
independent, already-verified Python implementations from this same research
run (`data/referee-batch-6/checker/common.py`, Referee Batch 6; and
`data/referee-reflective-3/encoder/defs.py`, Referee 5) — both themselves
built from the paper's text alone. Where a paper example is quoted verbatim
(e.g. the P₇^alt edge list), it is checked here by `#eval`/`decide` against
that quotation directly, a third independent cross-check.

No Mathlib dependency: this project is pure Lean 4 core. Combinatorics here
is finite, small (n ≤ 17), and fully decidable, so core `List`/`Nat` plus
`decide`/`native_decide` is sufficient and keeps builds fast (seconds, not
the hours a fresh Mathlib build could cost on a shared, niced machine mid-run).
-/

namespace RamseyFormal

/-- A 2-edge-colouring of `K_n` on vertices `{0,...,n-1}`: `col u v` is the
colour of edge `{u,v}`, meaningful for `u < v < n`. `true` = colour 2
("blue"), `false` = colour 1 ("red") — matches [DD26] p.5 eq.(1)-(2)'s own
convention: "x_{u,v} boolean, true iff edge has colour 2." -/
abbrev Coloring := Nat → Nat → Bool

/-- A permutation of `{0,...,m-1}`, represented as a total `Nat → Nat`
function (only its values on `0,...,m-1` are ever consulted). -/
abbrev Perm := Nat → Nat

/-- A pattern graph on vertex set `{0,...,order-1}`, given by an explicit
edge list (pairs `(i,j)` in the pattern's own base labelling; a group
element may send `i`,`j` anywhere in `0,...,order-1`, order not preserved
by `φ` itself — see `imageEdge`). -/
structure Pattern where
  order : Nat
  edges : List (Nat × Nat)
deriving Repr

/-! ### Pattern families ([DD26] §2, p.3, plus the v2-addendum nested-matching
definition on the same page per the paper's §2.2 changelog note). -/

/-- `P_n^mon`: the ordinary path on the natural vertex order, `i ~ i+1`.
[DD26] p.3. Used only for the `Aut`-triviality discussion below, not by any
of the 12 results directly (the paper itself: "used only in stating the
paper's Table 2/4/6 layout"). -/
def monotonePath (n : Nat) : Pattern :=
  { order := n, edges := (List.range (n - 1)).map (fun i => (i, i + 1)) }

/-- Fuel-driven builder for the alternating sequence
`(0, a-1, 1, a-2, 2, a-3, ..., ⌊a/2⌋)` ([DD26] p.3). Fuel = `a` is always
enough (each step consumes two elements of an `a`-element range), so this
terminates structurally on `fuel` well before running out. -/
def altSeqAux : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | n + 1, lo, hi =>
    if lo > hi then []
    else if lo == hi then [lo]
    else lo :: hi :: altSeqAux n (lo + 1) (hi - 1)

def altSeq (a : Nat) : List Nat := altSeqAux a 0 (a - 1)

/-- Consecutive-pair edges of a vertex sequence, each normalised to
`(min, max)` (an unordered edge). -/
def edgesOfSeq : List Nat → List (Nat × Nat)
  | [] => []
  | [_] => []
  | x :: y :: rest => (min x y, max x y) :: edgesOfSeq (y :: rest)

/-- `P_a^alt`: the alternating path ([DD26] p.3). For `a=7`: edges
`{0,6},{1,6},{1,5},{2,5},{2,4},{3,4}` — the paper's own worked example,
checked below by `decide`. -/
def alternatingPath (a : Nat) : Pattern :=
  { order := a, edges := edgesOfSeq (altSeq a) }

/-- `C_n^mon`: `P_n^mon` plus the closing edge `{0,n-1}` ([DD26] p.3,
v2 addendum). Only used here for `n ≥ 3` (Result 7's `C_3^mon`); the paper's
own `C_2^mon := K_2` special case is not needed by any of the 12 results and
is not encoded. -/
def monotoneCycle (n : Nat) : Pattern :=
  { order := n, edges := (0, n - 1) :: (List.range (n - 1)).map (fun i => (i, i + 1)) }

/-- `S_a^sc`: the "start-central" star, vertex `0` (the FIRST vertex in the
fixed natural order, not a middle or last vertex — [DD26] p.3, and flagged
explicitly in `paper/main.md` §9 item 2 as a place a wrong reading silently
produces a different, well-formed, wrong instance) adjacent to all other
`a-1` vertices. -/
def startCentralStar (a : Nat) : Pattern :=
  { order := a, edges := (List.range (a - 1)).map (fun i => (0, i + 1)) }

/-- `M_b^nest` (`b` even): the perfect "nested" matching pairing each vertex
with its antipode, `v ~ b-1-v` ([DD26] p.3, v2 addendum — added for Result
10). `b/2` disjoint edges. -/
def nestedMatching (b : Nat) : Pattern :=
  { order := b, edges := (List.range (b / 2)).map (fun v => (v, b - 1 - v)) }

/-- `K_b`: the complete graph on `{0,...,b-1}`, all `C(b,2)` pairs. -/
def completeGraph (b : Nat) : Pattern :=
  { order := b
    edges := (List.range b).bind (fun i => (List.range b).filterMap
      (fun j => if i < j then some (i, j) else none)) }

/-! ### Cross-checks against the paper's own worked example and against the
run's two independent Python reference implementations
(`defs.py`, Referee 5; `common.py`, Referee Batch 6). All `decide`, all
tiny — this is definitional sanity-checking, not a witness leg. -/

/-- [DD26] p.3, quoted directly in `paper/main.md` §2.2: "For a=7: edges
{0,6},{1,6},{1,5},{2,5},{2,4},{3,4} (6 edges)." -/
example : (alternatingPath 7).edges = [(0,6),(1,6),(1,5),(2,5),(2,4),(3,4)] := by decide

/-- Cross-check against `defs.py`'s own hard-coded assertions
(`palt_edges(3)`, `palt_edges(4)`, `palt_edges(5)`), independently derived
by Referee 5 from the same page-3 definition. -/
example : (alternatingPath 3).edges = [(0,2),(1,2)] := by decide
example : (alternatingPath 4).edges = [(0,3),(1,3),(1,2)] := by decide
example : (alternatingPath 5).edges = [(0,4),(1,4),(1,3),(2,3)] := by decide

/-- Cross-check against `common.py`'s `nested_matching`: `M_4^nest` and
`M_6^nest` have `4/2=2` and `6/2=3` edges respectively, antipodal pairing. -/
example : (nestedMatching 4).edges = [(0,3),(1,2)] := by decide
example : (nestedMatching 6).edges = [(0,5),(1,4),(2,3)] := by decide

/-- Cross-check against `common.py`'s `monotone_cycle`: `C_3^mon` is the
triangle on `{0,1,2}` under the natural order (Recommendation 6,
`paper/main.md` §9: "confirm it is the triangle on {0,1,2}"). -/
example : (monotoneCycle 3).edges = [(0,2),(0,1),(1,2)] := by decide

/-! ### Permutation groups ([DD26] §1-2, p.1-2). -/

/-- Rotation by `c`: `x ↦ (x+c) mod m`. `g^p` in the paper's own generator
notation, `p = c`. -/
def rotPerm (m c : Nat) : Perm := fun x => (x + c) % m

/-- Reflection-then-rotate-by-`c`: `x ↦ (m-1-x+c) mod m`. As `c` ranges over
`0,...,m-1` this produces exactly the same 2m-element *set* of functions as
the paper's own `t ∘ g^p` (`t(x)=m-1-x`, `t∘g^p(x) = m-1-((x+p) mod m)`) —
checked below for `m=7` by `decide` (list-equality up to the natural
index correspondence, not a claim about matching indices pointwise). -/
def reflPerm (m c : Nat) : Perm := fun x => (m - 1 - x + c) % m

/-- The dihedral group `⟨g,t⟩` of order `2m` ([DD26] p.2), given directly in
closed form (paper's own cross-check form, §2.1: "the closed form
{i↦i+c mod m} ∪ {i↦−i+c mod m}") rather than by BFS closure of the two
generators — both referee reports in the source run derived and cross-
checked both forms; here only the closed form is needed. As a `List` (not a
`Finset`), this may contain semantically-duplicate entries for very small
`m`; harmless, since every consumer below only ever does `List.all` over
the group (checking *every* element works — redundant checks change
nothing). -/
def dihedralGroup (m : Nat) : List Perm :=
  (List.range m).map (rotPerm m) ++ (List.range m).map (reflPerm m)

/-- The reflective group `{id, ρ}`, `ρ(x) = m-1-x` — the order-2 subgroup
([DD26] p.2: "The reflective group is the order-2 subgroup {id, ρ}."). -/
def reflectiveGroup (m : Nat) : List Perm := [fun x => x, fun x => m - 1 - x]

/-- Cross-check: dihedral group orders match the run's own referee-recorded
`gamma_order` fields (`data/referee-batch-6/claim*_result.json`) — e.g.
claim1 (`P_9^alt` vs `C_3^mon`, dihedral): `gamma1_order=18`, `gamma2_order=6`. -/
example : (dihedralGroup 9).length = 18 := by decide
example : (dihedralGroup 3).length = 6 := by decide
example : (dihedralGroup 7).length = 14 := by decide
example : (dihedralGroup 12).length = 24 := by decide
example : (dihedralGroup 15).length = 30 := by decide
example : (dihedralGroup 4).length = 8 := by decide
example : (dihedralGroup 6).length = 12 := by decide
/-- Reflective group order is always exactly 2 (claim6: `gamma1_order=2`,
`gamma2_order=2` for `P_7^alt`/`S_8^sc` under the reflective group). -/
example : (reflectiveGroup 7).length = 2 := by decide
example : (reflectiveGroup 8).length = 2 := by decide

/-! ### Γ-embeddability and the SAT-encoding predicate ([DD26] p.1-2, p.5
eqs.(1)-(2)). -/

/-- All strictly-increasing injections `{0,...,m-1} → {0,...,n-1}`,
represented as their (increasing) image lists. Standard "choose" recursion:
include the head of the remaining pool or don't. Structurally recursive on
the pool list in every branch (the `k+1,x::xs => ... ++ combos (k+1) xs`
branch keeps `k+1` fixed but the list argument strictly shrinks), so Lean's
default structural-recursion elaboration accepts this without a manual
`termination_by`. -/
def combos : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (combos k xs).map (x :: ·) ++ combos (k + 1) xs

/-- The increasing injections `ψ : V(H) → V(K_n)` of [DD26] p.1-2, as image
lists: `ψ i = (this list).getD i 0`. -/
def increasingMaps (m n : Nat) : List (List Nat) := combos m (List.range n)

/-- The image, under `ψ = S` (an increasing-injection image list) composed
with `φ ∈ Γ`, of a pattern edge `(i,j)` — i.e. `(ψ∘φ)(i), (ψ∘φ)(j)`,
normalised to `(min,max)` since host colourings are only defined for
`u < v`. This is exactly [DD26] p.1-2's "homomorphism of the form ψ∘φ." -/
def imageEdge (S : List Nat) (φ : Perm) (e : Nat × Nat) : Nat × Nat :=
  let a := S.getD (φ e.1) 0
  let b := S.getD (φ e.2) 0
  (min a b, max a b)

/-- Is the `Γ`-copy of `H` placed by `(φ,S)` entirely colour `c`? -/
def isMonochromatic (col : Coloring) (c : Bool) (H : Pattern) (φ : Perm) (S : List Nat) : Bool :=
  H.edges.all (fun e => let (u, v) := imageEdge S φ e; col u v == c)

/-- No `Γ`-embedded copy of `H` is monochromatic in colour `c`, inside
`K_n` — i.e. [DD26] p.5 eq.(1)/(2)'s clause set is satisfied by `col`, for
this one pattern/colour/host-size. `c=false`: forbids a colour-1 copy
(eq.(1)); `c=true`: forbids a colour-2 copy (eq.(2)). -/
def noMonoCopy (col : Coloring) (c : Bool) (H : Pattern) (Γ : List Perm) (n : Nat) : Bool :=
  (increasingMaps H.order n).all (fun S => Γ.all (fun φ => ! isMonochromatic col c H φ S))

/-- A 2-colouring of `K_n` witnesses `R((H1,Γ1),(H2,Γ2)) > n`: no colour-1
`Γ1`-copy of `H1`, no colour-2 `Γ2`-copy of `H2`. -/
def validWitness (H1 : Pattern) (Γ1 : List Perm) (H2 : Pattern) (Γ2 : List Perm)
    (col : Coloring) (n : Nat) : Bool :=
  noMonoCopy col false H1 Γ1 n && noMonoCopy col true H2 Γ2 n

/-- The **permutational Ramsey lower bound** `R((H1,Γ1),(H2,Γ2)) ≥ n`
([DD26] p.1-2's definition, lower-bound half only): a colouring of `K_{n-1}`
exists that avoids both forbidden monochromatic copies. This is the
*existential witness* half of the paper's `min n such that ...` definition
— it is exactly what a SAT witness at `n-1` proves, and exactly what
`decide`/`native_decide` can kernel-check once a concrete `col` is supplied
(§8 of `paper/main.md` is explicit that the matching *upper*-bound half,
`R ≤ n`, is a universally-quantified statement over the infinite `Coloring`
type, decided in this run only by an external DRAT proof — not attempted
here; see Statements.lean and notes/lean/L2-log.md for the honest scope
split). -/
def PermRamseyGE (H1 : Pattern) (Γ1 : List Perm) (H2 : Pattern) (Γ2 : List Perm) (n : Nat) : Prop :=
  ∃ col : Coloring, validWitness H1 Γ1 H2 Γ2 col (n - 1) = true

/-- The **full** permutational Ramsey number statement ([DD26] p.1-2's
`min n such that ...` definition, both directions): `n` is exactly
`R((H1,Γ1),(H2,Γ2))` iff (a) every 2-colouring of `K_n` has a forbidden
monochromatic copy on some side (the *upper*-bound half — `n` is high
enough), and (b) a `K_{n-1}` colouring avoiding both exists (`PermRamseyGE`,
the *lower*-bound half — `n` is not too high, i.e. minimal). Introduced as
a bare `Prop`-valued `def`, never asserted as a `theorem` or `axiom`
without a real proof term: for the 10 dihedral/reflective results in
Statements.lean, only the (b) half is proved here (see that file and
notes/lean/L2-log.md for exactly which theorems close it, and why (a) is
out of this pod's scope — it needs the external DRAT certificate, not
reproved in Lean). -/
def IsPermRamsey (H1 : Pattern) (Γ1 : List Perm) (H2 : Pattern) (Γ2 : List Perm) (n : Nat) : Prop :=
  (∀ col : Coloring, validWitness H1 Γ1 H2 Γ2 col n = false) ∧
  PermRamseyGE H1 Γ1 H2 Γ2 n

end RamseyFormal

/-
STAGING FILE — pod L2, 2026-08-11. See Defs.lean header for the
reconcile-with-L0 note; same status applies here.

Mission item 1: "K_b under the group action should reduce to ordinary
containment, prove that as a lemma if true." `paper/main.md` §5.6 records
the referees' own justification: "exploiting that Aut(K_b) already contains
every φ so all dihedral images of a K6 clause are identical" — `defs.py`
(Referee 5) states the same fact in prose but neither Python reference
proves it beyond "validated empirically" (paper's own words, §5.6). This
file proves it as an actual theorem: for the complete-graph pattern, using
the full permutation group vs. the trivial group changes nothing, for
*any* coloring and *any* host size — not just the specific witnesses this
run happens to have on disk.

NOT load-bearing for the 7 witness-leg proofs in Witnesses/: those check
`noMonoCopy` against the *honest* full dihedral/reflective group directly,
exactly matching R_dih/R_ref's own definition, so correctness of the 7
witness legs does not depend on anything in this file. This lemma is
additional mathematical content requested by the mission, not
infrastructure the witness legs need.
-/

namespace RamseyFormal

/-- `φ` permutes `{0,...,b-1}`: maps the range into itself, injectively and
surjectively. (Stated with all three conditions directly, rather than
derived from e.g. "injective ⟹ surjective on a finite set", to avoid
needing pigeonhole/cardinality machinery this project doesn't otherwise
need — Mathlib-free by design, see Defs.lean header.) -/
structure IsPermOn (b : Nat) (φ : Perm) : Prop where
  mapsInto : ∀ x, x < b → φ x < b
  inj : ∀ x y, x < b → y < b → φ x = φ y → x = y
  surj : ∀ y, y < b → ∃ x, x < b ∧ φ x = y

/-- The identity permutation trivially satisfies `IsPermOn`. -/
theorem isPermOn_id (b : Nat) : IsPermOn b (fun x => x) :=
  { mapsInto := fun _ h => h
    inj := fun _ _ _ _ h => h
    surj := fun y h => ⟨y, h, rfl⟩ }

/-- Tiny Mathlib-free helper: Bool equality is the And-both-ways of the two
`= true` propositions. Used once, to turn the top-level `Bool = Bool` goal
into an `Iff` we can `constructor` on. -/
theorem bool_eq_iff_iff (a b : Bool) : (a = b) ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> decide

/-- Core reindexing step: a `b`-bounded, pairwise property `Q` holds after
composing both arguments with any `φ` satisfying `IsPermOn b` iff it holds
outright. -/
theorem forall_pairs_reindex
    {b : Nat} {φ : Perm} (hφ : IsPermOn b φ) (Q : Nat → Nat → Prop) :
    (∀ i j, i < b → j < b → i ≠ j → Q (φ i) (φ j)) ↔
    (∀ i' j', i' < b → j' < b → i' ≠ j' → Q i' j') := by
  constructor
  · intro h i' j' hi' hj' hne
    obtain ⟨i, hi, hφi⟩ := hφ.surj i' hi'
    obtain ⟨j, hj, hφj⟩ := hφ.surj j' hj'
    have hij : i ≠ j := by
      intro heq; apply hne; rw [← hφi, ← hφj, heq]
    have := h i j hi hj hij
    rwa [hφi, hφj] at this
  · intro h i j hi hj hne
    have hne' : φ i ≠ φ j := fun heq => hne (hφ.inj i j hi hj heq)
    exact h (φ i) (φ j) (hφ.mapsInto i hi) (hφ.mapsInto j hj) hne'

/-- Membership in `K_b`'s edge list, unfolded to the raw arithmetic
condition. -/
theorem mem_completeGraph_edges (b i j : Nat) :
    (i, j) ∈ (completeGraph b).edges ↔ i < b ∧ j < b ∧ i < j := by
  simp only [completeGraph, List.mem_bind, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i', hi', j', hj', hcond⟩
    split at hcond
    · cases hcond; rename_i hlt; exact ⟨hi', hj', hlt⟩
    · cases hcond
  · rintro ⟨hi, hj, hlt⟩
    exact ⟨i, hi, j, hj, by simp [hlt]⟩

/-- For any `φ` permuting `{0,...,b-1}`, checking `K_b`-monochromaticity
through `φ` is the same as checking it through the identity — the pointwise
core of the reduction lemma. The reindexing happens over the *host*
vertices `S.getD (φ ·) 0`, not over the raw pattern indices — this is the
one place a naive first attempt at this lemma goes wrong. -/
theorem isMonochromatic_completeGraph_eq_id
    {b : Nat} {φ : Perm} (hφ : IsPermOn b φ)
    (col : Coloring) (c : Bool) (S : List Nat) :
    isMonochromatic col c (completeGraph b) φ S =
    isMonochromatic col c (completeGraph b) (fun x => x) S := by
  rw [bool_eq_iff_iff]
  simp only [isMonochromatic, List.all_eq_true]
  have hQ := forall_pairs_reindex hφ
    (fun u v => col (min (S.getD u 0) (S.getD v 0)) (max (S.getD u 0) (S.getD v 0)) = c)
  constructor
  · intro hp e he
    obtain ⟨i, j, hij⟩ : ∃ i j, e = (i, j) := ⟨e.1, e.2, rfl⟩
    subst hij
    have hmem := (mem_completeGraph_edges b i j).mp he
    have hp' : ∀ i' j', i' < b → j' < b → i' ≠ j' →
        col (min (S.getD (φ i') 0) (S.getD (φ j') 0))
            (max (S.getD (φ i') 0) (S.getD (φ j') 0)) = c := by
      intro i' j' hi' hj' hne'
      rcases Nat.lt_or_ge i' j' with hlt | hge
      · have hx := hp (i', j') ((mem_completeGraph_edges b i' j').mpr ⟨hi', hj', hlt⟩)
        simpa [imageEdge] using hx
      · have hgt : j' < i' := by omega
        have hx := hp (j', i') ((mem_completeGraph_edges b j' i').mpr ⟨hj', hi', hgt⟩)
        simp only [imageEdge, beq_iff_eq] at hx
        have e1 : min (S.getD (φ j') 0) (S.getD (φ i') 0)
                = min (S.getD (φ i') 0) (S.getD (φ j') 0) := by omega
        have e2 : max (S.getD (φ j') 0) (S.getD (φ i') 0)
                = max (S.getD (φ i') 0) (S.getD (φ j') 0) := by omega
        rwa [e1, e2] at hx
    have := hQ.mp hp' i j hmem.1 hmem.2.1 (Nat.ne_of_lt hmem.2.2)
    simpa [imageEdge] using this
  · intro hp e he
    obtain ⟨i, j, hij⟩ : ∃ i j, e = (i, j) := ⟨e.1, e.2, rfl⟩
    subst hij
    have hmem := (mem_completeGraph_edges b i j).mp he
    have hp' : ∀ i' j', i' < b → j' < b → i' ≠ j' →
        col (min (S.getD i' 0) (S.getD j' 0)) (max (S.getD i' 0) (S.getD j' 0)) = c := by
      intro i' j' hi' hj' hne'
      rcases Nat.lt_or_ge i' j' with hlt | hge
      · have hx := hp (i', j') ((mem_completeGraph_edges b i' j').mpr ⟨hi', hj', hlt⟩)
        simpa [imageEdge] using hx
      · have hgt : j' < i' := by omega
        have hx := hp (j', i') ((mem_completeGraph_edges b j' i').mpr ⟨hj', hi', hgt⟩)
        simp only [imageEdge, beq_iff_eq] at hx
        have e1 : min (S.getD j' 0) (S.getD i' 0) = min (S.getD i' 0) (S.getD j' 0) := by omega
        have e2 : max (S.getD j' 0) (S.getD i' 0) = max (S.getD i' 0) (S.getD j' 0) := by omega
        rwa [e1, e2] at hx
    have := hQ.mpr hp' i j hmem.1 hmem.2.1 (Nat.ne_of_lt hmem.2.2)
    simpa [imageEdge] using this

/-- **The K_b reduction lemma.** Checking `Γ`-embeddability of the complete
graph `K_b` in colour `c` is exactly the same as checking plain
(order-preserving, ungrouped) containment — for *any* nonempty `Γ` all of
whose elements permute `{0,...,b-1}`, *any* colouring, *any* host size.
This formalizes `paper/main.md` §5.6's "Aut(K_b) already contains every φ"
claim, and its Recommendation-9-item-6-tier empirical validation, into an
actual proof. -/
theorem noMonoCopy_completeGraph_reduce
    (b n : Nat) (c : Bool) (col : Coloring) (Γ : List Perm)
    (hΓ : ∀ φ ∈ Γ, IsPermOn b φ) (hne : Γ ≠ []) :
    noMonoCopy col c (completeGraph b) Γ n = noMonoCopy col c (completeGraph b) [fun x => x] n := by
  simp only [noMonoCopy]
  rw [bool_eq_iff_iff]
  simp only [List.all_eq_true, List.mem_singleton]
  constructor
  · intro h S hS φ hφ
    subst hφ
    cases Γ with
    | nil => exact absurd rfl hne
    | cons φ0 rest =>
      have hφ0mem : φ0 ∈ φ0 :: rest := List.mem_cons_self _ _
      have hstep := h S hS φ0 hφ0mem
      rwa [isMonochromatic_completeGraph_eq_id (hΓ φ0 hφ0mem) col c S] at hstep
  · intro h S hS φ hφmem
    rw [isMonochromatic_completeGraph_eq_id (hΓ φ hφmem) col c S]
    exact h S hS (fun x => x) rfl

end RamseyFormal

/-
TheoremB.lean — the ∀b lower bound of Theorem B, plus Lemma 3 (Dih(3)=Sym(3)),
machine-checked. Written 2026-08-12 for the Theorem B submission package
(`notes/theorem-b-preprint.md` §11; build/axiom log:
`notes/lean/theoremB-log.md`).

Extends pod L2's staging project: imports `Defs.lean`/`KbReduction.lean`,
never redefines their objects (per `notes/lean/README.md`'s one rule).

WHAT IS PROVED HERE (zero `sorry`, no `native_decide` — the `∀b` theorems
are genuine arguments, not kernel enumeration, so they carry only the three
standard axioms `propext`/`Classical.choice`/`Quot.sound`):

* `rotPerm_isPermOn` / `reflPerm_isPermOn` / `dihedralGroup_isPermOn` —
  every element of `dihedralGroup m` (`m ≥ 1`, symbolic) genuinely permutes
  `{0,...,m-1}`, by explicit two-sided inverses.
* `lemma3_dih3_eq_sym3` — **Lemma 3, Dih(3) = Sym(3)**, in this project's
  function encoding: every `dihedralGroup 3` element permutes `{0,1,2}`,
  and every permutation of `{0,1,2}` agrees on `{0,1,2}` with some
  `dihedralGroup 3` element.
* `noRed_P3alt` / `noBlue_Kb` / `lemma2_blockWitness` — **Lemma 2 at
  a = 3**: the block coloring (`u,v` red iff `u/2 = v/2`) admits no
  Γ-embedded `P₃ᵃˡᵗ` in red (any host size!) and no Λ-embedded `K_b` in
  blue on `2(b-1)` vertices — for ANY `Γ` of permutations of `{0,1,2}` and
  ANY `Λ` of permutations of `{0,...,b-1}`, not only the dihedral groups.
* `theoremB_lowerBound` — the lower-bound half of Theorem B, all b at once:
  `PermRamseyGE (alternatingPath 3) (dihedralGroup 3) (completeGraph b)
  (dihedralGroup b) (2*b - 1)` for every `b ≥ 1`, i.e.
  R_dih(P₃ᵃˡᵗ, K_b) ≥ 2b−1. (`theoremB_lowerBound_all_groups` is the same
  statement for arbitrary permutation families — Lemma 2's full group
  generality.)

```diff
- ===== NOT DONE =====
- The UPPER bound R_dih(P3alt, K_b) <= 2b-1 is NOT formalized, for any b
- beyond what kernel enumeration could reach elsewhere; in the submission
- package it rests on the citation chain Dih(3)=Sym(3) + Chvatal 1977 via
- [DD26, Theorem 4.13]. Lemma 1's formal counterpart is L2's
- KbReduction.lean (imported, cited), not re-proved here. Lemma 2 is
- formalized in its a=3 specialization (the only case Theorem B needs),
- general in both groups and in the host size on the red side, but NOT in
- the pattern argument ("any connected H of order a" stays paper-only).
- WHAT IT WOULD CHANGE: none of these gaps weakens the lower-bound claim
- proved here; the exact-value claim R = 2b-1 remains exactly as strong as
- the Chvatal citation, as the preprint's Section 11 already discloses.
```
-/

namespace RamseyFormal
namespace TheoremB

/-! ### The witness coloring (Lemma 2's block construction at a = 3) -/

/-- Block coloring: `u`,`v` are RED (colour 1, `false`) iff same size-2
block `{2q, 2q+1}`, i.e. `u/2 = v/2`; cross-block pairs BLUE (`true`).
[DD26]-faithful colour convention from `Defs.lean`: `true` = colour 2. -/
def blockColoring : Coloring := fun u v => !(u / 2 == v / 2)

theorem blockColoring_false_iff (u v : Nat) :
    blockColoring u v = false ↔ u / 2 = v / 2 := by
  simp [blockColoring]

theorem blockColoring_true_iff (u v : Nat) :
    blockColoring u v = true ↔ ¬ u / 2 = v / 2 := by
  simp [blockColoring]

/-- min/max don't affect the same-block test. -/
theorem minmax_same_block (u v : Nat) :
    (min u v) / 2 = (max u v) / 2 ↔ u / 2 = v / 2 := by
  rcases Nat.le_total u v with h | h
  · rw [Nat.min_eq_left h, Nat.max_eq_right h]
  · rw [Nat.min_eq_right h, Nat.max_eq_left h]
    exact ⟨fun hh => hh.symm, fun hh => hh.symm⟩

/-! ### List helpers (hand-rolled, core-only, per the project's no-mathlib
decision — see `Defs.lean` header) -/

/-- `List.range n` is strictly sorted. -/
theorem pairwise_lt_range (n : Nat) : (List.range n).Pairwise (· < ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ]
    refine List.pairwise_append.mpr ⟨ih, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact List.mem_range.mp ha

/-- Members of `combos k xs`: right length, sorted (for a sorted pool),
entries from the pool. -/
theorem combos_spec : ∀ (k : Nat) (xs : List Nat), xs.Pairwise (· < ·) →
    ∀ S ∈ combos k xs, S.length = k ∧ S.Pairwise (· < ·) ∧ ∀ v ∈ S, v ∈ xs := by
  intro k xs
  induction xs generalizing k with
  | nil =>
    intro _ S hS
    match k, hS with
    | 0, hS =>
      simp only [combos, List.mem_singleton] at hS
      subst hS
      exact ⟨rfl, List.Pairwise.nil, by simp⟩
    | k + 1, hS => simp [combos] at hS
  | cons x xs ih =>
    intro hpw S hS
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp hpw
    match k with
    | 0 =>
      simp only [combos, List.mem_singleton] at hS
      subst hS
      exact ⟨rfl, List.Pairwise.nil, by simp⟩
    | k + 1 =>
      simp only [combos, List.mem_append] at hS
      rcases hS with hL | hR
      · obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hL
        obtain ⟨hlen, hpwT, hmemT⟩ := ih k hxs T hT
        refine ⟨by simp [hlen], ?_, ?_⟩
        · exact List.pairwise_cons.mpr
            ⟨fun v hv => hx v (hmemT v hv), hpwT⟩
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact List.mem_cons_self _ _
          · exact List.mem_cons_of_mem _ (hmemT v hv)
      · obtain ⟨hlen, hpwS, hmemS⟩ := ih (k + 1) hxs S hR
        exact ⟨hlen, hpwS, fun v hv => List.mem_cons_of_mem _ (hmemS v hv)⟩

/-- Members of `increasingMaps m n` are strictly increasing length-`m`
lists of values `< n` — [DD26]'s increasing injections, as image lists. -/
theorem increasingMaps_spec (m n : Nat) :
    ∀ S ∈ increasingMaps m n,
      S.length = m ∧ S.Pairwise (· < ·) ∧ ∀ v ∈ S, v < n := by
  intro S hS
  obtain ⟨h1, h2, h3⟩ := combos_spec m (List.range n) (pairwise_lt_range n) S hS
  exact ⟨h1, h2, fun v hv => List.mem_range.mp (h3 v hv)⟩

theorem getD_mem : ∀ (l : List Nat) (i : Nat), i < l.length → l.getD i 0 ∈ l := by
  intro l
  induction l with
  | nil => intro i h; simp at h
  | cons a l ih =>
    intro i h
    match i with
    | 0 => exact List.mem_cons_self _ _
    | i + 1 =>
      exact List.mem_cons_of_mem _ (ih i (by simpa using Nat.lt_of_succ_lt_succ h))

theorem mem_getD : ∀ (l : List Nat) (v : Nat), v ∈ l →
    ∃ i, i < l.length ∧ l.getD i 0 = v := by
  intro l
  induction l with
  | nil => intro v hv; simp at hv
  | cons a l ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨i, hi, hgd⟩ := ih v hv
      exact ⟨i + 1, by simpa using Nat.succ_lt_succ hi, hgd⟩

/-- On a strictly sorted list, `getD` at distinct in-range positions gives
distinct values (in fact ordered). -/
theorem pairwise_getD_lt : ∀ (l : List Nat), l.Pairwise (· < ·) →
    ∀ i j, i < j → j < l.length → l.getD i 0 < l.getD j 0 := by
  intro l
  induction l with
  | nil => intro _ i j _ h; simp at h
  | cons a l ih =>
    intro hpw i j hij hj
    obtain ⟨ha, hpl⟩ := List.pairwise_cons.mp hpw
    match i, j, hij with
    | 0, j + 1, _ =>
      have hjl : j < l.length := by simpa using Nat.lt_of_succ_lt_succ hj
      exact ha _ (getD_mem l j hjl)
    | i + 1, j + 1, hij =>
      exact ih hpl i j (Nat.lt_of_succ_lt_succ hij) (Nat.lt_of_succ_lt_succ hj)

/-- Partition of a list's length by a Bool predicate. -/
theorem length_filter_partition (l : List Nat) (p : Nat → Bool) :
    (l.filter p).length + (l.filter (fun a => !(p a))).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hpa : p a <;> simp [List.filter_cons, hpa] <;> omega

/-- Filtering preserves `Pairwise`. -/
theorem pairwise_filter (p : Nat → Bool) :
    ∀ (l : List Nat), l.Pairwise (· < ·) → (l.filter p).Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro hpw
    obtain ⟨ha, hpl⟩ := List.pairwise_cons.mp hpw
    cases hpa : p a
    · simpa [List.filter_cons, hpa] using ih hpl
    · rw [List.filter_cons, hpa]
      exact List.pairwise_cons.mpr
        ⟨fun v hv => ha v (List.mem_filter.mp hv).1, ih hpl⟩

/-! ### Pigeonhole: `k+`-many sorted values below `2k` share a block -/

/-- Bool predicate for the pigeonhole filter step: `v` lies below the top
block, i.e. `v < 2k`. Named (not a lambda) so filter terms stay
syntactically stable across the lemmas below. -/
def below (k v : Nat) : Bool := decide (v < 2 * k)

/-- More than `k` distinct values `< 2k` cannot occupy `k` size-2 blocks
injectively: two of them share a block. Hand-rolled induction on `k`
(top block `{2k, 2k+1}` either holds two values — done — or at most one,
which filtering removes). -/
theorem exists_same_block : ∀ (k : Nat) (L : List Nat),
    L.Pairwise (· < ·) → (∀ v ∈ L, v < 2 * k) → k < L.length →
    ∃ x, x ∈ L ∧ ∃ y, y ∈ L ∧ x < y ∧ x / 2 = y / 2 := by
  intro k
  induction k with
  | zero =>
    intro L _ hlt hlen
    match L, hlen with
    | v :: _, _ =>
      have := hlt v (List.mem_cons_self _ _)
      omega
  | succ k ih =>
    intro L hpw hlt hlen
    by_cases htwo : ∃ x, x ∈ L ∧ ∃ y, y ∈ L ∧ x < y ∧ 2 * k ≤ x
    · obtain ⟨x, hx, y, hy, hxy, hx2⟩ := htwo
      have hxlt := hlt x hx
      have hylt := hlt y hy
      exact ⟨x, hx, y, hy, hxy, by omega⟩
    · -- at most one element is ≥ 2k: drop it, recurse on the rest
      have hpart := length_filter_partition L (below k)
      have hsmall : (L.filter (fun a => !(below k a))).length ≤ 1 := by
        cases hbig : L.filter (fun a => !(below k a)) with
        | nil => simp
        | cons a t =>
          cases t with
          | nil => simp
          | cons a' t' =>
            exfalso
            have hpwbig := pairwise_filter (fun a => !(below k a)) L hpw
            rw [hbig] at hpwbig
            have haa' : a < a' := (List.pairwise_cons.mp hpwbig).1 a'
              (List.mem_cons_self _ _)
            have hamem : a ∈ L.filter (fun a => !(below k a)) := by
              rw [hbig]; exact List.mem_cons_self _ _
            have ha'mem : a' ∈ L.filter (fun a => !(below k a)) := by
              rw [hbig]; exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)
            have haL := List.mem_filter.mp hamem
            have ha'L := List.mem_filter.mp ha'mem
            have ha2 : 2 * k ≤ a := by
              have hb := haL.2
              simp [below] at hb
              omega
            exact htwo ⟨a, haL.1, a', ha'L.1, haa', ha2⟩
      have hlen' : k < (L.filter (below k)).length := by omega
      have hpw' := pairwise_filter (below k) L hpw
      have hlt' : ∀ v ∈ L.filter (below k), v < 2 * k := by
        intro v hv
        have hb := (List.mem_filter.mp hv).2
        simpa [below] using hb
      obtain ⟨x, hx, y, hy, hxy, hq⟩ := ih _ hpw' hlt' hlen'
      exact ⟨x, (List.mem_filter.mp hx).1, y, (List.mem_filter.mp hy).1, hxy, hq⟩

/-! ### The dihedral group consists of genuine permutations
(explicit two-sided inverses; `m` symbolic throughout) -/

theorem rotPerm_isPermOn (m c : Nat) (hm : 1 ≤ m) (hc : c < m) :
    IsPermOn m (rotPerm m c) := by
  have hinv_right : ∀ y, y < m → rotPerm m c ((y + (m - c)) % m) = y := by
    intro y hy
    show ((y + (m - c)) % m + c) % m = y
    rw [Nat.mod_add_mod]
    have h1 : y + (m - c) + c = y + m := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hy]
  have hinv_left : ∀ x, x < m → (rotPerm m c x + (m - c)) % m = x := by
    intro x hx
    show ((x + c) % m + (m - c)) % m = x
    rw [Nat.mod_add_mod]
    have h1 : x + c + (m - c) = x + m := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hx]
  refine
    { mapsInto := fun x _ => Nat.mod_lt _ (by omega)
      inj := ?_
      surj := ?_ }
  · intro x y hx hy h
    have hx' := hinv_left x hx
    have hy' := hinv_left y hy
    rw [← hx', ← hy', h]
  · intro y hy
    exact ⟨(y + (m - c)) % m, Nat.mod_lt _ (by omega), hinv_right y hy⟩

theorem reflPerm_isPermOn (m c : Nat) (hm : 1 ≤ m) (hc : c < m) :
    IsPermOn m (reflPerm m c) := by
  -- reflPerm m c x = (m - 1 - x + c) % m; inverse: y ↦ m - 1 - ((y + (m - c)) % m)
  have hinv_right : ∀ y, y < m → reflPerm m c (m - 1 - ((y + (m - c)) % m)) = y := by
    intro y hy
    show (m - 1 - (m - 1 - ((y + (m - c)) % m)) + c) % m = y
    have ht : (y + (m - c)) % m < m := Nat.mod_lt _ (by omega)
    have h1 : m - 1 - (m - 1 - ((y + (m - c)) % m)) = (y + (m - c)) % m := by omega
    rw [h1, Nat.mod_add_mod]
    have h2 : y + (m - c) + c = y + m := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hy]
  have hinv_left : ∀ x, x < m → m - 1 - ((reflPerm m c x + (m - c)) % m) = x := by
    intro x hx
    show m - 1 - (((m - 1 - x + c) % m + (m - c)) % m) = x
    rw [Nat.mod_add_mod]
    have h1 : m - 1 - x + c + (m - c) = (m - 1 - x) + m := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : m - 1 - x < m)]
    omega
  refine
    { mapsInto := fun x _ => Nat.mod_lt _ (by omega)
      inj := ?_
      surj := ?_ }
  · intro x y hx hy h
    have hx' := hinv_left x hx
    have hy' := hinv_left y hy
    rw [← hx', ← hy', h]
  · intro y hy
    refine ⟨m - 1 - ((y + (m - c)) % m), by omega, hinv_right y hy⟩

/-- Every element of `dihedralGroup m` (`m ≥ 1`) genuinely permutes
`{0,...,m-1}`. Discharges `KbReduction.lean`'s `IsPermOn` hypothesis for
the actual dihedral groups, and feeds every theorem below. -/
theorem dihedralGroup_isPermOn (m : Nat) (hm : 1 ≤ m) :
    ∀ φ ∈ dihedralGroup m, IsPermOn m φ := by
  intro φ hφ
  simp only [dihedralGroup, List.mem_append, List.mem_map, List.mem_range] at hφ
  rcases hφ with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · exact rotPerm_isPermOn m c hm hc
  · exact reflPerm_isPermOn m c hm hc

/-! ### Lemma 3: Dih(3) = Sym(3) -/

theorem mem_dihedralGroup_rot (m c : Nat) (hc : c < m) :
    rotPerm m c ∈ dihedralGroup m :=
  List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

theorem mem_dihedralGroup_refl (m c : Nat) (hc : c < m) :
    reflPerm m c ∈ dihedralGroup m :=
  List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

/-- Sym(3) ⊆ Dih(3): every permutation of `{0,1,2}` agrees on `{0,1,2}`
with an element of `dihedralGroup 3`. (Function encoding forces "agrees on
`{0,1,2}`" rather than plain equality: `Perm` is all of `Nat → Nat`, and
only values below the order are ever consulted — see `Defs.lean`.) -/
theorem lemma3_sym3_covered (φ : Perm) (hφ : IsPermOn 3 φ) :
    ∃ ψ ∈ dihedralGroup 3, ∀ x, x < 3 → φ x = ψ x := by
  have h0 := hφ.mapsInto 0 (by omega)
  have h1 := hφ.mapsInto 1 (by omega)
  have h2 := hφ.mapsInto 2 (by omega)
  have h01 : φ 0 ≠ φ 1 := fun h => absurd (hφ.inj 0 1 (by omega) (by omega) h) (by omega)
  have h02 : φ 0 ≠ φ 2 := fun h => absurd (hφ.inj 0 2 (by omega) (by omega) h) (by omega)
  have h12 : φ 1 ≠ φ 2 := fun h => absurd (hφ.inj 1 2 (by omega) (by omega) h) (by omega)
  have htriple :
      (φ 0 = 0 ∧ φ 1 = 1 ∧ φ 2 = 2) ∨ (φ 0 = 1 ∧ φ 1 = 2 ∧ φ 2 = 0) ∨
      (φ 0 = 2 ∧ φ 1 = 0 ∧ φ 2 = 1) ∨ (φ 0 = 2 ∧ φ 1 = 1 ∧ φ 2 = 0) ∨
      (φ 0 = 0 ∧ φ 1 = 2 ∧ φ 2 = 1) ∨ (φ 0 = 1 ∧ φ 1 = 0 ∧ φ 2 = 2) := by
    omega
  have hcase : ∀ x, x < 3 → ∀ (ψ : Perm), φ 0 = ψ 0 → φ 1 = ψ 1 → φ 2 = ψ 2 → φ x = ψ x := by
    intro x hx ψ e0 e1 e2
    match x, hx with
    | 0, _ => exact e0
    | 1, _ => exact e1
    | 2, _ => exact e2
  rcases htriple with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ |
    ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
  · -- (0,1,2) = rotPerm 3 0
    exact ⟨rotPerm 3 0, mem_dihedralGroup_rot 3 0 (by omega),
      fun x hx => hcase x hx _ (by simp [rotPerm, e0]) (by simp [rotPerm, e1])
        (by simp [rotPerm, e2])⟩
  · -- (1,2,0) = rotPerm 3 1
    exact ⟨rotPerm 3 1, mem_dihedralGroup_rot 3 1 (by omega),
      fun x hx => hcase x hx _ (by simp [rotPerm, e0]) (by simp [rotPerm, e1])
        (by simp [rotPerm, e2])⟩
  · -- (2,0,1) = rotPerm 3 2
    exact ⟨rotPerm 3 2, mem_dihedralGroup_rot 3 2 (by omega),
      fun x hx => hcase x hx _ (by simp [rotPerm, e0]) (by simp [rotPerm, e1])
        (by simp [rotPerm, e2])⟩
  · -- (2,1,0) = reflPerm 3 0
    exact ⟨reflPerm 3 0, mem_dihedralGroup_refl 3 0 (by omega),
      fun x hx => hcase x hx _ (by simp [reflPerm, e0]) (by simp [reflPerm, e1])
        (by simp [reflPerm, e2])⟩
  · -- (0,2,1) = reflPerm 3 1
    exact ⟨reflPerm 3 1, mem_dihedralGroup_refl 3 1 (by omega),
      fun x hx => hcase x hx _ (by simp [reflPerm, e0]) (by simp [reflPerm, e1])
        (by simp [reflPerm, e2])⟩
  · -- (1,0,2) = reflPerm 3 2
    exact ⟨reflPerm 3 2, mem_dihedralGroup_refl 3 2 (by omega),
      fun x hx => hcase x hx _ (by simp [reflPerm, e0]) (by simp [reflPerm, e1])
        (by simp [reflPerm, e2])⟩

/-- **Lemma 3 (Dih(3) = Sym(3))**, both inclusions, in the function
encoding: `dihedralGroup 3` consists of permutations of `{0,1,2}`, and
every permutation of `{0,1,2}` is (on `{0,1,2}`) one of them. -/
theorem lemma3_dih3_eq_sym3 :
    (∀ φ ∈ dihedralGroup 3, IsPermOn 3 φ) ∧
    (∀ φ : Perm, IsPermOn 3 φ → ∃ ψ ∈ dihedralGroup 3, ∀ x, x < 3 → φ x = ψ x) :=
  ⟨dihedralGroup_isPermOn 3 (by omega), lemma3_sym3_covered⟩

/-- Kernel-checked spot check of the same fact: the six value-triples of
`dihedralGroup 3` are exactly the 3! = 6 permutations of `(0,1,2)`.
(`decide` — no `native_decide`.) -/
example : (dihedralGroup 3).map (fun φ => (φ 0, φ 1, φ 2)) =
    [(0, 1, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0), (0, 2, 1), (1, 0, 2)] := by decide

/-- Contrast (uniqueness of the collapse, smallest case): Dih(4) has 8
elements but Sym(4) has 24 — e.g. the transposition swapping only 0,1 is
not in `dihedralGroup 4`. Kernel-checked on value tables. -/
example : ¬ ∃ ψ ∈ dihedralGroup 4, (ψ 0, ψ 1, ψ 2, ψ 3) = (1, 0, 2, 3) := by decide

/-! ### Lemma 2 at a = 3, red side: no Γ-embedded P₃ᵃˡᵗ, any host size -/

theorem alternatingPath3_edges : (alternatingPath 3).edges = [(0, 2), (1, 2)] := by
  decide

/-- The block coloring's red graph is a matching (max degree 1), and any
Γ-embedded `P₃ᵃˡᵗ` needs two red edges sharing the image of pattern-vertex
2 — impossible. Holds for ANY `Γ` of genuine permutations of `{0,1,2}` and
ANY host size `n`. -/
theorem noRed_P3alt (Γ : List Perm) (hΓ : ∀ φ ∈ Γ, IsPermOn 3 φ) (n : Nat) :
    noMonoCopy blockColoring false (alternatingPath 3) Γ n = true := by
  rw [noMonoCopy, List.all_eq_true]
  intro S hS
  rw [List.all_eq_true]
  intro φ hφ
  obtain ⟨hlen, hpw, _⟩ := increasingMaps_spec (alternatingPath 3).order n S hS
  cases hmono : isMonochromatic blockColoring false (alternatingPath 3) φ S with
  | false => rfl
  | true =>
    exfalso
    -- unpack the two red-edge facts
    rw [isMonochromatic, alternatingPath3_edges, List.all_eq_true] at hmono
    have hred02 := hmono (0, 2) (List.mem_cons_self _ _)
    have hred12 := hmono (1, 2) (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
    simp only [imageEdge, beq_iff_eq] at hred02 hred12
    have hq02 : (S.getD (φ 0) 0) / 2 = (S.getD (φ 2) 0) / 2 :=
      (minmax_same_block _ _).mp ((blockColoring_false_iff _ _).mp hred02)
    have hq12 : (S.getD (φ 1) 0) / 2 = (S.getD (φ 2) 0) / 2 :=
      (minmax_same_block _ _).mp ((blockColoring_false_iff _ _).mp hred12)
    -- the three image vertices are pairwise distinct
    have hp := hΓ φ hφ
    have hφ0 := hp.mapsInto 0 (by omega)
    have hφ1 := hp.mapsInto 1 (by omega)
    have hφ2 := hp.mapsInto 2 (by omega)
    have hlen3 : S.length = 3 := hlen
    have hgetD_ne : ∀ i j, i < 3 → j < 3 → i ≠ j → S.getD i 0 ≠ S.getD j 0 := by
      intro i j hi hj hij
      rcases Nat.lt_or_ge i j with hlt | hge
      · exact Nat.ne_of_lt (pairwise_getD_lt S hpw i j hlt (by omega))
      · have hgt : j < i := by omega
        exact (Nat.ne_of_lt (pairwise_getD_lt S hpw j i hgt (by omega))).symm
    have hne01 : φ 0 ≠ φ 1 := fun h => absurd (hp.inj 0 1 (by omega) (by omega) h) (by omega)
    have hne02 : φ 0 ≠ φ 2 := fun h => absurd (hp.inj 0 2 (by omega) (by omega) h) (by omega)
    have hne12 : φ 1 ≠ φ 2 := fun h => absurd (hp.inj 1 2 (by omega) (by omega) h) (by omega)
    have hd02 := hgetD_ne (φ 0) (φ 2) hφ0 hφ2 hne02
    have hd12 := hgetD_ne (φ 1) (φ 2) hφ1 hφ2 hne12
    have hd01 := hgetD_ne (φ 0) (φ 1) hφ0 hφ1 hne01
    -- three distinct values, all in one size-2 block: impossible
    omega

/-! ### Lemma 2 at a = 3, blue side: no Λ-embedded K_b on 2(b−1) vertices -/

/-- Pigeonhole side: `b` sorted values below `2(b-1)` contain a same-block
pair, which is red — so no Λ-embedded `K_b` is all-blue. ANY `Λ` of genuine
permutations of `{0,...,b-1}`. -/
theorem noBlue_Kb (b : Nat) (hb : 1 ≤ b) (Λ : List Perm)
    (hΛ : ∀ φ ∈ Λ, IsPermOn b φ) :
    noMonoCopy blockColoring true (completeGraph b) Λ (2 * (b - 1)) = true := by
  rw [noMonoCopy, List.all_eq_true]
  intro S hS
  rw [List.all_eq_true]
  intro φ hφ
  obtain ⟨hlen, hpw, hlt⟩ := increasingMaps_spec (completeGraph b).order (2 * (b - 1)) S hS
  have hlenb : S.length = b := hlen
  cases hmono : isMonochromatic blockColoring true (completeGraph b) φ S with
  | false => rfl
  | true =>
    exfalso
    -- a same-block (hence red) pair among S's values
    obtain ⟨x, hx, y, hy, hxy, hq⟩ :=
      exists_same_block (b - 1) S hpw (fun v hv => hlt v hv) (by omega)
    obtain ⟨i, hi, hgi⟩ := mem_getD S x hx
    obtain ⟨j, hj, hgj⟩ := mem_getD S y hy
    have hij : i ≠ j := by
      intro h; subst h; rw [hgi] at hgj; omega
    have hib : i < b := by omega
    have hjb : j < b := by omega
    -- pull the positions back through φ
    have hp := hΛ φ hφ
    obtain ⟨p, hpb, hφp⟩ := hp.surj i hib
    obtain ⟨q, hqb, hφq⟩ := hp.surj j hjb
    have hpq : p ≠ q := by
      intro h; subst h; rw [hφp] at hφq; exact hij hφq
    -- the corresponding K_b pattern edge must be blue — but its image is red
    rw [isMonochromatic, List.all_eq_true] at hmono
    rcases Nat.lt_or_ge p q with hplt | hpge
    · have hmem := (mem_completeGraph_edges b p q).mpr ⟨hpb, hqb, hplt⟩
      have hcol := hmono (p, q) hmem
      simp only [imageEdge, beq_iff_eq] at hcol
      rw [hφp, hφq, hgi, hgj] at hcol
      have := (minmax_same_block x y).mpr hq
      have hblue := (blockColoring_true_iff _ _).mp hcol
      exact hblue this
    · have hqp : q < p := by omega
      have hmem := (mem_completeGraph_edges b q p).mpr ⟨hqb, hpb, hqp⟩
      have hcol := hmono (q, p) hmem
      simp only [imageEdge, beq_iff_eq] at hcol
      rw [hφq, hφp, hgj, hgi] at hcol
      have hq' : y / 2 = x / 2 := hq.symm
      have := (minmax_same_block y x).mpr hq'
      have hblue := (blockColoring_true_iff _ _).mp hcol
      exact hblue this

/-! ### Lemma 2 packaged, and the main lower-bound theorems -/

/-- **Lemma 2 at a = 3** (block-partition witness), general in both groups:
the block coloring of `K_{2(b-1)}` avoids every Γ-embedded `P₃ᵃˡᵗ` in red
and every Λ-embedded `K_b` in blue. -/
theorem lemma2_blockWitness (b : Nat) (hb : 1 ≤ b) (Γ Λ : List Perm)
    (hΓ : ∀ φ ∈ Γ, IsPermOn 3 φ) (hΛ : ∀ φ ∈ Λ, IsPermOn b φ) :
    validWitness (alternatingPath 3) Γ (completeGraph b) Λ blockColoring
      (2 * (b - 1)) = true := by
  rw [validWitness, Bool.and_eq_true]
  exact ⟨noRed_P3alt Γ hΓ _, noBlue_Kb b hb Λ hΛ⟩

/-- Lower bound for EVERY pair of permutation families at once — the full
group-generality of the preprint's Lemma 2 (specialized to a = 3):
`R((P₃ᵃˡᵗ)^Γ, K_b^Λ) ≥ 2b−1`. -/
theorem theoremB_lowerBound_all_groups (b : Nat) (hb : 1 ≤ b) (Γ Λ : List Perm)
    (hΓ : ∀ φ ∈ Γ, IsPermOn 3 φ) (hΛ : ∀ φ ∈ Λ, IsPermOn b φ) :
    PermRamseyGE (alternatingPath 3) Γ (completeGraph b) Λ (2 * b - 1) := by
  refine ⟨blockColoring, ?_⟩
  have h : 2 * b - 1 - 1 = 2 * (b - 1) := by omega
  rw [h]
  exact lemma2_blockWitness b hb Γ Λ hΓ hΛ

/-- **Theorem B, lower-bound half, for all b ≥ 1 at once**:
`R_dih(P₃ᵃˡᵗ, K_b) ≥ 2b − 1`. This is a genuine ∀b proof (pigeonhole +
max-degree-1), NOT a per-instance kernel enumeration — `decide` cannot
state an infinite family. The upper bound (Chvátal 1977 via
[DD26, Theorem 4.13]) is deliberately not formalized — see the file
header's NOT-DONE block and the preprint's §11. -/
theorem theoremB_lowerBound (b : Nat) (hb : 1 ≤ b) :
    PermRamseyGE (alternatingPath 3) (dihedralGroup 3) (completeGraph b)
      (dihedralGroup b) (2 * b - 1) :=
  theoremB_lowerBound_all_groups b hb _ _
    (dihedralGroup_isPermOn 3 (by omega)) (dihedralGroup_isPermOn b hb)

/-! ### Kernel spot-checks of instances of the general theorem
(cross-checks against `code/verify_theorem_b.py`'s output; plain `decide`) -/

/-- b = 3: the block coloring of K₄ is a valid witness — matches the
Python checker's b=3 anchor case (R ≥ 5). -/
example : validWitness (alternatingPath 3) (dihedralGroup 3) (completeGraph 3)
    (dihedralGroup 3) blockColoring 4 = true := by decide

/-- b = 4: the block coloring of K₆ is a valid witness (R ≥ 7). -/
example : validWitness (alternatingPath 3) (dihedralGroup 3) (completeGraph 4)
    (dihedralGroup 4) blockColoring 6 = true := by decide

end TheoremB
end RamseyFormal

-- Axiom audit (printed when the file is checked):
#print axioms RamseyFormal.TheoremB.theoremB_lowerBound
#print axioms RamseyFormal.TheoremB.theoremB_lowerBound_all_groups
#print axioms RamseyFormal.TheoremB.lemma2_blockWitness
#print axioms RamseyFormal.TheoremB.lemma3_dih3_eq_sym3
#print axioms RamseyFormal.noMonoCopy_completeGraph_reduce
