import Mathlib
set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This file formalizes the explicit Berkovich--Uncu bijection and its statistic
transfer, following the paper's four-map construction

  `F = G ∘ ψInv ∘ Φ ∘ φ : D n → D n`,

where

  `D n --φ--> A1 n --Φ--> A2 n --ψInv--> O n --G--> D n`.

Here, for each `n`:

* `D n` is the set of strict (distinct-part) partitions of `n`;
* `O n` is the set of partitions of `n` into odd parts;
* `A1 n` is the Chen--Gao--Ji--Li class (N = 2): partitions in which only even
  parts may be repeated, with the gap conditions (A1.2)-(A1.4);
* `A2 n` is the Chen--Gao--Ji--Li class (N = 2): partitions with no part
  divisible by 4 in which only even parts may be repeated.

Four statistics on strict partitions are involved:

* `e1 λ`: number of odd-valued parts in odd (one-based) positions of the
  decreasing part list;
* `e3 λ`: number of odd-valued parts in even (one-based) positions;
* `r1 σ`: number of parts congruent to 1 modulo 4;
* `r3 σ`: number of parts congruent to 3 modulo 4.

The four maps are given by computable constructions (the raw
multiset transforms `phiRaw`, `PhiRaw`, `psiInvRaw`, `GRaw`). The
previously-published bijectivity (and class membership / weight preservation) of
each map is treated as external input, supplied as fields of a structure
`BUData`. The four maps `φ`, `Φ`, `ψInv`, `G` are then defined as functions
between the partition classes whose underlying multiset of parts is
definitionally the corresponding raw transform applied to the input's parts.
Bijectivity of each map is also cited. None of the cited fields mention
any of the statistics `e1, e3, r1, r3`.

Proved here: the statistic lemmas `phi_stat`, `Phi_stat`,
`psiInv_oddMultiplicity` and `G_oddPart`; the composite transfer `F_stat`; and
the fiber equivalence `mainEquiv` together with the cardinality corollary
`main_cardinality`, the Berkovich--Uncu identity thm:BU.

Reference: `main-5.tex`, Sections 2.1--2.5, Definitions def:phi, def:Phi,
def:psiinv, def:G, Lemmas lem:phi, lem:Phi, lem:psiinv, lem:G, Theorem thm:main.
-/

namespace BerkovichUncu

open scoped BigOperators

/-! ## The four partition classes

We represent partitions by `Nat.Partition n` (a multiset of positive integers
summing to `n`, following Mathlib). Each class is a subtype cut out by a
predicate. `D n` corresponds to `Nat.Partition.distincts n`; `O n` corresponds
to `Nat.Partition.odds n`. -/

/-- A decreasing-list view of a partition: its parts sorted weakly decreasingly.
Positions in `e1, e3` are one-based indices into this list. -/
def sortedParts {n : ℕ} (p : Nat.Partition n) : List ℕ := p.parts.sort (· ≥ ·)

/-- `IsDistinct p` : the partition has distinct parts (is strict). -/
def IsDistinct {n : ℕ} (p : Nat.Partition n) : Prop := p.parts.Nodup

/-- `IsOddParts p` : every part of the partition is odd, matching
`Nat.Partition.odds`. -/
def IsOddParts {n : ℕ} (p : Nat.Partition n) : Prop := ∀ i ∈ p.parts, Odd i

-- Conditions (A1.1)-(A1.4).

/-- (A1.1) Only even parts may be repeated: every odd part has multiplicity ≤ 1. -/
def A1_repeat {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∀ m ∈ p.parts, Odd m → p.parts.count m ≤ 1

/-- (A1.2) Consecutive parts (in decreasing order) differ by at most 4. -/
def A1_gap {n : ℕ} (p : Nat.Partition n) : Prop :=
  (sortedParts p).IsChain (fun a b => a - b ≤ 4)

/-- (A1.3) Consecutive parts differ by less than 4 whenever either is even. -/
def A1_gapEven {n : ℕ} (p : Nat.Partition n) : Prop :=
  (sortedParts p).IsChain (fun a b => (Even a ∨ Even b) → a - b < 4)

/-- (A1.4) If nonempty, the smallest part is `< 4`. -/
def A1_small {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∀ m ∈ (sortedParts p).getLast?, m < 4

/-- Membership predicate for the class `A1 n`. -/
def IsA1 {n : ℕ} (p : Nat.Partition n) : Prop :=
  A1_repeat p ∧ A1_gap p ∧ A1_gapEven p ∧ A1_small p

-- Conditions (A2.1)-(A2.2).

/-- (A2.1) No part is divisible by 4. -/
def A2_noMul4 {n : ℕ} (p : Nat.Partition n) : Prop := ∀ m ∈ p.parts, ¬ (4 ∣ m)

/-- (A2.2) Only even parts may be repeated. -/
def A2_repeat {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∀ m ∈ p.parts, Odd m → p.parts.count m ≤ 1

/-- Membership predicate for the class `A2 n`. -/
def IsA2 {n : ℕ} (p : Nat.Partition n) : Prop := A2_noMul4 p ∧ A2_repeat p

/-- `D n`: strict partitions of `n` (partitions into distinct positive parts). -/
def D (n : ℕ) : Type := {p : Nat.Partition n // IsDistinct p}

/-- `O n`: partitions of `n` into odd parts. -/
def O (n : ℕ) : Type := {p : Nat.Partition n // IsOddParts p}

/-- `A1 n`: the Chen--Gao--Ji--Li class (N = 2). -/
def A1 (n : ℕ) : Type := {p : Nat.Partition n // IsA1 p}

/-- `A2 n`: the Chen--Gao--Ji--Li class (N = 2). -/
def A2 (n : ℕ) : Type := {p : Nat.Partition n // IsA2 p}

-- These classes are finite types with decidable equality.
instance (n : ℕ) : DecidableEq (D n) := by unfold D; infer_instance
instance (n : ℕ) : DecidableEq (O n) := by unfold O; infer_instance
instance (n : ℕ) : Fintype (D n) := by
  classical unfold D IsDistinct; infer_instance
instance (n : ℕ) : Fintype (O n) := by
  classical unfold O IsOddParts; infer_instance

/-- Bridge: `D n` corresponds to `Nat.Partition.distincts n`. -/
theorem mem_distincts_iff {n : ℕ} (p : Nat.Partition n) :
    p ∈ Nat.Partition.distincts n ↔ IsDistinct p := by
  simp [Nat.Partition.distincts, IsDistinct]

/-- Bridge: `O n` corresponds to `Nat.Partition.odds n`. -/
theorem mem_odds_iff {n : ℕ} (p : Nat.Partition n) :
    p ∈ Nat.Partition.odds n ↔ IsOddParts p := by
  simp [Nat.Partition.odds, Nat.Partition.restricted, IsOddParts]

/-! ## The four statistics -/

/-- `e1 λ`: number of odd-valued parts in odd one-based positions.
A one-based position `r` is odd iff its zero-based index `r - 1` is even. -/
def e1 {n : ℕ} (p : Nat.Partition n) : ℕ :=
  ((sortedParts p).zipIdx.filter (fun q => Odd q.1 ∧ Even q.2)).length

/-- `e3 λ`: number of odd-valued parts in even one-based positions.
A one-based position `r` is even iff its zero-based index `r - 1` is odd. -/
def e3 {n : ℕ} (p : Nat.Partition n) : ℕ :=
  ((sortedParts p).zipIdx.filter (fun q => Odd q.1 ∧ Odd q.2)).length

/-- `r1 σ`: number of parts congruent to `1` modulo `4`. -/
def r1 {n : ℕ} (p : Nat.Partition n) : ℕ := (p.parts.filter (fun m => m % 4 = 1)).card

/-- `r3 σ`: number of parts congruent to `3` modulo `4`. -/
def r3 {n : ℕ} (p : Nat.Partition n) : ℕ := (p.parts.filter (fun m => m % 4 = 3)).card

/-! ## The four forward maps (raw, on multisets)

Each map is defined as a concrete computable transformation of the underlying
multiset of parts. The examples in `main-5.tex` are reproduced by these
definitions:

* `phiRaw {5,3,2}       = {6,3,1}`      (Example ex:phi)
* `PhiRaw {6,4,3,2,1}   = {10,3,2,1}`   (Example ex:Phi1)
* `PhiRaw {7,4,4,1}     = {11,5}`       (Example ex:Phi2)
* `psiInvRaw {10,3,2,1} = {5,5,3,1,1,1}`(Example ex:psiinv)
* `GRaw {5,5,3,1,1,1}   = {10,3,2,1}`   (Example ex:G)
-/

/-! ### Map 1: `φ` — 2-modular conjugation (Definition def:phi) -/

/-- The column sum at column `c` (1-based) of the 2-modular diagram of a multiset
of parts. A part `p` contributes a `2` to column `c` iff `2c ≤ p`, and an extra
`1` iff `p = 2c - 1` (its terminal `1`). -/
def phiCol (s : Multiset ℕ) (c : ℕ) : ℕ :=
  2 * (s.filter (fun p => 2 * c ≤ p)).card + (s.filter (fun p => p = 2 * c - 1)).card

/-- The raw map `φ`: the multiset of column sums of the 2-modular diagram,
columns `1 .. maxCol`, dropping any zeros. -/
def phiRaw (s : Multiset ℕ) : Multiset ℕ :=
  let maxCol := (s.map (fun p => (p + 1) / 2)).sup
  (((List.range maxCol).map (fun i => phiCol s (i + 1))).filter (fun x => x ≠ 0) : Multiset ℕ)

/-! ### Map 2: `Φ` — the Chen--Gao--Ji--Li insertion map (Definition def:Phi)

Implemented with explicit fuel. The current object is always kept as a weakly
decreasing list; `sortDesc` re-sorts into weakly decreasing order. -/

/-- Sort a list of naturals into weakly decreasing order. -/
def sortDesc (l : List ℕ) : List ℕ := l.mergeSort (· ≥ ·)

/-- Whether the part at index `j` (0-based) of the descending list `l` is
*removable*: it is divisible by `4`, and either it is the largest part (`j = 0`)
or it is interior and its neighbours satisfy the A1 gap condition after deletion
(`l[j-1] - l[j+1] ≤ 4`, strict if either neighbour is even). -/
def isRemovableAt (l : List ℕ) (j : ℕ) : Bool :=
  match l[j]? with
  | none => false
  | some v =>
    if ¬ (4 ∣ v) then false
    else if j = 0 then true
    else
      match l[j-1]?, l[j+1]? with
      | some a, some b => if (a % 2 = 0 ∨ b % 2 = 0) then a - b < 4 else a - b ≤ 4
      | _, _ => false

/-- Index of the largest removable part (leftmost if the value repeats): since
`l` is descending, this is the least index that is removable. -/
def findRemovable (l : List ℕ) : Option ℕ :=
  (List.range l.length).find? (fun j => isRemovableAt l j)

/-- Pre-extraction, phase (i): repeatedly remove the largest removable part,
recording each removed value (unchanged) as a part of `δ`. -/
def preExtract : ℕ → List ℕ → List ℕ → (List ℕ × List ℕ)
  | 0, l, delta => (l, delta)
  | fuel + 1, l, delta =>
    match findRemovable l with
    | none => (l, delta)
    | some j =>
      match l[j]? with
      | none => (l, delta)
      | some v => preExtract fuel (l.eraseIdx j) (v :: delta)

/-- Index of the largest positive multiple of 4 (leftmost, i.e. least index in
the descending list). -/
def findMult4 (l : List ℕ) : Option ℕ :=
  (List.range l.length).find?
    (fun j => match l[j]? with | some v => decide (4 ∣ v ∧ 0 < v) | none => false)

/-- One step of iterative extraction, phase (ii): at the largest multiple of 4,
say in one-based position `s = j + 1` and equal to `4m`, subtract `4` from each
of the `s - 1 = j` preceding parts, delete the part, reorder, and record
`4(s-1) + 4m = 4·j + 4m`. -/
def iterExtractStep (l : List ℕ) : Option (List ℕ × ℕ) :=
  match findMult4 l with
  | none => none
  | some j =>
    match l[j]? with
    | none => none
    | some v =>
      let pre := (l.take j).map (fun x => x - 4)
      some (sortDesc (pre ++ l.drop (j + 1)), 4 * j + v)

/-- Iterative extraction, phase (ii), driven by fuel. -/
def iterExtract : ℕ → List ℕ → List ℕ → (List ℕ × List ℕ)
  | 0, l, delta => (l, delta)
  | fuel + 1, l, delta =>
    match iterExtractStep l with
    | none => (l, delta)
    | some (newl, rec) => iterExtract fuel newl (rec :: delta)

/-- Insert a single recorded part `d = 4h`: add `4` to each of the first
`h = d / 4` parts of the current list, then reorder. -/
def insertStep (l : List ℕ) (d : ℕ) : List ℕ :=
  let h := d / 4
  sortDesc (((l.take h).map (fun x => x + 4)) ++ l.drop h)

/-- Insertion stage: insert all recorded parts of `δ` in weakly decreasing
order. -/
def insertAll (l : List ℕ) (delta : List ℕ) : List ℕ :=
  (sortDesc delta).foldl insertStep l

/-- The full `Φ` algorithm on a weakly decreasing list. The fuel bound
`(∑ parts) + length + 1` dominates the number of extraction steps. -/
def PhiList (l : List ℕ) : List ℕ :=
  let fuel := l.foldl (· + ·) 0 + l.length + 1
  let (l1, d1) := preExtract fuel l []
  let (astar, d2) := iterExtract fuel l1 d1
  insertAll astar d2

/-- The raw map `Φ` on multisets: apply the algorithm to the descending part
list. -/
def PhiRaw (s : Multiset ℕ) : Multiset ℕ := (PhiList (s.sort (· ≥ ·)) : Multiset ℕ)

/-! ### Map 3: `ψInv` — the splitting map (Definition def:psiinv)

Each odd part `m` is kept; each even part `2m` (with `m` odd, by (A2.1)) becomes
two copies of `m`. Hence for odd `m`, `mult_μ(m) = b_m + 2·b_{2m}`. -/

/-- The raw map `ψInv`. -/
def psiInvRaw (s : Multiset ℕ) : Multiset ℕ :=
  s.bind (fun p => if p % 2 = 1 then {p} else {p / 2, p / 2})

/-! ### Map 4: `G` — Glaisher's bijection (Definition def:G)

For each odd `m` with multiplicity `k`, write `k` in binary and produce the
parts `2^c·m` for those bit positions `c` set in `k`. -/

/-- The distinct parts produced from `k` copies of a value `m`: `2^c·m` for the
set bits `c` of `k`. -/
def glaisherParts (m k : ℕ) : Multiset ℕ :=
  (((List.range (k + 1)).filter (fun c => Nat.testBit k c)).map (fun c => 2 ^ c * m) : Multiset ℕ)

/-- The raw map `G`. -/
def GRaw (s : Multiset ℕ) : Multiset ℕ :=
  s.dedup.bind (fun m => glaisherParts m (s.count m))

/-! ## Building maps from the cited data

`mkPartition` assembles a `Nat.Partition n` from a multiset given positivity and
sum proofs. It is how each raw multiset transform becomes a map between the
partition classes. -/

/-- Build a partition of `n` from a multiset `s` given positivity and sum. -/
def mkPartition {n : ℕ} (s : Multiset ℕ) (pos : ∀ i ∈ s, 0 < i) (hsum : s.sum = n) :
    Nat.Partition n where
  parts := s
  parts_pos := fun {i} hi => pos i hi
  parts_sum := hsum

@[simp] theorem mkPartition_parts {n : ℕ} (s : Multiset ℕ)
    (pos : ∀ i ∈ s, 0 < i) (hsum : s.sum = n) :
    (mkPartition s pos hsum).parts = s := rfl

/-! ## The cited bijectivity packages

`BUData n` bundles the non-Mathlib mathematical inputs: for each of the four raw
transforms, (a) that it preserves positivity of parts, (b) that it preserves the
weight `n`, (c) that it lands in the required class, and (d) that the resulting
map is bijective. No field mentions any statistic (`e1, e3, r1, r3`) nor any
fiber/final-theorem content.

The four maps `φ, Φ, ψInv, G` are then defined below using the membership and
weight fields, and their underlying parts are definitionally the corresponding
raw transform. The cited bijectivity is stated for exactly those maps. -/

structure BUData (n : ℕ) where
  -- φ : D n → A1 n (2-modular conjugation; cited: CGJL).
  φ_pos : ∀ (x : D n), ∀ i ∈ phiRaw x.1.parts, 0 < i
  φ_sum : ∀ (x : D n), (phiRaw x.1.parts).sum = n
  φ_mem : ∀ (x : D n), IsA1 (mkPartition (phiRaw x.1.parts) (φ_pos x) (φ_sum x))
  -- Φ : A1 n → A2 n (CGJL insertion; cited).
  Φ_pos : ∀ (x : A1 n), ∀ i ∈ PhiRaw x.1.parts, 0 < i
  Φ_sum : ∀ (x : A1 n), (PhiRaw x.1.parts).sum = n
  Φ_mem : ∀ (x : A1 n), IsA2 (mkPartition (PhiRaw x.1.parts) (Φ_pos x) (Φ_sum x))
  -- ψInv : A2 n → O n (splitting; cited).
  ψInv_pos : ∀ (x : A2 n), ∀ i ∈ psiInvRaw x.1.parts, 0 < i
  ψInv_sum : ∀ (x : A2 n), (psiInvRaw x.1.parts).sum = n
  ψInv_mem : ∀ (x : A2 n), IsOddParts (mkPartition (psiInvRaw x.1.parts) (ψInv_pos x) (ψInv_sum x))
  -- G : O n → D n (Glaisher; cited).
  G_pos : ∀ (x : O n), ∀ i ∈ GRaw x.1.parts, 0 < i
  G_sum : ∀ (x : O n), (GRaw x.1.parts).sum = n
  G_mem : ∀ (x : O n), IsDistinct (mkPartition (GRaw x.1.parts) (G_pos x) (G_sum x))
  -- Cited bijectivity of the four concrete maps (defined below via these fields).
  φ_bij : Function.Bijective
    (fun x : D n => (⟨mkPartition (phiRaw x.1.parts) (φ_pos x) (φ_sum x), φ_mem x⟩ : A1 n))
  Φ_bij : Function.Bijective
    (fun x : A1 n => (⟨mkPartition (PhiRaw x.1.parts) (Φ_pos x) (Φ_sum x), Φ_mem x⟩ : A2 n))
  ψInv_bij : Function.Bijective
    (fun x : A2 n => (⟨mkPartition (psiInvRaw x.1.parts) (ψInv_pos x) (ψInv_sum x), ψInv_mem x⟩ : O n))
  G_bij : Function.Bijective
    (fun x : O n => (⟨mkPartition (GRaw x.1.parts) (G_pos x) (G_sum x), G_mem x⟩ : D n))

variable {n : ℕ} (data : BUData n)

/-! ## The four forward maps between classes

Each map is a function between the partition classes, with parts definitionally
equal to the corresponding raw transform applied to the input (see the `_parts`
lemmas). -/

/-- `φ : D n → A1 n`, the 2-modular conjugation, as a concrete map. -/
def φ (x : D n) : A1 n :=
  ⟨mkPartition (phiRaw x.1.parts) (data.φ_pos x) (data.φ_sum x), data.φ_mem x⟩

/-- `Φ : A1 n → A2 n`, the CGJL insertion, as a concrete map. -/
def Φ (x : A1 n) : A2 n :=
  ⟨mkPartition (PhiRaw x.1.parts) (data.Φ_pos x) (data.Φ_sum x), data.Φ_mem x⟩

/-- `ψInv : A2 n → O n`, the splitting map, as a concrete map. -/
def ψInv (x : A2 n) : O n :=
  ⟨mkPartition (psiInvRaw x.1.parts) (data.ψInv_pos x) (data.ψInv_sum x), data.ψInv_mem x⟩

/-- `G : O n → D n`, Glaisher's bijection, as a concrete map. -/
def G (x : O n) : D n :=
  ⟨mkPartition (GRaw x.1.parts) (data.G_pos x) (data.G_sum x), data.G_mem x⟩

@[simp] theorem φ_parts (x : D n) : (φ data x).1.parts = phiRaw x.1.parts := rfl
@[simp] theorem Φ_parts (x : A1 n) : (Φ data x).1.parts = PhiRaw x.1.parts := rfl
@[simp] theorem ψInv_parts (x : A2 n) : (ψInv data x).1.parts = psiInvRaw x.1.parts := rfl
@[simp] theorem G_parts (x : O n) : (G data x).1.parts = GRaw x.1.parts := rfl

/-- The cited bijectivity, restated for the concrete maps `φ, Φ, ψInv, G`. -/
theorem φ_bijective : Function.Bijective (φ data) := data.φ_bij
theorem Φ_bijective : Function.Bijective (Φ data) := data.Φ_bij
theorem ψInv_bijective : Function.Bijective (ψInv data) := data.ψInv_bij
theorem G_bijective : Function.Bijective (G data) := data.G_bij

/-- The four cited equivalences, each with forward function *definitionally* the
corresponding concrete map. -/
noncomputable def φEquiv : D n ≃ A1 n := Equiv.ofBijective (φ data) (φ_bijective data)
noncomputable def ΦEquiv : A1 n ≃ A2 n := Equiv.ofBijective (Φ data) (Φ_bijective data)
noncomputable def ψInvEquiv : A2 n ≃ O n := Equiv.ofBijective (ψInv data) (ψInv_bijective data)
noncomputable def GEquiv : O n ≃ D n := Equiv.ofBijective (G data) (G_bijective data)

@[simp] theorem φEquiv_apply (x : D n) : φEquiv data x = φ data x := rfl
@[simp] theorem ΦEquiv_apply (x : A1 n) : ΦEquiv data x = Φ data x := rfl
@[simp] theorem ψInvEquiv_apply (x : A2 n) : ψInvEquiv data x = ψInv data x := rfl
@[simp] theorem GEquiv_apply (x : O n) : GEquiv data x = G data x := rfl

/-! ## The statistic lemmas -/

/-! ### Helper lemmas for `phi_stat`

Proved value by value over the multiset of parts `s`, which is `Nodup` for
`x : D n`:

For odd residue `d ∈ {1,3}`,
  `r_d(φλ)` counts columns `c` with `phiCol s c % 4 = d`; each such column has an
  odd sum, forcing a part `p = 2c-1 ∈ s`, and `phiCol s c = 2·#{p'∈s: p'>p} + 1`.
  Reindexing columns ↦ odd parts (`c = (p+1)/2`) turns `r_d(φλ)` into a count
  over odd parts `p∈s`. The residue `phiCol % 4` is `1` iff `#{p'>p}` even, `3`
  iff `#{p'>p}` odd. On the other side `e1/e3` count odd parts at even/odd
  0-based position of the descending list; that 0-based index equals `#{p'>p}`.

The pieces:
* `phi_col_residue`   — the residue computation for odd `p`.
* `phi_r_eq_countParts` — the reindexing: `r_d(φλ) = # odd p∈s with phiCol%4=d`.
* `e_eq_countParts`   — position ↔ `#{p'>p}`: `e1/e3 = # odd p with parity`. -/

/-- Residue of the (odd) column sum at column `c = (p+1)/2` for an odd part
`p ∈ s`: it is `2·#{p'∈s : p'>p} + 1`, whose residue mod 4 is `1` iff
`#{p'∈s: p'>p}` is even and `3` iff odd. -/
theorem phi_col_residue (s : Multiset ℕ) (hnd : s.Nodup) (p : ℕ) (hp : Odd p)
    (hmem : p ∈ s) :
    phiCol s ((p + 1) / 2) = 2 * (s.filter (fun q => p < q)).card + 1 := by
  obtain ⟨t, rfl⟩ := hp
  unfold phiCol
  have hc : 2 * ((2 * t + 1 + 1) / 2) = 2 * t + 2 := by omega
  rw [hc]
  have h1 : (s.filter (fun q => 2 * t + 2 ≤ q)) = (s.filter (fun q => 2 * t + 1 < q)) := by
    apply Multiset.filter_congr; intro q _; omega
  have heq : (2 * t + 2 - 1) = 2 * t + 1 := by omega
  have h2 : (s.filter (fun q => q = 2 * t + 2 - 1)).card = 1 := by
    simp only [heq]
    rw [Multiset.filter_eq', Multiset.count_eq_one_of_mem hnd hmem]
    rfl
  rw [h1, h2]

/-- Odd-column characterization: for `d` odd, if the column sum `phiCol s c ≡ d
(mod 4)` then the (unique, by Nodup) part `2c-1` lies in `s`. Membership of
`2c-1` is forced because the residue is odd, so the `+1` term is nonzero. -/
theorem phi_col_odd_mem (s : Multiset ℕ) (hnd : s.Nodup) (c : ℕ)
    (d : ℕ) (hd : d % 2 = 1) (hres : phiCol s c % 4 = d) : (2 * c - 1) ∈ s := by
  unfold phiCol at hres
  have hB : (s.filter (fun p => p = 2 * c - 1)).card = Multiset.count (2 * c - 1) s := by
    rw [Multiset.filter_eq', Multiset.card_replicate]
  have hle : Multiset.count (2 * c - 1) s ≤ 1 := Multiset.nodup_iff_count_le_one.mp hnd _
  have hBpos : 0 < (s.filter (fun p => p = 2 * c - 1)).card := by omega
  rw [hB] at hBpos
  exact Multiset.count_pos.mp hBpos

/-- Reindexing: for odd residue `d`, the number of columns of `phiRaw s` with
value `≡ d (mod 4)` equals the number of odd parts `p ∈ s` whose column
`phiCol s ((p+1)/2) ≡ d (mod 4)`. (Only odd parts give odd column sums; even
columns are `≡ 0/2 (mod 4)` and are not counted.) -/
theorem phi_r_eq_countParts (s : Multiset ℕ) (hnd : s.Nodup) (d : ℕ) (hd : d % 2 = 1) :
    (phiRaw s).countP (fun v => v % 4 = d)
      = (s.filter (fun p => Odd p ∧ phiCol s ((p + 1) / 2) % 4 = d)).card := by
  classical
  set maxCol := (s.map (fun p => (p + 1) / 2)).sup with hmax
  -- Step A: reduce LHS to a countP over `List.range maxCol`.
  have hdne : d ≠ 0 := by omega
  have hLHS : (phiRaw s).countP (fun v => v % 4 = d)
      = (List.range maxCol).countP (fun i => decide (phiCol s (i + 1) % 4 = d)) := by
    unfold phiRaw
    rw [← hmax]
    rw [Multiset.coe_countP]
    rw [List.countP_filter]
    rw [List.countP_map]
    apply List.countP_congr
    intro i _
    simp only [Function.comp_apply]
    by_cases hr : phiCol s (i + 1) % 4 = d
    · have hne : phiCol s (i + 1) ≠ 0 := by
        intro h0; rw [h0] at hr; simp at hr; omega
      simp [hr, hne]
    · simp [hr]
  rw [hLHS]
  -- Step A': list countP over range to Finset card
  have hLHS2 : (List.range maxCol).countP (fun i => decide (phiCol s (i + 1) % 4 = d))
      = ((Finset.range maxCol).filter (fun i => phiCol s (i + 1) % 4 = d)).card := by
    rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
    rw [← Finset.card_val ((Finset.range maxCol).filter (fun i => phiCol s (i + 1) % 4 = d))]
    rfl
  rw [hLHS2]
  -- Step B: RHS multiset filter card to Finset over s.toFinset
  have hRHS : (s.filter (fun p => Odd p ∧ phiCol s ((p + 1) / 2) % 4 = d)).card
      = (s.toFinset.filter (fun p => Odd p ∧ phiCol s ((p + 1) / 2) % 4 = d)).card := by
    rw [← Multiset.toFinset_card_of_nodup (Multiset.Nodup.filter _ hnd)]
    congr 1
    rw [Multiset.toFinset_filter]
  rw [hRHS]
  -- Step C: bijection  i ↦ 2i+1,  inverse p ↦ (p+1)/2 - 1
  apply Finset.card_nbij' (fun i => 2 * i + 1) (fun p => (p + 1) / 2 - 1)
  · -- MapsTo forward
    intro i hi
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi ⊢
    obtain ⟨hilt, hires⟩ := hi
    have hmem : (2 * (i + 1) - 1) ∈ s := phi_col_odd_mem s hnd (i + 1) d hd hires
    have h2i : 2 * (i + 1) - 1 = 2 * i + 1 := by omega
    rw [h2i] at hmem
    refine ⟨Multiset.mem_toFinset.mpr hmem, ⟨i, by omega⟩, ?_⟩
    have hc : (2 * i + 1 + 1) / 2 = i + 1 := by omega
    rw [hc]; exact hires
  · -- MapsTo backward
    intro p hp
    simp only [Finset.coe_filter, Finset.mem_range, Multiset.mem_toFinset,
      Set.mem_setOf_eq] at hp ⊢
    obtain ⟨hpmem, hpodd, hpres⟩ := hp
    obtain ⟨t, rfl⟩ := hpodd
    have hle : (2 * t + 1 + 1) / 2 ≤ maxCol := by
      rw [hmax]
      apply Multiset.le_sup
      rw [Multiset.mem_map]
      exact ⟨2 * t + 1, hpmem, rfl⟩
    have hc : (2 * t + 1 + 1) / 2 = t + 1 := by omega
    rw [hc] at hle hpres ⊢
    refine ⟨by omega, ?_⟩
    have hc2 : t + 1 - 1 + 1 = t + 1 := by omega
    rw [hc2]; exact hpres
  · -- LeftInvOn
    intro i hi
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
    have : (2 * i + 1 + 1) / 2 - 1 = i := by omega
    exact this
  · -- RightInvOn
    intro p hp
    simp only [Finset.coe_filter, Multiset.mem_toFinset, Set.mem_setOf_eq] at hp
    obtain ⟨hpmem, hpodd, hpres⟩ := hp
    obtain ⟨t, rfl⟩ := hpodd
    simp only
    omega

/-- `zipIdx (a :: t)` decomposes with the head at index `0` and the tail indices
shifted up by one. -/
theorem zipIdx_cons_shift (a : ℕ) (t : List ℕ) :
    (a :: t).zipIdx = (a, 0) :: (t.zipIdx.map (fun q => (q.1, q.2 + 1))) := by
  simp [List.zipIdx_cons, List.zipIdx_succ]

/-- Core index law (list version). For a strictly decreasing list `L`
(`Pairwise (· > ·)`), and any predicate `P` on the index, the count of odd parts
at positions satisfying `P` equals the count of odd parts `p` such that `P`
holds of the number of larger parts `#{q ∈ L : p < q}` (which is exactly the
0-based index of `p`). Proved by induction on `L`, generalizing `P`. -/
theorem zipIdx_filter_eq (P : ℕ → Prop) [DecidablePred P] (L : List ℕ)
    (h : L.Pairwise (· > ·)) :
    (L.zipIdx.filter (fun q => Odd q.1 ∧ P q.2)).length
      = (L.filter (fun p => Odd p ∧ P (L.filter (fun q => p < q)).length)).length := by
  induction L generalizing P with
  | nil => simp
  | cons a t ih =>
    rw [zipIdx_cons_shift]
    rw [List.pairwise_cons] at h
    obtain ⟨hhead, htail⟩ := h
    have hfa : (a :: t).filter (fun q => a < q) = [] := by
      rw [List.filter_cons]
      simp only [lt_irrefl, decide_false, Bool.false_eq_true, if_false]
      apply List.filter_eq_nil_iff.mpr
      intro b hb
      have : a > b := hhead b hb
      simp only [decide_eq_true_eq]; omega
    have hfp : ∀ p ∈ t, ((a :: t).filter (fun q => p < q)).length
        = (t.filter (fun q => p < q)).length + 1 := by
      intro p hp
      rw [List.filter_cons]
      have hap : a > p := hhead p hp
      simp only [show decide (p < a) = true by simp [hap]]
      simp
    have hmapfilter :
        ((t.zipIdx.map (fun q => (q.1, q.2 + 1))).filter
            (fun q => Odd q.1 ∧ P q.2)).length
          = (t.zipIdx.filter (fun q => Odd q.1 ∧ P (q.2 + 1))).length := by
      rw [List.filter_map, List.length_map]
      rfl
    rw [List.filter_cons, List.filter_cons]
    by_cases hc : (Odd a ∧ P 0)
    · have h1 : decide (Odd (a, 0).1 ∧ P (a, 0).2) = true := by simp [hc]
      have h2 : decide (Odd a ∧ P ((a :: t).filter (fun q => a < q)).length) = true := by
        rw [hfa]; simp [hc]
      rw [if_pos h1, if_pos h2]
      simp only [List.length_cons]
      rw [hmapfilter]
      have hrhs : (t.filter (fun p => Odd p ∧ P ((a :: t).filter (fun q => p < q)).length)).length
          = (t.filter (fun p => Odd p ∧ P ((t.filter (fun q => p < q)).length + 1)) ).length := by
        apply congrArg
        apply List.filter_congr
        intro p hp
        rw [hfp p hp]
      rw [hrhs, ih (fun j => P (j + 1)) htail]
    · have h1 : decide (Odd (a, 0).1 ∧ P (a, 0).2) = false := by simp [hc]
      have h2 : decide (Odd a ∧ P ((a :: t).filter (fun q => a < q)).length) = false := by
        rw [hfa]; simp [hc]
      rw [if_neg (by rw [h1]; simp), if_neg (by rw [h2]; simp)]
      rw [hmapfilter]
      have hrhs : (t.filter (fun p => Odd p ∧ P ((a :: t).filter (fun q => p < q)).length)).length
          = (t.filter (fun p => Odd p ∧ P ((t.filter (fun q => p < q)).length + 1)) ).length := by
        apply congrArg
        apply List.filter_congr
        intro p hp
        rw [hfp p hp]
      rw [hrhs, ih (fun j => P (j + 1)) htail]

/-- The sorted descending part list of a `Nodup` multiset is strictly
decreasing. -/
theorem sort_pairwise_gt (s : Multiset ℕ) (hnd : s.Nodup) :
    (s.sort (· ≥ ·)).Pairwise (· > ·) := by
  have hsorted : (s.sort (· ≥ ·)).Pairwise (· ≥ ·) := Multiset.pairwise_sort _ _
  have hndL : (s.sort (· ≥ ·)).Pairwise (· ≠ ·) := by
    have : (s.sort (· ≥ ·)).Nodup := by
      rw [← Multiset.coe_nodup, Multiset.sort_eq]; exact hnd
    exact this
  rw [List.pairwise_iff_get] at hsorted hndL ⊢
  intro i j hij
  have h1 := hsorted i j hij
  have h2 := hndL i j hij
  omega

/-- Transfer of the (parity-of-larger-part-count) multiset count to the list
form over the sorted list. -/
theorem countParts_transfer (P : ℕ → Prop) [DecidablePred P] (s : Multiset ℕ) :
    (s.filter (fun p => Odd p ∧ P (s.filter (fun q => p < q)).card)).card
      = ((s.sort (· ≥ ·)).filter
          (fun p => Odd p ∧ P ((s.sort (· ≥ ·)).filter (fun q => p < q)).length)).length := by
  set L := s.sort (· ≥ ·) with hL
  have hcoe : (↑L : Multiset ℕ) = s := Multiset.sort_eq s (· ≥ ·)
  have hinner : ∀ p, (s.filter (fun q => p < q)).card = (L.filter (fun q => p < q)).length := by
    intro p
    conv_lhs => rw [← hcoe]
    rw [Multiset.filter_coe, Multiset.coe_card]
  have step1 : (s.filter (fun p => Odd p ∧ P (s.filter (fun q => p < q)).card)).card
      = (s.filter (fun p => Odd p ∧ P (L.filter (fun q => p < q)).length)).card := by
    congr 1
    apply Multiset.filter_congr
    intro p _
    rw [hinner p]
  rw [step1]
  conv_lhs => rw [← hcoe]
  rw [Multiset.filter_coe, Multiset.coe_card]

/-- Position ↔ larger-part count: for a `Nodup` `s`, the `e`-statistics count odd
parts by the parity of `#{p'∈s : p'>p}` (which is the 0-based index in the
descending sort). `e1` uses even parity, `e3` odd. -/
theorem e_eq_countParts (s : Multiset ℕ) (hnd : s.Nodup) :
    (((s.sort (· ≥ ·)).zipIdx.filter (fun q => Odd q.1 ∧ Even q.2)).length
      = (s.filter (fun p => Odd p ∧ Even (s.filter (fun q => p < q)).card)).card)
    ∧ (((s.sort (· ≥ ·)).zipIdx.filter (fun q => Odd q.1 ∧ Odd q.2)).length
      = (s.filter (fun p => Odd p ∧ Odd (s.filter (fun q => p < q)).card)).card) := by
  have hpair : (s.sort (· ≥ ·)).Pairwise (· > ·) := sort_pairwise_gt s hnd
  refine ⟨?_, ?_⟩
  · rw [zipIdx_filter_eq Even _ hpair]
    exact (countParts_transfer Even s).symm
  · rw [zipIdx_filter_eq Odd _ hpair]
    exact (countParts_transfer Odd s).symm

/-- **`phi_stat` (Lemma lem:phi).** The 2-modular conjugation carries the
position statistic `(e1, e3)` to the residue statistic `(r1, r3)`.
(An odd part in one-based position `r` contributes the unique odd column sum
`2r - 1`, which is `≡ 1 (mod 4)` for odd `r` and `≡ 3 (mod 4)` for even `r`.) -/
theorem phi_stat (x : D n) :
    r1 (φ data x).1 = e1 x.1 ∧ r3 (φ data x).1 = e3 x.1 := by
  have hnd : x.1.parts.Nodup := x.2
  obtain ⟨he1, he3⟩ := e_eq_countParts x.1.parts hnd
  -- residue equivalences for the two filters.
  have hres1 : ∀ p ∈ x.1.parts, Odd p →
      (phiCol x.1.parts ((p + 1) / 2) % 4 = 1
        ↔ Even (x.1.parts.filter (fun q => p < q)).card) := by
    intro p hp hpo
    rw [phi_col_residue x.1.parts hnd p hpo hp]
    rw [Nat.even_iff]; omega
  have hres3 : ∀ p ∈ x.1.parts, Odd p →
      (phiCol x.1.parts ((p + 1) / 2) % 4 = 3
        ↔ Odd (x.1.parts.filter (fun q => p < q)).card) := by
    intro p hp hpo
    rw [phi_col_residue x.1.parts hnd p hpo hp]
    rw [Nat.odd_iff]; omega
  refine ⟨?_, ?_⟩
  · -- r1 (φ x) = e1 x
    show ((phiRaw x.1.parts).filter (fun m => m % 4 = 1)).card = e1 x.1
    rw [← Multiset.countP_eq_card_filter, phi_r_eq_countParts x.1.parts hnd 1 (by norm_num)]
    unfold e1 sortedParts
    rw [he1]
    congr 1
    apply Multiset.filter_congr
    intro p hp
    by_cases hpo : Odd p
    · simp only [hpo, true_and, hres1 p hp hpo]
    · simp [hpo]
  · show ((phiRaw x.1.parts).filter (fun m => m % 4 = 3)).card = e3 x.1
    rw [← Multiset.countP_eq_card_filter, phi_r_eq_countParts x.1.parts hnd 3 (by norm_num)]
    unfold e3 sortedParts
    rw [he3]
    congr 1
    apply Multiset.filter_congr
    intro p hp
    by_cases hpo : Odd p
    · simp only [hpo, true_and, hres3 p hp hpo]
    · simp [hpo]

namespace PhiStat

/-- The count of parts with residue `d` mod 4, as a list `countP`. -/
def Nd (d : ℕ) (l : List ℕ) : ℕ := l.countP (fun x => decide (x % 4 = d))

/-- `Nd` is invariant under permutation. -/
theorem Nd_perm {l l' : List ℕ} (d : ℕ) (h : l.Perm l') : Nd d l = Nd d l' :=
  List.Perm.countP_eq _ h

/-- `Nd` is additive over append. -/
theorem Nd_append (d : ℕ) (l l' : List ℕ) : Nd d (l ++ l') = Nd d l + Nd d l' := by
  unfold Nd; rw [List.countP_append]

/-- `Nd` is invariant under `sortDesc`. -/
theorem Nd_sortDesc (d : ℕ) (l : List ℕ) : Nd d (sortDesc l) = Nd d l := by
  apply Nd_perm
  exact List.mergeSort_perm _ _

/-- Adding 4 to every element of a list preserves `Nd`. -/
theorem Nd_map_add4 (d : ℕ) (l : List ℕ) :
    Nd d (l.map (fun x => x + 4)) = Nd d l := by
  unfold Nd
  rw [List.countP_map]
  apply List.countP_congr
  intro x _
  simp only [Function.comp_apply, decide_eq_true_eq]
  omega

/-- Subtracting 4 from every element of a list all of whose elements are `≥ 4`
preserves `Nd`. -/
theorem Nd_map_sub4 (d : ℕ) (l : List ℕ) (hge : ∀ x ∈ l, 4 ≤ x) :
    Nd d (l.map (fun x => x - 4)) = Nd d l := by
  unfold Nd
  rw [List.countP_map]
  apply List.countP_congr
  intro x hx
  simp only [Function.comp_apply, decide_eq_true_eq]
  have := hge x hx
  omega

/-- A part divisible by 4 has residue `0`, hence is not counted for `d ∈ {1,3}`. -/
theorem not_res_of_dvd4 {v d : ℕ} (hv : 4 ∣ v) (hd : d = 1 ∨ d = 3) :
    ¬ (v % 4 = d) := by
  obtain ⟨k, rfl⟩ := hv
  omega

/-- Deleting an element `v ≡ 0 mod 4` at a valid index preserves `Nd`
(for `d ∈ {1,3}`). -/
theorem Nd_eraseIdx (d : ℕ) (l : List ℕ) (j : ℕ) (v : ℕ)
    (hj : l[j]? = some v) (hv : 4 ∣ v) (hd : d = 1 ∨ d = 3) :
    Nd d (l.eraseIdx j) = Nd d l := by
  have hjlt : j < l.length := by
    by_contra h
    rw [not_lt] at h
    rw [List.getElem?_eq_none h] at hj
    exact absurd hj.symm (by simp)
  have hvval : l[j]'hjlt = v := by
    rw [List.getElem?_eq_getElem hjlt] at hj; injection hj
  have hperm : (l[j]'hjlt :: l.eraseIdx j).Perm l :=
    List.getElem_cons_eraseIdx_perm hjlt
  have := Nd_perm (l := l[j]'hjlt :: l.eraseIdx j) (l' := l) d hperm
  rw [hvval] at this
  rw [← this]
  unfold Nd
  rw [List.countP_cons]
  have hnc : ¬ (v % 4 = d) := not_res_of_dvd4 hv hd
  simp only [hnc, decide_false, Bool.false_eq_true, if_false]
  omega

/-- `preExtract` preserves `Nd` for `d ∈ {1,3}`. -/
theorem Nd_preExtract (d : ℕ) (hd : d = 1 ∨ d = 3) :
    ∀ (fuel : ℕ) (l delta : List ℕ),
      Nd d (preExtract fuel l delta).1 = Nd d l := by
  intro fuel
  induction fuel with
  | zero => intro l delta; simp [preExtract]
  | succ fuel ih =>
    intro l delta
    unfold preExtract
    rcases hfr : findRemovable l with _ | j
    · simp only
    · simp only
      rcases hv : l[j]? with _ | v
      · simp only
      · simp only
        -- 4 ∣ v from isRemovableAt l j = true
        have hrem : isRemovableAt l j = true := by
          have := List.find?_some hfr
          simpa using this
        have hdvd : 4 ∣ v := by
          unfold isRemovableAt at hrem
          rw [hv] at hrem
          by_contra hnd4
          simp [hnd4] at hrem
        rw [ih (l.eraseIdx j) (v :: delta), Nd_eraseIdx d l j v hv hdvd hd]

/-- One `iterExtractStep` preserves `Nd` when `l` is weakly decreasing
(so no natural-subtraction underflow), for `d ∈ {1,3}`. -/
theorem Nd_iterExtractStep (d : ℕ) (hd : d = 1 ∨ d = 3) (l : List ℕ)
    (hsorted : l.Pairwise (· ≥ ·)) (newl : List ℕ) (rec : ℕ)
    (hstep : iterExtractStep l = some (newl, rec)) :
    Nd d newl = Nd d l := by
  -- Extract j and v from hstep.
  unfold iterExtractStep at hstep
  rcases hf : findMult4 l with _ | j
  · rw [hf] at hstep; simp at hstep
  rw [hf] at hstep
  simp only at hstep
  rcases hv : l[j]? with _ | v
  · rw [hv] at hstep; simp at hstep
  rw [hv] at hstep
  simp only [Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨hnewl, _hrec⟩ := hstep
  -- From findMult4 l = some j: 4 ∣ v ∧ 0 < v, and j < l.length.
  have hjmem : j ∈ List.range l.length := List.mem_of_find?_eq_some hf
  have hjlt : j < l.length := List.mem_range.mp hjmem
  have hf' : (List.range l.length).find?
      (fun j => match l[j]? with | some v => decide (4 ∣ v ∧ 0 < v) | none => false) = some j := hf
  have hpred := List.find?_some hf'
  rw [hv] at hpred
  simp only [decide_eq_true_eq] at hpred
  obtain ⟨hdvd, hvpos⟩ := hpred
  have hv4 : 4 ≤ v := by
    obtain ⟨k, rfl⟩ := hdvd; omega
  -- Elements of l.take j are all ≥ v ≥ 4.
  have hsortedGE : ∀ i i' : ℕ, (hi : i < l.length) → (hi' : i' < l.length) → i ≤ i' →
      l[i']'hi' ≤ l[i]'hi := by
    rw [List.pairwise_iff_getElem] at hsorted
    intro i i' hi hi' hle
    rcases Nat.lt_or_ge i i' with hlt | hge
    · exact hsorted i i' hi hi' hlt
    · have hii : i = i' := by omega
      subst hii; exact le_refl _
  have htakege : ∀ x ∈ l.take j, 4 ≤ x := by
    intro x hx
    rw [List.mem_take_iff_getElem] at hx
    obtain ⟨i, hi, hval⟩ := hx
    have hilt : i < j := lt_of_lt_of_le hi (min_le_left _ _)
    have hival : i < l.length := by omega
    have hvval : l[j]'hjlt = v := by
      have := hv; rw [List.getElem?_eq_getElem hjlt] at this; injection this
    have hle2 : l[j]'hjlt ≤ l[i]'hival := hsortedGE i j hival hjlt (by omega)
    rw [hvval] at hle2
    have hxi : x = l[i]'hival := hval.symm
    omega
  -- Compute Nd d newl.
  rw [← hnewl, Nd_sortDesc, Nd_append, Nd_map_sub4 d _ htakege]
  -- Split l = l.take j ++ l[j] :: l.drop (j+1).
  have hvval : l[j]'hjlt = v := by
    have := hv; rw [List.getElem?_eq_getElem hjlt] at this; injection this
  have hsplit : l = l.take j ++ v :: l.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j l]
    congr 1
    rw [List.drop_eq_getElem_cons hjlt, hvval]
  conv_rhs => rw [hsplit, Nd_append]
  congr 1
  -- Nd d (v :: l.drop (j+1)) = Nd d (l.drop (j+1)) since v % 4 ≠ d.
  unfold Nd
  rw [List.countP_cons]
  have hnc : ¬ (v % 4 = d) := not_res_of_dvd4 hdvd hd
  simp only [hnc, decide_false, Bool.false_eq_true, if_false]
  omega

/-- `sortDesc` produces a weakly decreasing list. -/
theorem sortDesc_pairwise (l : List ℕ) : (sortDesc l).Pairwise (· ≥ ·) := by
  apply List.pairwise_mergeSort'

/-- `eraseIdx` preserves weak decrease. -/
theorem eraseIdx_pairwise {l : List ℕ} (j : ℕ) (h : l.Pairwise (· ≥ ·)) :
    (l.eraseIdx j).Pairwise (· ≥ ·) := by
  exact h.sublist (l.eraseIdx_sublist j)

/-- `preExtract` preserves weak decrease. -/
theorem preExtract_pairwise :
    ∀ (fuel : ℕ) (l delta : List ℕ), l.Pairwise (· ≥ ·) →
      (preExtract fuel l delta).1.Pairwise (· ≥ ·) := by
  intro fuel
  induction fuel with
  | zero => intro l delta hl; simpa [preExtract] using hl
  | succ fuel ih =>
    intro l delta hl
    unfold preExtract
    rcases hfr : findRemovable l with _ | j
    · simp only; exact hl
    · simp only
      rcases hv : l[j]? with _ | v
      · simp only; exact hl
      · simp only
        exact ih (l.eraseIdx j) (v :: delta) (eraseIdx_pairwise j hl)

/-- `iterExtract` preserves `Nd` for `d ∈ {1,3}` when the input is weakly
decreasing. -/
theorem Nd_iterExtract (d : ℕ) (hd : d = 1 ∨ d = 3) :
    ∀ (fuel : ℕ) (l delta : List ℕ), l.Pairwise (· ≥ ·) →
      Nd d (iterExtract fuel l delta).1 = Nd d l := by
  intro fuel
  induction fuel with
  | zero => intro l delta hl; simp [iterExtract]
  | succ fuel ih =>
    intro l delta hl
    unfold iterExtract
    rcases hstep : iterExtractStep l with _ | ⟨newl, rec⟩
    · simp only
    · simp only
      have hnewlsorted : newl.Pairwise (· ≥ ·) := by
        -- newl = sortDesc (...) from iterExtractStep
        unfold iterExtractStep at hstep
        rcases hf : findMult4 l with _ | j
        · rw [hf] at hstep; simp at hstep
        · rw [hf] at hstep
          simp only at hstep
          rcases hv : l[j]? with _ | v
          · rw [hv] at hstep; simp at hstep
          · rw [hv] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨hnewl, _⟩ := hstep
            rw [← hnewl]
            exact sortDesc_pairwise _
      rw [ih newl (rec :: delta) hnewlsorted]
      exact Nd_iterExtractStep d hd l hl newl rec hstep

/-- `insertStep` preserves `Nd`. -/
theorem Nd_insertStep (d : ℕ) (l : List ℕ) (d0 : ℕ) :
    Nd d (insertStep l d0) = Nd d l := by
  unfold insertStep
  simp only
  rw [Nd_sortDesc, Nd_append, Nd_map_add4]
  rw [← Nd_append, List.take_append_drop]

/-- `insertAll` preserves `Nd`. -/
theorem Nd_insertAll (d : ℕ) (l delta : List ℕ) :
    Nd d (insertAll l delta) = Nd d l := by
  unfold insertAll
  generalize (sortDesc delta) = ds
  induction ds generalizing l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons]
    rw [ih, Nd_insertStep]

/-- **Main invariance:** `PhiList` preserves `Nd` for `d ∈ {1,3}` on weakly
decreasing inputs. -/
theorem Nd_PhiList (d : ℕ) (hd : d = 1 ∨ d = 3) (l : List ℕ)
    (hsorted : l.Pairwise (· ≥ ·)) :
    Nd d (PhiList l) = Nd d l := by
  unfold PhiList
  simp only
  set fuel := l.foldl (· + ·) 0 + l.length + 1 with hfuel
  rcases hprod : preExtract fuel l [] with ⟨l1, d1⟩
  rcases hprod2 : iterExtract fuel l1 d1 with ⟨astar, d2⟩
  simp only
  have hl1 : Nd d l1 = Nd d l := by
    have := Nd_preExtract d hd fuel l []
    rw [hprod] at this; exact this
  have hl1sorted : l1.Pairwise (· ≥ ·) := by
    have := preExtract_pairwise fuel l [] hsorted
    rw [hprod] at this; exact this
  have hastar : Nd d astar = Nd d l1 := by
    have := Nd_iterExtract d hd fuel l1 d1 hl1sorted
    rw [hprod2] at this; exact this
  rw [Nd_insertAll, hastar, hl1]

/-- Bridge: card of a residue-`d` multiset filter equals `Nd` of any list whose
coercion is that multiset. -/
theorem card_filter_eq_Nd (l : List ℕ) (d : ℕ) :
    ((↑l : Multiset ℕ).filter (fun m => m % 4 = d)).card = Nd d l := by
  unfold Nd
  rw [Multiset.filter_coe, Multiset.coe_card, ← List.countP_eq_length_filter]

end PhiStat

/-- **`Phi_stat` (Lemma lem:Phi).** The CGJL insertion map preserves the
residue statistic `(r1, r3)` (all operations move parts by multiples of 4 or act
on parts divisible by 4; reordering does not change multiplicities). -/
theorem Phi_stat (x : A1 n) :
    r1 (Φ data x).1 = r1 x.1 ∧ r3 (Φ data x).1 = r3 x.1 := by
  have hsorted : (x.1.parts.sort (· ≥ ·)).Pairwise (· ≥ ·) := Multiset.pairwise_sort _ _
  have key : ∀ d, d = 1 ∨ d = 3 →
      ((PhiRaw x.1.parts).filter (fun m => m % 4 = d)).card
        = (x.1.parts.filter (fun m => m % 4 = d)).card := by
    intro d hd
    -- LHS: PhiRaw s = ↑(PhiList (s.sort ≥))
    have hL : ((PhiRaw x.1.parts).filter (fun m => m % 4 = d)).card
        = PhiStat.Nd d (PhiList (x.1.parts.sort (· ≥ ·))) := by
      unfold PhiRaw
      rw [PhiStat.card_filter_eq_Nd]
    -- RHS: s = ↑(s.sort ≥)
    have hR : (x.1.parts.filter (fun m => m % 4 = d)).card
        = PhiStat.Nd d (x.1.parts.sort (· ≥ ·)) := by
      conv_lhs => rw [show x.1.parts = (↑(x.1.parts.sort (· ≥ ·)) : Multiset ℕ)
        from (Multiset.sort_eq x.1.parts (· ≥ ·)).symm]
      rw [PhiStat.card_filter_eq_Nd]
    rw [hL, hR, PhiStat.Nd_PhiList d hd _ hsorted]
  exact ⟨key 1 (Or.inl rfl), key 3 (Or.inr rfl)⟩

/-- **`psiInv_oddMultiplicity` (Lemma lem:psiinv).** For `β ∈ A2 n` and odd
`m`, the multiplicity of `m` in `ψInv β` is odd iff `m` is a part of `β`.
(From `mult_μ(m) = b_m + 2·b_{2m} ≡ b_m (mod 2)` and `b_m ∈ {0, 1}`.) -/
theorem psiInv_oddMultiplicity (x : A2 n) (m : ℕ) (hm : Odd m) :
    Odd ((ψInv data x).1.parts.count m) ↔ m ∈ x.1.parts := by
  classical
  rw [ψInv_parts]
  set s := x.1.parts with hs
  -- helper: indicator sum over the multiset equals count
  have hind : ∀ a : ℕ, (s.map (fun p => if a = p then (1:ℕ) else 0)).sum
      = Multiset.count a s := by
    intro a
    have hb : s.bind (fun p => ({p} : Multiset ℕ)) = s := by
      simpa using Multiset.bind_singleton s id
    calc (s.map (fun p => if a = p then (1:ℕ) else 0)).sum
        = (s.map (fun p => Multiset.count a ({p} : Multiset ℕ))).sum := by
          apply congrArg Multiset.sum
          apply Multiset.map_congr rfl
          intro p _
          rw [Multiset.count_singleton]
      _ = Multiset.count a (s.bind (fun p => ({p} : Multiset ℕ))) := by
          rw [Multiset.count_bind]
      _ = Multiset.count a s := by rw [hb]
  -- key count formula: count m (psiInvRaw s) = count m s + 2 * count (2m) s
  have hcount : Multiset.count m (psiInvRaw s)
      = Multiset.count m s + 2 * Multiset.count (2 * m) s := by
    unfold psiInvRaw
    rw [Multiset.count_bind]
    have hmap : (s.map (fun p => Multiset.count m
          (if p % 2 = 1 then ({p} : Multiset ℕ) else {p / 2, p / 2})))
        = s.map (fun p => (if m = p then (1:ℕ) else 0)
            + 2 * (if (2 * m) = p then (1:ℕ) else 0)) := by
      apply Multiset.map_congr rfl
      intro p _
      by_cases hpo : p % 2 = 1
      · -- p odd summand {p}
        have hp2m : ¬ (2 * m = p) := by intro h; omega
        simp only [hpo, if_true, Multiset.count_singleton, hp2m, if_false,
          Nat.mul_zero, Nat.add_zero]
      · -- p even summand {p/2, p/2}
        have hpe : p % 2 = 0 := by omega
        have hpm : ¬ (m = p) := by
          intro h; rw [← h] at hpe; rw [Nat.odd_iff] at hm; omega
        have hcnt : Multiset.count m ({p / 2, p / 2} : Multiset ℕ)
            = 2 * (if m = p / 2 then 1 else 0) := by
          simp only [Multiset.insert_eq_cons, Multiset.count_cons,
            Multiset.count_singleton]
          by_cases hd : m = p / 2 <;> simp [hd]
        simp only [hpo, if_false, hcnt]
        rw [if_neg hpm]
        simp only [Nat.zero_add]
        by_cases hd : m = p / 2
        · have hp2m : (2 * m = p) := by omega
          rw [if_pos hd, if_pos hp2m]
        · have hp2m : ¬ (2 * m = p) := by intro h; apply hd; omega
          rw [if_neg hd, if_neg hp2m]
    rw [hmap, Multiset.sum_map_add, hind m]
    congr 1
    have hmul : (s.map (fun p => 2 * (if (2 * m) = p then (1:ℕ) else 0))).sum
        = 2 * (s.map (fun p => (if (2 * m) = p then (1:ℕ) else 0))).sum := by
      rw [Multiset.sum_map_mul_left]
    rw [hmul, hind (2 * m)]
  -- conclude parity
  rw [hcount]
  by_cases hmem : m ∈ s
  · -- member: count m s = 1
    have hle : Multiset.count m s ≤ 1 := x.2.2 m hmem hm
    have hpos : 0 < Multiset.count m s := Multiset.count_pos.mpr hmem
    have hc1 : Multiset.count m s = 1 := by omega
    rw [hc1]
    simp only [hmem, iff_true]
    rw [Nat.odd_iff]; omega
  · -- non-member: count m s = 0
    have hc0 : Multiset.count m s = 0 := Multiset.count_eq_zero.mpr hmem
    rw [hc0]
    simp only [hmem, iff_false, Nat.zero_add]
    rw [Nat.not_odd_iff]; omega

/-- **`G_oddPart` (Lemma lem:G).** For `μ ∈ O n` and odd `m`, `m` is a part
of `G μ` iff the multiplicity of `m` in `μ` is odd. (The zeroth binary digit
`ε_{m,0}` records the parity of `mult_μ(m)`.) -/
theorem G_oddPart (x : O n) (m : ℕ) (hm : Odd m) :
    m ∈ (G data x).1.parts ↔ Odd (x.1.parts.count m) := by
  -- Auxiliary factorization: for odd m, 2^c * m' = m forces c = 0 and m' = m.
  have hfact : ∀ (c m' : ℕ), 2 ^ c * m' = m → c = 0 ∧ m' = m := by
    intro c m' hc
    rcases Nat.eq_zero_or_pos c with hc0 | hcpos
    · subst hc0; simp only [pow_zero, one_mul] at hc; exact ⟨rfl, hc⟩
    · exfalso
      have hdvd : 2 ∣ m := by
        rw [← hc]
        exact Dvd.dvd.mul_right (dvd_pow_self 2 hcpos.ne') m'
      rw [Nat.odd_iff] at hm
      omega
  rw [G_parts]
  simp only [GRaw, Multiset.mem_bind, Multiset.mem_dedup]
  constructor
  · rintro ⟨m', hm'mem, hmem⟩
    simp only [glaisherParts, Multiset.mem_coe, List.mem_map, List.mem_filter,
      List.mem_range] at hmem
    obtain ⟨c, ⟨_, htb⟩, hval⟩ := hmem
    obtain ⟨hc0, hm'eq⟩ := hfact c m' hval
    subst hc0; subst hm'eq
    rw [Nat.testBit_zero] at htb
    rw [Nat.odd_iff]; simpa using htb
  · intro hcount
    have hmemS : m ∈ x.1.parts := by
      rw [← Multiset.count_pos]
      rw [Nat.odd_iff] at hcount; omega
    refine ⟨m, hmemS, ?_⟩
    simp only [glaisherParts, Multiset.mem_coe, List.mem_map, List.mem_filter,
      List.mem_range]
    refine ⟨0, ⟨by omega, ?_⟩, by simp⟩
    rw [Nat.testBit_zero]; rw [Nat.odd_iff] at hcount; simpa using hcount

/-! ### Counting bridges

Elementary facts used to convert residue counts `r1, r3` (multiset filter
cardinalities) into finite-set cardinalities and to compare them across the
`G ∘ ψInv` stage. -/

/-- A part with `m % 4 = d` and `d` odd is itself odd. -/
theorem odd_of_mod4 {m d : ℕ} (hd : d % 2 = 1) (h : m % 4 = d) : Odd m := by
  rcases Nat.even_or_odd m with he | ho
  · exfalso; obtain ⟨k, rfl⟩ := he; omega
  · exact ho

/-- If odd parts of `s` have multiplicity `≤ 1`, then, for odd residue `d`, the
sub-multiset of parts `≡ d (mod 4)` has no repeats. -/
theorem filter_nodup_mod4
    (s : Multiset ℕ) (d : ℕ) (hd : d % 2 = 1)
    (hrep : ∀ m ∈ s, Odd m → s.count m ≤ 1) :
    (s.filter (fun m => m % 4 = d)).Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  rw [Multiset.count_filter]
  split
  · rename_i ha
    by_cases hmem : a ∈ s
    · exact hrep a hmem (odd_of_mod4 hd ha)
    · rw [Multiset.count_eq_zero.mpr hmem]; omega
  · omega

/-- For a `Nodup` multiset, any residue-`d` sub-multiset is also `Nodup`. -/
theorem filter_nodup_mod4_of_nodup
    (s : Multiset ℕ) (d : ℕ) (hnd : s.Nodup) :
    (s.filter (fun m => m % 4 = d)).Nodup :=
  Multiset.Nodup.filter _ hnd

/-- If two multisets have the same odd values as members, and (for odd residue
`d`) both have their residue-`d` sub-multisets `Nodup`, then those sub-multisets
have equal cardinality. -/
theorem card_filter_mod4_eq
    (sβ sσ : Multiset ℕ) (d : ℕ) (hd : d % 2 = 1)
    (hmem : ∀ m, Odd m → (m ∈ sσ ↔ m ∈ sβ))
    (hndβ : (sβ.filter (fun m => m % 4 = d)).Nodup)
    (hndσ : (sσ.filter (fun m => m % 4 = d)).Nodup) :
    (sσ.filter (fun m => m % 4 = d)).card = (sβ.filter (fun m => m % 4 = d)).card := by
  rw [← Multiset.toFinset_card_of_nodup hndσ, ← Multiset.toFinset_card_of_nodup hndβ]
  rw [Multiset.toFinset_filter, Multiset.toFinset_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Multiset.mem_toFinset]
  constructor
  · rintro ⟨hm, hmod⟩; exact ⟨(hmem m (odd_of_mod4 hd hmod)).mp hm, hmod⟩
  · rintro ⟨hm, hmod⟩; exact ⟨(hmem m (odd_of_mod4 hd hmod)).mpr hm, hmod⟩

/-! ### Derived residue-preservation lemma for the second half `G ∘ ψInv`

Note that neither `ψInv` nor `G` preserves `r1, r3` *individually*: `ψInv` splits
an even part `2m` (with `m` odd) into two odd parts `m`, creating new parts in
residue classes `1, 3 (mod 4)`. It is the *composite* `G ∘ ψInv` that preserves
`r1, r3`, and that is what `psiInv_oddMultiplicity` and `G_oddPart` establish,
value by value, on the odd parts.

`psiG_stat` packages this: for `β ∈ A2 n`, the composite `σ = G (ψInv β) ∈ D n`
has the same `r1, r3` as `β`. Its content is: for every odd `m`,
`m ∈ σ ↔ mult_{ψInv β}(m) odd ↔ m ∈ β` (chaining `G_oddPart` then
`psiInv_oddMultiplicity`); since `σ` has distinct parts and `β ∈ A2 n` has odd
parts of multiplicity `≤ 1`, the residue counts `r1, r3` — which see only odd
parts in classes `1, 3 (mod 4)` — coincide. This is the form in which those two
lemmas enter the assembly of `F_stat`. -/

/-- The odd values that occur as parts of `σ = G (ψInv β)` are exactly the odd
values that occur as parts of `β`, by chaining `G_oddPart` and
`psiInv_oddMultiplicity`. -/
theorem psiG_mem (x : A2 n) (m : ℕ) (hm : Odd m) :
    m ∈ (G data (ψInv data x)).1.parts ↔ m ∈ x.1.parts := by
  rw [G_oddPart data (ψInv data x) m hm, psiInv_oddMultiplicity data x m hm]

/-- The composite `G ∘ ψInv` preserves the residue statistics `r1, r3`:
`psiG_mem` gives equality of odd members of `σ = G (ψInv β)` and `β`, and the
residue counts
`r1, r3` then agree by `card_filter_mod4_eq`, using that `σ` is `Nodup` (it lies
in `D n`) and that `β ∈ A2 n` has odd parts of multiplicity `≤ 1`. -/
theorem psiG_stat (x : A2 n) :
    r1 (G data (ψInv data x)).1 = r1 x.1 ∧ r3 (G data (ψInv data x)).1 = r3 x.1 := by
  -- `σ = G (ψInv x)` is distinct.
  have hσnd : (G data (ψInv data x)).1.parts.Nodup := (G data (ψInv data x)).2
  -- `x ∈ A2 n`: odd parts have multiplicity ≤ 1.
  have hxrep : ∀ m ∈ x.1.parts, Odd m → x.1.parts.count m ≤ 1 := x.2.2
  -- membership of odd values coincides.
  have hmem : ∀ m, Odd m →
      (m ∈ (G data (ψInv data x)).1.parts ↔ m ∈ x.1.parts) :=
    fun m hm => psiG_mem data x m hm
  refine ⟨?_, ?_⟩
  · unfold r1
    exact card_filter_mod4_eq x.1.parts (G data (ψInv data x)).1.parts 1 (by norm_num) hmem
      (filter_nodup_mod4 _ 1 (by norm_num) hxrep)
      (filter_nodup_mod4_of_nodup _ 1 hσnd)
  · unfold r3
    exact card_filter_mod4_eq x.1.parts (G data (ψInv data x)).1.parts 3 (by norm_num) hmem
      (filter_nodup_mod4 _ 3 (by norm_num) hxrep)
      (filter_nodup_mod4_of_nodup _ 3 hσnd)

/-! ## The composite and the fibers -/

/-- The composite equivalence `FEquiv : D n ≃ D n`, the composition of the four
cited equivalences. Its forward function is `F = G ∘ ψInv ∘ Φ ∘ φ`. -/
noncomputable def FEquiv : D n ≃ D n :=
  (φEquiv data).trans ((ΦEquiv data).trans ((ψInvEquiv data).trans (GEquiv data)))

/-- The composite map `F = G ∘ ψInv ∘ Φ ∘ φ : D n → D n`, the composition of the
four maps. -/
def F (x : D n) : D n := G data (ψInv data (Φ data (φ data x)))

/-- `F` is the forward function of `FEquiv`. -/
@[simp] theorem FEquiv_apply (x : D n) : FEquiv data x = F data x := rfl

/-- **`F_stat`.** The composite carries `(e1, e3)` to `(r1, r3)`, by chaining
`phi_stat`, `Phi_stat` and `psiG_stat`. -/
theorem F_stat (x : D n) :
    r1 (F data x).1 = e1 x.1 ∧ r3 (F data x).1 = e3 x.1 := by
  obtain ⟨hφ1, hφ3⟩ := phi_stat data x
  obtain ⟨hΦ1, hΦ3⟩ := Phi_stat data (φ data x)
  obtain ⟨hψG1, hψG3⟩ := psiG_stat data (Φ data (φ data x))
  refine ⟨?_, ?_⟩
  · show r1 (G data (ψInv data (Φ data (φ data x)))).1 = e1 x.1
    rw [hψG1, hΦ1, hφ1]
  · show r3 (G data (ψInv data (Φ data (φ data x)))).1 = e3 x.1
    rw [hψG3, hΦ3, hφ3]

/-- `DSource i j n`: the fiber `{λ ∈ D n : e1 λ = i ∧ e3 λ = j}`. -/
def DSource (i j n : ℕ) : Type := {x : D n // e1 x.1 = i ∧ e3 x.1 = j}

/-- `DTarget i j n`: the fiber `{σ ∈ D n : r1 σ = i ∧ r3 σ = j}`. -/
def DTarget (i j n : ℕ) : Type := {x : D n // r1 x.1 = i ∧ r3 x.1 = j}

instance (i j n : ℕ) : Fintype (DSource i j n) := by
  classical unfold DSource; infer_instance
instance (i j n : ℕ) : Fintype (DTarget i j n) := by
  classical unfold DTarget; infer_instance

/-! ## The main theorem

The fiber-membership characterization `mainEquiv_spec` follows from `F_stat`
alone. Because `FEquiv data x = F data x` definitionally, the two equalities
supplied by `F_stat` turn each side of the `↔` into the other by rewriting. Both
directions use the same `F_stat` equations, so no separate statement about
`FEquiv.symm` is required; the inverse of `mainEquiv` is inherited from `FEquiv`
via `Equiv.subtypeEquiv`. -/

/-- **Fiber-transfer characterization.** For every `λ ∈ D n`, membership of `λ`
in `DSource i j n` is equivalent to membership of `FEquiv λ` in `DTarget i j n`.
Follows from `F_stat`. -/
theorem mainEquiv_spec (i j : ℕ) (x : D n) :
    (e1 x.1 = i ∧ e3 x.1 = j) ↔
      (r1 (FEquiv data x).1 = i ∧ r3 (FEquiv data x).1 = j) := by
  obtain ⟨h1, h3⟩ := F_stat data x
  rw [FEquiv_apply, h1, h3]

/-- **`mainEquiv i j n : DSource i j n ≃ DTarget i j n`.** The restriction of
`FEquiv` to the fibers, built as `Equiv.subtypeEquiv FEquiv` along
`mainEquiv_spec`. The forward direction that `F` maps `DSource i j n` into
`DTarget i j n` is `F_stat`; the inverse is inherited from `FEquiv`. -/
noncomputable def mainEquiv (i j : ℕ) : DSource i j n ≃ DTarget i j n :=
  Equiv.subtypeEquiv (FEquiv data) (mainEquiv_spec data i j)

/-- **`main_cardinality i j n`** — the Berkovich--Uncu identity (thm:BU),
derived from `mainEquiv`: the number of strict partitions of `n` with
`e1 = i, e3 = j` equals the number with `r1 = i, r3 = j`. -/
theorem main_cardinality (data : BUData n) (i j : ℕ) :
    Fintype.card (DSource i j n) = Fintype.card (DTarget i j n) :=
  Fintype.card_congr (mainEquiv data i j)

end BerkovichUncu
