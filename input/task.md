# Formalize the explicit Berkovich--Uncu bijection and its statistic transfer

## Objective

Formalize the main theorem of `main-5.tex` using the four-map bijection stated in
that paper. Define the four maps concretely and prove the paper's statistic
bookkeeping. Treat the previously published bijectivity of the component maps as
external input, in the precise form described below.

This is not a request to reprove the Chen--Gao--Ji--Li/Bessenrodt insertion
theorem or Glaisher's bijectivity theorem. It is also not a request to discover a
new bijection.

The authoritative source for the target theorem is `main-5.tex`. Read it in
full before writing `problem.md`. The definitions and theorem in Sections
2.1--2.5, especially
Definitions `def:phi`, `def:Phi`, `def:psiinv`, and `def:G`, Lemmas `lem:phi`,
`lem:Phi`, `lem:psiinv`, and `lem:G`, and Theorem `thm:main`, fix the intended
formalization. The submission does not ask AxiomProver to formalize the cited
proofs that the component maps are bijective.

## Exact mathematical result

For each `n`, let `D n` be the finite type of partitions of `n` into distinct
positive parts, represented in decreasing order. For `lambda : D n`, define:

- `e1 lambda`: the number of odd-valued parts in odd-numbered positions, using
  one-based positions in the decreasing list;
- `e3 lambda`: the number of odd-valued parts in even-numbered positions;
- `r1 lambda`: the number of parts congruent to `1` modulo `4`;
- `r3 lambda`: the number of parts congruent to `3` modulo `4`.

For `i j n : Nat`, define the two fibers

- `DSource i j n = {lambda : D n | e1 lambda = i and e3 lambda = j}`;
- `DTarget i j n = {sigma : D n | r1 sigma = i and r3 sigma = j}`.

Construct the paper's concrete map

`F = G after psiInv after Phi after phi`

and prove that its restriction is an equivalence

`DSource i j n ~= DTarget i j n`.

Derive as a corollary that these two finite fibers have equal cardinality. The
equivalence is the primary result; cardinal equality alone is not an acceptable
replacement.

## Representation and Mathlib reuse

Use Mathlib's `Nat.Partition n` and `Nat.Partition.distincts n`. Do not introduce
a second foundational partition structure unless a small list-level helper is
needed internally. A decreasing list view of a partition may be defined for
computing position statistics, with bridge lemmas back to the underlying
multiset.

Reuse Mathlib's standard finite-set, subtype, `Equiv`, list, multiset, sorting,
parity, modular-arithmetic, and cardinality APIs. Mathlib's theorem
`Nat.Partition.card_odds_eq_card_distincts` is a cardinality theorem and is not a
substitute for the explicit Glaisher map required here.

## The four fixed maps

The formalization must use exactly the following route. Do not replace it with
an existentially chosen equivalence, fiber matching, a generating-function
argument, or another bijection.

### 1. Two-modular conjugation `phi : D n -> A1 n`

Define `A1 n` exactly by conditions (A1.1)--(A1.4) in `main-5.tex`.

For a strict partition `lambda`, form one row for each part:

- `2*q` becomes `q` entries equal to `2`;
- `2*q+1` becomes `q` entries equal to `2`, followed by one entry equal to `1`.

Define `phi lambda` to be the decreasing list of column sums. This is the map in
Definition `def:phi`; it is not an arbitrary map constrained by equations.

The previously published theorem that this concrete construction is a
bijection `D n <-> A1 n` must be an explicit hypothesis. It may be represented
as `Function.Bijective phi` or as an `Equiv` whose forward function is
definitionally `phi`. No concrete inverse definition or round-trip proof is
required in this task.

Prove internally the new statistic-transfer statement from Lemma `lem:phi`:

- `r1 (phi lambda) = e1 lambda`;
- `r3 (phi lambda) = e3 lambda`.

The proof must use the terminal-`1` column calculation: an odd part in one-based
position `r` contributes the unique odd column sum `2*r-1`, which is `1 mod 4`
for odd `r` and `3 mod 4` for even `r`.

### 2. CGJL/Bessenrodt insertion `Phi : A1 n -> A2 n`

Define `A2 n` exactly by conditions (A2.1)--(A2.2): no part is divisible by
`4`, and only even parts may repeat.

Define the forward algorithm `Phi` exactly as Definition `def:Phi` in
`main-5.tex`:

1. Pre-extraction repeatedly removes the largest removable multiple of `4`,
   using the stated neighbor-gap test, and records the removed value.
2. Iterative extraction chooses the largest remaining part `4*m` in one-based
   position `s`, subtracts `4` from the preceding `s-1` parts, deletes `4*m`,
   and records `4*(s-1)+4*m`.
3. Insertion processes recorded parts `4*h` in decreasing order, adds `4` to
   the first `h` parts, and re-sorts after each insertion.

Use a terminating finite implementation with an explicit fuel or decreasing
measure. Its computed output must agree with the preceding algorithm. Do not
invent a simplified insertion map.

The published facts that this concrete algorithm lands in `A2 n`, preserves
weight, and is bijective must be explicit hypotheses. Bijectivity may be
represented as `Function.Bijective Phi` or as an `Equiv` whose forward function
is definitionally this concrete algorithm. No concrete inverse definition or
round-trip proof is required in this task.

Prove internally Lemma `lem:Phi`:

- `r1 (Phi alpha) = r1 alpha`;
- `r3 (Phi alpha) = r3 alpha`.

This proof is elementary and must inspect the operations: deleted and recorded
parts are divisible by `4`; surviving parts are shifted only by `4`; sorting
does not alter multiplicities. Do not make statistic preservation a hypothesis.

### 3. Splitting map `psiInv : A2 n -> OddPartitions n`

Let `OddPartitions n` be partitions of `n` into odd parts. Define `psiInv`
concretely by multiplicities. For each odd positive `m`, if `b_m` and `b_(2*m)`
are the multiplicities of `m` and `2*m` in `beta`, set

`mult_(psiInv beta)(m) = b_m + 2*b_(2*m)`.

Because `beta` is in `A2 n`, every part is either odd or twice an odd number and
every odd part has multiplicity at most one.

The published facts that this concrete map lands in `OddPartitions n`, preserves
weight, and is bijective must be explicit hypotheses. No concrete inverse
definition or round-trip proof is required in this task.

Prove internally Lemma `lem:psiinv`: for every odd `m`, the multiplicity of `m`
in `psiInv beta` is odd exactly when `m` occurs as a part of `beta`. The proof
must reduce `b_m + 2*b_(2*m)` modulo `2` and use `b_m` in `{0,1}`.

### 4. Glaisher map `G : OddPartitions n -> D n`

Define `G` concretely by binary expansion. If an odd value `m` occurs with
multiplicity

`sum_c epsilon(m,c) * 2^c`, with each digit in `{0,1}`,

then output the distinct parts `2^c*m` for precisely the nonzero digits.

The classical facts that this concrete function lands in `D n`, preserves
weight, and is bijective must be explicit hypotheses. No concrete inverse
definition or round-trip proof is required. Do not replace the function with
Mathlib's generating-function proof of equal cardinality.

Prove internally Lemma `lem:G`: an odd value `m` occurs as an odd part of
`G mu` exactly when its multiplicity in `mu` is odd. This is the statement that
the zero-th binary digit records parity.

## Permitted external inputs

The only non-Mathlib mathematical inputs permitted are the following cited
bijectivity packages:

1. the concrete `phi` is a weight-preserving bijection `D n -> A1 n`;
2. the concrete CGJL/Bessenrodt `Phi` is a weight-preserving bijection
   `A1 n -> A2 n`;
3. the concrete `psiInv` is a weight-preserving bijection
   `A2 n -> OddPartitions n`;
4. the concrete Glaisher `G` is a weight-preserving bijection
   `OddPartitions n -> D n`.

These may be supplied as four `Function.Bijective` hypotheses or as four
`Equiv` parameters. Each must be pinned to the corresponding concrete forward
function above; an unconstrained abstract equivalence is not permitted.

No statistic-transfer assertion may be included in these external packages.
The four statistic lemmas are the proof obligations of this task.

## Required public declarations

Expose declarations corresponding to:

- the four partition classes `D`, `A1`, `A2`, and `OddPartitions`;
- the four concrete forward maps;
- the four cited bijectivity packages or equivalent explicit hypotheses;
- the statistics `e1`, `e3`, `r1`, and `r3`;
- `phi_stat`, containing the two conclusions of `lem:phi`;
- `Phi_stat`, containing the two conclusions of `lem:Phi`;
- `psiInv_oddMultiplicity`, corresponding to `lem:psiinv`;
- `G_oddPart`, corresponding to `lem:G`;
- the composite equivalence `FEquiv : D n ~= D n`;
- `F_stat`, proving `r1 (F lambda) = e1 lambda` and
  `r3 (F lambda) = e3 lambda`;
- `mainEquiv i j n : DSource i j n ~= DTarget i j n`;
- `main_cardinality i j n`, the cardinal-equality corollary.

Names may be adjusted to Lean conventions, but these mathematical boundaries
must remain separately visible.

## Proof route for the main theorem

After proving the four local statistic lemmas:

1. Compose the four cited equivalences to obtain `FEquiv`.
2. Chain `phi_stat` and `Phi_stat` to transport `e1,e3` to the two odd residue
   counts on `beta`.
3. Use `psiInv_oddMultiplicity` and `G_oddPart` to show that the odd parts and
   their values, hence their residues modulo `4`, are preserved through the
   last two stages.
4. Obtain `F_stat` pointwise.
5. Restrict `FEquiv` to the source and target fibers using `F_stat`; obtain the
   inverse from the cited bijectivity of the composite.
6. Derive finite cardinal equality from `mainEquiv`.

Do not prove surjectivity of the fiber restriction by a finite-cardinality or
disjoint-union argument. Use the explicit inverse inherited from the composite
equivalence.

## Faithfulness and anti-shortcut requirements

- Do not replace the requested map by `Fintype.equivOfCardEq`, choice, a matched
  enumeration of fibers, or any noncomputably selected equivalence.
- Do not prove cardinal equality first and manufacture an equivalence from it.
- Do not use generating functions, coefficient extraction, transfer matrices,
  or induction over the number being partitioned as a substitute for the
  four-map construction.
- Do not leave any of the four maps opaque or define one only through desired
  properties.
- Do not make cited bijectivity, weight preservation, or class membership new
  proof obligations.
- Do not make any statistic-transfer result an assumption.
- Do not strengthen an external package with the final theorem, a fiber
  equivalence, or any conclusion implying the desired statistic transfer.
- Do not introduce global axioms. All cited inputs must be explicit parameters
  of the relevant theorem or fields of an explicitly passed structure.
- Do not weaken the theorem to cardinal equality. The explicit fiber
  equivalence is required.
- Do not attempt to discover an alternative map during proof search. The four
  maps above are final before `problem.md` is written.
- The final file must compile without admitted proofs or new axioms.

## Phase-boundary requirement

Before accepting `problem.md`, verify that it already fixes:

1. the four partition classes;
2. the exact concrete definitions of all four forward maps;
3. the exact permitted cited-input packages;
4. the four internal statistic lemmas;
5. the composite and fiber-equivalence targets.

Phase B must encode those choices directly in `problem.lean`. Proof search is
responsible for proving the four statistic lemmas and assembling the composite;
it is not responsible for inventing or changing the maps, intermediate classes,
or external-input boundary.

If the source text is insufficient to implement any concrete map exactly, stop
with a structured request for that cited definition. Do not guess, replace the
map, or continue with an abstract placeholder.
