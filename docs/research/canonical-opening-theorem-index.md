# Canonical opening theorem index

This index records exactly what the canonical-opening modules prove. It is a
scope ledger, not a novelty claim or evidence that `P != NP`.

## Semantic opening

### `ExactOpening`

An `ExactOpening Query Answer Proof Challenge` contains:

- one canonical answer for each query;
- one honest proof accepted by every challenge; and
- for every noncanonical answer and every proof, at least one rejecting
  challenge.

The last clause is pointwise soundness: the rejecting challenge may depend on
the false answer and proof. The structure states no probability distribution,
computability, or resource bound.

### One, two, and adaptively many queries

The one-query, two-query, and well-founded adaptive theorems prove the same
equivalence:

```text
some challenge-independent strategy accepts every later challenge
  iff
the original verifier accepts the canonical oracle answers
```

All three results assume that `Challenge` is nonempty. Without that assumption,
universal acceptance over challenges would be vacuous.

The adaptive model permits a later query to depend on an earlier claimed
answer. It fixes every claimed answer and opening proof along the realized
original transcript before the later opening challenges are supplied. Thus the
theorem covers batched transcript projection; it does not transform a protocol
whose answers may depend on intervening verifier challenges.

The verifier is an inductive, well-founded tree. Every realized path is finite,
but the theorem supplies no uniform path-length or tree-size bound.

| Dimension | Checked scope |
| --- | --- |
| Verifier randomness | Represented abstractly by queries and challenges |
| Prover adaptivity | Earlier answers select later queries |
| Challenge dependence | Excluded from original answers by the strategy type |
| Soundness | Exact, pointwise: every false proof has some rejecting challenge |
| Completeness | Perfect: every challenge accepts the honest proof |
| Computability | Not asserted |
| Resources | Not asserted |

## Resource accounting

`OpeningResourceProfile` assigns a natural number to each tracked category:
rounds, prover bits, challenge bits, verifier time, verifier workspace,
compiler time, preprocessing time, input access, and inherited descriptions.

For an adaptive path with `q` queries, an original budget `B0`, and a uniform
per-opening budget `B`, Lean proves the coordinatewise accounting bound

```text
B0 + q * B.
```

This is a theorem about supplied profile values. It does not connect a Lean
program, Turing machine, or protocol implementation to those values. Every
complexity-theoretic consumer still needs an operational realization theorem.

## Recursive opening steps

`ExactOpeningStep` separates two invariants:

- an honest proof of a true parent never rejects and emits only true children;
- every proof of a false parent has a challenge that rejects or emits a false
  child.

The interface does not require the child to be smaller. Size reduction and its
cost must be proved by a concrete implementation.

`LinearContractionOpening.exactStep` instantiates this interface by sending all
slice contractions. It is exact over every finite index type and semiring with
decidable equality. Its message contains one scalar per slice.

## Local-slice barriers

The one-round product theorem assumes the exact shape

```text
parentMass = sliceCount * childMass.
```

If both factors are at most `B`, then `parentMass <= B^2`.

The repeated theorem assumes the stronger uniform shape

```text
parentMass = branching^rounds * childMass.
```

If branching and child mass are at most `B`, then
`parentMass <= B^(rounds + 1)`. Consequently, with parent mass `2^(m^2)` and
budget `2^(C*m)`, the two bounds are incompatible when
`C * (rounds + 1) < m`.

This rules out uniform local slicing that carries the selected slice forward
unchanged. It does not cover nonuniform slices, algebraic folds, checksums,
proximity protocols, or a challenge that constructs a different child.

## Checksum results

The checksum definition follows Chen, Hong, Kalai, and Xi, *Towards a Doubly
Efficient IP = PSPACE*, ECCC TR26-102, revision 1, June 19, 2026, Definition 6
and Proposition 1, p. 9 (PDF p. 11).

`IsUniqueDecodingChecksum d checksum` says that two distinct words within
Hamming radius `d` of one center have different checksums. Lean proves:

- equal checksums and distance at most `d` force equality;
- distinct equal-checksum words have distance greater than `d`; and
- an additive checksum has the property when every nonzero kernel word has
  Hamming weight greater than `2*d`.

These are binding statements. They neither show that a candidate is near the
canonical word nor locate an error in a far candidate.

If a checksum alone exactly decodes every coordinate of every word, Lean proves
that the checksum is injective. Hence a shorter binary checksum cannot exactly
decode every longer binary word without additional information or interaction.

## Sparse linear checksum barrier

For a radius-one linear checksum matrix, every input column has a nonzero
entry. If each row has support at most `L`, incidence counting gives

```text
input columns <= checksum rows * L.
```

Thus a matrix with at most `2^(C*m)` rows and row support at most `2^(C*m)`
cannot cover `2^(m^2)` columns when `2*C < m`.

This theorem covers sparse linear rows opened by exposing their full support.
It does not cover dense rows with a separate local algebraic opening, nonlinear
checksums, approximate soundness, or a near-far proximity subprotocol.

## Finite experiment

For three-bit binary words at radius one, exhaustive evaluation proves that:

- every one-row linear checksum fails;
- exactly six two-row matrices succeed; and
- every one-row matrix has a checked collision witness.

This is a complete finite certificate for that parameter choice. It is not the
general Hamming-code classification and carries no asymptotic lower bound.

## Open boundary

The missing primitive must combine near-case checksum binding with a charged
far-case proximity argument that either rejects or emits a genuinely smaller
false child. No current theorem supplies that primitive.
