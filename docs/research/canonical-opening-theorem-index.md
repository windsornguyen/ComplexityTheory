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

Hamming (1950, Section 3, pp. 150-154) gives the binary nonzero,
pairwise-distinct-column condition. At radius one over a finite field, Lean
proves its projective generalization:

```text
unique decoding
  iff
all columns are nonzero and no two are proportional.
```

Lean proves the exact cardinal inequality `1 + n*(q - 1) <= q^r`; the binary
specialization is `n <= 2^r - 1`. These finite-field bounds do not supply a
proximity test or a local implementation of a dense checksum row.

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

This is a complete finite certificate for that parameter choice. The later
projective classification explains the six survivors symbolically. The count
remains a regression test rather than an independent asymptotic result.

## Near-far composition

`NearFarFold` separates a unique-decoding checksum, a canonical object, a local
validity predicate, and an explicit proximity opening step. Lean proves that an
invalid canonical object is far from every valid object in its checksum fiber
and that an exact proximity step can be reinterpreted as an exact parent step.

The interface does not construct the proximity step. In particular, it does
not justify replacing a prover-selected checksum with the canonical checksum,
or permit an uncharged oracle for deciding proximity.

## Unbatched tensor accounting

`unbatchedTensorOpening_not_clockClosing` proves that the sufficient inequality
`Lambda^t < t` is impossible when `2 <= Lambda`. The companion winner-cost
theorem states the corresponding natural-number mass bound.

These results apply only to the audited unbatched tensor protocol composed with
the current multiplicative-round compiler certificate. They are not lower
bounds against arbitrary winner algorithms or tensor protocols.

## Finite strategy checking and response splicing

`hasCheatingOneStepStrategy` exhaustively decides whether a finite false parent
has one proof safe under every challenge. The checker proves the Boolean result
equivalent to the named existential proposition; candidate modules retain an
explicit witness in addition to the search result.

`SeparatedResponseStrategy.safeForEveryChallenge_iff` exposes the exact
splicing seam: if the global response and each local response are independently
safe under one commitment, they combine into a strategy safe for every
challenge.

`FourAxisSplicing` instantiates this grammar with a valid radius-one checksum.
For the zero `2 x 2 x 2 x 2` tensor and false top value one, the global branch
uses the odd checksum-kernel word `(1, 1, 1, 0)` while every local branch uses
the canonical zero word. Lean checks both the explicit strategy and the
exhaustive search result. This refutes only protocols that fail to bind the
global and local responses to one candidate.

## Exact four-axis affine fold

`FourCoordinateAffineBinding` gives a positive no-response baseline. For every
nonzero linear functional on four binary coordinates, it constructs a
three-bit radius-one checksum whose kernel vector has weight at least three and
affine value one. The public claimed bit plus the syndrome uniquely decodes one
four-coordinate word.

Lean proves the decoder equations, radius-one checksum property, exhaustive
absence of a cheating finite strategy, and an `ExactOpeningStep` theorem. The
tensor instantiation `FourAxisAffine.exactStep` groups a
`2 x 2 x 2 x 2` tensor into four inner-slice contractions; one public
coordinate challenge emits a two-axis child. There is no prover response after
the challenge.

This is semantic four-to-two shrinkage. The `Open2` type has two indices, but no
current theorem connects its Lean representation to an implementation that
copies exactly four field elements or avoids retaining a closure over the
parent tensor.

## Affine-binding cardinality barrier

`messageCardinality_ge_injectiveCanonicalFamily` isolates the underlying
pigeonhole argument: any decoder covering an injectively indexed canonical
family needs at least one message per family member. Applying it to a proposed
structured family still requires explicit proofs of injectivity and coverage.

`messageCardinality_ge_twoPow_freeCoordinates` assumes a deterministic decoder
represents every solution of one binary affine equation on `n + 1`
coordinates. Lean proves that its message space has at least `2^n` elements.
For an `r`-bit message, `binaryMessageLength_ge_freeCoordinates` gives
`n <= r`.

The coverage assumption is essential. This theorem does not cover a structured
subset of canonical words, a probabilistic or interactive binder, or a
protocol whose later messages contribute binding information.

## Open boundary

The exact four-to-two affine fold is an optimal finite correctness baseline,
but its direct `n`-coordinate generalization transmits at least `n - 1` bits.
The remaining asymptotic primitive must therefore exploit structure in the
canonical tensors or combine a shorter checksum with a charged proximity
interaction. No current theorem supplies square-log compression, an
operational resource realization, or evidence for `P != NP`.
