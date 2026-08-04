# ARZR oracle and parameter audit

*Research notebook, August 3, 2026. This is a dependency audit, not a
de-oraclization theorem or evidence that `P != NP`.*

The proposed exact-opening program depends on knowing which values the verifier
reads, who computes them, and which costs the published bounds hide behind a
fixed constant. The construction has three distinct layers. Conflating them
would make a tensor-opening lemma appear to eliminate oracles that it never
touches.

The source is Noor Athamnah, Noga Ron-Zewi, and Ron D. Rothblum, *Linear Prover
IOPs in Log Star Rounds*, ECCC TR25-090, revision 2, June 19, 2026. Page numbers
below are both printed and PDF page numbers.

## The three protocol layers

| Layer | Long prover objects | Terminal verifier access | Exact-opening status |
| --- | --- | --- | --- |
| Theorem 4.1 ordinary interactive proof | Explicit messages produced during the inner-product and code-switching protocols | Indices and claimed values for entries of tensor codewords `C_n(y_j)` | A tensor-entry opening could apply to the terminal claims, but the ordinary verifier already spends `n^gamma * poly(1/epsilon)` time. |
| Corollary 4.2 proof-composed IOP | Encodings `E(z_i)` of every ordinary prover message, plus a PCPP proof oracle | PCPP queries to the encoded messages, input codewords, and proof oracle | Opening tensor-code entries does not open the PCPP proof oracle. |
| Section 5 circuit IOP | Tensor-code oracles `Ez`, `Ea`, `Eb`, and `Ec`, plus proximity, correction, and lincheck PCPP oracles | Queries selected by several compiled subprotocols | Every oracle family needs a canonical generator and an exact opening before full de-oraclization follows. |

Theorem 4.1 is an ordinary `log* n + O(1)`-round protocol. It ends by producing
indices `i_j` and values `u_j` such that the remaining claims are
`(C_n(y_j))(i_j) = u_j`. Its verifier time and communication are
`n^gamma * poly(1/epsilon)` (Theorem 4.1, p. 31).

Corollary 4.2 is not merely a query-efficient presentation of the same prover
messages. The proof-composition step pads each ordinary message `z_i`, sends
`E(z_i)` as an oracle, and invokes a PCPP for a pair language describing an
accepting verifier transcript. The PCPP verifier queries both the implicit
input and a separate proof oracle (Section 4.5, pp. 49-50).

Section 5 then arithmetizes a regular R1CS instance. The prover sends `Ez`,
`Ea`, `Eb`, and `Ec`, but tensor-code proximity testing, relaxed correction,
and lincheck are themselves composed with PCPPs. The preprocessing bound also
uses the regular wiring structure of the target circuit (Section 5,
pp. 51-52).

## The fixed-`gamma` boundary

The paper explicitly assumes that `gamma > 0` is a constant. Its domains are
split into

```text
m = m1 + m2,
m1 <= log* n,
m2 = ceil(2 / gamma).
```

The conclusion `m = log* n + O(1)` therefore uses fixed `gamma` (Section 4.1,
pp. 32-33). The field sizes also depend on `gamma`: `a_t` is the smallest
double-exponential power exceeding
`d * n_t * t^2 / (epsilon * gamma)^sigma1` (Equation 8, p. 33).

The final code-switching phase performs `m2` slice rounds and one terminal
round. Its tensor dimension is `m2 = ceil(2 / gamma)` (Figure 6, p. 45;
verifier analysis, p. 48). In the terminal round, the verifier handles

```text
N1 <= 2^(sqrt(log n) * O(log* n))
```

work before upper-bounding it by `n^gamma` (p. 48). Substituting an
input-dependent `gamma(n)` is therefore invalid without redoing every bound.
For example, `gamma(n) = Theta(1 / sqrt(log n))` makes the tensor dimension
grow and leaves an extra `log* n` factor in this displayed terminal cost.

Proof composition adds another dependency. It uses proximity

```text
alpha = delta / (2 * (m + d * log |F1|)),
```

and a PCPP with `O(1 / alpha)` queries. It applies Theorem 4.1 with a constant
`gamma'` chosen sufficiently small as a function of the target constant
`gamma`; no uniform dependence for `gamma = gamma(n)` is proved (pp. 49-50).

## Fail-closed canonicality inventory

A de-oraclization theorem must project the expanded interaction back to the
original verifier transcript. Opening-protocol randomness must not influence
the canonical oracle being opened. For each queried oracle family it must
provide:

1. a total deterministic generator from the original input and transcript;
2. a claimed symbol whose type exposes its query address;
3. perfect completeness for the canonical symbol;
4. pointwise false descent: for every proof message for a false symbol, some
   public challenge rejects or produces a strictly smaller false claim; and
5. explicit bounds for generation, preprocessing, communication, verification,
   workspace, input access, and inherited descriptions.

Tensor codewords of deterministic trace data are plausible candidates for this
interface. An ordinary prover message can also be canonical only after fixing
a total honest-prover algorithm, rather than existentially selecting an
accepting message. The PCPP proof oracles are currently unresolved: the paper
proves that suitable proofs exist and are efficiently constructible, but it
does not put their individual symbols into the tensor-factorized opening
grammar proposed here.

Consequently, an exact opening theorem for one tensor-code symbol is necessary
and independently useful, but insufficient to de-oraclize Corollary 4.2 or the
Section 5 circuit IOP. Full de-oraclization may be claimed only after the same
obligation is discharged for every PCPP and correction oracle that the verifier
can query.

## Lean work forced by the audit

The first formal layer should not encode all of ARZR. It should prove the
semantic composition rule for one canonical query, with separate original and
expanded randomness and an explicit transcript projection. That theorem can
then be iterated only after a two-query adaptive case passes.

The first concrete experiment should target a terminal entry of the tensor code
from Theorem 4.1, not a generic symbol of the compiled circuit IOP. A positive
result must expose the claimed tensor factors and every challenge. A negative
result should retain a finite, Lean-checkable cheating certificate and state
the exact restricted grammar it refutes.
