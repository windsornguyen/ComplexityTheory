# ComplexityTheory Style

These rules govern every human and agent contribution to ComplexityTheory.
They exist to keep mathematical meaning, executable computation, and proof
provenance readable as the library grows.

## Correctness Boundaries

- Reuse Mathlib definitions and theorems when they express the required
  concept. Add a project-specific definition only when it names a genuine
  complexity-theory boundary or specializes Mathlib for a real consumer.
- Search the pinned dependency sources before adding a project-specific API.
  We can establish absence from those sources, not universal nonexistence. If
  a declaration lifts a generic operation into a project type, name the
  underlying operation and explain what certificate the wrapper adds.
- Do not use `sorry` or introduce axioms. Represent unresolved research
  boundaries as definitions of the desired property, not assumed facts.
- Keep these claims distinct: semantic truth, computability, polynomial-time
  computability, external Lean verification, and provability inside a bounded
  arithmetic theory. Never let one stand in for another.
- State every assumption explicitly. A theorem may be formally valid and still
  encode the wrong mathematical claim.

## Declarations

- Build larger statements from small, named definitions and functions. Name a
  recurring proposition, conversion, or function when the name exposes its
  mathematical role; do not create abstractions without a real consumer.
- Give every public declaration a docstring. First state its formal contract
  and assumptions, then explain in plain language why it exists or how later
  proofs use it.
- Prefer names that describe the mathematical object or invariant. Use full
  words unless a standard Lean or Mathlib abbreviation, such as `refl`,
  `trans`, `comp`, `inj`, or `iff`, carries its conventional meaning.
- Use explicit types, casts, finite ranges, and encodings where textbook
  notation relies on context or implicit coercion.
- Executable parsers and decoders must reject malformed input. Do not invent a
  value, silently ignore trailing data, or add a fallback representation.
- Do not add fallback execution paths. If the declared operation cannot run,
  expose a typed failure instead of silently selecting another implementation.
  A total mathematical map may require an output for rejected inputs; name it
  `rejectionOutput`, show the branch in its defining equation, and cite the
  totality requirement. Do not describe that output as a fallback.

## Sources

- Cite every borrowed definition or result with authors, title, year and
  edition or version, plus a precise definition, theorem, section, or page.
- When PDF and printed page numbers differ, record both. Example: "Arora and
  Barak, *Computational Complexity: A Modern Approach*, January 2007 web draft,
  Definition 1.2, p. 14 (PDF p. 30)."
- State every change in assumptions, encoding, notation, or formulation near
  the declaration it affects.
- A citation explains provenance; it does not replace a Lean proof.

## Lean Source

- Follow current Mathlib naming, formatting, and simplifier conventions.
- Use `[simp]` only for canonical reductions with a clear normal form.
- Prefer proofs whose intermediate names expose the argument over compressed
  tactic scripts. Proof brevity is useful only while the proof remains clear.
- Keep modules focused and add every public module to `ComplexityTheory.lean`.
- Keep files below 500 lines and pull requests below 200 changed lines when
  practical. Use stacked pull requests for dependent layers.

Mathlib's header linter requires the copyright and license lines in this exact
form; list the actual file authors on the final line:

```text
/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <comma-separated authors>
-/
```

The wording is a tooling convention, not a second license. The repository's
LICENSE file contains the controlling Apache License 2.0 text, and
`lakefile.toml` carries the SPDX identifier `Apache-2.0`.

## Verification

- Test the invariant at the smallest honest layer. Round-trip codecs, exact
  lengths, injectivity, and malformed-input rejection should be theorems.
- Before committing Lean changes, run:

```bash
lake build --wfail
lake lint
git diff --check
```

- Report local verification, remote CI, approval, and merge state separately.
  One is not evidence for another.
