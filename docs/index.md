# ComplexityTheory

ComplexityTheory formalizes computational complexity theory in Lean 4 on top
of Mathlib.

## Install

Install Lean with `elan`, then clone and build the library:

```bash
git clone https://github.com/windsornguyen/ComplexityTheory.git
cd ComplexityTheory
lake exe cache get
lake build --wfail
lake lint
```

To use the package from another Lake project, add its tagged release:

```toml
[[require]]
name = "complexitytheory"
git = "https://github.com/windsornguyen/ComplexityTheory.git"
rev = "v0.0.1"
```

## Use

Import the umbrella module, which exposes every public module in the package:

```lean
import ComplexityTheory
```

See the generated [Lean API reference](https://windsornguyen.github.io/ComplexityTheory/api/)
for declarations and source links.
