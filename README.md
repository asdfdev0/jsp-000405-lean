# JSP-000405 literal Lean proof

This repository formalizes a complete solution to the **literal published wording** of Justin Sun Prize problem JSP-000405:

> How many distinct circles must a planar point set determine if its points are not all concyclic?

Under that wording, the minimum is `0`: for every `n ≥ 3`, take `n` distinct collinear points. They are not all contained in a proper circle, and no three of them determine a circle.

The historical/source problem (Erdős problem #506) is stronger. Its source discussion says that a non-degeneracy condition is clearly intended; the standard corrected formulation excludes configurations that are all collinear as well as configurations that are all concyclic. This repository **does not claim to solve that corrected/original nondegenerate problem**.

## Main theorem

`JSP000405.jsp_000405_literal`

```lean
theorem jsp_000405_literal (n : ℕ) (hn : 3 ≤ n) :
    ∃ P : Fin n → Point,
      Function.Injective P ∧
      ¬ AllConcyclic P ∧
      circleCount P = 0
```

The witness is `axisConfig n`, the `n` distinct points `(0,0), (1,0), ..., (n-1,0)`.

## Definitions

A proper circle is represented by a monic equation

`x^2 + y^2 + u*x + v*y + w = 0`.

A circle is counted as determined by a configuration when it contains three distinct indexed points. The proof shows algebraically that one such circle cannot contain three distinct points of `axisConfig n`.

## Reproduction

The project pins Lean and Mathlib in `lean-toolchain` and `lakefile.toml`.

```bash
lake exe cache get
lake build
lake env lean JSP000405.lean
```

The source ends with:

```lean
#print axioms JSP000405.jsp_000405_literal
```

CI runs the build and axiom audit on every push and pull request.

## Scope and attribution

The missing non-collinearity condition is publicly noted in the Erdős #506 source discussion and is not claimed here as a new mathematical discovery. The contribution of this repository is the explicit complete literal solution and its Lean formalization.
