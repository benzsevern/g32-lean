import HodgeLean.Adapters.DeRhamAbelianProofs

/-! # The de Rham side for abelian `X`: frozen specification

Inputs stage 3b. Stage 3 (`BettiDeRham`) reduced `BettiDeRhamIso X` for abelian `X` to the de Rham
dimension count `dim H_dR^n(X) = C(2g, n)`. This file moves the de Rham side onto topology.

Claimed:
* the holomorphic Poincaré lemma as a `ℂ`-linear equivalence `H^n(X(ℂ); ℂ) ≃ H_dR^n(X)` for
  every smooth integral `X` and every `n`;
* universal coefficients over fields for singular cohomology: if `H^n(Y; ℚ)` is
  finite-dimensional then so is `H^n(Y; ℂ)`, with the same dimension, for every space `Y`;
* the complex singular Betti numbers of an abelian `X`: `dim H^k(X(ℂ); ℂ) = C(2g, k)`;
* for abelian `X`, bijectivity of `bettiDeRhamHQ X n` is equivalent to the count
  `dim H^n(X(ℂ); ℂ) = C(2g, n)` for constant-sheaf cohomology, and to the upper bound
  `dim H_dR^n(X) ≤ C(2g, n)` (with finite dimension);
* the implication from a `ℂ`-linear sheaf-to-singular comparison `H^n(X(ℂ); ℂ) ≃ H^n_sing(X(ℂ); ℂ)`
  in degree `n` to bijectivity of `bettiDeRhamHQ X n`;
* the falsification check that `H_dR^1(X)` is nonzero for abelian `X` of positive dimension.

Not claimed: the de Rham dimension count itself (the deferred `spec_finrank_deRham_one_abelian`
of `docs/specs/BettiDeRham.md`), the sheaf-to-singular comparison over `ℂ`, finiteness of coherent
cohomology, any graded piece of the Hodge filtration, invariant differential forms, or a period
pairing. No statement assumes `BettiDeRhamIso` or `HodgeDecomposition`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- The holomorphic Poincaré lemma, `ℂ`-linearly: constant-sheaf cohomology `H^n(X(ℂ); ℂ)` and
holomorphic de Rham hypercohomology `H_dR^n(X)` are isomorphic complex vector spaces.

Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 3 §5 (the holomorphic
Poincaré lemma: `ℂ → Ω•` is a resolution), through upstream's `complexConstantCohomologyDeRhamEquiv`
(`Filtration.lean:348`) and `constantsToHolomorphicDeRhamComplexInt_scalar` for the scalars. -/
theorem spec_complexCohomology_linearEquiv_deRham (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    Nonempty (H^n(X; ℂ) ≃ₗ[ℂ] H_dR^(n : ℤ)(X)) :=
  spec_complexCohomology_linearEquiv_deRham_aux X n

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    Nonempty (H^1(X; ℂ) ≃ₗ[ℂ] H_dR^((1 : ℕ) : ℤ)(X)) :=
  spec_complexCohomology_linearEquiv_deRham X 1

/-- Universal coefficients over fields: if rational singular cohomology of `Y` in degree `n` is
finite-dimensional, then complex singular cohomology in degree `n` is finite-dimensional of the
same dimension.

Source: Hatcher, *Algebraic Topology*, Theorem 3.2 and §3.A (over a field, `H^n(Y; F)` is dual to
`H_n(Y; F)`, and `H_n(Y; ℂ) = ℂ ⊗ H_n(Y; ℚ)`), through upstream's `cohomologyEquivDualHomology`
and `qToCHomology_isBaseChange`. -/
theorem spec_finrank_complexSingular_of_finite (Y : TopCat.{0}) (n : ℕ)
    (hY : Module.Finite ℚ (AlgebraicTopology.Singular.Cohomology ℚ Y n)) :
    Module.Finite ℂ (AlgebraicTopology.Singular.Cohomology ℂ Y n) ∧
      Module.finrank ℂ (AlgebraicTopology.Singular.Cohomology ℂ Y n) =
        Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology ℚ Y n) :=
  spec_finrank_complexSingular_of_finite_aux Y n hY

example (Y : TopCat.{0}) (hY : Module.Finite ℚ (AlgebraicTopology.Singular.Cohomology ℚ Y 1)) :
    Module.finrank ℂ (AlgebraicTopology.Singular.Cohomology ℂ Y 1) =
      Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology ℚ Y 1) :=
  (spec_finrank_complexSingular_of_finite Y 1 hY).2

/-- The complex singular Betti numbers of an abelian `X` of dimension `g`:
`H^k(X(ℂ); ℂ)` is finite-dimensional of dimension `C(2g, k)`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1,
through `cupComparison`, `finiteBetti_abelian` and `finrank_HQ_abelian`, with
`spec_finrank_complexSingular_of_finite`. -/
theorem spec_finrank_complexSingular_abelian (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (k : ℕ) :
    Module.Finite ℂ (AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) k) ∧
      Module.finrank ℂ
          (AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) k) =
        (2 * dim X.left).choose k :=
  spec_finrank_complexSingular_abelian_aux X k

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    Module.finrank ℂ (AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) 1) =
      (2 * dim X.left).choose 1 :=
  (spec_finrank_complexSingular_abelian X 1).2

/-- For abelian `X` of dimension `g`, `bettiDeRhamHQ X n` is bijective exactly when constant-sheaf
cohomology `H^n(X(ℂ); ℂ)` is finite-dimensional of dimension `C(2g, n)`. The de Rham side no longer
appears.

Source: `spec_bijective_bettiDeRhamHQ_iff_finrank`, `finrank_HQ_abelian` (Birkenhake–Lange,
Lemma 1.3.1) and `spec_complexCohomology_linearEquiv_deRham`. -/
theorem spec_bijective_bettiDeRhamHQ_iff_complexCohomology_abelian (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    Function.Bijective (bettiDeRhamHQ X n) ↔
      Module.Finite ℂ H^n(X; ℂ) ∧ Module.finrank ℂ H^n(X; ℂ) = (2 * dim X.left).choose n :=
  spec_bijective_bettiDeRhamHQ_iff_complexCohomology_abelian_aux X n

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    Function.Bijective (bettiDeRhamHQ X 1) ↔
      Module.Finite ℂ H^1(X; ℂ) ∧ Module.finrank ℂ H^1(X; ℂ) = (2 * dim X.left).choose 1 :=
  spec_bijective_bettiDeRhamHQ_iff_complexCohomology_abelian X 1

/-- For abelian `X` of dimension `g`, an upper bound suffices: `bettiDeRhamHQ X n` is bijective
exactly when `H_dR^n(X)` is finite-dimensional of dimension at most `C(2g, n)`. In degree one the
bound is `dim H_dR^1(X) ≤ 2g`.

Source: `spec_injective_bettiDeRhamHQ` and `finrank_HQ_abelian` (Birkenhake–Lange, Lemma 1.3.1);
an injective linear map from a space of dimension `C(2g, n)` into a space of dimension at most
`C(2g, n)` is bijective (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`). -/
theorem spec_bijective_bettiDeRhamHQ_iff_finrank_le_abelian (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    Function.Bijective (bettiDeRhamHQ X n) ↔
      Module.Finite ℂ H_dR^(n : ℤ)(X) ∧
        Module.finrank ℂ H_dR^(n : ℤ)(X) ≤ (2 * dim X.left).choose n :=
  spec_bijective_bettiDeRhamHQ_iff_finrank_le_abelian_aux X n

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    Function.Bijective (bettiDeRhamHQ X 1) ↔
      Module.Finite ℂ H_dR^((1 : ℕ) : ℤ)(X) ∧
        Module.finrank ℂ H_dR^((1 : ℕ) : ℤ)(X) ≤ (2 * dim X.left).choose 1 :=
  spec_bijective_bettiDeRhamHQ_iff_finrank_le_abelian X 1

/-- The implication from a `ℂ`-linear sheaf-to-singular comparison in degree `n` to bijectivity
of `bettiDeRhamHQ X n`, for abelian `X`. Upstream proves such a comparison only over `ℚ`
(`rationalCohomologyLinearEquivSingularCohomology`); the premise is its complex analogue in one
degree, passed as an argument and not assumed anywhere else.

Source: `spec_finrank_complexSingular_abelian` and
`spec_bijective_bettiDeRhamHQ_iff_complexCohomology_abelian`. -/
theorem spec_bijective_bettiDeRhamHQ_of_complexSingular (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ)
    (e : H^n(X; ℂ) ≃ₗ[ℂ]
      AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) n) :
    Function.Bijective (bettiDeRhamHQ X n) :=
  spec_bijective_bettiDeRhamHQ_of_complexSingular_aux X n e

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom]
    (e : H^1(X; ℂ) ≃ₗ[ℂ]
      AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) 1) :
    Function.Bijective (bettiDeRhamHQ X 1) :=
  spec_bijective_bettiDeRhamHQ_of_complexSingular X 1 e

/-- Falsification check: for abelian `X` of positive dimension, `H_dR^1(X)` is nonzero. The zero
space fails this, and so does `X = Spec ℂ` (dimension zero), which is why `0 < g` is assumed.

Source: `spec_injective_bettiDeRhamHQ` and `finrank_HQ_abelian` (Birkenhake–Lange, Lemma 1.3.1:
`H^1(X(ℂ); ℚ)` has dimension `2g > 0`). -/
theorem spec_nontrivial_deRham_one_abelian (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hg : 0 < dim X.left) :
    Nontrivial H_dR^((1 : ℕ) : ℤ)(X) :=
  spec_nontrivial_deRham_one_abelian_aux X hg

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hg : 0 < dim X.left) :
    ∃ α : H_dR^((1 : ℕ) : ℤ)(X), α ≠ 0 := by
  have := spec_nontrivial_deRham_one_abelian X hg
  exact exists_ne 0

end HodgeLean.Adapters
