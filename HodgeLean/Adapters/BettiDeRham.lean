import HodgeLean.Adapters.BettiDeRhamProofs

/-! # Betti–de Rham comparison for abelian `X`: frozen specification

Inputs stage 3. This file states facts about `bettiDeRhamHQ X n : ℂ ⊗[ℚ] HQ X n → H_dR^n(X)`, the
map whose bijectivity in every degree is the open input `BettiDeRhamIso X`.

Claimed: the map is injective in every degree for every smooth integral `X`; under `FiniteBetti X`,
bijectivity in degree `n` is equivalent to the de Rham side being finite-dimensional of the Betti
rank; for abelian `X`, `BettiDeRhamIso X` is equivalent to the de Rham dimension count
`dim H_dR^n(X) = C(2g, n)` (an implication from the dimension count, and conversely); bijectivity
in degree zero for projective `X`; the dimension `2g` of `H_dR^1(X)` for abelian `X`; and the
non-degeneracy check that the unit is sent to a nonzero class.

Not claimed: `BettiDeRhamIso X` itself, compatibility with cup product (upstream defines no
product on `H_dR^*`), any comparison with invariant differential forms, or any period pairing.
No statement assumes `BettiDeRhamIso` or `HodgeDecomposition`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- The Betti-to-de Rham map is injective in every degree, for every smooth integral `X`.

Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, Ch. II (sheaf cohomology is additive in the
coefficient sheaf), applied to a `ℚ`-linear splitting `ℂ ≅ ⊕ ℚ`, with upstream's holomorphic
Poincaré lemma `complexConstantCohomologyDeRhamEquiv` (`Filtration.lean:348`). -/
theorem spec_injective_bettiDeRhamHQ (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (n : ℕ) :
    Function.Injective (bettiDeRhamHQ X n) :=
  spec_injective_bettiDeRhamHQ_aux X n

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    Function.Injective (bettiDeRhamHQ X n) :=
  spec_injective_bettiDeRhamHQ X n

/-- With finite Betti numbers, bijectivity in degree `n` is equivalent to a dimension count: the
de Rham side is finite-dimensional over `ℂ` with dimension the rational Betti rank.

Source: `spec_injective_bettiDeRhamHQ` and `Module.finrank_baseChange` (an injective linear map
between spaces of the same finite dimension is bijective). -/
theorem spec_bijective_bettiDeRhamHQ_iff_finrank (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (hF : FiniteBetti X) (n : ℕ) :
    Function.Bijective (bettiDeRhamHQ X n) ↔
      Module.Finite ℂ H_dR^(n : ℤ)(X) ∧
        Module.finrank ℂ H_dR^(n : ℤ)(X) = Module.finrank ℚ (HQ X n) :=
  spec_bijective_bettiDeRhamHQ_iff_finrank_aux X hF n

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hF : FiniteBetti X) (n : ℕ) :
    Function.Bijective (bettiDeRhamHQ X n) ↔
      Module.Finite ℂ H_dR^(n : ℤ)(X) ∧
        Module.finrank ℂ H_dR^(n : ℤ)(X) = Module.finrank ℚ (HQ X n) :=
  spec_bijective_bettiDeRhamHQ_iff_finrank X hF n

/-- Assembly for abelian `X` of dimension `g`: `BettiDeRhamIso X` holds exactly when every
`H_dR^n(X)` is finite-dimensional of dimension `C(2g, n)`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1,
through `finrank_HQ_abelian` and `finiteBetti_abelian`, with
`spec_bijective_bettiDeRhamHQ_iff_finrank`. -/
theorem spec_bettiDeRhamIso_iff_finrank_abelian (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    BettiDeRhamIso X ↔ ∀ n : ℕ,
      Module.Finite ℂ H_dR^(n : ℤ)(X) ∧
        Module.finrank ℂ H_dR^(n : ℤ)(X) = (2 * dim X.left).choose n :=
  spec_bettiDeRhamIso_iff_finrank_abelian_aux X

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    BettiDeRhamIso X ↔ ∀ n : ℕ,
      Module.Finite ℂ H_dR^(n : ℤ)(X) ∧
        Module.finrank ℂ H_dR^(n : ℤ)(X) = (2 * dim X.left).choose n :=
  spec_bettiDeRhamIso_iff_finrank_abelian X

/-- Falsification check: the degree-zero map sends `1 ⊗ 1` to a nonzero class. The zero map
fails this.

Source: `spec_injective_bettiDeRhamHQ` and `unitClass_ne_zero'` (F-1683). -/
theorem spec_bettiDeRhamHQ_unit_ne_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] :
    bettiDeRhamHQ X 0 ((1 : ℂ) ⊗ₜ[ℚ] (unitClass X : HQ X 0)) ≠ 0 :=
  spec_bettiDeRhamHQ_unit_ne_zero_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    bettiDeRhamHQ X 0 ((1 : ℂ) ⊗ₜ[ℚ] (unitClass X : HQ X 0)) ≠ 0 :=
  spec_bettiDeRhamHQ_unit_ne_zero X

/-- Degree zero: for smooth projective integral `X`, the map is bijective in degree `0`.

Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, Ch. II (`H^0` of a constant sheaf is the group
of locally constant sections), with `pathConnectedSpace_complexPoint` (`X(ℂ)` is nonempty and
connected) and upstream's `complexConstantCohomologyDeRhamEquiv`. -/
theorem spec_bijective_bettiDeRhamHQ_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] :
    Function.Bijective (bettiDeRhamHQ X 0) :=
  spec_bijective_bettiDeRhamHQ_zero_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Function.Bijective (bettiDeRhamHQ X 0) :=
  spec_bijective_bettiDeRhamHQ_zero X

end HodgeLean.Adapters
