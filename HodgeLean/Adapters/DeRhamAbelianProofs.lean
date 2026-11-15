import HodgeLean.Adapters.BettiDeRham
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CoefficientBaseChange

/-! # Proofs for the de Rham side for abelian `X`

One obligation per statement of `HodgeLean.Adapters.DeRhamAbelian`, all proved.

* The `ℂ`-linear Poincaré comparison: `complexToDeRhamAddEquiv`, the additive equivalence
  `(hypercohomologyAddEquivConstantCohomology ℂ X n).symm.trans
  (complexConstantCohomologyDeRhamAddEquiv X n)`, is `ℂ`-linear by the argument of
  `complexH0ToDeRham_smul` in every degree (`hypercohomologyAddEquivConstantCohomology_symm_smul`
  and `constantsToHolomorphicDeRhamComplexInt_scalar`).
* The complex singular count: `cohomologyEquivDualHomology` over `ℚ` makes rational singular
  homology finite-dimensional (`Module.finite_dual_iff`); `qToCHomology_isBaseChange` (ported as
  `Foundations.Port.AlgebraicTopology.Singular.CoefficientBaseChange`) identifies complex singular
  homology with its base change to `ℂ`, of the same finite dimension; dualizing again over `ℂ`.
* The abelian count on the singular side: the previous item through `cupComparison`, with
  `finiteBetti_abelian` and `finrank_HQ_abelian`.
* The reductions: `spec_bijective_bettiDeRhamHQ_iff_finrank_aux` with `finrank_HQ_abelian`,
  transported along the Poincaré comparison; for the upper bound,
  `LinearMap.finrank_le_finrank_of_injective` applied to `spec_injective_bettiDeRhamHQ_aux`; the
  complex sheaf-to-singular premise transports the singular count to the sheaf side.
* Nontriviality in degree one: `ℂ ⊗[ℚ] HQ X 1` has dimension `2g > 0`, so it has a nonzero
  element, whose image is nonzero by injectivity. -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

section Poincare

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- `H^n(X; ℂ) → H_dR^n(X)`, the comparison through the Poincaré lemma, in every degree. -/
def complexToDeRhamAddEquiv (n : ℕ) : H^n(X; ℂ) ≃+ H_dR^(n : ℤ)(X) :=
  (hypercohomologyAddEquivConstantCohomology ℂ X n).symm.trans
    (complexConstantCohomologyDeRhamAddEquiv X (n : ℤ))

lemma complexToDeRhamAddEquiv_smul (n : ℕ) (c : ℂ) (w : H^n(X; ℂ)) :
    complexToDeRhamAddEquiv X n (c • w) = c • complexToDeRhamAddEquiv X n w := by
  change hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) (n : ℤ)
      ((hypercohomologyAddEquivConstantCohomology ℂ X n).symm (c • w)) =
    hypercohomologyMap X (scalarHolomorphicDeRhamComplexInt X c) (n : ℤ)
      (hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) (n : ℤ)
        ((hypercohomologyAddEquivConstantCohomology ℂ X n).symm w))
  rw [hypercohomologyAddEquivConstantCohomology_symm_smul, ← hypercohomologyMap_comp_apply,
    ← hypercohomologyMap_comp_apply, constantsToHolomorphicDeRhamComplexInt_scalar,
    complexScalarComplexInt_eq_fieldScalarComplex]

/-- The `ℂ`-linear Poincaré comparison `H^n(X; ℂ) ≃ₗ[ℂ] H_dR^n(X)`. -/
def complexToDeRhamLinearEquiv (n : ℕ) : H^n(X; ℂ) ≃ₗ[ℂ] H_dR^(n : ℤ)(X) :=
  (complexToDeRhamAddEquiv X n).toLinearEquiv (complexToDeRhamAddEquiv_smul X n)

end Poincare

theorem spec_complexCohomology_linearEquiv_deRham_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    Nonempty (H^n(X; ℂ) ≃ₗ[ℂ] H_dR^(n : ℤ)(X)) :=
  ⟨complexToDeRhamLinearEquiv X n⟩

section BaseChange

open AlgebraicTopology.Singular

local instance (Y : TopCat) (n : ℕ) : Module ℚ ((CChains Y).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (Y : TopCat) (n : ℕ) : IsScalarTower ℚ ℂ ((CChains Y).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- Complex singular homology is rational singular homology base changed to `ℂ`. -/
def complexHomologyEquivBaseChange (Y : TopCat.{0}) (n : ℕ) :
    ℂ ⊗[ℚ] (QChains Y).homology n ≃ₗ[ℂ] (CChains Y).homology n :=
  (qToCHomology_isBaseChange Y n).equiv

end BaseChange

theorem spec_finrank_complexSingular_of_finite_aux (Y : TopCat.{0}) (n : ℕ)
    (hY : Module.Finite ℚ (AlgebraicTopology.Singular.Cohomology ℚ Y n)) :
    Module.Finite ℂ (AlgebraicTopology.Singular.Cohomology ℂ Y n) ∧
      Module.finrank ℂ (AlgebraicTopology.Singular.Cohomology ℂ Y n) =
        Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology ℚ Y n) := by
  open AlgebraicTopology.Singular in
  have hHQ : Module.Finite ℚ (Homology ℚ Y n) :=
    (Module.finite_dual_iff ℚ).mp (Module.Finite.equiv (cohomologyEquivDualHomology ℚ Y n))
  have hHQ' : Module.Finite ℚ ((QChains Y).homology n) := hHQ
  let eC : ℂ ⊗[ℚ] (QChains Y).homology n ≃ₗ[ℂ] Homology ℂ Y n :=
    complexHomologyEquivBaseChange Y n
  have hHC : Module.Finite ℂ (Homology ℂ Y n) := Module.Finite.equiv eC
  have hrC : Module.finrank ℂ (Homology ℂ Y n) = Module.finrank ℚ (Homology ℚ Y n) :=
    eC.finrank_eq.symm.trans Module.finrank_baseChange
  refine ⟨Module.Finite.equiv (cohomologyEquivDualHomology ℂ Y n).symm, ?_⟩
  rw [(cohomologyEquivDualHomology ℂ Y n).finrank_eq, (cohomologyEquivDualHomology ℚ Y n).finrank_eq,
    Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, hrC]

theorem spec_finrank_complexSingular_abelian_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (k : ℕ) :
    Module.Finite ℂ (AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) k) ∧
      Module.finrank ℂ
          (AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) k) =
        (2 * dim X.left).choose k := by
  have := (finiteBetti_abelian X).finite k
  have hfin : Module.Finite ℚ
      (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint X)) k) :=
    Module.Finite.equiv (cupComparison X k)
  obtain ⟨h1, h2⟩ := spec_finrank_complexSingular_of_finite_aux _ k hfin
  exact ⟨h1, by rw [h2, ← (cupComparison X k).finrank_eq, finrank_HQ_abelian]⟩

theorem spec_bijective_bettiDeRhamHQ_iff_complexCohomology_abelian_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    Function.Bijective (bettiDeRhamHQ X n) ↔
      Module.Finite ℂ H^n(X; ℂ) ∧ Module.finrank ℂ H^n(X; ℂ) = (2 * dim X.left).choose n := by
  let e := complexToDeRhamLinearEquiv X n
  rw [spec_bijective_bettiDeRhamHQ_iff_finrank_aux X (finiteBetti_abelian X) n,
    finrank_HQ_abelian X n, e.finrank_eq]
  exact ⟨fun ⟨h, hr⟩ => ⟨Module.Finite.equiv e.symm, hr⟩,
    fun ⟨h, hr⟩ => ⟨Module.Finite.equiv e, hr⟩⟩

theorem spec_bijective_bettiDeRhamHQ_iff_finrank_le_abelian_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    Function.Bijective (bettiDeRhamHQ X n) ↔
      Module.Finite ℂ H_dR^(n : ℤ)(X) ∧
        Module.finrank ℂ H_dR^(n : ℤ)(X) ≤ (2 * dim X.left).choose n := by
  have := (finiteBetti_abelian X).finite n
  rw [spec_bijective_bettiDeRhamHQ_iff_finrank_aux X (finiteBetti_abelian X) n,
    finrank_HQ_abelian X n]
  refine ⟨fun ⟨h, hr⟩ => ⟨h, hr.le⟩, fun ⟨h, hr⟩ => ⟨h, le_antisymm hr ?_⟩⟩
  have hdim : Module.finrank ℂ (ℂ ⊗[ℚ] HQ X n) = (2 * dim X.left).choose n :=
    Module.finrank_baseChange.trans (finrank_HQ_abelian X n)
  rw [← hdim]
  exact LinearMap.finrank_le_finrank_of_injective (spec_injective_bettiDeRhamHQ_aux X n)

theorem spec_bijective_bettiDeRhamHQ_of_complexSingular_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ)
    (e : H^n(X; ℂ) ≃ₗ[ℂ]
      AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) n) :
    Function.Bijective (bettiDeRhamHQ X n) := by
  obtain ⟨h1, h2⟩ := spec_finrank_complexSingular_abelian_aux X n
  refine (spec_bijective_bettiDeRhamHQ_iff_complexCohomology_abelian_aux X n).mpr
    ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, h2]

theorem spec_nontrivial_deRham_one_abelian_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hg : 0 < dim X.left) :
    Nontrivial H_dR^((1 : ℕ) : ℤ)(X) := by
  have := (finiteBetti_abelian X).finite 1
  have hpos : 0 < Module.finrank ℂ (ℂ ⊗[ℚ] HQ X 1) := by
    rw [Module.finrank_baseChange, finrank_HQ_abelian X 1]
    simpa using hg
  have : Nontrivial (ℂ ⊗[ℚ] HQ X 1) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨x, hx⟩ := exists_ne (0 : ℂ ⊗[ℚ] HQ X 1)
  refine ⟨⟨bettiDeRhamHQ X 1 x, 0, fun h => hx ?_⟩⟩
  exact spec_injective_bettiDeRhamHQ_aux X 1 (h.trans (map_zero _).symm)

end HodgeLean.Adapters
