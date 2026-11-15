import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.PeriodFormDuality

/-! # Normalized basis coordinates on the original period quotient

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Basis coordinates on the original period quotient, retaining the chosen forms themselves.
Source: Forster, §21; periodQuotientDualEquiv and Module.Basis.constr.
HC no distance; AV milestone no distance. -/
def quotientBasisEquiv (h : Module.finrank ℂ E = 1) {ι : Type}
    (b : Module.Basis ι ℂ (b3_HolForm E C)) :
    ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) ≃ₗ[ℂ] (ι → ℂ) :=
  (periodQuotientDualEquiv h).trans (b.constr ℂ).symm

/-- The basis-coordinate equivalence is exactly the existing normalized period evaluation.
Source: Forster, §21; b3Rest_evalQ_mk.
HC no distance; AV milestone no distance. -/
theorem quotientBasisEquiv_apply (h : Module.finrank ℂ E = 1) {ι : Type}
    (b : Module.Basis ι ℂ (b3_HolForm E C))
    (w : (ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) :
    quotientBasisEquiv h b w = b3Rest_evalQ b w := by
  ext j
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (b3_periodF E C) w
  exact periodQuotientDualEquiv_mk h v (b j)

/-- The inverse basis coordinates retain every specified form value without projection.
Source: Forster, §21; quotientBasisEquiv_apply.
HC no distance; AV milestone no distance. -/
theorem quotientBasisEquiv_symm_eval (h : Module.finrank ℂ E = 1) {ι : Type}
    (b : Module.Basis ι ℂ (b3_HolForm E C)) (v : ι → ℂ) :
    b3Rest_evalQ b ((quotientBasisEquiv h b).symm v) = v :=
  (quotientBasisEquiv_apply h b _).symm.trans ((quotientBasisEquiv h b).apply_symm_apply v)

/-- A basis form evaluated on inverse period coordinates returns its specified coordinate.
Source: Forster, §21; quotientBasisEquiv_symm_eval.
HC no distance; AV milestone no distance. -/
theorem periodLinear_basis_coord [Module.Finite ℤ (b3_periodLattice E C)]
    (h : Module.finrank ℂ E = 1) {ι : Type}
    (b : Module.Basis ι ℂ (b3_HolForm E C)) (v : ι → ℂ) (j : ι) :
    periodLinear (b j) (b2_coord (b3Rest2_QJ E C) ((quotientBasisEquiv h b).symm v)) = v j := by
  change (b3_periodF E C).liftQ (b3_cplxPeriod E C) le_rfl
    ((b2_coord (b3Rest2_QJ E C)).symm
      (b2_coord (b3Rest2_QJ E C) ((quotientBasisEquiv h b).symm v))) (b j) = v j
  rw [LinearEquiv.symm_apply_apply]
  have he (w : (ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) :
      (b3_periodF E C).liftQ (b3_cplxPeriod E C) le_rfl w (b j) = b3Rest_evalQ b w j := by
    induction w using Submodule.Quotient.induction_on with
    | H w => rfl
  exact (he _).trans (congrFun (quotientBasisEquiv_symm_eval h b v) j)

#print axioms quotientBasisEquiv
#print axioms quotientBasisEquiv_apply
#print axioms quotientBasisEquiv_symm_eval
#print axioms periodLinear_basis_coord

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
