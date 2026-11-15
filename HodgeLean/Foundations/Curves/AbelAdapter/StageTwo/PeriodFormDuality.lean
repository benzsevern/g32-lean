import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.ThetaForms

/-! # Dual coordinates of the original period quotient

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The linear-function submodule is the ordinary algebraic dual of the space of forms.
Source: Bourbaki, Algèbre, chapter II §2; b3A_toDual.
HC no distance; AV milestone no distance. -/
def periodFunctionalEquiv : b3_linearDual E C ≃ₗ[ℂ] Module.Dual ℂ (b3_HolForm E C) where
  toFun := b3A_toDual
  invFun f := ⟨f, by intro a θ η; rw [map_add, map_smul]; rfl⟩
  left_inv f := rfl
  right_inv f := by ext θ; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The unaltered period quotient is exactly the dual of the original curve forms.
Source: Forster, §21; b3A_range_cplxPeriod.
HC no distance; AV milestone no distance. -/
def periodQuotientDualEquiv [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) :
    ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) ≃ₗ[ℂ]
      Module.Dual ℂ (b3_HolForm E C) :=
  ((b3_cplxPeriod E C).quotKerEquivRange.trans
    (LinearEquiv.ofEq _ _ (b3A_range_cplxPeriod h))).trans periodFunctionalEquiv

/-- The dual quotient coordinates retain the original complexified period values.
Source: Forster, §21; LinearMap.quotKerEquivRange.
HC no distance; AV milestone no distance. -/
theorem periodQuotientDualEquiv_mk [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (v : ℂ ⊗[ℤ] b3_periodLattice E C)
    (θ : b3_HolForm E C) :
    periodQuotientDualEquiv h (Submodule.Quotient.mk v) θ = b3_cplxPeriod E C v θ := rfl

variable [FiniteDimensional ℂ E] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [Module.Finite ℤ (b3_periodLattice E C)]

/-- Curve forms identified with continuous covectors on the unaltered period cover.
Source: Forster, §21; Module.evalEquiv and b3A_range_cplxPeriod.
HC no distance; AV milestone no distance. -/
def periodFormEquiv (h : Module.finrank ℂ E = 1) :
    b3_HolForm E C ≃ₗ[ℂ] (b3Rest2_VJ E C →L[ℂ] ℂ) := by
  letI := b3_holForm_finiteDimensional (C := C) h
  exact (((Module.evalEquiv ℂ (b3_HolForm E C)).trans
    (periodQuotientDualEquiv h).dualMap).trans
      (b2_coord (b3Rest2_QJ E C)).symm.dualMap).trans LinearMap.toContinuousLinearMap

/-- The covector equivalence retains the literal original period normalization.
Source: Forster, §21; periodQuotientDualEquiv_mk.
HC no distance; AV milestone no distance. -/
theorem periodFormEquiv_apply (h : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) :
    periodFormEquiv h θ = periodLinear θ := by
  ext v
  change periodQuotientDualEquiv h ((b2_coord (b3Rest2_QJ E C)).symm v) θ =
    (b3_periodF E C).liftQ (b3_cplxPeriod E C) le_rfl
      ((b2_coord (b3Rest2_QJ E C)).symm v) θ
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective (b3_periodF E C)
    ((b2_coord (b3Rest2_QJ E C)).symm v)
  rw [← hw, periodQuotientDualEquiv_mk]
  rfl

#print axioms periodFunctionalEquiv
#print axioms periodQuotientDualEquiv
#print axioms periodQuotientDualEquiv_mk
#print axioms periodFormEquiv
#print axioms periodFormEquiv_apply

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
