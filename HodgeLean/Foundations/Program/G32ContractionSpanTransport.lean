import HodgeLean.Foundations.Program.G32ContractionPullbackC
import HodgeLean.Foundations.Program.G32ContractionScalar
import HodgeLean.Foundations.Program.G32ContractionTwoDefs
import HodgeLean.Foundations.Program.CycleFoundationsSpans
import HodgeLean.Foundations.Program.CycleFoundationsPullback

/-! # Bodies of the second stage of the G32 contraction

One auxiliary body per statement of `G32ContractionTwo.lean`. HC no distance; AV milestone no
distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option Elab.async false

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program


theorem g32c_corrC_span_aux (Y B : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (c p q : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (ξ : ℂ ⊗[ℚ] HQ (Y ⊗ B) (2 * c)) (hξ : ξ ∈ (algebraicCycleClassSpan (Y ⊗ B) c).baseChange ℂ)
    (x : ℂ ⊗[ℚ] HQ B (2 * p)) (hx : x ∈ (algebraicCycleClassSpan B p).baseChange ℂ) :
    g32c_corrC Y B d I c p q h ξ x ∈ (algebraicCycleClassSpan Y q).baseChange ℂ := by
  apply g32c_baseChange_bilinear_mem (g32c_corrC Y B d I c p q h)
    (algebraicCycleClassSpan (Y ⊗ B) c) (algebraicCycleClassSpan B p)
    (algebraicCycleClassSpan Y q) _ ξ hξ x hx
  intro a b v hv t ht
  simp only [g32c_corrC, TensorProduct.curry_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
    LinearMap.baseChange_tmul, TensorProduct.lift.tmul]
  have hv' : v ∈ cfd_cycleSpan (Y ⊗ B) c := by rwa [g32c_cycleSpan_eq]
  have ht' : t ∈ cfd_cycleSpan B p := by rwa [g32c_cycleSpan_eq]
  have hz := cfd_correspondence_span Y B d hB I c p q h v hv' t ht'
  rw [g32c_cycleSpan_eq] at hz
  exact Submodule.tmul_mem_baseChange_of_mem (a * b) hz

end HodgeLean.Foundations.Program
