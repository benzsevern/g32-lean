import HodgeLean.Foundations.TubularEuler.HermitianSymmetrizationHelpers
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # Hermitian forms induced by real linear immersions

The original immersion differential pulls back the real Euclidean form before Hermitian symmetrization.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.TubularEuler

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def immersionHermitianForm (A : E →L[ℝ] H) : realMetricForms E :=
  hermitianSymmetrization ((innerSL ℝ (E := H)).bilinearComp A A)

theorem immersionHermitianForm_apply (A : E →L[ℝ] H) (u w : E) :
    immersionHermitianForm A u w =
      inner ℝ (A u) (A w) + inner ℝ (A (Complex.I • u)) (A (Complex.I • w)) := by
  simp only [immersionHermitianForm, hermitianSymmetrization_apply,
    ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]

theorem immersionHermitianForm_positive (A : E →L[ℝ] H)
    (hA : Function.Injective A) (u : E) (hu : u ≠ 0) :
    0 < immersionHermitianForm A u u := by
  apply hermitianSymmetrization_positive _ ?_ u hu
  intro v hv
  change 0 < inner ℝ (A v) (A v)
  exact real_inner_self_pos.mpr (fun h =>
    hv (hA (h.trans (map_zero A).symm)))

theorem immersionHermitianForm_symmetric (A : E →L[ℝ] H) (u w : E) :
    immersionHermitianForm A u w = immersionHermitianForm A w u := by
  apply hermitianSymmetrization_symmetric
  intro v z
  exact real_inner_comm (A z) (A v)

theorem immersionHermitianForm_hermitian (A : E →L[ℝ] H) (u w : E) :
    immersionHermitianForm A (Complex.I • u) (Complex.I • w) =
      immersionHermitianForm A u w :=
  hermitianSymmetrization_hermitian _ u w

theorem immersionHermitianForm_transport
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : E →L[ℝ] H) (B : F →L[ℝ] H) (D : E →L[ℂ] F)
    (hD : A = B.comp (D.restrictScalars ℝ)) (u w : E) :
    immersionHermitianForm A u w = immersionHermitianForm B (D u) (D w) := by
  apply hermitianSymmetrization_transport _ _ D
  intro v z
  simp only [ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]
  rw [hD]
  rfl

theorem immersionHermitianForm_contDiffOn
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {s : Set P} {A : P → E →L[ℝ] H} {n : WithTop ℕ∞}
    (hA : ContDiffOn ℝ n A s) :
    ContDiffOn ℝ n (fun p => immersionHermitianForm (A p)) s := by
  apply hermitianSymmetrization_contDiffOn
  let flip := (ContinuousLinearMap.flipₗᵢ ℝ E H ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have h₁ := (contDiffOn_const (c := innerSL ℝ (E := H))).clm_comp hA
  have h₂ := flip.contDiff.comp_contDiffOn h₁
  have h₃ := h₂.clm_comp hA
  exact (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn h₃

theorem immersionHermitianForm_fderiv_contDiffOn
    {s : Set E} {f : E → H} (hs : IsOpen s) (hf : ContDiffOn ℝ ⊤ f s) :
    ContDiffOn ℝ ⊤ (fun p => immersionHermitianForm (fderiv ℝ f p)) s := by
  exact immersionHermitianForm_contDiffOn (hf.fderiv_of_isOpen hs (by simp))

theorem immersionHermitianForm_transport_real
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : E →L[ℝ] H) (B : F →L[ℝ] H) (D : E →L[ℝ] F)
    (hD : A = B.comp D) (hJ : ∀ u, D (Complex.I • u) = Complex.I • D u)
    (u w : E) :
    immersionHermitianForm A u w = immersionHermitianForm B (D u) (D w) := by
  simp only [immersionHermitianForm_apply, hD, ContinuousLinearMap.comp_apply, hJ]

#print axioms immersionHermitianForm_transport_real

#print axioms immersionHermitianForm_fderiv_contDiffOn

#print axioms immersionHermitianForm_contDiffOn

#print axioms immersionHermitianForm_transport

#print axioms immersionHermitianForm_hermitian

#print axioms immersionHermitianForm_symmetric

#print axioms immersionHermitianForm_positive

#print axioms immersionHermitianForm
#print axioms immersionHermitianForm_apply

end HodgeLean.Foundations.TubularEuler
