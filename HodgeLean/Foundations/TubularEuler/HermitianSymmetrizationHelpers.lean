import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

/-! # Hermitian symmetrization of real analytic metric coefficients

The operation preserves positivity and analytic dependence, and commutes with
complex linear coordinate changes. HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

abbrev realMetricForms (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

def hermitianSymmetrization (g : realMetricForms E) : realMetricForms E :=
  g + g.bilinearComp ((Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ)
    ((Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ)

theorem hermitianSymmetrization_apply (g : realMetricForms E) (u w : E) :
    hermitianSymmetrization g u w = g u w + g (Complex.I • u) (Complex.I • w) := rfl

theorem hermitianSymmetrization_symmetric (g : realMetricForms E)
    (hg : ∀ u w, g u w = g w u) (u w : E) :
    hermitianSymmetrization g u w = hermitianSymmetrization g w u := by
  rw [hermitianSymmetrization_apply, hermitianSymmetrization_apply, hg u w,
    hg (Complex.I • u) (Complex.I • w)]

theorem hermitianSymmetrization_positive (g : realMetricForms E)
    (hg : ∀ u, u ≠ 0 → 0 < g u u) (u : E) (hu : u ≠ 0) :
    0 < hermitianSymmetrization g u u := by
  rw [hermitianSymmetrization_apply]
  exact add_pos (hg u hu) (hg _ (smul_ne_zero Complex.I_ne_zero hu))

theorem hermitianSymmetrization_hermitian (g : realMetricForms E) (u w : E) :
    hermitianSymmetrization g (Complex.I • u) (Complex.I • w) =
      hermitianSymmetrization g u w := by
  simp only [hermitianSymmetrization_apply, smul_smul, Complex.I_mul_I,
    neg_smul, one_smul, map_neg, ContinuousLinearMap.neg_apply, neg_neg, add_comm]

theorem hermitianSymmetrization_transport (g : realMetricForms E) (h : realMetricForms F)
    (D : E →L[ℂ] F) (hD : ∀ u w, g u w = h (D u) (D w)) (u w : E) :
    hermitianSymmetrization g u w = hermitianSymmetrization h (D u) (D w) := by
  simp only [hermitianSymmetrization_apply, hD, map_smul]

theorem hermitianSymmetrization_contDiffOn
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {s : Set A} {g : A → realMetricForms E} {n : WithTop ℕ∞}
    (hg : ContDiffOn ℝ n g s) :
    ContDiffOn ℝ n (fun a => hermitianSymmetrization (g a)) s := by
  let J : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  let flip := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have h₁ := hg.clm_comp (contDiffOn_const (c := J))
  have h₂ := flip.contDiff.comp_contDiffOn h₁
  have h₃ := h₂.clm_comp (contDiffOn_const (c := J))
  exact hg.add (flip.contDiff.comp_contDiffOn h₃)

#print axioms hermitianSymmetrization
#print axioms hermitianSymmetrization_apply
#print axioms hermitianSymmetrization_symmetric
#print axioms hermitianSymmetrization_positive
#print axioms hermitianSymmetrization_transport
#print axioms hermitianSymmetrization_contDiffOn
#print axioms hermitianSymmetrization_hermitian

end HodgeLean.Foundations.TubularEuler
