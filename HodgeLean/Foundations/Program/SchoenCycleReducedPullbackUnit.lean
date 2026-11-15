import HodgeLean.Foundations.Program.SchoenCycleAnalyticAssociatedGerms
import HodgeLean.Foundations.Program.SchoenCycleAnalyticCoordinateGerms

/-! # Analytic unit comparison from reduced pullback products -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open scoped BigOperators
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Foundations.Program

/-- Equal zero germs with the same reduced coordinate-product pullbacks differ by an analytic unit.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B and III.A. -/
theorem s2e_analytic_unit_of_reduced_pullback_product
    {n m : ℕ} (φ : (Fin n → ℂ) → (Fin m → ℂ))
    (hφ : AnalyticAt ℂ φ 0) (he : φ 0 = 0)
    (F G : (Fin m → ℂ) → ℂ) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (S : Finset (Fin n)) (u v : (AnalyticGermAt n 0)ˣ)
    (hFu : s2e_analyticGermPullback φ hφ he
      (⟨Filter.Germ.ofFun F, F, hF, rfl⟩ : AnalyticGermAt m 0) =
        (∏ i ∈ S, s2e_analyticCoordinateGerm n i) * (u : AnalyticGermAt n 0))
    (hGv : s2e_analyticGermPullback φ hφ he
      (⟨Filter.Germ.ofFun G, G, hG, rfl⟩ : AnalyticGermAt m 0) =
        (∏ i ∈ S, s2e_analyticCoordinateGerm n i) * (v : AnalyticGermAt n 0))
    (hz : ∀ᶠ z in 𝓝 0, F z = 0 ↔ G z = 0) :
    ∃ η : (Fin m → ℂ) → ℂ, AnalyticAt ℂ η 0 ∧ η 0 ≠ 0 ∧
      F =ᶠ[𝓝 0] fun z => η z * G z := by
  have hP := s2e_analyticCoordinateGerm_product_squarefree n S
  have hFs : Squarefree (⟨Filter.Germ.ofFun F, F, hF, rfl⟩ : AnalyticGermAt m 0) := by
    apply s2e_analyticGermPullback_squarefree φ hφ he
    rw [hFu]
    exact (associated_mul_unit_right _ _ u.isUnit).squarefree_iff.mp hP
  have hGs : Squarefree (⟨Filter.Germ.ofFun G, G, hG, rfl⟩ : AnalyticGermAt m 0) := by
    apply s2e_analyticGermPullback_squarefree φ hφ he
    rw [hGv]
    exact (associated_mul_unit_right _ _ v.isUnit).squarefree_iff.mp hP
  exact HodgeLean.Foundations.AnalyticDivisorAlgebraic18.spec_reduced_zero_germs_associated
    m 0 F G hF hG hFs hGs hz

/-- A full local neighbourhood image descends analytic unit comparison from the same reduced coordinate-product pullbacks.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B and III.A. -/
theorem s2e_analytic_unit_of_open_reduced_pullback
    {n m : ℕ} (φ : (Fin n → ℂ) → (Fin m → ℂ))
    (hφ : AnalyticAt ℂ φ 0) (he : φ 0 = 0)
    (hmap : Filter.map φ (𝓝 0) = 𝓝 0)
    (F G : (Fin m → ℂ) → ℂ) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (S : Finset (Fin n)) (u v : (AnalyticGermAt n 0)ˣ)
    (hFu : s2e_analyticGermPullback φ hφ he
      (⟨Filter.Germ.ofFun F, F, hF, rfl⟩ : AnalyticGermAt m 0) =
        (∏ i ∈ S, s2e_analyticCoordinateGerm n i) * (u : AnalyticGermAt n 0))
    (hGv : s2e_analyticGermPullback φ hφ he
      (⟨Filter.Germ.ofFun G, G, hG, rfl⟩ : AnalyticGermAt m 0) =
        (∏ i ∈ S, s2e_analyticCoordinateGerm n i) * (v : AnalyticGermAt n 0)) :
    ∃ η : (Fin m → ℂ) → ℂ, AnalyticAt ℂ η 0 ∧ η 0 ≠ 0 ∧
      F =ᶠ[𝓝 0] fun z => η z * G z := by
  have ha : Associated
      (s2e_analyticGermPullback φ hφ he
        (⟨Filter.Germ.ofFun F, F, hF, rfl⟩ : AnalyticGermAt m 0))
      (s2e_analyticGermPullback φ hφ he
        (⟨Filter.Germ.ofFun G, G, hG, rfl⟩ : AnalyticGermAt m 0)) := by
    rw [hFu, hGv]
    exact (associated_mul_unit_right _ _ u.isUnit).symm.trans
      (associated_mul_unit_right _ _ v.isUnit)
  have ha' : Associated
      (⟨Filter.Germ.ofFun (F ∘ φ), F ∘ φ, hF.comp_of_eq hφ he, rfl⟩ : AnalyticGermAt n 0)
      (⟨Filter.Germ.ofFun (G ∘ φ), G ∘ φ, hG.comp_of_eq hφ he, rfl⟩ : AnalyticGermAt n 0) := ha
  obtain ⟨η, hη, hη0, hηeq⟩ := s2e_associated_analyticGerms_unit
    (F ∘ φ) (G ∘ φ) (hF.comp_of_eq hφ he) (hG.comp_of_eq hφ he) ha'
  have hzup : ∀ᶠ z in 𝓝 0, F (φ z) = 0 ↔ G (φ z) = 0 := by
    filter_upwards [hηeq, hη.continuousAt.eventually_ne hη0] with z hz hne
    change (F ∘ φ) z = 0 ↔ (G ∘ φ) z = 0
    rw [hz, mul_eq_zero]
    exact or_iff_right hne
  have hz : ∀ᶠ z in Filter.map φ (𝓝 0), F z = 0 ↔ G z = 0 := hzup
  rw [hmap] at hz
  exact s2e_analytic_unit_of_reduced_pullback_product φ hφ he F G hF hG S u v hFu hGv hz

end HodgeLean.Foundations.Program
