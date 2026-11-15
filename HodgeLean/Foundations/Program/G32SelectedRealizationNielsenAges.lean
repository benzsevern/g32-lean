import HodgeLean.Foundations.Program.G32SelectedRealizationConjugateAges
import HodgeLean.Foundations.Program.G32SelectedRealizationNielsenConjugacy

noncomputable section
open Manifold HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem g32y_nielsen_exponent_weights
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction g32p_G C] [FaithfulSMul g32p_G C]
    (hG : ∀ a : g32p_G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun y : C ↦ a • y))
    (H : Subgroup g32p_G) {m : ℕ} [NeZero m]
    (χ : H →* Multiplicative (ZMod m)) (w : ZMod m → ℝ) (hw : w 0 = 0)
    (r : C → H) (hr : ∀ y, b4_IsRotGen ℂ y (r y))
    (g : Fin 13 → g32p_G) (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (x : Fin 13 → C) (hx : ∀ i, b4_IsRotGen ℂ (x i) (g i)) :
    (∑ i, ((papersExps H χ (g i)).map w).sum) =
      ((papersExpsList H χ g32p_classList).map fun a : ℕ ↦ w (a : ZMod m)).sum := by
  classical
  obtain ⟨σ, hs⟩ := g32y_nielsen_group_conjugacy g hg
  have hi (i : Fin 13) : ((papersExps H χ (g i)).map w).sum =
      ((papersExps H χ (g32p_classDatum (σ i))).map w).sum := by
    obtain ⟨k, hk⟩ := hs i
    have hh := g32y_conjugate_exponent_weights (by simp : Module.finrank ℂ ℂ = 1)
      hG H (x i) (g i) k⁻¹ (hx i) χ w hw r hr
    have he : k⁻¹ * g i * (k⁻¹)⁻¹ = g32p_classDatum (σ i) := by
      rw [hk]
      simp [mul_assoc]
    rw [he] at hh
    exact hh.symm
  calc
    _ = ∑ i, ((papersExps H χ (g32p_classDatum (σ i))).map w).sum :=
      Finset.sum_congr rfl (fun i _ ↦ hi i)
    _ = ∑ i, ((papersExps H χ (g32p_classDatum i)).map w).sum :=
      Equiv.sum_comp σ (fun i ↦ ((papersExps H χ (g32p_classDatum i)).map w).sum)
    _ = _ := by
      rw [g32y_papers_exponent_list_weight]
      simp only [g32p_classList, List.map_ofFn, List.sum_ofFn]
      rfl

end HodgeLean.Foundations.Program
