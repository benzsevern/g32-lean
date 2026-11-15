import HodgeLean.Foundations.Curves.AbelTheorem.FiniteTransverseGlobalPath
import HodgeLean.Foundations.Curves.AbelTheorem.TransverseStepPath
import HodgeLean.Foundations.Curves.AbelTheorem.CompactStepPath

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [ConnectedSpace C]
attribute [local instance] b3Forms_isManifold_real

theorem exists_divisor_paths_transverse_to_finite_loops (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) {ι : Type} [Fintype ι] (γ : ι → b3_SmoothLoop E C)
    (hav : ∀ i t, (γ i).val t ∉ D.support) :
    ∃ (p : C) (paths : C → ℝ → C),
      (∀ x, b3A_IsGoodPath (E := E) (paths x) p x) ∧
      (∀ x, range (paths x) = (paths x) '' Icc (0 : ℝ) 1) ∧
      (∀ i s, (γ i).val s ≠ p) ∧
      ∀ i x, x ∈ D.support → ∀ s t, (γ i).val s = paths x t →
        b3_orient E (b3_velocity E C (γ i).val s) (b3_velocity E C (paths x) t) ≠ 0 := by
  classical
  obtain ⟨p, hp⟩ := (dense_complement_of_finite_smooth_paths h (fun i => (γ i).val)
    (fun i => (γ i).property.2)).nonempty
  have hpoff : ∀ i s, (γ i).val s ≠ p :=
    fun i s he => hp (mem_iUnion.mpr ⟨i, s, he⟩)
  have hex (x : C) : ∃ δ : ℝ → C, b3A_IsGoodPath (E := E) δ p x ∧
      (x ∈ D.support → ∀ i s t, (γ i).val s = δ t →
        b3_orient E (b3_velocity E C (γ i).val s) (b3_velocity E C δ t) ≠ 0) := by
    by_cases hx : x ∈ D.support
    · obtain ⟨δ, hδ, htr⟩ := exists_finitely_transverse_good_path h γ p x hpoff
        (fun i s he => hav i s (he ▸ hx))
      exact ⟨δ, hδ, fun _ => htr⟩
    · obtain ⟨δ, hδ⟩ := b3A_joined (E := E) p x
      exact ⟨δ, hδ, fun hs => False.elim (hx hs)⟩
  choose δ hδ htr using hex
  let paths : C → ℝ → C := fun x => δ x ∘ b3A_step
  have hgood (x : C) : b3A_IsGoodPath (E := E) (paths x) p x := by
    have he := b3A_isGoodPath_reparam (δ x) (hδ x).1
    rwa [(hδ x).apply_zero, (hδ x).apply_one] at he
  refine ⟨p, paths, hgood, fun x => step_path_range_eq_interval_image (δ x), hpoff, ?_⟩
  intro i x hx
  apply transverse_step_path (γ i) (δ x) (hδ x).1 (htr x hx i)
  intro s
  rw [(hδ x).apply_zero, (hδ x).apply_one]
  exact ⟨hpoff i s, fun he => hav i s (he ▸ hx)⟩

end HodgeLean.Foundations.Curves.AbelTheorem
