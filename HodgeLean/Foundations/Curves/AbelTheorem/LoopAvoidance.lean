import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology Set
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [ConnectedSpace C]

theorem good_path_with_finite_plateaus (h : Module.finrank ℂ E = 1) (p : C)
    (s : Finset C) :
    ∃ γ : ℝ → C, b3A_IsGoodPath (E := E) γ p p ∧
      ∀ x ∈ s, ∃ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ u in 𝓝 t, γ u = x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => p, b3A_isGoodPath_const p, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨γ, hγ, hmarks⟩ := ih
    obtain ⟨δ, hδ⟩ := b3A_joined (E := E) p x
    let η : ℝ → C := fun t => if t ≤ 1 / 2 then γ (2 * t) else δ (2 * t - 1)
    have hη : b3A_IsGoodPath (E := E) η p x := hγ.trans hδ
    let ζ : ℝ → C := fun t => if t ≤ 1 / 2 then η (2 * t) else δ (1 - (2 * t - 1))
    refine ⟨ζ, hη.trans hδ.symm, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · refine ⟨1 / 2, by constructor <;> norm_num, ?_⟩
      have hleft : ∀ᶠ u in 𝓝 (1 / 2 : ℝ), η (2 * u) = y := by
        have ht : Tendsto (fun u : ℝ => 2 * u) (𝓝 (1 / 2)) (𝓝 1) := by
          have hc : Continuous (fun u : ℝ => 2 * u) := continuous_const.mul continuous_id
          simpa using hc.tendsto (1 / 2 : ℝ)
        exact ht hη.2.2
      have hright : ∀ᶠ u in 𝓝 (1 / 2 : ℝ), δ (1 - (2 * u - 1)) = y := by
        have ht : Tendsto (fun u : ℝ => 1 - (2 * u - 1)) (𝓝 (1 / 2)) (𝓝 1) := by
          have hc : Continuous (fun u : ℝ => 1 - (2 * u - 1)) := by fun_prop
          convert hc.tendsto (1 / 2 : ℝ) using 1 <;> norm_num
        exact ht hδ.2.2
      filter_upwards [hleft, hright] with u hl hr
      dsimp only [ζ]
      split_ifs <;> assumption
    · obtain ⟨t, ht, hplateau⟩ := hmarks y hy
      refine ⟨t / 4, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      have hv : Tendsto (fun u : ℝ => 4 * u) (𝓝 (t / 4)) (𝓝 t) := by
        have hc : Continuous (fun u : ℝ => 4 * u) := continuous_const.mul continuous_id
        convert hc.tendsto (t / 4) using 1 <;> ring
      filter_upwards [hv hplateau, Iio_mem_nhds (show t / 4 < (1 / 4 : ℝ) by linarith [ht.2])]
        with u hu hub
      change γ (4 * u) = y at hu
      change u < 1 / 4 at hub
      dsimp only [ζ, η]
      rw [if_pos (by linarith : u ≤ 1 / 2), if_pos (by linarith : 2 * u ≤ 1 / 2)]
      convert hu using 1 <;> congr 1 <;> ring

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem loop_periods_avoiding_finite (h : Module.finrank ℂ E = 1) (p : C)
    (s : Finset C) (δ : b3_SmoothLoop E C) :
    ∃ δ' : b3_SmoothLoop E C,
      (∀ t, δ'.val t ∉ s) ∧ b3_period E C δ' = b3_period E C δ := by
  classical
  obtain ⟨γ, hγ, hmarks⟩ := good_path_with_finite_plateaus h p s
  let Γ := b3A_toLoop hγ
  obtain ⟨δ', htr, hp⟩ := b3Rest_exists_transverse h Γ δ
  refine ⟨δ', fun t ht => ?_, hp⟩
  obtain ⟨u, hu, he⟩ := hmarks (δ'.val t) ht
  have hΓ : Γ.val =ᶠ[𝓝 u] fun _ => δ'.val t := by
    filter_upwards [he, Ioo_mem_nhds hu.1 hu.2] with v hv hvI
    change γ (Int.fract v) = _
    rw [Int.fract_eq_self.mpr ⟨hvI.1.le, hvI.2⟩]
    exact hv
  have hΓu : Γ.val u = δ'.val t := hΓ.eq_of_nhds
  have hz : b3_velocity E C Γ.val u = 0 := by
    unfold b3_velocity
    rw [hΓ.mfderiv_eq, mfderiv_const]
    rfl
  have hn := htr u t hΓu
  apply hn
  rw [hz]
  unfold b3_orient
  apply Finset.sum_eq_zero
  intro i hi
  have hzi : (Module.finBasis ℂ E).equivFun (0 : E) i = 0 :=
    congrFun (map_zero (Module.finBasis ℂ E).equivFun) i
  rw [hzi]
  norm_num

end HodgeLean.Foundations.Curves.AbelTheorem
