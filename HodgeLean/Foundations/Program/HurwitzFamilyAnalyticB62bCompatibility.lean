import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bValueTransitions

noncomputable section
open Filter Manifold
open scoped Topology ContDiff Manifold

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6a_contDiffAt_value_root (r : ((Fin 10 → ℂ) × ℂ) → ℂ)
    (x : (Fin 10 → ℂ) × ℂ) (ht : x.1 ∈ b6_chart)
    (j k : Fin 13) (m e : ℕ) (hm : 0 < m) (he : 0 < e)
    (hr : ∀ᶠ z in 𝓝 x, ContinuousAt r z)
    (hv : ∀ᶠ z in 𝓝 x, b6a_value z.1 j (z.2 ^ m) = b6a_value z.1 k (r z ^ e)) :
    ContDiffAt ℂ ω r x := by
  by_cases hz : r x = 0
  · by_cases hx : x.2 = 0
    · have hvx := hv.self_of_nhds
      rw [hx, hz, zero_pow hm.ne', zero_pow he.ne', b6a_value_zero, b6a_value_zero] at hvx
      have hjk : j = k := ht hvx
      subst k
      have hp : ∀ᶠ z in 𝓝 x, r z ^ e = z.2 ^ m :=
        hv.mono fun z hz ↦ (b6a_value_injective z.1 j hz).symm
      have hxeq : x = (x.1, (0 : ℂ)) := Prod.ext rfl hx
      rw [hxeq] at hr hp ⊢
      exact b6a_contDiffAt_root_product_monomial r x.1 e m he hr hp
    · have heq := b6a_value_root_exponent r x j k m e hm he hr hz hx hv
      subst e
      have hc := b6a_valueCoord_comp_contDiffAt Prod.fst
        (fun z ↦ b6a_value z.1 j (z.2 ^ m)) x k (r x ^ 1)
        contDiffAt_fst (b6a_value_power_contMDiff j m).contMDiffAt hv.self_of_nhds
      apply hc.congr_of_eventuallyEq
      filter_upwards [hv] with z hz
      simp only [hz, b6a_valueCoord_value, pow_one]
  · exact b6a_root_contDiffAt_of_value Prod.fst
      (fun z ↦ b6a_value z.1 j (z.2 ^ m)) r x k e he contDiffAt_fst
      (b6a_value_power_contMDiff j m).contMDiffAt hr.self_of_nhds hz hv

theorem b6a_transitions_contDiffOn (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (f : C → OnePoint ℂ) (n : C → ℕ)
    (hn : ∀ x, 0 < n x)
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2)) :
    ∀ q q', ContDiffOn ℂ ω ((A q).symm.trans (A q'))
      ((A q).symm.trans (A q')).source := by
  intro q q' z hz
  apply ContDiffAt.contDiffWithinAt
  by_cases htarget : f q'.2 ∈ Set.range (b6_branch b)
  · obtain ⟨k, hk⟩ := htarget
    let T := (A q).symm.trans (A q')
    obtain ⟨j, m, hm, hmodel⟩ : ∃ (j : Fin 13) (m : ℕ), 0 < m ∧
        ∀ y ∈ (A q).source, b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ m) := by
      by_cases hsource : f q.2 ∈ Set.range (b6_branch b)
      · obtain ⟨j, hj⟩ := hsource
        exact ⟨j, n q.2, hn q.2, hmark q j hj.symm⟩
      · refine ⟨10, 1, by decide, ?_⟩
        intro y hy
        simpa [b6a_value] using hfree q hsource y hy
    have ht : z.1 ∈ b6_chart := by
      have hp := hparam q ((A q).symm z) ((A q).map_target hz.1)
      rw [(A q).right_inv hz.1] at hp
      rw [hp]
      exact (b6t_polydisc_neighbourhood b hb).2.2.2 ((A q).symm z).1.property
    have hr : ∀ᶠ w in 𝓝 z, ContinuousAt (fun v ↦ (T v).2) w := by
      filter_upwards [T.open_source.mem_nhds hz] with w hw
      exact (T.continuousAt hw).snd
    have hv : ∀ᶠ w in 𝓝 z,
        b6a_value w.1 j (w.2 ^ m) = b6a_value w.1 k ((T w).2 ^ n q'.2) := by
      filter_upwards [T.open_source.mem_nhds hz] with w hw
      have hys := (A q).map_target hw.1
      have hp := hparam q ((A q).symm w) hys
      rw [(A q).right_inv hw.1] at hp
      have h₁ := hmodel ((A q).symm w) hys
      have h₂ := hmark q' k hk.symm ((A q).symm w) hw.2
      rw [(A q).right_inv hw.1, ← hp] at h₁
      rw [← hp] at h₂
      exact h₁.symm.trans h₂
    have hroot := b6a_contDiffAt_value_root (fun w ↦ (T w).2) z ht j k m (n q'.2)
      hm (hn q'.2) hr hv
    apply (contDiffAt_fst.prodMk hroot).congr_of_eventuallyEq
    filter_upwards [T.open_source.mem_nhds hz] with w hw
    exact Prod.ext (b6a_transition_fst b C A hparam q q' w hw) rfl
  · exact b6a_transition_contDiffAt_of_free b C f n A hparam hfree hmark q q' htarget z hz

end HodgeLean.Foundations.Program
