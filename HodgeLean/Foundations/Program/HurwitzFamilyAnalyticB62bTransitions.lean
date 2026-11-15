import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bRoot
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bHolomorphic
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bStationary

noncomputable section

open Filter
open scoped Topology ContDiff Manifold
open Manifold

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6a_contDiffAt_of_pow {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (r : E → ℂ) (x : E) (e : ℕ) (he : 0 < e)
    (hr : ContinuousAt r x) (hne : r x ≠ 0)
    (hh : ContDiffAt ℂ ω (fun y ↦ r y ^ e) x) : ContDiffAt ℂ ω r x := by
  let p : ℂ → ℂ := fun z ↦ z ^ e
  have hp : ContDiffAt ℂ ω p (r x) := by
    dsimp [p]
    fun_prop
  have hc : (e : ℂ) * r x ^ (e - 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr he.ne') (pow_ne_zero _ hne)
  let d : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ
    (Units.mk0 ((e : ℂ) * r x ^ (e - 1)) hc)
  have hpd : HasFDerivAt p (d : ℂ →L[ℂ] ℂ) (r x) := by
    exact (hasDerivAt_pow e (r x)).hasFDerivAt_equiv hc
  let l : ℂ → ℂ := hp.localInverse hpd (by simp)
  have hl : ContDiffAt ℂ ω l (r x ^ e) := hp.to_localInverse hpd (by simp)
  apply (hl.comp x hh).congr_of_eventuallyEq
  have hleft : ∀ᶠ z in 𝓝 (r x), l (p z) = z :=
    hp.hasStrictFDerivAt' hpd (by simp) |>.eventually_left_inverse
  filter_upwards [hr hleft] with y hy
  exact hy.symm

def b6a_valueCoord (j : Fin 13) (q : (Fin 10 → ℂ) × OnePoint ℂ) : ℂ :=
  if h : j.val < 10 then b4cov_chart0 q.2 - q.1 ⟨j.val, h⟩
  else if j.val = 10 then b4cov_chart0 q.2
  else if j.val = 11 then b4cov_chart0 q.2 - 1
  else b4cov_chartInf q.2

theorem b6a_valueCoord_value (t : Fin 10 → ℂ) (j : Fin 13) (w : ℂ) :
    b6a_valueCoord j (t, b6a_value t j w) = w := by
  unfold b6a_valueCoord b6a_value
  split_ifs <;> simp [b4cov_chart0_coe, b4cov_chartInf_apply]
  rw [b4cov_sphInv_involutive, b4cov_chart0_coe]

theorem b6a_valueCoord_comp_contDiffAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : E → (Fin 10 → ℂ)) (g : E → OnePoint ℂ) (x : E) (j : Fin 13) (w : ℂ)
    (hs : ContDiffAt ℂ ω s x)
    (hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω g x)
    (hw : g x = b6a_value (s x) j w) :
    ContDiffAt ℂ ω (fun y ↦ b6a_valueCoord j (s y, g y)) x := by
  have hfinite {z : ℂ} (hz : g x = (z : OnePoint ℂ)) :
      ContDiffAt ℂ ω (fun y ↦ b4cov_chart0 (g y)) x := by
    have hmem : g x ∈ b4cov_chart0.source := by
      rw [hz, b4cov_chart0_source]
      exact ⟨z, rfl⟩
    have hc : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω b4cov_chart0 (g x) :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (by
        change b4cov_chart0 ∈ ({b4cov_chart0, b4cov_chartInf} : Set _)
        simp)) hmem
    exact (hc.comp x hg).contDiffAt
  unfold b6a_valueCoord
  split_ifs with hj hj0 hj1
  · exact (hfinite (by simpa [b6a_value, hj] using hw)).sub
      ((contDiff_apply ℂ ℂ _).contDiffAt.comp x hs)
  · exact hfinite (by simpa [b6a_value, hj, hj0] using hw)
  · exact (hfinite (by simpa [b6a_value, hj, hj0, hj1] using hw)).sub contDiffAt_const
  · have hval : g x = b4cov_chartInf.symm w := by
      simpa [b6a_value, hj, hj0, hj1, b4cov_chartInf_symm] using hw
    have hmem : g x ∈ b4cov_chartInf.source := by
      rw [hval]
      exact b4cov_chartInf_symm_mem w
    have hc : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω b4cov_chartInf (g x) :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (by
        change b4cov_chartInf ∈ ({b4cov_chart0, b4cov_chartInf} : Set _)
        simp)) hmem
    exact (hc.comp x hg).contDiffAt

theorem b6a_root_contDiffAt_of_value {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : E → (Fin 10 → ℂ)) (g : E → OnePoint ℂ) (r : E → ℂ)
    (x : E) (j : Fin 13) (e : ℕ) (he : 0 < e)
    (hs : ContDiffAt ℂ ω s x) (hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω g x)
    (hr : ContinuousAt r x) (hne : r x ≠ 0)
    (hvalue : ∀ᶠ y in 𝓝 x, g y = b6a_value (s y) j (r y ^ e)) :
    ContDiffAt ℂ ω r x := by
  apply b6a_contDiffAt_of_pow r x e he hr hne
  have hcoord := b6a_valueCoord_comp_contDiffAt s g x j (r x ^ e) hs hg
    hvalue.self_of_nhds
  apply hcoord.congr_of_eventuallyEq
  filter_upwards [hvalue] with y hy
  simp only [hy, b6a_valueCoord_value]

theorem b6a_map_in_chart_contMDiffAt (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (f : C → OnePoint ℂ) (n : C → ℕ)
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2))
    (q : b6t_polydisc b × C) (z : (Fin 10 → ℂ) × ℂ) (hz : z ∈ (A q).target) :
    ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
      (fun w ↦ b6a_map b f ((A q).symm w)) z := by
  by_cases hq : f q.2 ∈ Set.range (b6_branch b)
  · obtain ⟨j, hj⟩ := hq
    apply (b6a_value_power_contMDiff j (n q.2)).contMDiffAt.congr_of_eventuallyEq
    filter_upwards [(A q).open_target.mem_nhds hz] with w hw
    have hm := hmark q j hj.symm ((A q).symm w) ((A q).map_target hw)
    have hp := hparam q ((A q).symm w) ((A q).map_target hw)
    rw [(A q).right_inv hw] at hm hp
    simpa only [← hp] using hm
  · have hc : ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
        (fun w : (Fin 10 → ℂ) × ℂ ↦ (w.2 : OnePoint ℂ)) :=
      b4cov_coe_contMDiff.comp contDiff_snd.contMDiff
    apply hc.contMDiffAt.congr_of_eventuallyEq
    filter_upwards [(A q).open_target.mem_nhds hz] with w hw
    have hm := hfree q hq ((A q).symm w) ((A q).map_target hw)
    simpa only [(A q).right_inv hw] using hm

theorem b6a_transition_fst (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (q q' : b6t_polydisc b × C) (z : (Fin 10 → ℂ) × ℂ)
    (hz : z ∈ ((A q).symm.trans (A q')).source) :
    (((A q).symm.trans (A q')) z).1 = z.1 := by
  calc
    (((A q).symm.trans (A q')) z).1 = ((A q).symm z).1.val :=
      hparam q' ((A q).symm z) hz.2
    _ = (A q ((A q).symm z)).1 :=
      (hparam q ((A q).symm z) ((A q).map_target hz.1)).symm
    _ = z.1 := congrArg Prod.fst ((A q).right_inv hz.1)

theorem b6a_transition_contDiffAt_of_mark_ne_zero (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] (f : C → OnePoint ℂ) (n : C → ℕ) (hn : ∀ x, 0 < n x)
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2))
    (q q' : b6t_polydisc b × C) (j : Fin 13) (hj : f q'.2 = b6_branch b j)
    (z : (Fin 10 → ℂ) × ℂ) (hz : z ∈ ((A q).symm.trans (A q')).source)
    (hne : (((A q).symm.trans (A q')) z).2 ≠ 0) :
    ContDiffAt ℂ ω ((A q).symm.trans (A q')) z := by
  let T := (A q).symm.trans (A q')
  let g := fun w ↦ b6a_map b f ((A q).symm w)
  have hg : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω g z :=
    b6a_map_in_chart_contMDiffAt b C f n A hparam hfree hmark q z hz.1
  have hv : ∀ᶠ w in 𝓝 z, g w = b6a_value w.1 j ((T w).2 ^ n q'.2) := by
    filter_upwards [T.open_source.mem_nhds hz] with w hw
    have hm := hmark q' j hj ((A q).symm w) hw.2
    have hp := hparam q ((A q).symm w) ((A q).map_target hw.1)
    rw [(A q).right_inv hw.1] at hp
    simpa only [← hp, T, OpenPartialHomeomorph.trans_apply] using hm
  have hr := b6a_root_contDiffAt_of_value Prod.fst g (fun w ↦ (T w).2) z j (n q'.2)
    (hn q'.2) contDiffAt_fst hg (T.continuousAt hz).snd hne hv
  apply (contDiffAt_fst.prodMk hr).congr_of_eventuallyEq
  filter_upwards [T.open_source.mem_nhds hz] with w hw
  exact Prod.ext (b6a_transition_fst b C A hparam q q' w hw) rfl

theorem b6a_transition_contDiffAt_of_free (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] (f : C → OnePoint ℂ) (n : C → ℕ)
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2))
    (q q' : b6t_polydisc b × C) (hq' : f q'.2 ∉ Set.range (b6_branch b))
    (z : (Fin 10 → ℂ) × ℂ) (hz : z ∈ ((A q).symm.trans (A q')).source) :
    ContDiffAt ℂ ω ((A q).symm.trans (A q')) z := by
  let T := (A q).symm.trans (A q')
  let g := fun w ↦ b6a_map b f ((A q).symm w)
  have hg : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω g z :=
    b6a_map_in_chart_contMDiffAt b C f n A hparam hfree hmark q z hz.1
  have hv : ∀ᶠ w in 𝓝 z, g w = b6a_value w.1 10 (T w).2 := by
    filter_upwards [T.open_source.mem_nhds hz] with w hw
    exact hfree q' hq' ((A q).symm w) hw.2
  have hc := b6a_valueCoord_comp_contDiffAt Prod.fst g z 10 (T z).2
    contDiffAt_fst hg hv.self_of_nhds
  have hr : ContDiffAt ℂ ω (fun w ↦ (T w).2) z := by
    apply hc.congr_of_eventuallyEq
    filter_upwards [hv] with w hw
    simp only [hw, b6a_valueCoord_value]
  apply (contDiffAt_fst.prodMk hr).congr_of_eventuallyEq
  filter_upwards [T.open_source.mem_nhds hz] with w hw
  exact Prod.ext (b6a_transition_fst b C A hparam q q' w hw) rfl

end HodgeLean.Foundations.Program
