import HodgeLean.Foundations.Program.RelativeFrameFamilyCentre

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem rf7_fill_disc_coordinate {Y : Type} [TopologicalSpace Y]
    (q : Y → ℂ) (hq : Continuous q) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (p : Y → Metric.ball c ρ) (hproper : IsProperMap p)
    (hproj : ∀ y, (p y).val = q y) (x : Y) (hx : q x = c)
    (hsingle : ∀ y, q y = c → y = x) (k : ℕ) (hk : 0 < k)
    [Nonempty (rf7_nonzeroLocus q hq c)]
    (v : rf7_nonzeroLocus q hq c → ℂ) (hv : IsOpenEmbedding v)
    (hrange : range v = {z : ℂ | z ≠ 0 ∧ ‖z‖ ^ k < ρ})
    (hpower : ∀ y, q y.val = c + v y ^ k) :
    ∃ u : OpenPartialHomeomorph Y ℂ, u.source = univ ∧
      u.target = {z : ℂ | ‖z‖ ^ k < ρ} ∧ u x = 0 ∧ ∀ y, q y = c + u y ^ k := by
  classical
  letI : Nonempty Y := ⟨x⟩
  let U := rf7_nonzeroLocus q hq c
  let w : Y → ℂ := fun y ↦ if h : q y ≠ c then v ⟨y, h⟩ else 0
  have hwv (u : U) : w u.val = v u := by
    dsimp only [w]
    rw [dite_eq_left (show q u.val ≠ c from u.2)]
  have hwpow (u : Y) : w u ^ k = q u - c := by
    by_cases h : q u ≠ c
    · rw [show w u = v ⟨u, h⟩ by simp only [w, dite_eq_left h], hpower ⟨u, h⟩]
      ring
    · simp only [w, dite_eq_right h, zero_pow hk.ne', not_not] at *
      rw [h, sub_self]
  have hwzero (u : Y) : w u = 0 ↔ q u = c := by
    constructor
    · intro h
      have hp := hwpow u
      rw [h, zero_pow hk.ne'] at hp
      exact sub_eq_zero.mp hp.symm
    · intro h
      simp [w, h]
  have hwU : Continuous (w ∘ (Subtype.val : U → Y)) := by
    have heq : w ∘ (Subtype.val : U → Y) = v := funext hwv
    rw [heq]
    exact hv.continuous
  have hwpowcont : Continuous (fun u : Y ↦ w u ^ k) := by
    have heq : (fun u : Y ↦ w u ^ k) = fun u ↦ q u - c := funext hwpow
    rw [heq]
    exact hq.sub continuous_const
  have hw : Continuous w := by
    apply continuous_iff_continuousAt.mpr
    intro u
    by_cases hu : q u = c
    · exact rf7_continuousAt_zero_of_pow w k hk u ((hwzero u).mpr hu) hwpowcont.continuousAt
    · exact (rf7_nonzeroLocus q hq c).isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
        (hwU.continuousAt (x := ⟨u, hu⟩))
  have hwi : Function.Injective w := by
    intro y z hyz
    by_cases hy : w y = 0
    · have hz : w z = 0 := hyz.symm.trans hy
      exact (hsingle y ((hwzero y).mp hy)).trans (hsingle z ((hwzero z).mp hz)).symm
    · have hqy : q y ≠ c := fun h ↦ hy ((hwzero y).mpr h)
      have hqz : q z ≠ c := by
        intro h
        exact hy (hyz.trans ((hwzero z).mpr h))
      have h : v ⟨y, hqy⟩ = v ⟨z, hqz⟩ := by
        rw [← hwv ⟨y, hqy⟩, ← hwv ⟨z, hqz⟩]
        exact hyz
      exact congrArg Subtype.val (hv.injective h)
  have hwmem (y : Y) : ‖w y‖ ^ k < ρ := by
    rw [← norm_pow, hwpow]
    have hh := (p y).2
    simpa only [Metric.mem_ball, dist_eq_norm, hproj] using hh
  have hwR : range w = {z : ℂ | ‖z‖ ^ k < ρ} := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact hwmem y
    · intro hz
      by_cases hz0 : z = 0
      · subst z
        exact ⟨x, (hwzero x).mpr hx⟩
      · obtain ⟨y, hy⟩ := hrange.symm ▸ (show z ∈ {z : ℂ | z ≠ 0 ∧ ‖z‖ ^ k < ρ} from ⟨hz0, hz⟩)
        exact ⟨y.val, (hwv y).trans hy⟩
  let W : TopologicalSpace.Opens ℂ := ⟨{z | ‖z‖ ^ k < ρ}, isOpen_lt (continuous_norm.pow k) continuous_const⟩
  let wc : Y → W := fun y ↦ ⟨w y, hwmem y⟩
  have hwc : Continuous wc := hw.subtype_mk _
  have hwci : Function.Injective wc := fun y z h ↦ hwi (congrArg Subtype.val h)
  have hwcs : Function.Surjective wc := by
    intro z
    have hz : z.val ∈ {z : ℂ | ‖z‖ ^ k < ρ} := z.2
    obtain ⟨y, hy⟩ := hwR.symm ▸ hz
    exact ⟨y, Subtype.ext hy⟩
  let g : W → Metric.ball c ρ := fun z ↦ ⟨c + z.val ^ k, by
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_pow] using (show ‖z.val‖ ^ k < ρ from z.2)⟩
  have hg : Continuous g := (continuous_const.add (continuous_subtype_val.pow k)).subtype_mk _
  have hgp : g ∘ wc = p := by
    funext y
    apply Subtype.ext
    change c + w y ^ k = (p y).val
    rw [hproj, hwpow]
    ring
  have hwproper : IsProperMap wc := isProperMap_of_comp_of_t2 hwc hg (by rw [hgp]; exact hproper)
  let H : Y ≃ₜ W := (Equiv.ofBijective wc ⟨hwci, hwcs⟩).toHomeomorphOfContinuousClosed hwc hwproper.isClosedMap
  have hwo : IsOpenEmbedding w := W.isOpen.isOpenEmbedding_subtypeVal.comp H.isOpenEmbedding
  let u := hwo.toOpenPartialHomeomorph w
  refine ⟨u, rfl, ?_, (hwzero x).mpr hx, ?_⟩
  · simpa only [u, IsOpenEmbedding.toOpenPartialHomeomorph_target] using hwR
  · intro y
    change q y = c + w y ^ k
    rw [hwpow]
    ring


set_option backward.isDefEq.respectTransparency false in
theorem rf7_power_mfderiv_ne_zero (k : ℕ) (hk : 0 < k) (z : ℂ) (hz : z ≠ 0) :
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun w : ℂ ↦ w ^ k) z ≠ 0 := by
  have hp : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun w : ℂ ↦ w ^ k) :=
    (contDiff_id.pow k).contMDiff
  intro h
  have hh := (b4cov_mfderiv_eq_zero_iff (fun w : ℂ ↦ w ^ k) hp z z
    (mem_extChartAt_source _) (mem_extChartAt_source _)).mp h
  simp only [writtenInExtChartAt, mfld_simps] at hh
  have hd : HasDerivAt (fun w : ℂ ↦ w ^ k) ((k : ℂ) * z ^ (k - 1)) z := by
    convert! (hasDerivAt_id z).pow k using 1 <;> simp
  have h1 := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L 1) (hd.hasFDerivAt.fderiv.symm.trans hh)
  have hscalar : (k : ℂ) * z ^ (k - 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hk.ne') (pow_ne_zero _ hz)
  exact hscalar (by simpa using h1)


theorem rf7_contMDiff_root_of_finite_zero {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] (w : Y → ℂ) (hw : Continuous w) (k : ℕ) (hk : 0 < k)
    (hpow : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun y ↦ w y ^ k))
    (hfin : {y | w y = 0}.Finite) : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω w := by
  apply b6m_contMDiff_of_finite_exceptional w hw {y | w y = 0} hfin
  intro y hy
  exact b6m_contMDiffAt_of_unramified_comp w hw (fun y ↦ w y ^ k) (fun z : ℂ ↦ z ^ k)
    hpow ((contDiff_id.pow k).contMDiff) (fun _ ↦ rfl) y
    (rf7_power_mfderiv_ne_zero k hk (w y) hy)

end HodgeLean.Foundations.Program
