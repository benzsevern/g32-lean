import HodgeLean.Foundations.Program.RelativeFrameOperatorCorrection

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

def rf4_tensorInChart {X : Type} [TopologicalSpace X]
    (e a : OpenPartialHomeomorph X ℂ) (f : ℂ → ℂ) (p q : ℕ) (z : ℂ) : ℂ := by
  classical
  exact if a.symm z ∈ e.source then
    f (e (a.symm z)) * deriv (e ∘ a.symm) z ^ p * star (deriv (e ∘ a.symm) z) ^ q else 0

theorem rf4_tensorInChart_transition {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (e a b : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (hb : b ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (f : ℂ → ℂ) (p q : ℕ) (z w : ℂ) (hz : z ∈ a.target) (hw : w ∈ b.target)
    (hzw : a.symm z = b.symm w) :
    rf4_tensorInChart e a f p q z = rf4_tensorInChart e b f p q w *
      deriv (b ∘ a.symm) z ^ p * star (deriv (b ∘ a.symm) z) ^ q := by
  classical
  by_cases hp : a.symm z ∈ e.source
  · have hp' : b.symm w ∈ e.source := hzw ▸ hp
    have hpb : a.symm z ∈ b.source := by
      rw [hzw]
      exact b.map_target hw
    have hew : b (a.symm z) = w := by rw [hzw, b.right_inv hw]
    have hder := rf4_atlas_transition_deriv a b e ha hb he z hz hpb hp
    rw [hew] at hder
    simp only [rf4_tensorInChart, if_pos hp, if_pos hp', hder, hzw, mul_pow, star_mul]
    ring
  · have hp' : b.symm w ∉ e.source := hzw ▸ hp
    simp only [rf4_tensorInChart, if_neg hp, if_neg hp', zero_mul]

theorem rf4_tensorInChart_smoothAt {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] (e a : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (f : ℂ → ℂ) (hc : HasCompactSupport f) (hs : tsupport f ⊆ e.target)
    (V : Set X) (hf : ∀ u ∈ e.target, e.symm u ∈ V → ContDiffAt ℝ ∞ f u)
    (p q : ℕ) (z : ℂ) (hz : z ∈ a.target) (hV : a.symm z ∈ V) :
    ContDiffAt ℝ ∞ (rf4_tensorInChart e a f p q) z := by
  classical
  by_cases hp : a.symm z ∈ e.source
  · have ht := rf4_atlas_transition_analytic a e ha he z hz hp
    have hfp := hf (e (a.symm z)) (e.map_source hp)
      (by simpa only [e.left_inv hp] using hV)
    have hlocal : ContDiffAt ℝ ∞ (fun u ↦ f (e (a.symm u)) *
        deriv (e ∘ a.symm) u ^ p * star (deriv (e ∘ a.symm) u) ^ q) z :=
      ((hfp.comp z (ht.contDiffAt.restrict_scalars ℝ)).mul
        ((ht.deriv.contDiffAt.restrict_scalars ℝ).pow p)).mul
        ((Complex.conjCLE.contDiff.contDiffAt.comp z
          (ht.deriv.contDiffAt.restrict_scalars ℝ)).pow q)
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [(a.isOpen_inter_preimage_symm e.open_source).mem_nhds
      (show z ∈ a.target ∩ a.symm ⁻¹' e.source from ⟨hz, hp⟩)] with u hu
    exact if_pos hu.2
  · let K := e.symm '' tsupport f
    have hK : IsCompact K := hc.image_of_continuousOn (e.continuousOn_symm.mono hs)
    have hzK : a.symm z ∉ K := by
      rintro ⟨u, hu, heu⟩
      exact hp (heu ▸ e.map_target (hs hu))
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℂ ↦ (0 : ℂ)) z).congr_of_eventuallyEq
    filter_upwards [(a.isOpen_inter_preimage_symm hK.isClosed.isOpen_compl).mem_nhds
      (show z ∈ a.target ∩ a.symm ⁻¹' Kᶜ from ⟨hz, hzK⟩)] with u hu
    dsimp [rf4_tensorInChart]
    split_ifs with heU
    · have hfu : f (e (a.symm u)) = 0 := by
        by_contra hne
        exact hu.2 ⟨e (a.symm u), subset_closure hne, e.left_inv heU⟩
      rw [hfu, zero_mul, zero_mul]
    · rfl

theorem rf4_tensorInChart_bdd {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] (e a : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (f : ℂ → ℂ) (hc : HasCompactSupport f) (hs : tsupport f ⊆ e.target)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ u, ‖f u‖ ≤ B)
    (K : Set ℂ) (hK : IsCompact K) (hsK : K ⊆ a.target) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, ‖rf4_tensorInChart e a f 1 0 z‖ ≤ M := by
  classical
  obtain ⟨C, hC⟩ := rf4_transition_bdd a e ha he K (tsupport f) hK hc hsK hs
  refine ⟨B * max C 0, mul_nonneg hB (le_max_right _ _), ?_⟩
  intro z hz
  by_cases hp : a.symm z ∈ e.source
  · by_cases hzero : f (e (a.symm z)) = 0
    · simp only [rf4_tensorInChart, if_pos hp, hzero, zero_mul, norm_zero]
      exact mul_nonneg hB (le_max_right _ _)
    · have hts : e (a.symm z) ∈ tsupport f := subset_closure hzero
      have hd := hC z hz (e (a.symm z)) hts (e.left_inv hp).symm
      simp only [rf4_tensorInChart, if_pos hp, pow_one, pow_zero, mul_one, norm_mul]
      exact mul_le_mul (hf _) (hd.trans (le_max_left _ _)) (norm_nonneg _) hB
  · simp only [rf4_tensorInChart, if_neg hp, norm_zero]
    exact mul_nonneg hB (le_max_right _ _)

theorem rf4_smoothFormCoeff_localTensor {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {p q : ℕ} (v : rf2_smoothForms X p q)
    (e a : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (f : ℂ → ℂ) (hv : v.val = rf4_chartTensor e f p q)
    (z : ℂ) (hz : z ∈ a.target) :
    rf4_smoothFormCoeff v a z = rf4_tensorInChart e a f p q z := by
  let y := a.symm z
  let b := chartAt ℂ y
  have hy : y ∈ b.source := mem_chart_source ℂ y
  have hyt : b y ∈ b.target := b.map_source hy
  have ht := rf4_tensorInChart_transition e a b he ha (IsManifold.chart_mem_maximalAtlas y)
    f p q z (b y) hz hyt (b.left_inv hy).symm
  change v.val y ⟨b y, hyt⟩ * deriv (b ∘ a.symm) z ^ p *
    star (deriv (b ∘ a.symm) z) ^ q = _
  rw [hv]
  exact ht.symm

theorem rf4_tensorInChart_dbar {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] (e a : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (f : ℂ → ℂ) (hc : HasCompactSupport f) (hs : tsupport f ⊆ e.target)
    (z : ℂ) (hz : z ∈ a.target)
    (hf : a.symm z ∈ e.source → DifferentiableAt ℝ f (e (a.symm z))) :
    wirtingerDbar (rf4_tensorInChart e a f 1 0) z =
      rf4_tensorInChart e a (wirtingerDbar f) 1 1 z := by
  classical
  by_cases hp : a.symm z ∈ e.source
  · let t : ℂ → ℂ := e ∘ a.symm
    have ht := rf4_atlas_transition_analytic a e ha he z hz hp
    have hF : DifferentiableAt ℝ f (t z) := hf hp
    have hev : rf4_tensorInChart e a f 1 0 =ᶠ[𝓝 z] fun u ↦ f (t u) * deriv t u := by
      filter_upwards [(a.isOpen_inter_preimage_symm e.open_source).mem_nhds
        (show z ∈ a.target ∩ a.symm ⁻¹' e.source from ⟨hz, hp⟩)] with u hu
      have huS : a.symm u ∈ e.source := hu.2
      simp only [rf4_tensorInChart, if_pos huS, pow_one, pow_zero, mul_one]
      rfl
    have hd : wirtingerDbar (rf4_tensorInChart e a f 1 0) z =
        deriv t z * (star (deriv t z) * wirtingerDbar f (t z)) := by
      have hh : wirtingerDbar (rf4_tensorInChart e a f 1 0) z =
          wirtingerDbar (fun u ↦ f (t u) * deriv t u) z :=
        congrArg (fun L : ℂ →L[ℝ] ℂ ↦ antiLinearPart L 1) hev.fderiv_eq
      rw [hh]
      change wirtingerDbar (fun u ↦ (f ∘ t) u * deriv t u) z = _
      rw [rf2_wirtingerDbar_mul (hF.comp z (ht.differentiableAt.restrictScalars ℝ))
        (ht.deriv.differentiableAt.restrictScalars ℝ),
        rf2_wirtingerDbar_hol ht.deriv.differentiableAt, mul_zero, zero_add,
        rf2_wirtingerDbar_comp hF ht.differentiableAt]
    rw [hd]
    simp only [rf4_tensorInChart, if_pos hp, pow_one]
    dsimp only [t, Function.comp_apply]
    ring
  · have hev : rf4_tensorInChart e a f 1 0 =ᶠ[𝓝 z] fun _ ↦ 0 := by
      let K := e.symm '' tsupport f
      have hK : IsCompact K := hc.image_of_continuousOn (e.continuousOn_symm.mono hs)
      have hzK : a.symm z ∉ K := by
        rintro ⟨u, hu, heu⟩
        exact hp (heu ▸ e.map_target (hs hu))
      filter_upwards [(a.isOpen_inter_preimage_symm hK.isClosed.isOpen_compl).mem_nhds
        (show z ∈ a.target ∩ a.symm ⁻¹' Kᶜ from ⟨hz, hzK⟩)] with u hu
      dsimp [rf4_tensorInChart]
      split_ifs with heU
      · have hfu : f (e (a.symm u)) = 0 := by
          by_contra hne
          exact hu.2 ⟨e (a.symm u), subset_closure hne, e.left_inv heU⟩
        rw [hfu, zero_mul, zero_mul]
      · rfl
    rw [rf4_wirtingerDbar_eq_zero_of_eventually_constant _ 0 z hev]
    simp only [rf4_tensorInChart, if_neg hp]

theorem rf4_smoothFormCoeff_sumTensor {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] {I : Type} [Fintype I]
    (e : I → OpenPartialHomeomorph X ℂ)
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (f : I → ℂ → ℂ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hc : ∀ i, HasCompactSupport (f i)) (hs : ∀ i, tsupport (f i) ⊆ (e i).target)
    (p q : ℕ) (σ : rf2_smoothForms X p q)
    (hσ : σ.val = ∑ i, rf4_chartTensor (e i) (f i) p q)
    (a : OpenPartialHomeomorph X ℂ) (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (z : ℂ) (hz : z ∈ a.target) :
    rf4_smoothFormCoeff σ a z = ∑ i, rf4_tensorInChart (e i) a (f i) p q z := by
  classical
  let v : I → rf2_smoothForms X p q := fun i ↦
    ⟨rf4_chartTensor (e i) (f i) p q, rf4_chartTensor_mem (e i) (he i) (f i)
      (hf i) (hc i) (hs i) p q⟩
  have hv : σ = ∑ i, v i := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum] using hσ
  change (rf4_smoothFormCoeffLinear a p q σ) z = _
  rw [hv, map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact rf4_smoothFormCoeff_localTensor (v i) (e i) a (he i) ha (f i) rfl z hz

end HodgeLean.Foundations.Program
