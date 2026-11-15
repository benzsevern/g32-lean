import HodgeLean.Foundations.Program.RelativeFrameOperatorRecoveryDbar

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_tensorInChart_zero_off {X : Type} [TopologicalSpace X]
    (e a : OpenPartialHomeomorph X ℂ) (f : ℂ → ℂ) (U : Set ℂ)
    (hf : ∀ u, u ∉ U → f u = 0) (p q : ℕ) (z : ℂ)
    (hz : a.symm z ∉ e.symm '' U) : rf4_tensorInChart e a f p q z = 0 := by
  classical
  unfold rf4_tensorInChart
  split_ifs with hp
  · have hU : e (a.symm z) ∉ U := fun h ↦ hz ⟨e (a.symm z), h, e.left_inv hp⟩
    rw [hf _ hU, zero_mul, zero_mul]
  · rfl

section rf4_InnerCorrections
variable {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

def rf4_innerCorrection (S : rf4_Plumbing D ε X) (χ : Fin D.m → ℂ → ℂ)
    (φ : rf4_Tgt D) (v : rf2_smoothForms X 1 0) (x : Fin D.m)
    (a : OpenPartialHomeomorph X ℂ) (z : ℂ) : ℂ :=
  rf4_tensorInChart (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)) a
    (fun u ↦ (χ x u - 1) * rf4_extendBdd (φ x) u) 1 0 z + rf4_smoothFormCoeff v a z

theorem rf4_innerCorrection_smoothAt [T2Space X] (S : rf4_Plumbing D ε X)
    (χ : Fin D.m → ℂ → ℂ) (hχ : ∀ x, ContDiff ℝ ∞ (χ x))
    (hone : ∀ x u, ‖u‖ ^ D.deg x < 5 * D.r / 4 → χ x u = 1)
    (φ : rf4_Tgt D) (v : rf2_smoothForms X 1 0) (x : Fin D.m)
    (a : OpenPartialHomeomorph X ℂ) (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (z : ℂ) (hz : z ∈ a.target)
    (hi : a.symm z ∈ (S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x)) :
    ContDiffAt ℝ ∞ (rf4_innerCorrection S χ φ v x a) z := by
  let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)
  have hK : IsCompact (closure (b63r_annulus (D.deg x) D.r)) := by
    simpa only [D.hann x] using D.P.compact (D.ann x)
  have hcomp := rf4_cutoff_coeff_compact (φ x) (χ x) 1 hK
  have ht : closure (b63r_annulus (D.deg x) D.r) ⊆ e.target := by
    dsimp only [e]
    rw [rf4_stationaryChart_target]
    exact (closure_mono (D.hann x).ge).trans (D.P.contained (D.ann x))
  have hpart : ContDiffAt ℝ ∞ (rf4_tensorInChart e a
      (fun u ↦ (χ x u - 1) * rf4_extendBdd (φ x) u) 1 0) z := by
    apply rf4_tensorInChart_smoothAt e a (S.stationary (D.ann x)) ha _ hcomp.1
      (hcomp.2.trans ht) ((S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x)) _ 1 0 z hz hi
    intro u hu hIu
    apply rf4_inner_cutoff_smooth (D.deg x) D.r D.hr (χ x) (hχ x) (hone x) (φ x) u
    exact fun h ↦ rf4_outerBoundary_not_inner S x u h hIu
  exact hpart.add (((rf4_smoothFormCoeff_smooth v a ha) z hz).contDiffAt
    (a.open_target.mem_nhds hz))

theorem rf4_innerCorrection_bdd [T2Space X] (S : rf4_Plumbing D ε X)
    (χ : Fin D.m → ℂ → ℂ) (hχ : ∀ x, ContDiff ℝ ∞ (χ x))
    (φ : rf4_Tgt D) (v : rf2_smoothForms X 1 0) (x : Fin D.m)
    (a : OpenPartialHomeomorph X ℂ) (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (K : Set ℂ) (hK : IsCompact K) (hsK : K ⊆ a.target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ‖rf4_innerCorrection S χ φ v x a z‖ ≤ B := by
  let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)
  have hA : IsCompact (closure (b63r_annulus (D.deg x) D.r)) := by
    simpa only [D.hann x] using D.P.compact (D.ann x)
  have hcomp := rf4_cutoff_coeff_compact (φ x) (χ x) 1 hA
  obtain ⟨B, hB, hf⟩ := rf4_cutoff_coeff_bdd (φ x) (χ x) 1 hA (hχ x).continuous.continuousOn
  have ht : closure (b63r_annulus (D.deg x) D.r) ⊆ e.target := by
    dsimp only [e]
    rw [rf4_stationaryChart_target]
    exact (closure_mono (D.hann x).ge).trans (D.P.contained (D.ann x))
  obtain ⟨M, hM, hMb⟩ := rf4_tensorInChart_bdd e a (S.stationary (D.ann x)) ha _ hcomp.1
    (hcomp.2.trans ht) B hB hf K hK hsK
  obtain ⟨N, hN⟩ := rf4_smoothFormCoeff_bdd v a ha K hK hsK
  refine ⟨M + max N 0, add_nonneg hM (le_max_right _ _), ?_⟩
  intro z hz
  have hv : ‖rf4_smoothFormCoeff v a z‖ ≤ max N 0 :=
    (hN ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  have hbound := hMb z hz
  have hadd := norm_add_le (rf4_tensorInChart e a
    (fun u ↦ (χ x u - 1) * rf4_extendBdd (φ x) u) 1 0 z) (rf4_smoothFormCoeff v a z)
  change ‖rf4_tensorInChart e a (fun u ↦ (χ x u - 1) * rf4_extendBdd (φ x) u) 1 0 z +
    rf4_smoothFormCoeff v a z‖ ≤ _
  linarith

theorem rf4_innerCorrection_dbar [T2Space X] (S : rf4_Plumbing D ε X)
    (χ : Fin D.m → ℂ → ℂ) (hχ : ∀ x, ContDiff ℝ ∞ (χ x))
    (hone : ∀ x u, ‖u‖ ^ D.deg x < 5 * D.r / 4 → χ x u = 1)
    (hc : ∀ x, HasCompactSupport (wirtingerDbar (χ x)))
    (hs : ∀ x, tsupport (wirtingerDbar (χ x)) ⊆ b63r_annulus (D.deg x) D.r)
    (φ : rf4_Tgt D) (v : rf2_smoothForms X 1 0) (σ : rf2_smoothForms X 1 1)
    (hσ : σ.val = ∑ y, rf4_chartTensor
      (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann y))
      (fun u ↦ rf4_extendBdd (φ y) u * wirtingerDbar (χ y) u) 1 1)
    (hv : rf2_dbar10 X v.val = σ.val) (x : Fin D.m)
    (a : OpenPartialHomeomorph X ℂ) (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (z : ℂ) (hz : z ∈ a.target)
    (hi : a.symm z ∈ (S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x)) :
    wirtingerDbar (rf4_innerCorrection S χ φ v x a) z = 0 := by
  classical
  let e : Fin D.m → OpenPartialHomeomorph X ℂ := fun y ↦
    S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann y)
  let f : ℂ → ℂ := fun u ↦ (χ x u - 1) * rf4_extendBdd (φ x) u
  let d : Fin D.m → ℂ → ℂ := fun y u ↦ rf4_extendBdd (φ y) u * wirtingerDbar (χ y) u
  have ht (y : Fin D.m) : closure (b63r_annulus (D.deg y) D.r) ⊆ (e y).target := by
    dsimp only [e]
    rw [rf4_stationaryChart_target]
    exact (closure_mono (D.hann y).ge).trans (D.P.contained (D.ann y))
  have hK : IsCompact (closure (b63r_annulus (D.deg x) D.r)) := by
    simpa only [D.hann x] using D.P.compact (D.ann x)
  have hcomp := rf4_cutoff_coeff_compact (φ x) (χ x) 1 hK
  have hlocal (u : ℂ)
      (hIu : (e x).symm u ∈ (S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x)) :
      ContDiffAt ℝ ∞ f u := by
    apply rf4_inner_cutoff_smooth (D.deg x) D.r D.hr (χ x) (hχ x) (hone x) (φ x) u
    exact fun h ↦ rf4_outerBoundary_not_inner S x u h hIu
  have hsm := rf4_tensorInChart_smoothAt (e x) a (S.stationary (D.ann x)) ha f hcomp.1
    (hcomp.2.trans (ht x)) ((S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x))
    (fun u _ hIu ↦ hlocal u hIu) 1 0 z hz hi
  have hdf : wirtingerDbar (rf4_tensorInChart (e x) a f 1 0) z =
      rf4_tensorInChart (e x) a (d x) 1 1 z := by
    rw [rf4_tensorInChart_dbar (e x) a (S.stationary (D.ann x)) ha f hcomp.1
      (hcomp.2.trans (ht x)) z hz (fun hp ↦
        (hlocal _ (by simpa only [(e x).left_inv hp] using hi)).differentiableAt (by simp))]
    by_cases hp : a.symm z ∈ (e x).source
    · have hIu : (e x).symm (e x (a.symm z)) ∈
          (S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x) := by
        simpa only [(e x).left_inv hp] using hi
      have hne : ‖e x (a.symm z)‖ ^ D.deg x ≠ 2 * D.r :=
        fun h ↦ rf4_outerBoundary_not_inner S x _ h hIu
      have hd := rf4_inner_cutoff_dbar (D.deg x) D.r D.hr (χ x) (hχ x) (hone x)
        (φ x) (e x (a.symm z)) hne
      simp only [rf4_tensorInChart, if_pos hp, pow_one]
      rw [hd]
    · simp only [rf4_tensorInChart, if_neg hp]
  have hdensity (y : Fin D.m) := rf4_annulus_density_smooth (D.deg y) D.r
    (χ y) (hχ y) (hc y) (hs y) (φ y)
  have hcoeff := rf4_smoothFormCoeff_sumTensor e (fun y ↦ S.stationary (D.ann y)) d
    (fun y ↦ (hdensity y).1) (fun y ↦ (hdensity y).2.1)
    (fun y ↦ (hdensity y).2.2.trans (subset_closure.trans (ht y))) 1 1 σ hσ a ha z hz
  have hsum : (∑ y, rf4_tensorInChart (e y) a (d y) 1 1 z) =
      rf4_tensorInChart (e x) a (d x) 1 1 z := by
    apply Finset.sum_eq_single x
    · intro y _ hyx
      refine rf4_tensorInChart_zero_off (e y) a (d y) (b63r_annulus (D.deg y) D.r) ?_ 1 1 z ?_
      · intro u hu
        simp only [d, rf4_extendBdd, dif_neg hu, zero_mul]
      · intro hp
        have hpAnn : a.symm z ∈
            S.h '' ((D.P.chart (D.ann y)).symm '' b63r_annulus (D.deg y) D.r) := by
          obtain ⟨u, hu, heq⟩ := hp
          exact ⟨(D.P.chart (D.ann y)).symm u, ⟨u, hu, rfl⟩, heq⟩
        exact Set.disjoint_left.mp (S.disjoint hyx) (rf4_annulus_in_inner S y hpAnn) hi
    · intro hx
      exact False.elim (hx (Finset.mem_univ x))
  rw [hsum] at hcoeff
  have hvform : (⟨rf2_dbar10 X v.val, rf2_dbar10_smooth_aux X v⟩ : rf2_smoothForms X 1 1) = σ :=
    Subtype.ext hv
  have hvd := rf4_smoothFormCoeff_dbar v a ha z hz
  rw [hvform, hcoeff] at hvd
  have hvs : DifferentiableAt ℝ (rf4_smoothFormCoeff v a) z :=
    (((rf4_smoothFormCoeff_smooth v a ha) z hz).contDiffAt
      (a.open_target.mem_nhds hz)).differentiableAt (by simp)
  change wirtingerDbar (fun u ↦ rf4_tensorInChart (e x) a f 1 0 u +
    rf4_smoothFormCoeff v a u) z = 0
  rw [rf4_wirtingerDbar_add (hsm.differentiableAt (by simp)) hvs, hdf, hvd, neg_add_cancel]

theorem rf4_innerCorrection_transition (S : rf4_Plumbing D ε X) (χ : Fin D.m → ℂ → ℂ)
    (φ : rf4_Tgt D) (v : rf2_smoothForms X 1 0) (x : Fin D.m)
    (a b : OpenPartialHomeomorph X ℂ)
    (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (hb : b ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (z w : ℂ) (hz : z ∈ a.target) (hw : w ∈ b.target) (hzw : a.symm z = b.symm w) :
    rf4_innerCorrection S χ φ v x a z =
      rf4_innerCorrection S χ φ v x b w * deriv (b ∘ a.symm) z := by
  have ht := rf4_tensorInChart_transition
    (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)) a b
    (S.stationary (D.ann x)) ha hb (fun u ↦ (χ x u - 1) * rf4_extendBdd (φ x) u)
    1 0 z w hz hw hzw
  have hv := rf4_smoothFormCoeff_transition v a b ha hb z w hz hw hzw
  simp only [pow_one, pow_zero, mul_one] at ht hv
  simp only [rf4_innerCorrection]
  rw [ht, hv]
  ring

theorem rf4_innerCorrection_data [T2Space X] (S : rf4_Plumbing D ε X)
    (χ : Fin D.m → ℂ → ℂ) (hχ : ∀ x, ContDiff ℝ ∞ (χ x))
    (hone : ∀ x u, ‖u‖ ^ D.deg x < 5 * D.r / 4 → χ x u = 1)
    (hc : ∀ x, HasCompactSupport (wirtingerDbar (χ x)))
    (hs : ∀ x, tsupport (wirtingerDbar (χ x)) ⊆ b63r_annulus (D.deg x) D.r)
    (φ : rf4_Tgt D) (v : rf2_smoothForms X 1 0) (σ : rf2_smoothForms X 1 1)
    (hσ : σ.val = ∑ y, rf4_chartTensor
      (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann y))
      (fun u ↦ rf4_extendBdd (φ y) u * wirtingerDbar (χ y) u) 1 1)
    (hv : rf2_dbar10 X v.val = σ.val) (x : Fin D.m) :
    DifferentiableOn ℂ (rf4_innerCorrection S χ φ v x (S.w x))
      (rf4_innerDisc (D.deg x) D.r (ε x)) ∧
    BddAbove ((fun w ↦ ‖rf4_innerCorrection S χ φ v x (S.w x) w‖) ''
      rf4_innerDisc (D.deg x) D.r (ε x)) := by
  let U := rf4_innerDisc (D.deg x) D.r (ε x)
  have hU : IsOpen U := isOpen_lt (by fun_prop : Continuous (fun w : ℂ ↦
    ‖w ^ D.deg x + ε x‖)) continuous_const
  have ht : U ⊆ (S.w x).target := subset_closure.trans (S.w_target x)
  have hreal : ContDiffOn ℝ ∞ (rf4_innerCorrection S χ φ v x (S.w x)) U := by
    intro z hz
    exact (rf4_innerCorrection_smoothAt S χ hχ hone φ v x (S.w x) (S.w_mem x)
      z (ht hz) ⟨z, hz, rfl⟩).contDiffWithinAt
  have han := rf2_analyticOnNhd_of_wirtinger_zero U hU _ hreal (fun z hz ↦
    rf4_innerCorrection_dbar S χ hχ hone hc hs φ v σ hσ hv x (S.w x) (S.w_mem x)
      z (ht hz) ⟨z, hz, rfl⟩)
  refine ⟨han.differentiableOn, ?_⟩
  obtain ⟨B, _, hB⟩ := rf4_innerCorrection_bdd S χ hχ φ v x (S.w x) (S.w_mem x)
    (closure U) (rf4_innerDisc_closure_compact _ (D.hdeg x) _ _) (S.w_target x)
  refine ⟨B, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hB z (subset_closure hz)

end rf4_InnerCorrections
end HodgeLean.Foundations.Program
