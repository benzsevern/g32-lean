import HodgeLean.Foundations.Program.RelativeFrameOperatorRecovery

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program
section
variable {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X]

theorem rf4_outerCorrection_dbar (S : rf4_Plumbing D ε X) (χ : Fin D.m → ℂ → ℂ)
    (hχ : ∀ x, ContDiff ℝ ∞ (χ x))
    (hzero : ∀ x u, 7 * D.r / 4 ≤ ‖u‖ ^ D.deg x → χ x u = 0)
    (hc : ∀ x, HasCompactSupport (wirtingerDbar (χ x)))
    (hs : ∀ x, tsupport (wirtingerDbar (χ x)) ⊆ b63r_annulus (D.deg x) D.r)
    (φ : rf4_Tgt D) (v : rf2_smoothForms X 1 0) (σ : rf2_smoothForms X 1 1)
    (hσ : σ.val = ∑ x, rf4_chartTensor
      (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x))
      (fun u ↦ rf4_extendBdd (φ x) u * wirtingerDbar (χ x) u) 1 1)
    (hv : rf2_dbar10 X v.val = σ.val)
    (a : OpenPartialHomeomorph X ℂ) (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (z : ℂ) (hz : z ∈ a.target) (ho : a.symm z ∈ S.h '' O) :
    wirtingerDbar (rf4_outerCorrection S χ φ v a) z = 0 := by
  classical
  let e : Fin D.m → OpenPartialHomeomorph X ℂ := fun x ↦
    S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)
  let f : Fin D.m → ℂ → ℂ := fun x u ↦ χ x u * rf4_extendBdd (φ x) u
  let d : Fin D.m → ℂ → ℂ := fun x u ↦ rf4_extendBdd (φ x) u * wirtingerDbar (χ x) u
  have ht (x : Fin D.m) : closure (b63r_annulus (D.deg x) D.r) ⊆ (e x).target := by
    dsimp only [e]
    rw [rf4_stationaryChart_target]
    exact (closure_mono (D.hann x).ge).trans (D.P.contained (D.ann x))
  have hpart (x : Fin D.m) :
      DifferentiableAt ℝ (rf4_tensorInChart (e x) a (f x) 1 0) z ∧
      wirtingerDbar (rf4_tensorInChart (e x) a (f x) 1 0) z =
        rf4_tensorInChart (e x) a (d x) 1 1 z := by
    have hK : IsCompact (closure (b63r_annulus (D.deg x) D.r)) := by
      simpa only [D.hann x] using D.P.compact (D.ann x)
    have hcomp := rf4_cutoff_coeff_compact (φ x) (χ x) 0 hK
    simp only [sub_zero] at hcomp
    have hlocal (u : ℂ) (hOu : (e x).symm u ∈ S.h '' O) :
        ContDiffAt ℝ ∞ (f x) u := by
      apply rf4_outer_cutoff_smooth (D.deg x) D.r D.hr (χ x) (hχ x) (hzero x) (φ x) u
      exact fun h ↦ rf4_innerBoundary_not_outer S x u h hOu
    have hsm := rf4_tensorInChart_smoothAt (e x) a (S.stationary (D.ann x)) ha
      (f x) hcomp.1 (hcomp.2.trans (ht x)) (S.h '' O) (fun u _ hOu ↦ hlocal u hOu)
      1 0 z hz ho
    refine ⟨hsm.differentiableAt (by simp), ?_⟩
    rw [rf4_tensorInChart_dbar (e x) a (S.stationary (D.ann x)) ha (f x) hcomp.1
      (hcomp.2.trans (ht x)) z hz (fun hp ↦
        (hlocal _ (by simpa only [(e x).left_inv hp] using ho)).differentiableAt (by simp))]
    by_cases hp : a.symm z ∈ (e x).source
    · have hOu : (e x).symm (e x (a.symm z)) ∈ S.h '' O := by
        simpa only [(e x).left_inv hp] using ho
      have hne : ‖e x (a.symm z)‖ ^ D.deg x ≠ D.r :=
        fun h ↦ rf4_innerBoundary_not_outer S x _ h hOu
      have hd := rf4_outer_cutoff_dbar (D.deg x) D.r D.hr (χ x) (hχ x) (hzero x)
        (φ x) (e x (a.symm z)) hne
      simp only [rf4_tensorInChart, if_pos hp, pow_one]
      rw [hd]
    · simp only [rf4_tensorInChart, if_neg hp]
  have hdensity (x : Fin D.m) := rf4_annulus_density_smooth (D.deg x) D.r
    (χ x) (hχ x) (hc x) (hs x) (φ x)
  have hcoeff := rf4_smoothFormCoeff_sumTensor e (fun x ↦ S.stationary (D.ann x)) d
    (fun x ↦ (hdensity x).1) (fun x ↦ (hdensity x).2.1)
    (fun x ↦ (hdensity x).2.2.trans (subset_closure.trans (ht x))) 1 1 σ hσ a ha z hz
  have hvform : (⟨rf2_dbar10 X v.val, rf2_dbar10_smooth_aux X v⟩ : rf2_smoothForms X 1 1) = σ :=
    Subtype.ext hv
  have hvd := rf4_smoothFormCoeff_dbar v a ha z hz
  rw [hvform, hcoeff] at hvd
  have hvs : DifferentiableAt ℝ (rf4_smoothFormCoeff v a) z :=
    (((rf4_smoothFormCoeff_smooth v a ha) z hz).contDiffAt
      (a.open_target.mem_nhds hz)).differentiableAt (by simp)
  change wirtingerDbar (fun u ↦ (∑ x, rf4_tensorInChart (e x) a (f x) 1 0 u) +
    rf4_smoothFormCoeff v a u) z = 0
  have hsum : DifferentiableAt ℝ (fun u ↦ ∑ x, rf4_tensorInChart (e x) a (f x) 1 0 u) z :=
    DifferentiableAt.fun_sum (fun x _ ↦ (hpart x).1)
  rw [rf4_wirtingerDbar_add hsum hvs, rf4_wirtingerDbar_sum Finset.univ _ z
    (fun x _ ↦ (hpart x).1)]
  simp_rw [(hpart _).2]
  rw [hvd, neg_add_cancel]

theorem rf4_outerCorrection_tuple (S : rf4_Plumbing D ε X) (χ : Fin D.m → ℂ → ℂ)
    (hχ : ∀ x, ContDiff ℝ ∞ (χ x))
    (hzero : ∀ x u, 7 * D.r / 4 ≤ ‖u‖ ^ D.deg x → χ x u = 0)
    (hc : ∀ x, HasCompactSupport (wirtingerDbar (χ x)))
    (hs : ∀ x, tsupport (wirtingerDbar (χ x)) ⊆ b63r_annulus (D.deg x) D.r)
    (φ : rf4_Tgt D) (v : rf2_smoothForms X 1 0) (σ : rf2_smoothForms X 1 1)
    (hσ : σ.val = ∑ x, rf4_chartTensor
      (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x))
      (fun u ↦ rf4_extendBdd (φ x) u * wirtingerDbar (χ x) u) 1 1)
    (hv : rf2_dbar10 X v.val = σ.val) :
    ∃ α : rf2_bddForm D.P, ∀ i (z : D.P.piece i),
      (α.val i : D.P.piece i →ᵇ ℂ) z =
        rf4_outerCorrection S χ φ v (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i) z := by
  classical
  let e : Fin D.P.n → OpenPartialHomeomorph X ℂ := fun i ↦
    S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i
  have ht (i : Fin D.P.n) : closure (D.P.piece i) ⊆ (e i).target := by
    dsimp only [e]
    rw [rf4_stationaryChart_target]
    exact D.P.contained i
  have ho (i : Fin D.P.n) (z : D.P.piece i) : (e i).symm z ∈ S.h '' O := by
    refine ⟨(D.P.chart i).symm z, ?_, rfl⟩
    exact (Set.ext_iff.mp D.P.covers _).mpr (mem_iUnion.mpr ⟨i, ⟨z, z.property, rfl⟩⟩)
  have hdata (i : Fin D.P.n) : ∃ g : b63r_bddHol (D.P.piece i),
      ∀ z : D.P.piece i, (g : D.P.piece i →ᵇ ℂ) z = rf4_outerCorrection S χ φ v (e i) z := by
    have hreal : ContDiffOn ℝ ∞ (rf4_outerCorrection S χ φ v (e i)) (D.P.piece i) := by
      intro z hz
      exact (rf4_outerCorrection_smoothAt S χ hχ hzero φ v (e i) (S.stationary i)
        z (ht i (subset_closure hz)) (ho i ⟨z, hz⟩)).contDiffWithinAt
    have han := rf2_analyticOnNhd_of_wirtinger_zero (D.P.piece i) (D.P.isOpen i) _ hreal
      (fun z hz ↦ rf4_outerCorrection_dbar S χ hχ hzero hc hs φ v σ hσ hv
        (e i) (S.stationary i) z (ht i (subset_closure hz)) (ho i ⟨z, hz⟩))
    obtain ⟨B, _, hB⟩ := rf4_outerCorrection_bdd S χ hχ φ v (e i) (S.stationary i)
      (closure (D.P.piece i)) (D.P.compact i) (ht i)
    have hb : BddAbove ((fun z ↦ ‖rf4_outerCorrection S χ φ v (e i) z‖) '' D.P.piece i) := by
      refine ⟨B, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hB z (subset_closure hz)
    exact ⟨rf4_bddHolOfBddAbove _ _ han.differentiableOn hb, fun _ ↦ rfl⟩
  choose g hg using hdata
  refine ⟨⟨g, ?_⟩, hg⟩
  intro i j z w hzw
  have hz := ht i (subset_closure z.property)
  have hw := ht j (subset_closure w.property)
  have hsame : (e i).symm z = (e j).symm w := by
    change S.h ((D.P.chart i).symm z) = S.h ((D.P.chart j).symm w)
    exact congrArg S.h hzw
  have htrans := rf4_outerCorrection_transition S χ φ v (e i) (e j)
    (S.stationary i) (S.stationary j) z w hz hw hsame
  have hfun : (e j) ∘ (e i).symm = (D.P.chart j) ∘ (D.P.chart i).symm := by
    funext u
    change D.P.chart j (S.h.symm (S.h ((D.P.chart i).symm u))) =
      D.P.chart j ((D.P.chart i).symm u)
    rw [S.h.symm_apply_apply]
  rw [hg i z, hg j w, ← hfun]
  exact htrans

end
end HodgeLean.Foundations.Program
