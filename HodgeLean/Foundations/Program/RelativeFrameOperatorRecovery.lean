import HodgeLean.Foundations.Program.RelativeFrameOperatorRecoveryAnalysis

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_delta_mem_range_of_local_coefficients {C : Type} [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {ε : Fin D.m → ℂ} {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (S : rf4_Plumbing D ε X)
    (φ : rf4_Tgt D) (α : rf2_bddForm D.P) (β : Fin D.m → ℂ → ℂ)
    (hβ : ∀ x, DifferentiableOn ℂ (β x) (rf4_innerDisc (D.deg x) D.r (ε x)))
    (hb : ∀ x, BddAbove ((fun w ↦ ‖β x w‖) '' rf4_innerDisc (D.deg x) D.r (ε x)))
    (hmatch : ∀ x (u : b63r_annulus (D.deg x) D.r),
      (α.val (D.ann x) : D.P.piece (D.ann x) →ᵇ ℂ) ⟨u, (D.hann x).ge u.property⟩ -
        β x (rf4_rootMap (D.deg x) (ε x) u) * deriv (rf4_rootMap (D.deg x) (ε x)) u =
          (φ x : b63r_annulus (D.deg x) D.r →ᵇ ℂ) u) :
    φ ∈ (rf4_delta D ε).range := by
  classical
  choose g hg using fun x ↦ rf4_sector_surjective_core (D.deg x) (D.hdeg x) D.r D.hr
    (D.c x) (ε x) (S.small x) (β x) (hβ x) (hb x)
  refine ⟨(α, g), ?_⟩
  funext x
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro u
  change (α.val (D.ann x) : D.P.piece (D.ann x) →ᵇ ℂ)
    ⟨u, (D.hann x).ge u.property⟩ -
      ((rf4_sectorOp (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x) (g x) :
        b63r_bddHol (b63r_annulus (D.deg x) D.r)) :
          b63r_annulus (D.deg x) D.r →ᵇ ℂ) u =
      (φ x : b63r_annulus (D.deg x) D.r →ᵇ ℂ) u
  have hp := (rf4_sector_pullback (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x)
    (S.small x) u u.property (fun _ _ ↦ 0)).1
  have hroot : rf4_rootMap (D.deg x) (ε x) u ∈ rf4_innerDisc (D.deg x) D.r (ε x) := by
    change ‖rf4_rootMap (D.deg x) (ε x) u ^ D.deg x + ε x‖ < 2 * D.r
    rw [hp, sub_add_cancel, norm_pow]
    exact u.property.2
  rw [← rf4_sectorOp_pullback (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x)
    (S.small x) (g x) u, ← hg x _ hroot]
  exact hmatch x u

section rf4_Corrections
variable {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

def rf4_outerCorrection (S : rf4_Plumbing D ε X) (χ : Fin D.m → ℂ → ℂ)
    (φ : rf4_Tgt D) (v : rf2_smoothForms X 1 0) (a : OpenPartialHomeomorph X ℂ) (z : ℂ) : ℂ :=
  (∑ x, rf4_tensorInChart (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)) a
    (fun u ↦ χ x u * rf4_extendBdd (φ x) u) 1 0 z) + rf4_smoothFormCoeff v a z

theorem rf4_outerCorrection_transition (S : rf4_Plumbing D ε X) (χ : Fin D.m → ℂ → ℂ)
    (φ : rf4_Tgt D) (v : rf2_smoothForms X 1 0) (a b : OpenPartialHomeomorph X ℂ)
    (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (hb : b ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (z w : ℂ) (hz : z ∈ a.target) (hw : w ∈ b.target) (hzw : a.symm z = b.symm w) :
    rf4_outerCorrection S χ φ v a z =
      rf4_outerCorrection S χ φ v b w * deriv (b ∘ a.symm) z := by
  have ht (x : Fin D.m) :
      rf4_tensorInChart (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)) a
        (fun u ↦ χ x u * rf4_extendBdd (φ x) u) 1 0 z =
      rf4_tensorInChart (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)) b
        (fun u ↦ χ x u * rf4_extendBdd (φ x) u) 1 0 w * deriv (b ∘ a.symm) z := by
    simpa only [pow_one, pow_zero, mul_one] using
      rf4_tensorInChart_transition _ a b (S.stationary (D.ann x)) ha hb
        (fun u ↦ χ x u * rf4_extendBdd (φ x) u) 1 0 z w hz hw hzw
  have hv := rf4_smoothFormCoeff_transition v a b ha hb z w hz hw hzw
  simp only [pow_one, pow_zero, mul_one] at hv
  simp only [rf4_outerCorrection]
  simp_rw [ht]
  rw [← Finset.sum_mul, hv]
  ring

theorem rf4_outerCorrection_smoothAt [T2Space X] (S : rf4_Plumbing D ε X)
    (χ : Fin D.m → ℂ → ℂ) (hχ : ∀ x, ContDiff ℝ ∞ (χ x))
    (hzero : ∀ x u, 7 * D.r / 4 ≤ ‖u‖ ^ D.deg x → χ x u = 0)
    (φ : rf4_Tgt D) (v : rf2_smoothForms X 1 0) (a : OpenPartialHomeomorph X ℂ)
    (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (z : ℂ) (hz : z ∈ a.target) (ho : a.symm z ∈ S.h '' O) :
    ContDiffAt ℝ ∞ (rf4_outerCorrection S χ φ v a) z := by
  have hpart (x : Fin D.m) : ContDiffAt ℝ ∞
      (rf4_tensorInChart (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)) a
        (fun u ↦ χ x u * rf4_extendBdd (φ x) u) 1 0) z := by
    let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)
    have hK : IsCompact (closure (b63r_annulus (D.deg x) D.r)) := by
      simpa only [D.hann x] using D.P.compact (D.ann x)
    have hcomp := rf4_cutoff_coeff_compact (φ x) (χ x) 0 hK
    simp only [sub_zero] at hcomp
    have ht : closure (b63r_annulus (D.deg x) D.r) ⊆ e.target := by
      dsimp only [e]
      rw [rf4_stationaryChart_target]
      exact (closure_mono (D.hann x).ge).trans (D.P.contained (D.ann x))
    apply rf4_tensorInChart_smoothAt e a (S.stationary (D.ann x)) ha _ hcomp.1
      (hcomp.2.trans ht) (S.h '' O) _ 1 0 z hz ho
    intro u hu hOu
    apply rf4_outer_cutoff_smooth (D.deg x) D.r D.hr (χ x) (hχ x) (hzero x) (φ x) u
    intro hboundary
    exact rf4_innerBoundary_not_outer S x u hboundary hOu
  exact (ContDiffAt.sum (s := Finset.univ) (fun x _ ↦ hpart x)).add
    (((rf4_smoothFormCoeff_smooth v a ha) z hz).contDiffAt (a.open_target.mem_nhds hz))

theorem rf4_outerCorrection_bdd [T2Space X] (S : rf4_Plumbing D ε X)
    (χ : Fin D.m → ℂ → ℂ) (hχ : ∀ x, ContDiff ℝ ∞ (χ x))
    (φ : rf4_Tgt D) (v : rf2_smoothForms X 1 0) (a : OpenPartialHomeomorph X ℂ)
    (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (K : Set ℂ) (hK : IsCompact K) (hsK : K ⊆ a.target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ‖rf4_outerCorrection S χ φ v a z‖ ≤ B := by
  classical
  have hpart (x : Fin D.m) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K,
      ‖rf4_tensorInChart (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)) a
        (fun u ↦ χ x u * rf4_extendBdd (φ x) u) 1 0 z‖ ≤ B := by
    let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)
    have hA : IsCompact (closure (b63r_annulus (D.deg x) D.r)) := by
      simpa only [D.hann x] using D.P.compact (D.ann x)
    have hcomp := rf4_cutoff_coeff_compact (φ x) (χ x) 0 hA
    obtain ⟨B, hB, hf⟩ := rf4_cutoff_coeff_bdd (φ x) (χ x) 0 hA (hχ x).continuous.continuousOn
    simp only [sub_zero] at hcomp hf
    have ht : closure (b63r_annulus (D.deg x) D.r) ⊆ e.target := by
      dsimp only [e]
      rw [rf4_stationaryChart_target]
      exact (closure_mono (D.hann x).ge).trans (D.P.contained (D.ann x))
    exact rf4_tensorInChart_bdd e a (S.stationary (D.ann x)) ha _ hcomp.1
      (hcomp.2.trans ht) B hB hf K hK hsK
  choose B hBpos hB using hpart
  obtain ⟨C, hC⟩ := rf4_smoothFormCoeff_bdd v a ha K hK hsK
  refine ⟨(∑ x, B x) + max C 0,
    add_nonneg (Finset.sum_nonneg (fun x _ ↦ hBpos x)) (le_max_right _ _), ?_⟩
  intro z hz
  have hv : ‖rf4_smoothFormCoeff v a z‖ ≤ max C 0 :=
    (hC ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  have hsum := norm_sum_le Finset.univ (fun x ↦
    rf4_tensorInChart (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)) a
      (fun u ↦ χ x u * rf4_extendBdd (φ x) u) 1 0 z)
  have hsumB := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) ↦ hB x z hz)
  have hadd := norm_add_le
    (∑ x, rf4_tensorInChart (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)) a
      (fun u ↦ χ x u * rf4_extendBdd (φ x) u) 1 0 z) (rf4_smoothFormCoeff v a z)
  dsimp only [rf4_outerCorrection]
  linarith

end rf4_Corrections
end HodgeLean.Foundations.Program
