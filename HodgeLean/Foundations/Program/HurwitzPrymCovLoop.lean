import HodgeLean.Foundations.Program.HurwitzPrymCovRot

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-cov`: holomorphic maps and `C¹` loops

A holomorphic map is real `C¹` (same charts, restriction of scalars), so it carries `C¹` loops to
`C¹` loops, and the velocity of `g ∘ γ` is `dg (γ')`. On a complex line `dg` is a scalar `c`, and
`b3_orient (c v) (c w) = |c|² b3_orient v w`: a biholomorphism preserves transversality and the
signs of crossings.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold Set Filter Topology
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Loop

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {C' : Type} [TopologicalSpace C'] [ChartedSpace E' C']

theorem b4cov_extChartAt_real (x : C) :
    ⇑(extChartAt 𝓘(ℝ, E) x) = ⇑(extChartAt 𝓘(ℂ, E) x) := by
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]

theorem b4cov_extChartAt_real_symm (x : C) :
    ⇑(extChartAt 𝓘(ℝ, E) x).symm = ⇑(extChartAt 𝓘(ℂ, E) x).symm := by
  simp only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id]

theorem b4cov_written_real (g : C → C') (x : C) :
    writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E') x g = writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x g := by
  simp only [writtenInExtChartAt, b4cov_extChartAt_real, b4cov_extChartAt_real_symm]

/-- **A holomorphic map is real `C¹`.** -/
theorem b4cov_contMDiff_real (g : C → C') (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω g) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') 1 g := by
  intro x
  have h := (contMDiffAt_iff.1 (hg x))
  rw [contMDiffAt_iff]
  refine ⟨h.1, ?_⟩
  have h2 := (h.2.restrict_scalars ℝ).of_le (show ((1 : ℕ∞) : WithTop ℕ∞) ≤ ω from le_top)
  simp only [modelWithCornersSelf_coe, range_id] at h2 ⊢
  rw [show extChartAt 𝓘(ℝ, E') (g x) ∘ g ∘ (extChartAt 𝓘(ℝ, E) x).symm =
    extChartAt 𝓘(ℂ, E') (g x) ∘ g ∘ (extChartAt 𝓘(ℂ, E) x).symm by
      simp only [b4cov_extChartAt_real, b4cov_extChartAt_real_symm],
    b4cov_extChartAt_real]
  exact h2

/-- **The real and complex derivatives of a holomorphic map agree.** -/
theorem b4cov_mfderiv_real (g : C → C') (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω g) (x : C)
    (v : E) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') g x v = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') g x v := by
  have hc : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E') g x := (hg x).mdifferentiableAt (by simp)
  have hr : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E') g x :=
    (b4cov_contMDiff_real g hg x).mdifferentiableAt (by simp)
  rw [hr.mfderiv_abuse, hc.mfderiv_abuse]
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ, b4cov_written_real,
    b4cov_extChartAt_real]
  have hd : DifferentiableAt ℂ (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x g)
      (extChartAt 𝓘(ℂ, E) x x) := by
    have := hc.differentiableWithinAt_writtenInExtChartAt
    rw [modelWithCornersSelf_coe, range_id, differentiableWithinAt_univ] at this
    exact this
  rw [hd.fderiv_restrictScalars ℝ]
  rfl

variable [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω C']

/-- **The image of a `C¹` loop under a holomorphic map.** -/
def b4cov_mapLoop (g : C → C') (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω g) (γ : b3_SmoothLoop E C) :
    b3_SmoothLoop E' C' :=
  ⟨g ∘ γ.1, fun t ↦ by simp only [Function.comp_apply, γ.2.1 t],
    (b4cov_contMDiff_real g hg).comp γ.2.2⟩

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω C'] in
theorem b4cov_mapLoop_coe (g : C → C') (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω g)
    (γ : b3_SmoothLoop E C) : (b4cov_mapLoop g hg γ).1 = g ∘ γ.1 := rfl

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω C'] in
/-- **The velocity of `g ∘ γ` is `dg (γ')`.** -/
theorem b4cov_velocity_comp (g : C → C') (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω g) (γ : ℝ → C)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (t : ℝ) :
    b3_velocity E' C' (g ∘ γ) t = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') g (γ t) (b3_velocity E C γ t) := by
  have hgr : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E') g (γ t) :=
    (b4cov_contMDiff_real g hg (γ t)).mdifferentiableAt (by simp)
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t := (hγ t).mdifferentiableAt (by simp)
  rw [b3_velocity, mfderiv_comp t hgr hγd, ContinuousLinearMap.comp_apply]
  exact b4cov_mfderiv_real g hg (γ t) _

end Loop

section Orient

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Complex scalars scale the orientation form by `|c|²`.** -/
theorem b4cov_orient_smul (c : ℂ) (v w : E) :
    b3_orient E (c • v) (c • w) = ‖c‖ ^ 2 * b3_orient E v w := by
  simp only [b3_orient, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, show starRingEnd ℂ c * starRingEnd ℂ ((Module.finBasis ℂ E).equivFun v i) *
      (c * (Module.finBasis ℂ E).equivFun w i) =
      (starRingEnd ℂ c * c) * (starRingEnd ℂ ((Module.finBasis ℂ E).equivFun v i) *
        (Module.finBasis ℂ E).equivFun w i) by ring, Complex.conj_mul', ← Complex.ofReal_pow,
    Complex.im_ofReal_mul]

end Orient

section Action

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {G : Type} [Group G] [MulAction G C]

/-- The scalar of the derivative of an automorphism at `y`. -/
def b4cov_scal (hE : Module.finrank ℂ E = 1) (g : G) (y : C) : ℂ :=
  (b4cov_lineEquiv hE).symm
    ((mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun x : C ↦ g • x) y : E →L[ℂ] E) (b4cov_lineEquiv hE 1))

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b4cov_mfderiv_smul_apply (hE : Module.finrank ℂ E = 1) (g : G) (y : C) (v : E) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun x : C ↦ g • x) y v = b4cov_scal hE g y • v :=
  b4cov_eq_smul hE _ v

/-- The derivative of an automorphism is a nonzero scalar. -/
theorem b4cov_scal_ne_zero (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) (g : G) (y : C) :
    b4cov_scal hE g y ≠ 0 := by
  intro h0
  have hcomp : (fun x : C ↦ g⁻¹ • x) ∘ (fun x : C ↦ g • x) = id :=
    funext fun x ↦ inv_smul_smul g x
  have h1 : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) (fun x : C ↦ g⁻¹ • x) (g • y) :=
    ((hG g⁻¹) _).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) (fun x : C ↦ g • x) y :=
    ((hG g) _).mdifferentiableAt (by simp)
  have := mfderiv_comp y h1 h2
  rw [hcomp, mfderiv_id] at this
  have hv := DFunLike.congr_fun this (b4cov_lineEquiv hE 1)
  change b4cov_lineEquiv hE 1 = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun x : C ↦ g⁻¹ • x) (g • y)
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun x : C ↦ g • x) y (b4cov_lineEquiv hE 1)) at hv
  rw [b4cov_mfderiv_smul_apply hE g y, h0, zero_smul] at hv
  exact b4cov_lineEquiv_one_ne_zero hE (by rw [hv]; exact map_zero _)

/-- **Orientation at a crossing of the image loops.** -/
theorem b4cov_orient_map (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) (g : G)
    (γ δ : b3_SmoothLoop E C) (s t : ℝ) (hst : γ.1 s = δ.1 t) :
    b3_orient E (b3_velocity E C (b4cov_mapLoop (fun x : C ↦ g • x) (hG g) γ).1 s)
        (b3_velocity E C (b4cov_mapLoop (fun x : C ↦ g • x) (hG g) δ).1 t) =
      ‖b4cov_scal hE g (γ.1 s)‖ ^ 2 * b3_orient E (b3_velocity E C γ.1 s)
        (b3_velocity E C δ.1 t) := by
  rw [b4cov_mapLoop_coe, b4cov_mapLoop_coe, b4cov_velocity_comp _ (hG g) _ γ.2.2,
    b4cov_velocity_comp _ (hG g) _ δ.2.2]
  have hpt : (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun x : C ↦ g • x) (δ.1 t) : E →L[ℂ] E) =
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun x : C ↦ g • x) (γ.1 s) := by rw [hst]
  change b3_orient E ((mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun x : C ↦ g • x) (γ.1 s) : E →L[ℂ] E)
      (b3_velocity E C γ.1 s)) ((mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun x : C ↦ g • x) (δ.1 t) :
        E →L[ℂ] E) (b3_velocity E C δ.1 t)) = _
  rw [hpt]
  erw [b4cov_mfderiv_smul_apply hE, b4cov_mfderiv_smul_apply hE]
  exact b4cov_orient_smul _ _ _

theorem b4cov_crossings_map (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (g : G) (γ δ : b3_SmoothLoop E C) :
    b3_crossings E (b4cov_mapLoop (fun x : C ↦ g • x) (hG g) γ)
      (b4cov_mapLoop (fun x : C ↦ g • x) (hG g) δ) = b3_crossings E γ δ := by
  ext p
  simp only [b3_crossings, mem_ofPred_eq, b4cov_mapLoop_coe, Function.comp_apply,
    smul_left_cancel_iff]

/-- **Automorphisms preserve transversality.** -/
theorem b4cov_transverse_map (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) (g : G)
    (γ δ : b3_SmoothLoop E C) (h : b3_Transverse E γ δ) :
    b3_Transverse E (b4cov_mapLoop (fun x : C ↦ g • x) (hG g) γ)
      (b4cov_mapLoop (fun x : C ↦ g • x) (hG g) δ) := by
  intro s t hst
  have hst' : γ.1 s = δ.1 t := by
    simpa only [b4cov_mapLoop_coe, Function.comp_apply, smul_left_cancel_iff] using hst
  rw [b4cov_orient_map hE hG g γ δ s t hst']
  exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 (b4cov_scal_ne_zero hE hG g _))) (h s t hst')

/-- **Automorphisms preserve intersection numbers.** -/
theorem b4cov_intersection_map (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) (g : G)
    (γ δ : b3_SmoothLoop E C) :
    b3_intersection E (b4cov_mapLoop (fun x : C ↦ g • x) (hG g) γ)
      (b4cov_mapLoop (fun x : C ↦ g • x) (hG g) δ) = b3_intersection E γ δ := by
  rw [b3_intersection, b3_intersection, b4cov_crossings_map hG g γ δ]
  refine finsum_mem_congr rfl fun p hp ↦ ?_
  rw [b4cov_orient_map hE hG g γ δ p.1 p.2 hp.2.2, sign_mul,
    sign_pos (pow_pos (norm_pos_iff.2 (b4cov_scal_ne_zero hE hG g _)) 2), one_mul]

end Action

end HodgeLean.Foundations.Program
