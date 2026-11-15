import HodgeLean.Foundations.Program.RelativeFrameOperatorTransport

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

def rf4_smoothFormCoeff {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p q : ℕ} (v : rf2_smoothForms X p q) (e : OpenPartialHomeomorph X ℂ) (z : ℂ) : ℂ :=
  let y := e.symm z
  v.val y ⟨chartAt ℂ y y, (chartAt ℂ y).map_source (mem_chart_source ℂ y)⟩ *
    deriv (chartAt ℂ y ∘ e.symm) z ^ p * star (deriv (chartAt ℂ y ∘ e.symm) z) ^ q

theorem rf4_smoothFormCoeff_local {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {p q : ℕ} (v : rf2_smoothForms X p q)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (z : ℂ) (hz : z ∈ e.target) (x : X) (hx : e.symm z ∈ (chartAt ℂ x).source) :
    rf4_smoothFormCoeff v e z =
      rf2_extend X v.val x (chartAt ℂ x (e.symm z)) *
        deriv (chartAt ℂ x ∘ e.symm) z ^ p *
          star (deriv (chartAt ℂ x ∘ e.symm) z) ^ q := by
  let y := e.symm z
  have hy : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have hyt : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hy
  have hxt : chartAt ℂ x y ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hx
  have ht := v.property.2 y x ⟨chartAt ℂ y y, hyt⟩ ⟨chartAt ℂ x y, hxt⟩
    (by rw [(chartAt ℂ y).left_inv hy, (chartAt ℂ x).left_inv hx])
  have hd := rf4_atlas_transition_deriv e (chartAt ℂ y) (chartAt ℂ x) he
    (IsManifold.chart_mem_maximalAtlas y) (IsManifold.chart_mem_maximalAtlas x) z hz hy hx
  change v.val y ⟨chartAt ℂ y y, hyt⟩ *
    deriv (chartAt ℂ y ∘ e.symm) z ^ p * star (deriv (chartAt ℂ y ∘ e.symm) z) ^ q = _
  rw [ht]
  have hE : rf2_extend X v.val x (chartAt ℂ x (e.symm z)) =
      v.val x ⟨chartAt ℂ x y, hxt⟩ := by
    unfold rf2_extend
    exact dif_pos hxt
  rw [hE, hd]
  simp only [mul_pow, star_mul]
  dsimp only [y]
  ring

theorem rf4_smoothFormCoeff_smooth {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {p q : ℕ} (v : rf2_smoothForms X p q)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X) :
    ContDiffOn ℝ ∞ (rf4_smoothFormCoeff v e) e.target := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  let x := e.symm z
  let a := chartAt ℂ x
  let t : ℂ → ℂ := a ∘ e.symm
  have hx : e.symm z ∈ a.source := mem_chart_source ℂ x
  have htz : t z ∈ a.target := a.map_source hx
  obtain ⟨g, hg, hval⟩ := v.property.1 x
  have ht := rf4_atlas_transition_analytic e a he (IsManifold.chart_mem_maximalAtlas x) z hz hx
  have hG : ContDiffAt ℝ ∞ g (t z) :=
    (hg (t z) htz).contDiffAt (a.open_target.mem_nhds htz)
  have hlocal : ContDiffAt ℝ ∞ (fun u ↦ g (t u) * deriv t u ^ p * star (deriv t u) ^ q) z :=
    ((hG.comp z (ht.contDiffAt.restrict_scalars ℝ)).mul
      ((ht.deriv.contDiffAt.restrict_scalars ℝ).pow p)).mul
      ((Complex.conjCLE.contDiff.contDiffAt.comp z
        (ht.deriv.contDiffAt.restrict_scalars ℝ)).pow q)
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [(e.isOpen_inter_preimage_symm a.open_source).mem_nhds
    (show z ∈ e.target ∩ e.symm ⁻¹' a.source from ⟨hz, hx⟩)] with u hu
  rw [rf4_smoothFormCoeff_local v e he u hu.1 x hu.2]
  have htu : t u ∈ a.target := a.map_source hu.2
  change rf2_extend X v.val x (t u) * deriv t u ^ p * star (deriv t u) ^ q = _
  have hE : rf2_extend X v.val x (t u) = g (t u) := by
    unfold rf2_extend
    rw [dif_pos htu]
    exact hval ⟨t u, htu⟩
  rw [hE]

theorem rf4_smoothFormCoeff_dbar {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (v : rf2_smoothForms X 1 0)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (z : ℂ) (hz : z ∈ e.target) :
    rf4_smoothFormCoeff (⟨rf2_dbar10 X v.val, rf2_dbar10_smooth_aux X v⟩ :
      rf2_smoothForms X 1 1) e z = -wirtingerDbar (rf4_smoothFormCoeff v e) z := by
  let x := e.symm z
  let a := chartAt ℂ x
  let t : ℂ → ℂ := a ∘ e.symm
  let F := rf2_extend X v.val x
  have hx : e.symm z ∈ a.source := mem_chart_source ℂ x
  have htz : t z ∈ a.target := a.map_source hx
  have ht := rf4_atlas_transition_analytic e a he (IsManifold.chart_mem_maximalAtlas x) z hz hx
  have hF : DifferentiableAt ℝ F (t z) :=
    rf4_smoothCoeff_differentiableAt X v x ⟨t z, htz⟩
  have hv : rf4_smoothFormCoeff v e =ᶠ[𝓝 z] fun u ↦ F (t u) * deriv t u := by
    filter_upwards [(e.isOpen_inter_preimage_symm a.open_source).mem_nhds
      (show z ∈ e.target ∩ e.symm ⁻¹' a.source from ⟨hz, hx⟩)] with u hu
    simpa only [F, t, a, Function.comp_apply, pow_one, pow_zero, mul_one] using
      rf4_smoothFormCoeff_local v e he u hu.1 x hu.2
  have hd : wirtingerDbar (rf4_smoothFormCoeff v e) z =
      deriv t z * (star (deriv t z) * wirtingerDbar F (t z)) := by
    have hh : wirtingerDbar (rf4_smoothFormCoeff v e) z =
        wirtingerDbar (fun u ↦ F (t u) * deriv t u) z :=
      congrArg (fun L : ℂ →L[ℝ] ℂ ↦ antiLinearPart L 1) hv.fderiv_eq
    rw [hh]
    change wirtingerDbar (fun u ↦ (F ∘ t) u * deriv t u) z = _
    rw [rf2_wirtingerDbar_mul (hF.comp z (ht.differentiableAt.restrictScalars ℝ))
      (ht.deriv.differentiableAt.restrictScalars ℝ),
      rf2_wirtingerDbar_hol ht.deriv.differentiableAt, mul_zero, zero_add,
      rf2_wirtingerDbar_comp hF ht.differentiableAt]
  rw [rf4_smoothFormCoeff_local _ e he z hz x hx]
  have hE : rf2_extend X (rf2_dbar10 X v.val) x (t z) = -wirtingerDbar F (t z) := by
    unfold rf2_extend
    rw [dif_pos htz]
    rfl
  change rf2_extend X (rf2_dbar10 X v.val) x (t z) * deriv t z ^ 1 *
    star (deriv t z) ^ 1 = _
  rw [hE, hd, pow_one]
  ring

theorem rf4_smoothFormCoeff_transition {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {p q : ℕ} (v : rf2_smoothForms X p q)
    (e d : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (z w : ℂ) (hz : z ∈ e.target) (hw : w ∈ d.target)
    (hzw : e.symm z = d.symm w) :
    rf4_smoothFormCoeff v e z = rf4_smoothFormCoeff v d w *
      deriv (d ∘ e.symm) z ^ p * star (deriv (d ∘ e.symm) z) ^ q := by
  have hp : e.symm z ∈ d.source := by
    rw [hzw]
    exact d.map_target hw
  have hew : d (e.symm z) = w := by rw [hzw, d.right_inv hw]
  have hpoint : e.symm z ∈ (chartAt ℂ (e.symm z)).source := mem_chart_source ℂ _
  have hder := rf4_atlas_transition_deriv e d (chartAt ℂ (e.symm z)) he hd
    (IsManifold.chart_mem_maximalAtlas _) z hz hp hpoint
  rw [hew] at hder
  have hbase := congrArg (fun y : X ↦ v.val y
    ⟨chartAt ℂ y y, (chartAt ℂ y).map_source (mem_chart_source ℂ y)⟩) hzw
  simp only [rf4_smoothFormCoeff]
  rw [hbase, hder]
  simp only [hzw, mul_pow, star_mul]
  ring

theorem rf4_atlas_inverse_deriv {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) (hz : z ∈ e.target) :
    deriv (e ∘ e.symm) z = 1 := by
  have he : e ∘ e.symm =ᶠ[𝓝 z] id := by
    filter_upwards [e.open_target.mem_nhds hz] with u hu
    exact e.right_inv hu
  rw [he.deriv_eq]
  exact deriv_id z

def rf4_smoothFormCoeffLinear {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (p q : ℕ) :
    rf2_smoothForms X p q →ₗ[ℂ] (ℂ → ℂ) where
  toFun v := rf4_smoothFormCoeff v e
  map_add' v w := by
    funext z
    simp only [rf4_smoothFormCoeff, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c v := by
    funext z
    simp only [rf4_smoothFormCoeff, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

theorem rf4_smoothFormCoeff_tensor {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {p q : ℕ} (v : rf2_smoothForms X p q)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (f : ℂ → ℂ) (hv : v.val = rf4_chartTensor e f p q) (z : ℂ) (hz : z ∈ e.target) :
    rf4_smoothFormCoeff v e z = f z := by
  classical
  let y := e.symm z
  let a := chartAt ℂ y
  have hy : y ∈ a.source := mem_chart_source ℂ y
  have hyt : a y ∈ a.target := a.map_source hy
  have hp : y ∈ e.source := e.map_target hz
  have hd := rf4_atlas_transition_deriv e a e he (IsManifold.chart_mem_maximalAtlas y)
    he z hz hy hp
  rw [rf4_atlas_inverse_deriv e z hz] at hd
  have hval : rf4_chartTensor e f p q y ⟨a y, hyt⟩ =
      f z * deriv (e ∘ a.symm) (a y) ^ p * star (deriv (e ∘ a.symm) (a y)) ^ q := by
    change (if a.symm (a y) ∈ e.source then
      f (e (a.symm (a y))) * deriv (e ∘ a.symm) (a y) ^ p *
        star (deriv (e ∘ a.symm) (a y)) ^ q else 0) = _
    rw [a.left_inv hy, if_pos hp]
    have hey : e y = z := e.right_inv hz
    rw [hey]
  change v.val y ⟨a y, hyt⟩ * deriv (a ∘ e.symm) z ^ p *
    star (deriv (a ∘ e.symm) z) ^ q = _
  rw [hv, hval]
  have hnum (c A B : ℂ) (h : A * B = 1) :
      c * A ^ p * star A ^ q * B ^ p * star B ^ q = c := by
    calc
      _ = c * (A * B) ^ p * star (A * B) ^ q := by
        simp only [mul_pow, star_mul]
        ring
      _ = c := by simp only [h, one_pow, star_one, mul_one]
  exact hnum _ _ _ hd.symm

theorem rf4_smoothFormCoeff_bdd {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {p q : ℕ} (v : rf2_smoothForms X p q)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (K : Set ℂ) (hK : IsCompact K) (hs : K ⊆ e.target) :
    BddAbove ((fun z ↦ ‖rf4_smoothFormCoeff v e z‖) '' K) := by
  exact hK.bddAbove_image ((rf4_smoothFormCoeff_smooth v e he).continuousOn.mono hs).norm

end HodgeLean.Foundations.Program
