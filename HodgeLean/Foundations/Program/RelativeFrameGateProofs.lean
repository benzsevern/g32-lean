import HodgeLean.Foundations.Program.RelativeFrameGateDefs

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program
local instance rf2_decidableProofs (p : Prop) : Decidable p := Classical.propDecidable p

theorem rf2_bddHol_closed {U : Set ℂ} (hU : IsOpen U) :
    IsClosed (b63r_bddHol U : Set (U →ᵇ ℂ)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro F f hF hlim
  choose g hg he using hF
  let g₀ : ℂ → ℂ := fun z ↦ if hz : z ∈ U then f ⟨z, hz⟩ else 0
  refine ⟨g₀, ?_, ?_⟩
  · have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
    have hu' : TendstoUniformlyOn g g₀ atTop U := by
      rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
      have he' : (fun n (z : U) ↦ g n z) = (fun n (z : U) ↦ F n z) := by
        funext n z
        exact (he n z).symm
      rw [he']
      have he₀ : g₀ ∘ (Subtype.val : U → ℂ) = (fun z : U ↦ f z) := by
        funext z
        exact dif_pos z.property
      rw [he₀]
      exact hu
    exact hu'.tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall hg) hU
  · intro z
    simp only [g₀, dite_eq_left z.property]

theorem rf2_bddForm_banach_aux {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (P : rf2_PieceCover C O) :
    IsClosed (rf2_bddForm P : Set (∀ i, b63r_bddHol (P.piece i))) ∧
      CompleteSpace (rf2_bddForm P) := by
  have hf : IsClosed (rf2_bddForm P : Set (∀ i, b63r_bddHol (P.piece i))) := by
    change IsClosed {f : ∀ i, b63r_bddHol (P.piece i) | ∀ i j (z : P.piece i) (w : P.piece j),
      (P.chart i).symm z = (P.chart j).symm w →
      (f i : P.piece i →ᵇ ℂ) z = (f j : P.piece j →ᵇ ℂ) w *
        deriv (P.chart j ∘ (P.chart i).symm) z}
    simp only [setOf_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro z
    apply isClosed_iInter
    intro w
    apply isClosed_iInter
    intro h
    apply isClosed_eq <;> fun_prop
  letI : ∀ i, CompleteSpace (b63r_bddHol (P.piece i)) :=
    fun i ↦ (rf2_bddHol_closed (P.isOpen i)).completeSpace_coe
  exact ⟨hf, hf.completeSpace_coe⟩

theorem rf2_bddForm_coeff_bound_aux {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (P : rf2_PieceCover C O) (i : Fin P.n) :
    ‖rf2_bddForm_coeff P i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖f.val i‖ ≤ 1 * ‖f.val‖
  simpa only [one_mul] using (norm_le_pi_norm f.val i)

theorem rf2_wirtingerDbar_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ → ℂ} (ha : ContDiffOn ℝ ∞ a U) :
    ContDiffOn ℝ ∞ (wirtingerDbar a) U := by
  unfold wirtingerDbar
  exact (antiLinearPart.contDiff.comp_contDiffOn
    (ha.fderiv_of_isOpen hU (by simp))).clm_apply contDiffOn_const

theorem rf2_antiLinearPart_scalar (L : ℂ →L[ℝ] ℂ) (a : ℂ) :
    antiLinearPart L a = star a * antiLinearPart L 1 := by
  have he := RiemannRochAna_antilinear (E := ℂ) L a 1 0
  simpa only [smul_eq_mul, mul_one, add_zero, map_zero, mul_zero, zero_div,
    antiLinearPart_apply, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat,
    div_eq_mul_inv, zero_mul, add_zero, mul_comm (2⁻¹ : ℂ)] using he

theorem rf2_wirtingerDbar_comp {g t : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g (t z)) (ht : DifferentiableAt ℂ t z) :
    wirtingerDbar (g ∘ t) z = star (deriv t z) * wirtingerDbar g (t z) := by
  unfold wirtingerDbar
  rw [fderiv_comp z hg (ht.restrictScalars ℝ), ht.fderiv_restrictScalars ℝ,
    antiLinearPart_comp_restrictScalars]
  change antiLinearPart (fderiv ℝ g (t z)) ((fderiv ℂ t z) 1) = _
  rw [fderiv_eq_deriv_mul, mul_one, rf2_antiLinearPart_scalar]

theorem rf2_wirtingerDbar_mul {g h : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) (hh : DifferentiableAt ℝ h z) :
    wirtingerDbar (fun z ↦ g z * h z) z =
      g z * wirtingerDbar h z + h z * wirtingerDbar g z := by
  simp only [wirtingerDbar, fderiv_fun_mul hg hh, antiLinearPart_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat, mul_one]
  ring

theorem rf2_wirtingerDbar_hol {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) : wirtingerDbar g z = 0 := by
  unfold wirtingerDbar
  rw [hg.fderiv_restrictScalars ℝ, antiLinearPart_restrictScalars]
  rfl

theorem rf2_chart_transition_analytic (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (x y : C) (z : ℂ)
    (hz : z ∈ (chartAt ℂ x).target)
    (hy : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source) :
    AnalyticAt ℂ (chartAt ℂ y ∘ (chartAt ℂ x).symm) z := by
  simpa only [extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp] using
    b4cov_analyticAt_chart (id : C → C) contMDiff_id x y z
      (by simpa only [mfld_simps] using hz)
      (by simpa only [mfld_simps] using hy)

theorem rf2_dbar10_smooth_aux (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (v : rf2_smoothForms C 1 0) :
    rf2_dbar10 C v.val ∈ rf2_smoothForms C 1 1 := by
  choose g hg he using v.property.1
  have hder (x : C) (z : (chartAt ℂ x).target) :
      wirtingerDbar (rf2_extend C v.val x) z = wirtingerDbar (g x) z := by
    have heq : rf2_extend C v.val x =ᶠ[𝓝 (z : ℂ)] g x := by
      filter_upwards [(chartAt ℂ x).open_target.mem_nhds z.property] with u hu
      simp only [rf2_extend, dite_eq_left hu, he x ⟨u, hu⟩]
    exact congrArg (fun L : ℂ →L[ℝ] ℂ ↦ antiLinearPart L 1) heq.fderiv_eq
  constructor
  · intro x
    refine ⟨fun z ↦ -wirtingerDbar (g x) z,
      (rf2_wirtingerDbar_contDiffOn (chartAt ℂ x).open_target (hg x)).neg, ?_⟩
    intro z
    exact congrArg Neg.neg (hder x z)
  · intro x y z w hzw
    let t : ℂ → ℂ := chartAt ℂ y ∘ (chartAt ℂ x).symm
    have hy : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source := by
      rw [hzw]
      exact (chartAt ℂ y).map_target w.property
    have htw : t z = w := by
      dsimp [t]
      rw [hzw, (chartAt ℂ y).right_inv w.property]
    have ht : AnalyticAt ℂ t z := rf2_chart_transition_analytic C x y z z.property hy
    have hgy : DifferentiableAt ℝ (g y) (t z) := by
      rw [htw]
      exact ((hg y w w.property).contDiffAt
        ((chartAt ℂ y).open_target.mem_nhds w.property)).differentiableAt (by simp)
    have heq : g x =ᶠ[𝓝 (z : ℂ)] (fun u ↦ g y (t u) * deriv t u) := by
      let e := (chartAt ℂ x).symm.trans (chartAt ℂ y)
      have hz : (z : ℂ) ∈ e.source := ⟨z.property, hy⟩
      filter_upwards [e.open_source.mem_nhds hz] with u hu
      have htu : t u ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hu.2
      have hh := v.property.2 x y ⟨u, hu.1⟩ ⟨t u, htu⟩
        ((chartAt ℂ y).left_inv hu.2).symm
      simpa only [he, pow_one, pow_zero, mul_one] using hh
    have hd : wirtingerDbar (g x) z =
        deriv t z * (star (deriv t z) * wirtingerDbar (g y) (t z)) := by
      have hh : wirtingerDbar (g x) z =
          wirtingerDbar (fun u ↦ g y (t u) * deriv t u) z :=
        congrArg (fun L : ℂ →L[ℝ] ℂ ↦ antiLinearPart L 1) heq.fderiv_eq
      rw [hh]
      change wirtingerDbar (fun u ↦ (g y ∘ t) u * deriv t u) (z : ℂ) = _
      rw [rf2_wirtingerDbar_mul (hgy.comp (z : ℂ) (ht.differentiableAt.restrictScalars ℝ))
        (ht.deriv.differentiableAt.restrictScalars ℝ),
        rf2_wirtingerDbar_hol ht.deriv.differentiableAt, mul_zero, zero_add]
      rw [rf2_wirtingerDbar_comp hgy ht.differentiableAt]
    change -wirtingerDbar (rf2_extend C v.val x) z =
      -wirtingerDbar (rf2_extend C v.val y) w * deriv t z ^ 1 * star (deriv t z) ^ 1
    rw [hder x z, hder y w, hd, htw, pow_one, pow_one]
    ring

local instance rf2_tangentCharted (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] : ChartedSpace (ℂ × ℂ) (TangentBundle 𝓘(ℂ, ℂ) C) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ℂ) (TangentBundle 𝓘(ℂ, ℂ) C))

def rf2_coeffToTangent (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] :
    rf2_smoothForms C 0 1 →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) C → ℂ) where
  toFun f p := f.val p.1 ⟨chartAt ℂ p.1 p.1, mem_chart_target ℂ p.1⟩ * (starRingEnd ℂ) p.2
  map_add' := by intros; ext p; exact add_mul _ _ _
  map_smul' := by intros; ext p; exact mul_assoc _ _ _

theorem rf2_coeffToTangent_fibre (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (f : rf2_smoothForms C 0 1)
    (x : C) (a v w : ℂ) :
    rf2_coeffToTangent C f ⟨x, a • v + w⟩ =
      star a * rf2_coeffToTangent C f ⟨x, v⟩ + rf2_coeffToTangent C f ⟨x, w⟩ := by
  change _ * star (a * v + w) = _
  rw [star_add, star_mul]
  change _ = star a * (_ * star v) + _ * star w
  ring

theorem rf2_coeffToTangent_chartVec (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (f : rf2_smoothForms C 0 1)
    (x : C) (z : (chartAt ℂ x).target) (v : ℂ) :
    rf2_coeffToTangent C f (b3Forms_chartVec x v z) = f.val x z * star v := by
  let y : C := (chartAt ℂ x).symm z
  have he := f.property.2 x y z
    ⟨chartAt ℂ y y, mem_chart_target ℂ y⟩ (by
      exact ((chartAt ℂ y).left_inv (mem_chart_source ℂ y)).symm)
  simp only [pow_zero, pow_one, mul_one] at he
  change f.val y ⟨chartAt ℂ y y, mem_chart_target ℂ y⟩ *
    star (fderiv ℂ (b3Forms_tr (E := ℂ) x y) (z : ℂ) v) = _
  rw [fderiv_eq_deriv_mul, star_mul, he]
  simp only [b3Forms_tr]
  ring

theorem rf2_tangentChart_symm (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (p : TangentBundle 𝓘(ℂ, ℂ) C)
    (u : ℂ × ℂ) (hu : u.1 ∈ (chartAt ℂ p.1).target) :
    (chartAt (ℂ × ℂ) p).symm u = b3Forms_chartVec p.1 u.2 u.1 := by
  change (⟨(chartAt ℂ p.1).symm u.1,
    (tangentBundleCore 𝓘(ℂ, ℂ) C).coordChange (achart ℂ p.1)
      (achart ℂ ((chartAt ℂ p.1).symm u.1)) ((chartAt ℂ p.1).symm u.1) u.2⟩ :
      TangentBundle 𝓘(ℂ, ℂ) C) = _
  simp only [tangentBundleCore_coordChange, mfld_simps,
    (chartAt ℂ p.1).right_inv hu, b3Forms_chartVec, b3Forms_tr, fderivWithin_univ]

attribute [local instance] b3Forms_isManifold_real

theorem rf2_coeffToTangent_smooth (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (f : rf2_smoothForms C 0 1) :
    ContMDiff 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞ (rf2_coeffToTangent C f) := by
  intro p
  obtain ⟨g, hg, he⟩ := f.property.1 p.1
  let q : ℂ × ℂ := chartAt (ℂ × ℂ) p p
  have hq : q.1 ∈ (chartAt ℂ p.1).target := mem_chart_target ℂ p.1
  have hA : ContDiffAt ℝ ∞ (fun u : ℂ × ℂ ↦ g u.1 * star u.2) q :=
    ((hg q.1 hq).contDiffAt ((chartAt ℂ p.1).open_target.mem_nhds hq)).comp q contDiffAt_fst |>.mul
      (Complex.conjCLE.contDiff.contDiffAt.comp q contDiffAt_snd)
  rw [contMDiffAt_iff_source]
  simp only [ModelWithCorners.tangent, ← modelWithCornersSelf_prod, mfld_simps]
  apply hA.contMDiffAt.congr_of_eventuallyEq
  filter_upwards [(chartAt ℂ p.1).open_target.preimage continuous_fst |>.mem_nhds hq] with u hu
  change rf2_coeffToTangent C f ((chartAt (ℂ × ℂ) p).symm u) = g u.1 * star u.2
  rw [rf2_tangentChart_symm C p u hu, rf2_coeffToTangent_chartVec C f p.1 ⟨u.1, hu⟩ u.2,
    he ⟨u.1, hu⟩]

theorem rf2_chartVec_transition (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (x y : C) (z : (chartAt ℂ x).target)
    (w : (chartAt ℂ y).target)
    (hzw : (chartAt ℂ x).symm z = (chartAt ℂ y).symm w) :
    b3Forms_chartVec x (1 : ℂ) z =
      b3Forms_chartVec y (deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z) w := by
  let p : C := (chartAt ℂ y).symm w
  have hy : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source := by
    rw [hzw]
    exact (chartAt ℂ y).map_target w.property
  have hp : (chartAt ℂ x).symm z ∈ (chartAt ℂ p).source := by
    rw [hzw]
    exact mem_chart_source ℂ p
  have ht : b3Forms_tr x y (z : ℂ) = w := by
    change chartAt ℂ y ((chartAt ℂ x).symm z) = w
    rw [hzw, (chartAt ℂ y).right_inv w.property]
  have hd := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L 1)
    (b3Forms_fderiv_tr_comp_complex (x := x) (y := y) (z := p) ⟨z.property, hy⟩ hp)
  rw [ContinuousLinearMap.comp_apply, ht, fderiv_eq_deriv_mul, mul_one] at hd
  simp only [b3Forms_chartVec, hzw]
  congr 1

def rf2_tangentToCoeff (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] :
    b4c_Smooth01 ℂ C →ₗ[ℂ] rf2_smoothForms C 0 1 where
  toFun θ := ⟨fun x z ↦ θ.val (b3Forms_chartVec x (1 : ℂ) z), by
    constructor
    · intro x
      refine ⟨fun z ↦ θ.val (b3Forms_chartVec x (1 : ℂ) z), ?_, fun _ ↦ rfl⟩
      have hc : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ).tangent ∞
          (b3Forms_chartVec x (1 : ℂ)) (chartAt ℂ x).target := by
        intro u hu
        have h := b3Forms_contMDiffOn_chartVec x (1 : ℂ) u hu
        simp only [ModelWithCorners.tangent, ← modelWithCornersSelf_prod] at h ⊢
        exact (b3A_contMDiffWithinAt_real h).of_le (by simp)
      exact (θ.property.1.comp_contMDiffOn hc).contDiffOn
    · intro x y z w hzw
      simp only [pow_zero, pow_one, mul_one]
      rw [rf2_chartVec_transition C x y z w hzw]
      let a := deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) (z : ℂ)
      have hθ := θ.property.2 ((chartAt ℂ y).symm w) a
        ((b3Forms_chartVec y (1 : ℂ) w).2) 0
      simp only [add_zero, RiemannRochAna_zero_fibre θ, add_zero] at hθ
      simp only [b3Forms_chartVec, fderiv_eq_smul_deriv, one_smul] at hθ ⊢
      change θ.val ⟨(chartAt ℂ y).symm w,
        a * deriv (b3Forms_tr (E := ℂ) y ((chartAt ℂ y).symm w)) (w : ℂ)⟩ =
        star a * θ.val ⟨(chartAt ℂ y).symm w,
          deriv (b3Forms_tr (E := ℂ) y ((chartAt ℂ y).symm w)) (w : ℂ)⟩ at hθ
      change θ.val ⟨(chartAt ℂ y).symm w,
        a * deriv (b3Forms_tr (E := ℂ) y ((chartAt ℂ y).symm w)) (w : ℂ)⟩ =
        θ.val ⟨(chartAt ℂ y).symm w,
          deriv (b3Forms_tr (E := ℂ) y ((chartAt ℂ y).symm w)) (w : ℂ)⟩ * star a
      exact hθ.trans (mul_comm _ _)⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def rf2_coeffToSmoothTangent (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] :
    rf2_smoothForms C 0 1 →ₗ[ℂ] b4c_Smooth01 ℂ C :=
  (rf2_coeffToTangent C).codRestrict (b4c_Smooth01 ℂ C) (fun f ↦
    ⟨rf2_coeffToTangent_smooth C f, rf2_coeffToTangent_fibre C f⟩)

def rf2_smooth01Equiv (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] :
    rf2_smoothForms C 0 1 ≃ₗ[ℂ] b4c_Smooth01 ℂ C where
  toLinearMap := rf2_coeffToSmoothTangent C
  invFun := rf2_tangentToCoeff C
  left_inv f := by
    apply Subtype.ext
    funext x z
    change rf2_coeffToTangent C f (b3Forms_chartVec x (1 : ℂ) z) = f.val x z
    simpa only [star_one, mul_one] using rf2_coeffToTangent_chartVec C f x z 1
  right_inv θ := by
    apply Subtype.ext
    funext p
    have hv : b3Forms_chartVec p.1 (1 : ℂ) (chartAt ℂ p.1 p.1) =
        (⟨p.1, (1 : ℂ)⟩ : TangentBundle 𝓘(ℂ, ℂ) C) := by
      simp only [b3Forms_chartVec, (chartAt ℂ p.1).left_inv (mem_chart_source ℂ p.1)]
      rw [(b3Forms_tr_self_eventuallyEq (mem_chart_target ℂ p.1)).fderiv_eq, fderiv_id]
      rw [(chartAt ℂ p.1).left_inv (mem_chart_source ℂ p.1)]
      rfl
    change θ.val (b3Forms_chartVec p.1 (1 : ℂ) (chartAt ℂ p.1 p.1)) * (starRingEnd ℂ) p.2 = θ.val p
    rw [hv]
    have hθ := θ.property.2 p.1 (p.2 : ℂ) (1 : ℂ) (0 : ℂ)
    simp only [smul_eq_mul, mul_one, add_zero, RiemannRochAna_zero_fibre θ, add_zero] at hθ
    change θ.val p = (starRingEnd ℂ) p.2 * θ.val ⟨p.1, (1 : ℂ)⟩ at hθ
    exact (mul_comm _ _).trans hθ.symm

theorem rf2_dbar_chart (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (u : b4c_SmoothFun ℂ C)
    (x : C) (z : (chartAt ℂ x).target) :
    b4c_dbar ℂ C u (b3Forms_chartVec x (1 : ℂ) z) =
      wirtingerDbar ((u : C → ℂ) ∘ (chartAt ℂ x).symm) z := by
  let p : C := (chartAt ℂ x).symm z
  let t : ℂ → ℂ := chartAt ℂ p ∘ (chartAt ℂ x).symm
  let k : ℂ → ℂ := (u : C → ℂ) ∘ (chartAt ℂ p).symm
  have ht : AnalyticAt ℂ t z :=
    rf2_chart_transition_analytic C x p z z.property (mem_chart_source ℂ p)
  have hk : DifferentiableAt ℝ k (t z) :=
    differentiableAt_comp_chartAt_symm (by simp) (u.property p)
  have heq : (u : C → ℂ) ∘ (chartAt ℂ x).symm =ᶠ[𝓝 (z : ℂ)] k ∘ t := by
    filter_upwards [(b3Forms_isOpen_trDom x p).mem_nhds
      (b3Forms_mem_trDom_self z.property)] with w hw
    simp only [k, t, Function.comp_apply, (chartAt ℂ p).left_inv hw.2]
  have hr : wirtingerDbar ((u : C → ℂ) ∘ (chartAt ℂ x).symm) z =
      star (deriv t z) * wirtingerDbar k (t z) := by
    unfold wirtingerDbar
    rw [heq.fderiv_eq]
    exact rf2_wirtingerDbar_comp hk ht.differentiableAt
  rw [hr]
  have hm := mfderiv_eq_fderiv_comp_chartAt_symm
    (u.property.mdifferentiable (by simp) p)
  let du : ℂ →L[ℝ] ℂ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (u : C → ℂ) p
  change (du ((fderiv ℂ t z) 1) + Complex.I * du (Complex.I * ((fderiv ℂ t z) 1))) / 2 = _
  have hdu : du = fderiv ℝ k (t z) := hm
  rw [hdu, fderiv_eq_deriv_mul, mul_one]
  have ha := rf2_antiLinearPart_scalar (fderiv ℝ k (t z)) (deriv t z)
  simpa only [wirtingerDbar, antiLinearPart_apply, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_ofNat, div_eq_mul_inv,
    mul_comm (2⁻¹ : ℂ), smul_eq_mul] using ha

def rf2_dbar00Linear (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] : b4c_SmoothFun ℂ C →ₗ[ℂ] rf2_smoothForms C 0 1 :=
  (rf2_tangentToCoeff C).comp
    ((RiemannRochAna_dbarLinear (E := ℂ) (C := C)).codRestrict (b4c_Smooth01 ℂ C)
      (fun u ↦ b4c_dbar_mem u))

theorem rf2_dbar00Linear_val (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (u : b4c_SmoothFun ℂ C) :
    (rf2_dbar00Linear C u).val = rf2_dbar00 C u := by
  funext x z
  exact rf2_dbar_chart C u x z

theorem rf2_dbar00_image_span (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] :
    (Submodule.span ℂ (rf2_dbar00 C '' (b4c_SmoothFun ℂ C : Set (C → ℂ))) :
      Set (rf2_Coeff C)) = rf2_dbar00 C '' (b4c_SmoothFun ℂ C : Set (C → ℂ)) := by
  let L := (rf2_smoothForms C 0 1).subtype.comp (rf2_dbar00Linear C)
  have he : rf2_dbar00 C '' (b4c_SmoothFun ℂ C : Set (C → ℂ)) = (L.range : Set _) := by
    ext f
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rf2_dbar00Linear_val C ⟨u, hu⟩⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.property, (rf2_dbar00Linear_val C u).symm⟩
  rw [he, Submodule.span_eq]

theorem rf2_dolbeault01_compare_aux (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] :
    Nonempty (((rf2_smoothForms C 0 1) ⧸ rf2_boundaries01 C) ≃ₗ[ℂ]
      b4c_Dolbeault01 ℂ C) := by
  let e := rf2_smooth01Equiv C
  let Q : Submodule ℂ (b4c_Smooth01 ℂ C) :=
    (Submodule.span ℂ (b4c_dbar ℂ C '' (b4c_SmoothFun ℂ C : Set (C → ℂ)))).comap
      (b4c_Smooth01 ℂ C).subtype
  have hmem (f : rf2_smoothForms C 0 1) :
      f ∈ rf2_boundaries01 C ↔ e f ∈ Q := by
    change f.val ∈ Submodule.span ℂ (rf2_dbar00 C '' (b4c_SmoothFun ℂ C : Set (C → ℂ))) ↔
      (e f).val ∈ Submodule.span ℂ (b4c_dbar ℂ C '' (b4c_SmoothFun ℂ C : Set (C → ℂ)))
    rw [← SetLike.mem_coe, ← SetLike.mem_coe, rf2_dbar00_image_span C,
      b4c_dbar_image_eq (E := ℂ) (C := C) (Module.finrank_self ℂ)]
    constructor
    · rintro ⟨u, hu, he⟩
      refine ⟨u, hu, ?_⟩
      have hf : rf2_dbar00Linear C ⟨u, hu⟩ = f :=
        Subtype.ext ((rf2_dbar00Linear_val C ⟨u, hu⟩).trans he)
      rw [← hf]
      exact (congrArg Subtype.val (e.apply_symm_apply ⟨b4c_dbar ℂ C u, b4c_dbar_mem ⟨u, hu⟩⟩)).symm
    · rintro ⟨u, hu, he⟩
      refine ⟨u, hu, ?_⟩
      have hf : (e f) = ⟨b4c_dbar ℂ C u, b4c_dbar_mem ⟨u, hu⟩⟩ := Subtype.ext he.symm
      have hi := congrArg (fun θ ↦ (e.symm θ).val) hf
      rw [e.symm_apply_apply] at hi
      exact (rf2_dbar00Linear_val C ⟨u, hu⟩).symm.trans hi.symm
  have hmap : (rf2_boundaries01 C).map e.toLinearMap = Q := by
    ext θ
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (hmem f).mp hf
    · intro hθ
      exact ⟨e.symm θ, (hmem _).mpr (by simpa only [e.apply_symm_apply] using hθ),
        e.apply_symm_apply θ⟩
  exact ⟨Submodule.Quotient.equiv (rf2_boundaries01 C) Q e hmap⟩

theorem rf2_cutoff (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Metric.ball 0 R ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, χ z = 1) := by
  let b : ContDiffBump (0 : ℂ) := ⟨r, (r + R) / 2, hr, by linarith⟩
  refine ⟨fun z ↦ (b z : ℂ), Complex.ofRealCLM.contDiff.comp b.contDiff, ?_, ?_, ?_⟩
  · exact b.hasCompactSupport.comp_left (g := fun t : ℝ ↦ (t : ℂ)) Complex.ofReal_zero
  · have hs : tsupport (fun z ↦ (b z : ℂ)) ⊆ tsupport b :=
      tsupport_comp_subset (g := fun t : ℝ ↦ (t : ℂ)) (by simp) b
    exact hs.trans (by rw [b.tsupport_eq]; exact Metric.closedBall_subset_ball (by change (r + R) / 2 < R; linarith))
  · intro z hz
    change (b z : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)]
    exact Complex.ofReal_one

theorem rf2_cutoff_extend (a χ : ℂ → ℂ) (R : ℝ)
    (ha : ContDiffOn ℝ ∞ a (Metric.ball 0 R)) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Metric.ball 0 R) :
    ContDiff ℝ ∞ (fun z ↦ if z ∈ Metric.ball (0 : ℂ) R then -(χ z * a z) else 0) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ Metric.ball (0 : ℂ) R
  · apply ((hχ.contDiffAt.mul ((ha z hz).contDiffAt
        (Metric.isOpen_ball.mem_nhds hz))).neg).congr_of_eventuallyEq
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact if_pos hw
  · have hz' : z ∉ tsupport χ := fun h ↦ hz (hs h)
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℂ ↦ (0 : ℂ)) z).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz'] with w hw
    have hw' := image_eq_zero_of_notMem_tsupport hw
    simp only [hw', zero_mul, neg_zero, ite_self]

theorem rf2_local_cauchy_aux (a : ℂ → ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (ha : ContDiffOn ℝ ∞ a (Metric.ball 0 R)) :
    ∃ χ ψ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧ ContDiff ℝ ∞ ψ ∧
      HasCompactSupport χ ∧ HasCompactSupport ψ ∧
      tsupport χ ⊆ Metric.ball 0 R ∧ tsupport ψ ⊆ Metric.ball 0 ((r + R) / 2) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ((r + R) / 2), χ z = 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, ψ z = 1) ∧
      let v := fun z ↦ ψ z * cauchyTransform
        (fun ζ ↦ if ζ ∈ Metric.ball (0 : ℂ) R then -(χ ζ * a ζ) else 0) z
      ContDiff ℝ ∞ v ∧ tsupport v ⊆ Metric.ball 0 R ∧
        ∀ z ∈ Metric.ball (0 : ℂ) r, -wirtingerDbar v z = a z := by
  obtain ⟨χ, hχ, hcχ, hsχ, hoχ⟩ := rf2_cutoff ((r + R) / 2) R (by linarith) (by linarith)
  obtain ⟨ψ, hψ, hcψ, hsψ, hoψ⟩ := rf2_cutoff r ((r + R) / 2) hr (by linarith)
  let g : ℂ → ℂ := fun ζ ↦ if ζ ∈ Metric.ball (0 : ℂ) R then -(χ ζ * a ζ) else 0
  have hg : ContDiff ℝ ∞ g := rf2_cutoff_extend a χ R ha hχ hsχ
  have hsg : Function.support g ⊆ Function.support χ := by
    intro z hz
    by_contra hzχ
    have hzχ' : χ z = 0 := by simpa only [Function.mem_support, not_not] using hzχ
    exact hz (by simp only [g, hzχ', zero_mul, neg_zero, ite_self])
  have hcg : HasCompactSupport g := hcχ.mono hsg
  refine ⟨χ, ψ, hχ, hψ, hcχ, hcψ, hsχ, hsψ, hoχ, hoψ, ?_⟩
  refine ⟨hψ.mul (spec_contDiff_cauchyTransform hg hcg), ?_, ?_⟩
  · exact tsupport_mul_subset_left.trans (hsψ.trans (Metric.ball_subset_ball (by linarith)))
  · intro z hz
    have he : (fun z ↦ ψ z * cauchyTransform g z) =ᶠ[𝓝 z] cauchyTransform g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      rw [hoψ w hw, one_mul]
    unfold wirtingerDbar
    rw [he.fderiv_eq]
    change -wirtingerDbar (cauchyTransform g) z = a z
    rw [spec_wirtingerDbar_cauchyTransform (hg.of_le (by simp)) hcg]
    have hzR : z ∈ Metric.ball (0 : ℂ) R := Metric.ball_subset_ball hrR.le hz
    have hzM : z ∈ Metric.ball (0 : ℂ) ((r + R) / 2) :=
      Metric.ball_subset_ball (by linarith) hz
    simp only [g, if_pos hzR, hoχ z hzM, one_mul, neg_neg]

theorem rf2_smoothForms_star (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {p q : ℕ} (f : rf2_smoothForms C p q) :
    (fun x z ↦ star (f.val x z)) ∈ rf2_smoothForms C q p := by
  constructor
  · intro x
    obtain ⟨g, hg, he⟩ := f.property.1 x
    refine ⟨fun z ↦ star (g z), Complex.conjCLE.contDiff.comp_contDiffOn hg, ?_⟩
    intro z
    exact congrArg star (he z)
  · intro x y z w h
    dsimp only
    rw [f.property.2 x y z w h]
    simp only [star_mul, star_pow, star_star]
    ring

theorem rf2_smoothForms_mul (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {p q r s : ℕ}
    (f : rf2_smoothForms C p q) (g : rf2_smoothForms C r s) :
    (fun x z ↦ f.val x z * g.val x z) ∈ rf2_smoothForms C (p + r) (q + s) := by
  constructor
  · intro x
    obtain ⟨a, ha, he⟩ := f.property.1 x
    obtain ⟨b, hb, hf⟩ := g.property.1 x
    refine ⟨fun z ↦ a z * b z, ha.mul hb, ?_⟩
    intro z
    dsimp only
    rw [he z, hf z]
  · intro x y z w h
    dsimp only
    rw [f.property.2 x y z w h, g.property.2 x y z w h]
    simp only [pow_add]
    ring

def rf2_scalarCoeffs (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (u : b4c_SmoothFun ℂ C) : rf2_smoothForms C 0 0 := by
  refine ⟨fun x z ↦ u.val ((chartAt ℂ x).symm z), ?_⟩
  constructor
  · intro x
    refine ⟨u.val ∘ (chartAt ℂ x).symm, ?_, fun _ ↦ rfl⟩
    exact (u.property.comp_contMDiffOn
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := x))).contDiffOn
  · intro x y z w h
    dsimp only
    simp only [h, pow_zero, mul_one]

def rf2_chartSmoothScalar (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] (x : C) (g : ℂ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ (chartAt ℂ x).target) : b4c_SmoothFun ℂ C := by
  let f : C → ℂ := fun p ↦ if p ∈ (chartAt ℂ x).source then g (chartAt ℂ x p) else 0
  let S : Set C := (chartAt ℂ x).symm '' tsupport g
  have hSc : IsCompact S := hc.isCompact.image_of_continuousOn
    ((chartAt ℂ x).continuousOn_symm.mono hs)
  have hfs : Function.support f ⊆ S := by
    intro p hp
    by_cases hx : p ∈ (chartAt ℂ x).source
    · have hg' : g (chartAt ℂ x p) ≠ 0 := by simpa only [Function.mem_support, f, if_pos hx] using hp
      exact ⟨chartAt ℂ x p, subset_tsupport g hg', (chartAt ℂ x).left_inv hx⟩
    · exact False.elim (hp (by simp only [f, if_neg hx]))
  refine ⟨f, ?_⟩
  intro p
  by_cases hx : p ∈ (chartAt ℂ x).source
  · have hchart := (contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := x)).contMDiffAt
      ((chartAt ℂ x).open_source.mem_nhds hx)
    apply (hg.contDiffAt.contMDiffAt.comp p hchart).congr_of_eventuallyEq
    filter_upwards [(chartAt ℂ x).open_source.mem_nhds hx] with q hq
    exact if_pos hq
  · have hp : p ∉ S := by
      rintro ⟨u, hu, rfl⟩
      exact hx ((chartAt ℂ x).map_target (hs hu))
    apply (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hSc.isClosed.isOpen_compl.mem_nhds hp] with q hq
    by_contra hn
    exact hq (hfs hn)

theorem rf2_local_primitive (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] (x : C)
    (U : Set C) (hU : IsOpen U) (hx : x ∈ U) (τ : rf2_smoothForms C 1 1) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (chartAt ℂ x x) r ⊆
      (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' U ∧
      ∃ v : rf2_smoothForms C 1 0,
        (∀ y (z : (chartAt ℂ y).target), (chartAt ℂ y).symm z ∉ U → v.val y z = 0) ∧
        ∀ z : (chartAt ℂ x).target, (z : ℂ) ∈ Metric.ball (chartAt ℂ x x) r →
          τ.val x z = rf2_dbar10 C v.val x z := by
  let c : ℂ := chartAt ℂ x x
  have hV : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' U) :=
    (chartAt ℂ x).isOpen_inter_preimage_symm hU
  have hcV : c ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' U := by
    refine ⟨mem_chart_target ℂ x, ?_⟩
    change (chartAt ℂ x).symm (chartAt ℂ x x) ∈ U
    rwa [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hV c hcV
  let r := R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r]; linarith
  obtain ⟨g, hg, he⟩ := τ.property.1 x
  let a : ℂ → ℂ := fun z ↦ g (z + c)
  have ha : ContDiffOn ℝ ∞ a (Metric.ball 0 R) := by
    apply hg.comp (contDiffOn_id.add contDiffOn_const)
    intro z hz
    exact (hball (by simpa only [Function.id_def, Pi.add_apply, Metric.mem_ball, dist_eq_norm, add_sub_cancel_right,
      sub_zero] using hz)).1
  obtain ⟨χ, ψ, hχ, hψ, hcχ, hcψ, hsχ, hsψ, hoχ, hoψ, hv0, hs0, hsolve⟩ :=
    rf2_local_cauchy_aux a r R hr hrR ha
  let v0 : ℂ → ℂ := fun z ↦ ψ z * cauchyTransform
    (fun ζ ↦ if ζ ∈ Metric.ball (0 : ℂ) R then -(χ ζ * a ζ) else 0) z
  change ContDiff ℝ ∞ v0 at hv0
  change tsupport v0 ⊆ Metric.ball 0 R at hs0
  have hshift (k : ℂ → ℂ) (hk : tsupport k ⊆ Metric.ball 0 R) :
      tsupport (fun u ↦ k (u - c)) ⊆ Metric.ball c R := by
    apply (tsupport_comp_subset_preimage k (continuous_id.sub continuous_const)).trans
    intro u hu
    simpa only [Function.id_def, Pi.sub_apply, Metric.mem_ball, dist_eq_norm, sub_zero] using hk hu
  let V : ℂ → ℂ := fun u ↦ v0 (u - c)
  have hVd : ContDiff ℝ ∞ V := hv0.comp (contDiff_id.sub contDiff_const)
  have hVs : tsupport V ⊆ Metric.ball c R := hshift v0 hs0
  have hVc : HasCompactSupport V := (isCompact_closedBall c R).of_isClosed_subset
    (isClosed_tsupport V) (hVs.trans Metric.ball_subset_closedBall)
  let B : ℂ → ℂ := fun u ↦ χ (u - c) * u
  have hBd : ContDiff ℝ ∞ B := (hχ.comp (contDiff_id.sub contDiff_const)).mul contDiff_id
  have hBs : tsupport B ⊆ Metric.ball c R := tsupport_mul_subset_left.trans (hshift χ hsχ)
  have hBc : HasCompactSupport B := (isCompact_closedBall c R).of_isClosed_subset
    (isClosed_tsupport B) (hBs.trans Metric.ball_subset_closedBall)
  let f := rf2_chartSmoothScalar C x V hVd hVc (hVs.trans (hball.trans inter_subset_left))
  let h := rf2_chartSmoothScalar C x B hBd hBc (hBs.trans (hball.trans inter_subset_left))
  let hb : b4c_SmoothFun ℂ C :=
    ⟨fun p ↦ star (h.val p), Complex.conjCLE.contDiff.contMDiff.comp h.property⟩
  let φ : rf2_smoothForms C 1 0 :=
    ⟨fun y z ↦ star ((rf2_dbar00Linear C hb).val y z),
      rf2_smoothForms_star C (rf2_dbar00Linear C hb)⟩
  let v : rf2_smoothForms C 1 0 :=
    ⟨fun y z ↦ (rf2_scalarCoeffs C f).val y z * φ.val y z,
      rf2_smoothForms_mul C (rf2_scalarCoeffs C f) φ⟩
  have hrball : Metric.ball c r ⊆ Metric.ball c R := Metric.ball_subset_ball hrR.le
  have hval : ∀ u (hu : u ∈ Metric.ball c r), v.val x ⟨u, (hball (hrball hu)).1⟩ = V u := by
    intro u hu
    have huT := (hball (hrball hu)).1
    have hh : h.val ∘ (chartAt ℂ x).symm =ᶠ[𝓝 u] (id : ℂ → ℂ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hu] with w hw
      have hwT := (hball (hrball hw)).1
      change (if (chartAt ℂ x).symm w ∈ (chartAt ℂ x).source then
        B (chartAt ℂ x ((chartAt ℂ x).symm w)) else 0) = w
      rw [if_pos ((chartAt ℂ x).map_target hwT), (chartAt ℂ x).right_inv hwT]
      have hw0 : w - c ∈ Metric.ball (0 : ℂ) ((r + R) / 2) := by
        exact Metric.ball_subset_ball (show r ≤ (r + R) / 2 by linarith)
          (show w - c ∈ Metric.ball (0 : ℂ) r from by
            simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hw)
      change χ (w - c) * w = w
      rw [hoχ (w - c) hw0, one_mul]
    have hhb : hb.val ∘ (chartAt ℂ x).symm =ᶠ[𝓝 u] (starRingEnd ℂ : ℂ → ℂ) := by
      filter_upwards [hh] with w hw
      exact congrArg star hw
    have hdb : wirtingerDbar (hb.val ∘ (chartAt ℂ x).symm) u = 1 := by
      unfold wirtingerDbar
      rw [hhb.fderiv_eq]
      rw [show fderiv ℝ (starRingEnd ℂ) u = (Complex.conjCLE : ℂ →L[ℝ] ℂ) from Complex.conjCLE.fderiv]
      norm_num [antiLinearPart_apply, Complex.conjCLE_apply, Complex.I_mul_I]
    have hφ : φ.val x ⟨u, huT⟩ = 1 := by
      change star ((rf2_dbar00Linear C hb).val x ⟨u, huT⟩) = 1
      rw [rf2_dbar00Linear_val]
      change star (wirtingerDbar (hb.val ∘ (chartAt ℂ x).symm) u) = 1
      rw [hdb, star_one]
    change f.val ((chartAt ℂ x).symm u) * φ.val x ⟨u, huT⟩ = V u
    rw [hφ, mul_one]
    change (if (chartAt ℂ x).symm u ∈ (chartAt ℂ x).source then
      V (chartAt ℂ x ((chartAt ℂ x).symm u)) else 0) = V u
    rw [if_pos ((chartAt ℂ x).map_target huT), (chartAt ℂ x).right_inv huT]
  refine ⟨r, hr, hrball.trans hball, v, ?_, ?_⟩
  · intro y z hz
    change f.val ((chartAt ℂ y).symm z) * φ.val y z = 0
    have hf0 : f.val ((chartAt ℂ y).symm z) = 0 := by
      set p := (chartAt ℂ y).symm z
      change (if p ∈ (chartAt ℂ x).source then V (chartAt ℂ x p) else 0) = 0
      split_ifs with hp
      · by_contra hn
        have hpV := hVs (subset_tsupport V hn)
        have hpU := (hball hpV).2
        change (chartAt ℂ x).symm (chartAt ℂ x p) ∈ U at hpU
        rw [(chartAt ℂ x).left_inv hp] at hpU
        exact hz hpU
      · rfl
    rw [hf0, zero_mul]
  · intro z hz
    have hE : rf2_extend C v.val x =ᶠ[𝓝 (z : ℂ)] V := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with u hu
      change (if h : u ∈ (chartAt ℂ x).target then v.val x ⟨u, h⟩ else 0) = V u
      rw [dite_eq_left ((hball (hrball hu)).1)]
      exact hval u hu
    have hd : wirtingerDbar (rf2_extend C v.val x) z = wirtingerDbar V z :=
      congrArg (fun L : ℂ →L[ℝ] ℂ ↦ antiLinearPart L 1) hE.fderiv_eq
    have hDV : wirtingerDbar V z = wirtingerDbar v0 ((z : ℂ) - c) := by
      change wirtingerDbar (v0 ∘ (fun u : ℂ ↦ u - c)) (z : ℂ) = _
      have ht : DifferentiableAt ℂ (fun u : ℂ ↦ u - c) (z : ℂ) :=
        differentiableAt_id.sub_const c
      rw [rf2_wirtingerDbar_comp (g := v0) (t := fun u : ℂ ↦ u - c)
        (z := (z : ℂ)) (hv0.differentiable (by simp)).differentiableAt ht]
      simp only [deriv_sub_const, deriv_id'', star_one, one_mul]
    change τ.val x z = -wirtingerDbar (rf2_extend C v.val x) z
    rw [he z, hd, hDV]
    have hz0 : (z : ℂ) - c ∈ Metric.ball (0 : ℂ) r := by
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hz
    simpa only [a, sub_add_cancel] using (hsolve ((z : ℂ) - c) hz0).symm

theorem rf2_dbar10_sum (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {ι : Type*} (s : Finset ι)
    (v : ι → rf2_smoothForms C 1 0) :
    rf2_dbar10 C (∑ i ∈ s, v i).val = ∑ i ∈ s, rf2_dbar10 C (v i).val := by
  have hcoe : (∑ i ∈ s, v i).val = ∑ i ∈ s, (v i).val :=
    map_sum (rf2_smoothForms C 1 0).subtype v s
  rw [hcoe]
  funext x z
  have he : rf2_extend C (∑ i ∈ s, (v i).val) x =
      fun u ↦ ∑ i ∈ s, rf2_extend C (v i).val x u := by
    funext u
    by_cases hu : u ∈ (chartAt ℂ x).target
    · simp only [rf2_extend, dite_eq_left hu, Finset.sum_apply]
    · simp only [rf2_extend, dite_eq_right hu, Finset.sum_const_zero]
  have hd (i : ι) (_ : i ∈ s) : DifferentiableAt ℝ (rf2_extend C (v i).val x) z := by
    obtain ⟨g, hg, hv⟩ := (v i).property.1 x
    apply (((hg z z.property).contDiffAt
      ((chartAt ℂ x).open_target.mem_nhds z.property)).differentiableAt (by simp)).congr_of_eventuallyEq
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds z.property] with u hu
    simp only [rf2_extend, dite_eq_left hu]
    exact hv ⟨u, hu⟩
  change -antiLinearPart (fderiv ℝ (rf2_extend C (∑ i ∈ s, (v i).val) x) z) 1 = _
  rw [he, fderiv_fun_sum hd]
  simp only [map_sum, ContinuousLinearMap.sum_apply, Finset.sum_apply,
    Finset.sum_neg_distrib, rf2_dbar10, wirtingerDbar]

theorem rf2_dbar10_zero_on (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (U : Set C) (hU : IsOpen U) (f : rf2_Coeff C)
    (hf : ∀ x (z : (chartAt ℂ x).target), (chartAt ℂ x).symm z ∈ U → f x z = 0)
    (x : C) (z : (chartAt ℂ x).target) (hz : (chartAt ℂ x).symm z ∈ U) :
    rf2_dbar10 C f x z = 0 := by
  have he : rf2_extend C f x =ᶠ[𝓝 (z : ℂ)] 0 := by
    filter_upwards [((chartAt ℂ x).isOpen_inter_preimage_symm hU).mem_nhds
      (show (z : ℂ) ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' U from
        ⟨z.property, hz⟩)] with u hu
    change (if h : u ∈ (chartAt ℂ x).target then f x ⟨u, h⟩ else 0) = 0
    rw [dite_eq_left hu.1]
    exact hf x ⟨u, hu.1⟩ hu.2
  change -antiLinearPart (fderiv ℝ (rf2_extend C f x) z) 1 = 0
  rw [he.fderiv_eq]
  simp only [fderiv_zero, Pi.zero_apply, map_zero, ContinuousLinearMap.zero_apply, neg_zero]

theorem rf2_dbar11_localize_aux (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] (Z : Finset C) (τ : rf2_smoothForms C 1 1) :
    ∃ (N : Set C) (v : rf2_smoothForms C 1 0), IsOpen N ∧ (↑Z : Set C) ⊆ N ∧
      ∀ x (z : (chartAt ℂ x).target), (chartAt ℂ x).symm z ∈ N →
        τ.val x z - rf2_dbar10 C v.val x z = 0 := by
  obtain ⟨U, hU, hdisj⟩ := (Z.finite_toSet).t2_separation
  have hlocal (x : C) := rf2_local_primitive C x (U x) (hU x).2 (hU x).1 τ
  choose r hr hrt v hv0 hveq using hlocal
  let V : rf2_smoothForms C 1 0 := ∑ i ∈ Z, v i
  let D : rf2_smoothForms C 1 1 := ⟨rf2_dbar10 C V.val, rf2_dbar10_smooth_aux C V⟩
  let N : Set C := ⋃ i : {x // x ∈ Z}, (chartAt ℂ i.val).source ∩
    (chartAt ℂ i.val) ⁻¹' Metric.ball (chartAt ℂ i.val i.val) (r i.val)
  refine ⟨N, V, isOpen_iUnion (fun i ↦ (chartAt ℂ i.val).isOpen_inter_preimage Metric.isOpen_ball), ?_, ?_⟩
  · intro x hx
    apply mem_iUnion.mpr
    refine ⟨⟨x, hx⟩, mem_chart_source ℂ x, ?_⟩
    exact Metric.mem_ball_self (hr x)
  · intro y z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    let w : (chartAt ℂ i.val).target := ⟨chartAt ℂ i.val ((chartAt ℂ y).symm z),
      (chartAt ℂ i.val).map_source hi.1⟩
    have hpt : (chartAt ℂ y).symm z = (chartAt ℂ i.val).symm w :=
      ((chartAt ℂ i.val).left_inv hi.1).symm
    have hpU : (chartAt ℂ i.val).symm w ∈ U i.val := (hrt i.val hi.2).2
    have hsum := congrArg (fun f : rf2_Coeff C ↦ f i.val w) (rf2_dbar10_sum C Z v)
    simp only [Finset.sum_apply] at hsum
    have hself : rf2_dbar10 C V.val i.val w = rf2_dbar10 C (v i.val).val i.val w := by
      rw [hsum]
      apply Finset.sum_eq_single i.val
      · intro j hj hji
        apply rf2_dbar10_zero_on C (U i.val) (hU i.val).2 (v j).val _ i.val w hpU
        intro a b hp
        apply hv0 j a b
        intro hpj
        exact Set.disjoint_left.mp (hdisj i.property hj (Ne.symm hji)) hp hpj
      · exact fun h ↦ False.elim (h i.property)
    have hτ := τ.property.2 y i.val z w hpt
    have hD := D.property.2 y i.val z w hpt
    have he : D.val i.val w = τ.val i.val w := hself.trans (hveq i.val w hi.2).symm
    rw [he] at hD
    exact sub_eq_zero.mpr (hτ.trans hD.symm)

theorem rf2_normalized_unit_at (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [ConnectedSpace C]
    (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ))
    (hgw : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) w x) 0 ≠ ⊤)
    (x : C) (hx : b4c_ordForm (hE := Module.finrank_self ℂ) w x = 0) :
    AnalyticAt ℂ (HurwitzPrymRR_loc (Module.finrank_self ℂ)
      (b4c_residue_normalizedForm (Module.finrank_self ℂ) w) x) 0 ∧
      HurwitzPrymRR_loc (Module.finrank_self ℂ)
        (b4c_residue_normalizedForm (Module.finrank_self ℂ) w) x 0 ≠ 0 := by
  have hfin := b4c_meroForm_order_ne_top (Module.finrank_self ℂ) w hgw x
  rw [b4c_ordForm, WithTop.untop₀_eq_zero] at hx
  have ho := hx.resolve_right hfin
  refine ⟨b4c_residue_normalizedForm_analytic (Module.finrank_self ℂ) w x (by rw [ho]), ?_⟩
  rw [(b4c_residue_normalizedForm_loc (Module.finrank_self ℂ) w x).eq_of_nhds]
  exact ((w.property.2 x).meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero).mp ho

theorem rf2_inverse_chart_vector (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (x : C) (z : (chartAt ℂ x).target) (v : ℂ) :
    (⟨(chartAt ℂ x).symm z,
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ x).symm z v⟩ :
      TangentBundle 𝓘(ℂ, ℂ) C) = b3Forms_chartVec x v z := by
  have h := tangentMap_chart_symm (I := 𝓘(ℂ, ℂ))
    (p := (⟨x, (0 : ℂ)⟩ : TangentBundle 𝓘(ℂ, ℂ) C))
    (q := (⟨(z : ℂ), v⟩ : TangentBundle 𝓘(ℂ, ℂ) ℂ)) z.property
  exact h.trans (rf2_tangentChart_symm C ⟨x, (0 : ℂ)⟩ ((z : ℂ), v) z.property)

theorem rf2_linear_chart_transition (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (hθ : HurwitzPrymRR_IsLinear θ) (x y : C) (z : (chartAt ℂ x).target)
    (w : (chartAt ℂ y).target)
    (hzw : (chartAt ℂ x).symm z = (chartAt ℂ y).symm w) :
    θ (b3Forms_chartVec x (1 : ℂ) z) = θ (b3Forms_chartVec y (1 : ℂ) w) *
      deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z := by
  rw [rf2_chartVec_transition C x y z w hzw]
  let a := deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) (z : ℂ)
  have hz : θ ⟨(chartAt ℂ y).symm w, (0 : ℂ)⟩ = 0 := by
    rw [b4c_residue_linear_value (Module.finrank_self ℂ) θ hθ]
    simp only [map_zero, mul_zero]
  have hh := hθ ((chartAt ℂ y).symm w) a ((b3Forms_chartVec y (1 : ℂ) w).2) 0
  simp only [add_zero, hz, add_zero] at hh
  simp only [b3Forms_chartVec, fderiv_eq_smul_deriv, one_smul] at hh ⊢
  change θ ⟨(chartAt ℂ y).symm w,
    a * deriv (b3Forms_tr (E := ℂ) y ((chartAt ℂ y).symm w)) (w : ℂ)⟩ = _ at hh
  change θ ⟨(chartAt ℂ y).symm w,
    a * deriv (b3Forms_tr (E := ℂ) y ((chartAt ℂ y).symm w)) (w : ℂ)⟩ = _
  exact hh.trans (mul_comm _ _)

theorem rf2_linear_chart_coefficient (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (hθ : HurwitzPrymRR_IsLinear θ) (x : C) (z : (chartAt ℂ x).target) :
    θ (b3Forms_chartVec x (1 : ℂ) z) =
      HurwitzPrymRR_loc (Module.finrank_self ℂ) θ x
        ((b4cov_lineEquiv (Module.finrank_self ℂ)).symm ((z : ℂ) - chartAt ℂ x x)) *
          (b4cov_lineEquiv (Module.finrank_self ℂ)).symm 1 := by
  apply Complex.ext
  · have h := b4c_residue_loc_realForm_coefficient (Module.finrank_self ℂ) θ hθ
      Complex.reCLM z.property (1 : ℂ)
    rwa [b4c_residue_loc_realForm_apply (Module.finrank_self ℂ) θ hθ
      Complex.reCLM z.property (1 : ℂ)] at h
  · have h := b4c_residue_loc_realForm_coefficient (Module.finrank_self ℂ) θ hθ
      Complex.imCLM z.property (1 : ℂ)
    rwa [b4c_residue_loc_realForm_apply (Module.finrank_self ℂ) θ hθ
      Complex.imCLM z.property (1 : ℂ)] at h

theorem rf2_chart_transition_deriv_ne_zero (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (x y : C) (z : (chartAt ℂ x).target)
    (hy : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source) :
    deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z ≠ 0 := by
  have h := b3Forms_fderiv_tr_comp_complex (x := x) (y := y) (z := x)
    ⟨z.property, hy⟩ ((chartAt ℂ x).map_target z.property)
  rw [(b3Forms_tr_self_eventuallyEq z.property).fderiv_eq, fderiv_id] at h
  have hh := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L 1) h
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    fderiv_eq_deriv_mul, mul_one] at hh
  change deriv (b3Forms_tr (E := ℂ) x y) (z : ℂ) ≠ 0
  intro hd
  rw [hd, mul_zero] at hh
  exact one_ne_zero hh

theorem rf2_meroCoeff_regular (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [ConnectedSpace C]
    (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ))
    (hgw : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) w x) 0 ≠ ⊤)
    (x : C) (z : (chartAt ℂ x).target)
    (hz : b4c_ordForm (hE := Module.finrank_self ℂ) w ((chartAt ℂ x).symm z) = 0) :
    AnalyticAt ℂ (rf2_extend C (rf2_meroCoeff C w) x) z ∧ rf2_meroCoeff C w x z ≠ 0 := by
  let p : C := (chartAt ℂ x).symm z
  let θ := b4c_residue_normalizedForm (Module.finrank_self ℂ) w
  have hθ : HurwitzPrymRR_IsLinear θ := b4c_residue_normalizedForm_linear _ w
  let L := b4cov_lineEquiv (Module.finrank_self ℂ)
  let H := HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p
  let t : ℂ → ℂ := chartAt ℂ p ∘ (chartAt ℂ x).symm
  have ht : AnalyticAt ℂ t z :=
    rf2_chart_transition_analytic C x p z z.property (mem_chart_source ℂ p)
  have hunit := rf2_normalized_unit_at C w hgw p hz
  have harg : AnalyticAt ℂ (fun u ↦ L.symm (t u - chartAt ℂ p p)) z :=
    (L.symm.toContinuousLinearMap.analyticAt _).comp (ht.sub analyticAt_const)
  have harg0 : L.symm (t z - chartAt ℂ p p) = 0 := by
    simp only [t, Function.comp_apply, ← show (chartAt ℂ x).symm z = p from rfl,
      sub_self, map_zero]
  have hH : AnalyticAt ℂ H (L.symm (t z - chartAt ℂ p p)) := by
    rw [harg0]
    exact hunit.1
  let G : ℂ → ℂ := fun u ↦ H (L.symm (t u - chartAt ℂ p p)) * L.symm 1 * deriv t u
  have hG : AnalyticAt ℂ G z := ((hH.comp (f := fun u : ℂ ↦ L.symm (t u - chartAt ℂ p p)) harg).mul
    analyticAt_const).mul ht.deriv
  have he : rf2_extend C (rf2_meroCoeff C w) x =ᶠ[𝓝 (z : ℂ)] G := by
    filter_upwards [(b3Forms_isOpen_trDom x p).mem_nhds
      (b3Forms_mem_trDom_self z.property)] with u hu
    have htu : t u ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source hu.2
    have hp : (chartAt ℂ x).symm u = (chartAt ℂ p).symm (t u) :=
      ((chartAt ℂ p).left_inv hu.2).symm
    change (if h : u ∈ (chartAt ℂ x).target then
      rf2_meroCoeff C w x ⟨u, h⟩ else 0) = G u
    rw [dite_eq_left hu.1]
    change θ ⟨(chartAt ℂ x).symm u,
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ x).symm u (1 : ℂ)⟩ = G u
    rw [rf2_inverse_chart_vector C x ⟨u, hu.1⟩ (1 : ℂ),
      rf2_linear_chart_transition C θ hθ x p ⟨u, hu.1⟩ ⟨t u, htu⟩ hp,
      rf2_linear_chart_coefficient C θ hθ p ⟨t u, htu⟩]
  have hL : L.symm 1 ≠ 0 := by
    intro h
    exact (one_ne_zero : (1 : ℂ) ≠ 0) (L.symm.injective (h.trans (map_zero _).symm))
  have hn : G z ≠ 0 := by
    dsimp only [G]
    rw [harg0]
    exact mul_ne_zero (mul_ne_zero hunit.2 hL)
      (rf2_chart_transition_deriv_ne_zero C x p z (mem_chart_source ℂ p))
  refine ⟨hG.congr he.symm, ?_⟩
  have hv := he.eq_of_nhds
  simp only [rf2_extend, dite_eq_left z.property] at hv
  rw [hv]
  exact hn

theorem rf2_regular_factor_equiv (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (N : Set C) (hN : IsOpen N) (a : rf2_Coeff C)
    (ha : ∀ x (z : (chartAt ℂ x).target), (chartAt ℂ x).symm z ∉ N →
      ContDiffAt ℝ ∞ (rf2_extend C a x) z ∧ a x z ≠ 0)
    (ht : ∀ x y (z : (chartAt ℂ x).target) (w : (chartAt ℂ y).target),
      (chartAt ℂ x).symm z = (chartAt ℂ y).symm w →
        a x z = a y w * deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z) :
    ∃ e : rf2_vanishing C 0 1 N ≃ₗ[ℂ] rf2_vanishing C 1 1 N,
      ∀ θ x z, (e θ).val.val x z = a x z * θ.val.val x z := by
  have hs {p q : ℕ} (f : rf2_smoothForms C p q) (x : C) (z : (chartAt ℂ x).target) :
      ContDiffAt ℝ ∞ (rf2_extend C f.val x) z := by
    obtain ⟨g, hg, he⟩ := f.property.1 x
    apply ((hg z z.property).contDiffAt
      ((chartAt ℂ x).open_target.mem_nhds z.property)).congr_of_eventuallyEq
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds z.property] with u hu
    simp only [rf2_extend, dite_eq_left hu]
    exact he ⟨u, hu⟩
  have hzero {p q : ℕ} (f : rf2_vanishing C p q N) (x : C)
      (z : (chartAt ℂ x).target) (hz : (chartAt ℂ x).symm z ∈ N) :
      rf2_extend C f.val.val x =ᶠ[𝓝 (z : ℂ)] 0 := by
    filter_upwards [((chartAt ℂ x).isOpen_inter_preimage_symm hN).mem_nhds
      (show (z : ℂ) ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' N from
        ⟨z.property, hz⟩)] with u hu
    change (if h : u ∈ (chartAt ℂ x).target then f.val.val x ⟨u, h⟩ else 0) = 0
    rw [dite_eq_left hu.1]
    exact f.property x ⟨u, hu.1⟩ hu.2
  have hm (f : rf2_vanishing C 0 1 N) :
      (fun x z ↦ a x z * f.val.val x z) ∈ rf2_smoothForms C 1 1 := by
    constructor
    · intro x
      refine ⟨fun u ↦ rf2_extend C a x u * rf2_extend C f.val.val x u, ?_, ?_⟩
      · intro u hu
        apply ContDiffAt.contDiffWithinAt
        by_cases hz : (chartAt ℂ x).symm u ∈ N
        · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
          filter_upwards [hzero f x ⟨u, hu⟩ hz] with v hv
          simp only [hv, Pi.zero_apply, mul_zero]
        · exact (ha x ⟨u, hu⟩ hz).1.mul (hs f.val x ⟨u, hu⟩)
      · intro z
        simp only [rf2_extend, dite_eq_left z.property]
    · intro x y z w h
      have hf := f.val.property.2 x y z w h
      simp only [pow_zero, pow_one, mul_one] at hf ⊢
      rw [ht x y z w h, hf]
      ring
  have hd (f : rf2_vanishing C 1 1 N) :
      (fun x z ↦ f.val.val x z / a x z) ∈ rf2_smoothForms C 0 1 := by
    constructor
    · intro x
      refine ⟨fun u ↦ rf2_extend C f.val.val x u / rf2_extend C a x u, ?_, ?_⟩
      · intro u hu
        apply ContDiffAt.contDiffWithinAt
        by_cases hz : (chartAt ℂ x).symm u ∈ N
        · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
          filter_upwards [hzero f x ⟨u, hu⟩ hz] with v hv
          simp only [hv, Pi.zero_apply, zero_div]
        · have hn : rf2_extend C a x u ≠ 0 := by
            simpa only [rf2_extend, dite_eq_left hu] using (ha x ⟨u, hu⟩ hz).2
          have hi : ContDiffAt ℝ ∞ (fun y : ℂ ↦ y⁻¹) (rf2_extend C a x u) :=
            (show AnalyticAt ℂ (fun y : ℂ ↦ y⁻¹) (rf2_extend C a x u) from
              analyticAt_id.inv hn).contDiffAt.restrict_scalars ℝ
          simp only [div_eq_mul_inv]
          exact (hs f.val x ⟨u, hu⟩).mul (hi.comp u (ha x ⟨u, hu⟩ hz).1)
      · intro z
        simp only [rf2_extend, dite_eq_left z.property]
    · intro x y z w h
      simp only [pow_zero, pow_one, mul_one]
      by_cases hz : (chartAt ℂ x).symm z ∈ N
      · rw [f.property x z hz, f.property y w (h ▸ hz), zero_div, zero_div, zero_mul]
      · have haw := (ha y w (by rwa [← h])).2
        have haz := (ha x z hz).2
        have ht' := ht x y z w h
        have hdne : deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z ≠ 0 := by
          intro hh
          exact haz (ht'.trans (by rw [hh, mul_zero]))
        have hf := f.val.property.2 x y z w h
        simp only [pow_one] at hf
        rw [hf, ht']
        field_simp [haw, hdne]
  let T : rf2_vanishing C 0 1 N →ₗ[ℂ] rf2_vanishing C 1 1 N :=
    { toFun := fun f ↦ ⟨⟨fun x z ↦ a x z * f.val.val x z, hm f⟩,
        fun x z hz ↦ by change a x z * f.val.val x z = 0; rw [f.property x z hz, mul_zero]⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        apply Subtype.ext
        funext x z
        exact mul_add _ _ _
      map_smul' := by
        intro r f
        apply Subtype.ext
        apply Subtype.ext
        funext x z
        change a x z * (r * f.val.val x z) = r * (a x z * f.val.val x z)
        ring }
  let D : rf2_vanishing C 1 1 N → rf2_vanishing C 0 1 N :=
    fun f ↦ ⟨⟨fun x z ↦ f.val.val x z / a x z, hd f⟩,
      fun x z hz ↦ by change f.val.val x z / a x z = 0; rw [f.property x z hz, zero_div]⟩
  refine ⟨{ toLinearMap := T, invFun := D, left_inv := ?_, right_inv := ?_ }, fun _ _ _ ↦ rfl⟩
  · intro f
    apply Subtype.ext
    apply Subtype.ext
    funext x z
    change a x z * f.val.val x z / a x z = f.val.val x z
    by_cases hz : (chartAt ℂ x).symm z ∈ N
    · rw [f.property x z hz, mul_zero, zero_div]
    · field_simp [(ha x z hz).2]
  · intro f
    apply Subtype.ext
    apply Subtype.ext
    funext x z
    change a x z * (f.val.val x z / a x z) = f.val.val x z
    by_cases hz : (chartAt ℂ x).symm z ∈ N
    · rw [f.property x z hz, zero_div, mul_zero]
    · field_simp [(ha x z hz).2]

theorem rf2_divide_by_form_aux (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ))
    (hw : (w : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) ≠ 0)
    (hgw : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) w x) 0 ≠ ⊤) (N : Set C) (hN : IsOpen N)
    (hZN : Function.support (b4c_ordForm (hE := Module.finrank_self ℂ) w) ⊆ N) :
    ∃ e : rf2_vanishing C 0 1 N ≃ₗ[ℂ] rf2_vanishing C 1 1 N,
      ∀ (θ : rf2_vanishing C 0 1 N) x (z : (chartAt ℂ x).target),
        (e θ).val.val x z = rf2_meroCoeff C w x z * θ.val.val x z := by
  apply rf2_regular_factor_equiv C N hN (rf2_meroCoeff C w)
  · intro x z hz
    have ho : b4c_ordForm (hE := Module.finrank_self ℂ) w ((chartAt ℂ x).symm z) = 0 := by
      by_contra hh
      exact hz (hZN hh)
    have hr := rf2_meroCoeff_regular C w hgw x z ho
    exact ⟨hr.1.contDiffAt.restrict_scalars ℝ, hr.2⟩
  · intro x y z v h
    let θ := b4c_residue_normalizedForm (Module.finrank_self ℂ) w
    change θ ⟨(chartAt ℂ x).symm z,
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ x).symm z (1 : ℂ)⟩ =
      θ ⟨(chartAt ℂ y).symm v,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ y).symm v (1 : ℂ)⟩ * _
    rw [rf2_inverse_chart_vector C x z (1 : ℂ), rf2_inverse_chart_vector C y v (1 : ℂ)]
    exact rf2_linear_chart_transition C θ (b4c_residue_normalizedForm_linear _ w) x y z v h

theorem rf2_principalPart_eq_zero_iff {m : ℕ} (hm : 0 < m)
    (c h : Fin m → ℂ) (hc : c ⟨0, hm⟩ ≠ 0) :
    rf2_principalPart m c h = 0 ↔ h = 0 := by
  constructor
  · intro he
    have hz : ∀ n (hn : n < m), h ⟨n, hn⟩ = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro hn
        have hk := congrFun he ⟨n, hn⟩
        change (∑ j : Fin m, if j.val ≤ n then c ⟨n - j.val, by omega⟩ * h j else 0) = 0 at hk
        rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin m)] at hk
        · simp only [le_refl, ↓reduceIte, Nat.sub_self] at hk
          exact (mul_eq_zero.mp hk).resolve_left hc
        · intro j _ hj
          split_ifs with hjn
          · have hjlt : j.val < n := by
              have hjne : j.val ≠ n := by intro hv; apply hj; exact Fin.ext hv
              omega
            rw [ih j.val hjlt j.isLt, mul_zero]
          · rfl
        · simp
    ext k
    exact hz k.val k.isLt
  · rintro rfl
    exact map_zero _

theorem rf2_pole_removable_iff_order (m : ℕ) (c h : ℂ → ℂ)
    (hc : AnalyticAt ℂ c 0) (hc0 : c 0 ≠ 0) (hh : AnalyticAt ℂ h 0) :
    (∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧
      (fun z ↦ z ^ (-(m : ℤ)) * c z * h z) =ᶠ[𝓝[≠] 0] F) ↔
      (m : ℕ∞) ≤ analyticOrderAt h 0 := by
  constructor
  · rintro ⟨F, hF, he⟩
    let G : ℂ → ℂ := fun z ↦ F z / c z
    have hG : AnalyticAt ℂ G 0 := hF.div hc hc0
    have he' : h =ᶠ[𝓝[≠] 0] (fun z ↦ z ^ m * G z) := by
      filter_upwards [he, (hc.continuousAt.eventually_ne hc0).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with z hz hcz hz0
      have hzn : z ≠ 0 := hz0
      dsimp [G]
      rw [← hz, zpow_neg, zpow_natCast]
      field_simp
    have he'' : h =ᶠ[𝓝 0] (fun z ↦ z ^ m * G z) :=
      (hh.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        ((analyticAt_id.pow m).mul hG).continuousAt).mp he'
    exact (natCast_le_analyticOrderAt hh).mpr
      ⟨G, hG, by simpa only [Filter.EventuallyEq, sub_zero, smul_eq_mul] using he''⟩
  · intro ho
    obtain ⟨G, hG, he⟩ := (natCast_le_analyticOrderAt hh).mp ho
    refine ⟨fun z ↦ c z * G z, hc.mul hG, ?_⟩
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz0
    have hzn : z ≠ 0 := hz0
    simp only [sub_zero, smul_eq_mul] at hz
    rw [hz, zpow_neg, zpow_natCast]
    field_simp

theorem rf2_principalPart_removable_aux (m : ℕ) (hm : 0 < m) (c h : ℂ → ℂ)
    (hc : AnalyticAt ℂ c 0) (hc0 : c 0 ≠ 0) (hh : AnalyticAt ℂ h 0) :
    (∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧
      (fun z ↦ z ^ (-(m : ℤ)) * c z * h z) =ᶠ[𝓝[≠] 0] F) ↔
      rf2_principalPart m (fun k ↦ iteratedDeriv k.val c 0 / (k.val.factorial : ℂ))
        (fun k ↦ iteratedDeriv k.val h 0 / (k.val.factorial : ℂ)) = 0 := by
  rw [rf2_pole_removable_iff_order m c h hc hc0 hh]
  rw [rf2_principalPart_eq_zero_iff hm _ _ (by simpa using hc0)]
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hh]
  constructor
  · intro hz
    ext k
    simp only [hz k.val k.isLt, zero_div, Pi.zero_apply]
  · intro hz i hi
    have he := congrFun hz ⟨i, hi⟩
    change iteratedDeriv i h 0 / (i.factorial : ℂ) = 0 at he
    exact (div_eq_zero_iff).mp he |>.resolve_right (by exact_mod_cast i.factorial_ne_zero)

theorem rf2_exactAway_primitive_section (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (N : Set C) (p : C) :
    ∃ P : rf2_exactAway C N →ₗ[ℂ] b4c_SmoothFun ℂ C,
      (∀ θ, rf2_dbar00 C (P θ) = θ.val.val) ∧ (∀ θ, (P θ).val p = 0) := by
  let L := rf2_dbar00Linear C
  have hmem (θ : rf2_exactAway C N) : θ.val ∈ L.range := by
    have ht := θ.property.1
    change θ.val.val ∈ Submodule.span ℂ
      (rf2_dbar00 C '' (b4c_SmoothFun ℂ C : Set (C → ℂ))) at ht
    rw [← SetLike.mem_coe, rf2_dbar00_image_span C] at ht
    obtain ⟨u, hu, he⟩ := ht
    exact ⟨⟨u, hu⟩, Subtype.ext ((rf2_dbar00Linear_val C ⟨u, hu⟩).trans he)⟩
  let j : rf2_exactAway C N →ₗ[ℂ] L.range :=
    { toFun := fun θ ↦ ⟨θ.val, hmem θ⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  letI : Module.Free ℂ L.range := Module.Free.of_divisionRing ℂ L.range
  letI : Module.Projective ℂ L.range := Module.Projective.of_free
  obtain ⟨S, hS⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  let D := S.comp j
  have hD (θ : rf2_exactAway C N) : L (D θ) = θ.val := by
    exact congrArg Subtype.val (LinearMap.congr_fun hS (j θ))
  let k : ℂ →ₗ[ℂ] b4c_SmoothFun ℂ C :=
    { toFun := fun c ↦ ⟨fun _ ↦ c, contMDiff_const⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let ev : b4c_SmoothFun ℂ C →ₗ[ℂ] ℂ :=
    (LinearMap.proj p).comp (b4c_SmoothFun ℂ C).subtype
  have hk (c : ℂ) : L (k c) = 0 := by
    apply Subtype.ext
    rw [rf2_dbar00Linear_val]
    funext x z
    change wirtingerDbar (fun _ : ℂ ↦ c) (z : ℂ) = 0
    simp only [wirtingerDbar, fderiv_const_apply, map_zero, ContinuousLinearMap.zero_apply]
  let P := D - k.comp (ev.comp D)
  refine ⟨P, ?_, ?_⟩
  · intro θ
    have he : L (P θ) = θ.val := by
      change L (D θ - k (ev (D θ))) = θ.val
      rw [map_sub, hk, sub_zero, hD]
    exact (rf2_dbar00Linear_val C (P θ)).symm.trans (congrArg Subtype.val he)
  · intro θ
    change (D θ).val p - (D θ).val p = 0
    exact sub_self _

theorem rf2_analyticOnNhd_of_wirtinger_zero (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → ℂ) (hu : ContDiffOn ℝ ∞ u U)
    (hzero : ∀ z ∈ U, wirtingerDbar u z = 0) : AnalyticOnNhd ℂ u U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro z hz
  have hd : DifferentiableAt ℝ u z :=
    ((hu z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have ha : antiLinearPart (fderiv ℝ u z) = 0 := by
    ext v
    rw [rf2_antiLinearPart_scalar]
    change star v * wirtingerDbar u z = 0
    rw [hzero z hz, mul_zero]
  obtain ⟨L, hL⟩ := exists_restrictScalars_eq_of_antiLinearPart_eq_zero _ ha
  exact (hasFDerivAt_of_restrictScalars ℝ hd.hasFDerivAt hL).differentiableAt.differentiableWithinAt

theorem rf2_exactAway_primitive_analytic (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (N : Set C) (hN : IsOpen N)
    (θ : rf2_exactAway C N) (u : b4c_SmoothFun ℂ C)
    (hu : rf2_dbar00 C u = θ.val.val) (x : C) :
    AnalyticOnNhd ℂ (u.val ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' N) := by
  apply rf2_analyticOnNhd_of_wirtinger_zero _ ((chartAt ℂ x).isOpen_inter_preimage_symm hN)
  · exact (u.property.comp_contMDiffOn
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := x))).contDiffOn.mono inter_subset_left
  · intro z hz
    have he := congrFun (congrFun hu x) ⟨z, hz.1⟩
    exact he.trans (θ.property.2 x ⟨z, hz.1⟩ hz.2)

def rf2_normalizeLinearField (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) :
    TangentBundle 𝓘(ℂ, ℂ) C → ℂ :=
  fun v ↦ toMeromorphicNFAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ v.proj) 0 0 *
    (b4cov_lineEquiv (Module.finrank_self ℂ)).symm v.2

theorem rf2_normalizeLinearField_linear (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) :
    HurwitzPrymRR_IsLinear (rf2_normalizeLinearField C θ) := by
  intro x a v w
  change _ * (b4cov_lineEquiv (Module.finrank_self ℂ)).symm (a • (v : ℂ) + (w : ℂ)) =
    a * (_ * (b4cov_lineEquiv (Module.finrank_self ℂ)).symm v) +
      _ * (b4cov_lineEquiv (Module.finrank_self ℂ)).symm w
  erw [map_add, map_smul]
  simp only [smul_eq_mul]
  ring

theorem rf2_normalizeLinearField_eq (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (hθ : HurwitzPrymRR_IsLinear θ) (x : C)
    (hx : AnalyticAt ℂ (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ x) 0)
    (v : TangentSpace 𝓘(ℂ, ℂ) x) :
    rf2_normalizeLinearField C θ ⟨x, v⟩ = θ ⟨x, v⟩ := by
  rw [rf2_normalizeLinearField, toMeromorphicNFAt_eq_self.mpr hx.meromorphicNFAt]
  rw [b4c_residue_linear_value (Module.finrank_self ℂ) θ hθ x v]
  congr 1
  dsimp only [HurwitzPrymRR_loc, b4cov_coef]
  erw [(b4cov_lineEquiv (Module.finrank_self ℂ)).map_zero, add_zero,
    (extChartAt 𝓘(ℂ, ℂ) x).left_inv (mem_extChartAt_source x), b4cov_vec_self]

theorem rf2_normalizeLinearField_loc (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (hθ : HurwitzPrymRR_IsLinear θ) (x : C)
    (hm : MeromorphicAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ x) 0) :
    HurwitzPrymRR_loc (Module.finrank_self ℂ) (rf2_normalizeLinearField C θ) x =ᶠ[𝓝 0]
      toMeromorphicNFAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ x) 0 := by
  let hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  let L := b4cov_lineEquiv hE
  let e := extChartAt 𝓘(ℂ, ℂ) x
  have hx : x ∈ e.source := mem_extChartAt_source x
  have ht : ∀ᶠ τ : ℂ in 𝓝 0, e x + L τ ∈ e.target := by
    have hc : ContinuousAt (fun τ : ℂ ↦ e x + L τ) 0 :=
      continuousAt_const.add L.continuous.continuousAt
    apply hc.preimage_mem_nhds
    simpa only [map_zero, add_zero] using (isOpen_extChartAt_target x).mem_nhds (e.map_source hx)
  have hA : ∀ᶠ τ in 𝓝 (0 : ℂ), τ ≠ 0 → AnalyticAt ℂ (HurwitzPrymRR_loc hE θ x) τ := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_singleton_iff] using
      (hm).eventually_analyticAt
  filter_upwards [ht, hA] with τ hτ hAτ
  by_cases hzero : τ = 0
  · subst τ
    dsimp only [HurwitzPrymRR_loc, b4cov_coef]
    erw [(b4cov_lineEquiv hE).map_zero, add_zero,
      (extChartAt 𝓘(ℂ, ℂ) x).left_inv (mem_extChartAt_source x), b4cov_vec_self]
    change _ * (b4cov_lineEquiv hE).symm (b4cov_lineEquiv hE 1) = _
    rw [ContinuousLinearEquiv.symm_apply_apply, mul_one]
  · let y := e.symm (e x + L τ)
    have hy : y ∈ e.source := e.map_target hτ
    have hcoord : L.symm (e y - e x) = τ := by
      rw [e.right_inv hτ, add_sub_cancel_left, ContinuousLinearEquiv.symm_apply_apply]
    have hlocal : AnalyticAt ℂ (HurwitzPrymRR_loc hE θ y) 0 :=
      b4c_residue_analytic_chart hE θ hθ x y hy (by
        change AnalyticAt ℂ (HurwitzPrymRR_loc hE θ x) (L.symm (e y - e x))
        rw [hcoord]
        exact hAτ hzero)
    change rf2_normalizeLinearField C θ ⟨y, b4cov_vec x y (L 1)⟩ = _
    rw [rf2_normalizeLinearField_eq C θ hθ y hlocal]
    exact (hm).eqOn_compl_singleton_toMeromorphicNFAt
      (show τ ∈ ({0} : Set ℂ)ᶜ from hzero)

theorem rf2_linear_chart_coefficients_smooth (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (hθ : HurwitzPrymRR_IsLinear θ)
    (hc : ∀ p, ContDiffAt ℝ ∞ (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p) 0) :
    (fun x (z : (chartAt ℂ x).target) ↦ θ (b3Forms_chartVec x (1 : ℂ) z)) ∈
      rf2_smoothForms C 1 0 := by
  let a : rf2_Coeff C := fun x z ↦ θ (b3Forms_chartVec x (1 : ℂ) z)
  have hsm (x : C) (z : (chartAt ℂ x).target) : ContDiffAt ℝ ∞ (rf2_extend C a x) z := by
    let p : C := (chartAt ℂ x).symm z
    let L := b4cov_lineEquiv (Module.finrank_self ℂ)
    let H := HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p
    let t : ℂ → ℂ := chartAt ℂ p ∘ (chartAt ℂ x).symm
    have ht : AnalyticAt ℂ t z :=
      rf2_chart_transition_analytic C x p z z.property (mem_chart_source ℂ p)
    have harg : ContDiffAt ℝ ∞ (fun u ↦ L.symm (t u - chartAt ℂ p p)) z :=
      (L.symm.contDiff.contDiffAt.restrict_scalars ℝ).comp (z : ℂ)
        ((ht.contDiffAt.restrict_scalars ℝ).sub contDiffAt_const)
    have harg0 : L.symm (t z - chartAt ℂ p p) = 0 := by
      change L.symm (chartAt ℂ p p - chartAt ℂ p p) = 0
      rw [sub_self, map_zero]
    have hH : ContDiffAt ℝ ∞ H (L.symm (t z - chartAt ℂ p p)) := by
      rw [harg0]
      exact hc p
    let G : ℂ → ℂ := fun u ↦ H (L.symm (t u - chartAt ℂ p p)) * L.symm 1 * deriv t u
    have hG : ContDiffAt ℝ ∞ G z :=
      ((hH.comp (z : ℂ) harg).mul contDiffAt_const).mul (ht.deriv.contDiffAt.restrict_scalars ℝ)
    apply hG.congr_of_eventuallyEq
    filter_upwards [(b3Forms_isOpen_trDom x p).mem_nhds
      (b3Forms_mem_trDom_self z.property)] with u hu
    have htu : t u ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source hu.2
    have hp : (chartAt ℂ x).symm u = (chartAt ℂ p).symm (t u) :=
      ((chartAt ℂ p).left_inv hu.2).symm
    change (if h : u ∈ (chartAt ℂ x).target then a x ⟨u, h⟩ else 0) = G u
    rw [dite_eq_left hu.1]
    change θ (b3Forms_chartVec x (1 : ℂ) u) = G u
    rw [rf2_linear_chart_transition C θ hθ x p ⟨u, hu.1⟩ ⟨t u, htu⟩ hp,
      rf2_linear_chart_coefficient C θ hθ p ⟨t u, htu⟩]
  constructor
  · intro x
    refine ⟨rf2_extend C a x, fun u hu ↦ (hsm x ⟨u, hu⟩).contDiffWithinAt, ?_⟩
    intro z
    change a x z = rf2_extend C a x z
    simp only [rf2_extend, dite_eq_left z.property]
  · intro x y z w h
    dsimp only
    simp only [pow_one, pow_zero, mul_one]
    exact rf2_linear_chart_transition C θ hθ x y z w h

def rf2_analyticJetMap {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] (ℂ → ℂ)) (ha : ∀ v, AnalyticAt ℂ (f v) 0) (m : ℕ) :
    V →ₗ[ℂ] (Fin m → ℂ) where
  toFun v k := iteratedDeriv k.val (f v) 0
  map_add' := by
    intro v w
    ext k
    change iteratedDeriv k.val (f (v + w)) 0 =
      iteratedDeriv k.val (f v) 0 + iteratedDeriv k.val (f w) 0
    rw [map_add]
    exact iteratedDeriv_add (ha v).contDiffAt (ha w).contDiffAt
  map_smul' := by
    intro r v
    ext k
    change iteratedDeriv k.val (f (r • v)) 0 = r • iteratedDeriv k.val (f v) 0
    rw [map_smul]
    exact iteratedDeriv_const_smul_field r (f v)

theorem rf2_analyticJetMap_order {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] (ℂ → ℂ)) (ha : ∀ v, AnalyticAt ℂ (f v) 0) (m : ℕ)
    (v : V) (hv : v ∈ (rf2_analyticJetMap f ha m).ker) :
    (m : ℕ∞) ≤ analyticOrderAt (f v) 0 := by
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (ha v)).mpr
  intro i hi
  exact congrFun (LinearMap.mem_ker.mp hv) ⟨i, hi⟩

theorem rf2_pole_cleared_by_jet (m : ℕ) (f h : ℂ → ℂ)
    (hf : MeromorphicAt f 0) (hfo : meromorphicOrderAt f 0 = (-(m : ℤ) : ℤ))
    (hh : AnalyticAt ℂ h 0) (ho : (m : ℕ∞) ≤ analyticOrderAt h 0) :
    0 ≤ meromorphicOrderAt (fun z ↦ f z * h z) 0 := by
  change 0 ≤ meromorphicOrderAt (f * h) 0
  rw [meromorphicOrderAt_mul hf hh.meromorphicAt, hfo, hh.meromorphicOrderAt_eq]
  cases hn : analyticOrderAt h 0 with
  | top =>
    rw [ENat.map_top]
    exact le_top
  | coe n =>
    have hmn : m ≤ n := by simpa only [hn, ENat.natCast_le_natCast] using ho
    rw [ENat.map_natCast, ← WithTop.coe_add]
    exact_mod_cast (show (0 : ℤ) ≤ -(m : ℤ) + (n : ℤ) by omega)

theorem rf2_linearField_loc_congr_on_open (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (U : Set C) (hU : IsOpen U) (p : C) (hp : p ∈ U)
    (θ η : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (he : ∀ q ∈ U, ∀ v : TangentSpace 𝓘(ℂ, ℂ) q, θ ⟨q, v⟩ = η ⟨q, v⟩) :
    HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p =ᶠ[𝓝 0]
      HurwitzPrymRR_loc (Module.finrank_self ℂ) η p := by
  let e := chartAt ℂ p
  let L := b4cov_lineEquiv (Module.finrank_self ℂ)
  have ht0 : ContinuousAt (fun τ : ℂ ↦ e p + L τ) 0 :=
    continuousAt_const.add L.continuous.continuousAt
  have ht : Tendsto (fun τ : ℂ ↦ e p + L τ) (𝓝 0) (𝓝 (e p)) := by
    simpa only [map_zero, add_zero] using ht0.tendsto
  have hb : Tendsto (fun τ : ℂ ↦ e.symm (e p + L τ)) (𝓝 0) (𝓝 p) := by
    have h := (e.continuousAt_symm (mem_chart_target ℂ p)).tendsto.comp ht
    change Tendsto (fun τ : ℂ ↦ e.symm (e p + L τ)) (𝓝 0) (𝓝 (e.symm (e p))) at h
    rw [e.left_inv (mem_chart_source ℂ p)] at h
    exact h
  filter_upwards [hb.eventually (hU.mem_nhds hp)] with τ hτ
  change θ ⟨(extChartAt 𝓘(ℂ, ℂ) p).symm
      (extChartAt 𝓘(ℂ, ℂ) p p + L τ), _⟩ = η ⟨_, _⟩
  apply he
  change e.symm (e p + L τ) ∈ U
  exact hτ

def rf2_repairLinearField (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (Z : Set C) (η : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) :
    TangentBundle 𝓘(ℂ, ℂ) C → ℂ :=
  fun v ↦ if v.proj ∈ Z then rf2_normalizeLinearField C η v else η v

theorem rf2_repairLinearField_linear (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (Z : Set C) (η : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (hη : HurwitzPrymRR_IsLinear η) : HurwitzPrymRR_IsLinear (rf2_repairLinearField C Z η) := by
  intro p a v w
  by_cases hp : p ∈ Z
  · simp only [rf2_repairLinearField, if_pos hp]
    exact rf2_normalizeLinearField_linear C η p a v w
  · simp only [rf2_repairLinearField, if_neg hp]
    exact hη p a v w

theorem rf2_repairLinearField_loc_on (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (Z N : Set C) (hN : IsOpen N)
    (η : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) (hη : HurwitzPrymRR_IsLinear η)
    (ha : ∀ q ∈ N, q ∉ Z → AnalyticAt ℂ (HurwitzPrymRR_loc (Module.finrank_self ℂ) η q) 0)
    (p : C) (hp : p ∈ N) :
    HurwitzPrymRR_loc (Module.finrank_self ℂ) (rf2_repairLinearField C Z η) p =ᶠ[𝓝 0]
      HurwitzPrymRR_loc (Module.finrank_self ℂ) (rf2_normalizeLinearField C η) p := by
  apply rf2_linearField_loc_congr_on_open C N hN p hp
  intro q hq v
  by_cases hqZ : q ∈ Z
  · exact if_pos hqZ
  · change (if q ∈ Z then rf2_normalizeLinearField C η ⟨q, v⟩ else η ⟨q, v⟩) = _
    rw [if_neg hqZ]
    exact (rf2_normalizeLinearField_eq C η hη q (ha q hq hqZ) v).symm

theorem rf2_repairLinearField_smooth (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (Z N : Set C) (hZ : IsClosed Z) (hN : IsOpen N) (hZN : Z ⊆ N)
    (η : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) (hη : HurwitzPrymRR_IsLinear η)
    (hm : ∀ p ∈ N, MeromorphicAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) η p) 0)
    (ho : ∀ p ∈ N, 0 ≤ meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) η p) 0)
    (ha : ∀ p ∈ N, p ∉ Z → AnalyticAt ℂ (HurwitzPrymRR_loc (Module.finrank_self ℂ) η p) 0)
    (hs : ∀ p ∉ Z, ContDiffAt ℝ ∞ (HurwitzPrymRR_loc (Module.finrank_self ℂ) η p) 0) :
    (fun x (z : (chartAt ℂ x).target) ↦ rf2_repairLinearField C Z η (b3Forms_chartVec x (1 : ℂ) z)) ∈
      rf2_smoothForms C 1 0 := by
  apply rf2_linear_chart_coefficients_smooth C _ (rf2_repairLinearField_linear C Z η hη)
  intro p
  by_cases hp : p ∈ Z
  · have hpN := hZN hp
    have he := (rf2_repairLinearField_loc_on C Z N hN η hη ha p hpN).trans
      (rf2_normalizeLinearField_loc C η hη p (hm p hpN))
    have han := (hm p hpN).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp (ho p hpN)
    exact (han.contDiffAt.restrict_scalars ℝ).congr_of_eventuallyEq he
  · have he := rf2_linearField_loc_congr_on_open C Zᶜ hZ.isOpen_compl p hp
      (rf2_repairLinearField C Z η) η (fun q hq v ↦ if_neg hq)
    exact (hs p hp).congr_of_eventuallyEq he

def rf2_primitiveFamily {V : Type*} [AddCommGroup V] [Module ℂ V]
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    (P : V →ₗ[ℂ] b4c_SmoothFun ℂ C) (p : C) : V →ₗ[ℂ] (ℂ → ℂ) where
  toFun θ τ := (P θ).val ((chartAt ℂ p).symm
    (chartAt ℂ p p + b4cov_lineEquiv (Module.finrank_self ℂ) τ))
  map_add' := by
    intro θ η
    funext τ
    exact congrArg (fun f : b4c_SmoothFun ℂ C ↦ f.val ((chartAt ℂ p).symm
      (chartAt ℂ p p + b4cov_lineEquiv (Module.finrank_self ℂ) τ))) (map_add P θ η)
  map_smul' := by
    intro a θ
    funext τ
    exact congrArg (fun f : b4c_SmoothFun ℂ C ↦ f.val ((chartAt ℂ p).symm
      (chartAt ℂ p p + b4cov_lineEquiv (Module.finrank_self ℂ) τ))) (map_smul P a θ)

theorem rf2_primitiveFamily_analytic (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (N : Set C) (hN : IsOpen N)
    (P : rf2_exactAway C N →ₗ[ℂ] b4c_SmoothFun ℂ C)
    (hP : ∀ θ, rf2_dbar00 C (P θ) = θ.val.val) (p : C) (hp : p ∈ N)
    (θ : rf2_exactAway C N) : AnalyticAt ℂ (rf2_primitiveFamily C P p θ) 0 := by
  have ha := rf2_exactAway_primitive_analytic C N hN θ (P θ) (hP θ) p
  have hc : chartAt ℂ p p ∈ (chartAt ℂ p).target ∩ (chartAt ℂ p).symm ⁻¹' N := by
    refine ⟨mem_chart_target ℂ p, ?_⟩
    change (chartAt ℂ p).symm (chartAt ℂ p p) ∈ N
    rwa [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
  let L := b4cov_lineEquiv (Module.finrank_self ℂ)
  change AnalyticAt ℂ (((P θ).val ∘ (chartAt ℂ p).symm) ∘
    (fun τ : ℂ ↦ chartAt ℂ p p + L τ)) 0
  have ht : AnalyticAt ℂ (fun τ : ℂ ↦ chartAt ℂ p p + L τ) 0 :=
    analyticAt_const.add (L.toContinuousLinearMap.analyticAt (0 : ℂ))
  exact (ha (chartAt ℂ p p) hc).comp_of_eq ht (by
    change chartAt ℂ p p + L 0 = chartAt ℂ p p
    rw [map_zero, add_zero])

theorem rf2_primitiveFamily_smooth {V : Type*} [AddCommGroup V] [Module ℂ V]
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    (P : V →ₗ[ℂ] b4c_SmoothFun ℂ C) (p : C) (θ : V) :
    ContDiffAt ℝ ∞ (rf2_primitiveFamily C P p θ) 0 := by
  have hg := ((P θ).property.comp_contMDiffOn
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := p))).contDiffOn
  have ha := (hg (chartAt ℂ p p) (mem_chart_target ℂ p)).contDiffAt
    ((chartAt ℂ p).open_target.mem_nhds (mem_chart_target ℂ p))
  let L := b4cov_lineEquiv (Module.finrank_self ℂ)
  change ContDiffAt ℝ ∞ (((P θ).val ∘ (chartAt ℂ p).symm) ∘
    (fun τ : ℂ ↦ chartAt ℂ p p + L τ)) 0
  have hc : ContDiffAt ℝ ∞ (fun τ : ℂ ↦ chartAt ℂ p p + L τ) 0 :=
    contDiffAt_const.add (L.contDiff.contDiffAt.restrict_scalars ℝ)
  apply ContDiffAt.comp (x := (0 : ℂ)) _ hc
  simpa only [map_zero, add_zero] using ha

theorem rf2_poleJetMap (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ))
    (hgw : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) w p) 0 ≠ ⊤)
    (N : Set C) (hN : IsOpen N)
    (hZN : Function.support (b4c_ordForm (hE := Module.finrank_self ℂ) w) ⊆ N) :
    ∃ (P : rf2_exactAway C N →ₗ[ℂ] b4c_SmoothFun ℂ C)
      (π : rf2_exactAway C N →ₗ[ℂ] (Fin (rf2_poleBudget C w) → ℂ)),
      (∀ θ, rf2_dbar00 C (P θ) = θ.val.val) ∧
      ∀ θ ∈ π.ker, ∀ p ∈ N,
        0 ≤ meromorphicOrderAt (fun τ ↦
          HurwitzPrymRR_loc (Module.finrank_self ℂ)
            (b4c_residue_normalizedForm (Module.finrank_self ℂ) w) p τ *
            rf2_primitiveFamily C P p θ τ) 0 := by
  obtain ⟨P, hP, _⟩ := rf2_exactAway_primitive_section C N (Classical.arbitrary C)
  let D := b4c_divForm (hE := Module.finrank_self ℂ) w
  have hfin := b4c_meroForm_orderSupport_finite (Module.finrank_self ℂ) w
  have hD (p : C) : D p = b4c_ordForm (hE := Module.finrank_self ℂ) w p :=
    RiemannRochAna_divForm_apply_of_finite (Module.finrank_self ℂ) w hfin p
  have hiN (i : D.support) : i.val ∈ N := by
    apply hZN
    change b4c_ordForm (hE := Module.finrank_self ℂ) w i.val ≠ 0
    rw [← hD]
    exact Finsupp.mem_support_iff.mp i.property
  let JType := (i : D.support) → Fin ((-D i.val).toNat) → ℂ
  let J : rf2_exactAway C N →ₗ[ℂ] JType := LinearMap.pi fun i ↦
    rf2_analyticJetMap (rf2_primitiveFamily C P i.val)
      (rf2_primitiveFamily_analytic C N hN P hP i.val (hiN i)) ((-D i.val).toNat)
  have hdim : Module.finrank ℂ JType = rf2_poleBudget C w := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_pi, Fintype.card_fin, Finsupp.sum]
    exact Finset.sum_attach D.support (fun p ↦ (-D p).toNat)
  let e : JType ≃ₗ[ℂ] (Fin (rf2_poleBudget C w) → ℂ) := LinearEquiv.ofFinrankEq (R := ℂ) JType (Fin (rf2_poleBudget C w) → ℂ) (by
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using hdim)
  let π := e.toLinearMap.comp J
  refine ⟨P, π, hP, ?_⟩
  intro θ hθ p hp
  have ha := rf2_primitiveFamily_analytic C N hN P hP p hp θ
  let f := HurwitzPrymRR_loc (Module.finrank_self ℂ)
    (b4c_residue_normalizedForm (Module.finrank_self ℂ) w) p
  have hm : MeromorphicAt f 0 := (b4c_residue_normalizedForm_mem (Module.finrank_self ℂ) w).2 p
  have hwOrder : meromorphicOrderAt f 0 = (D p : WithTop ℤ) := by
    rw [meromorphicOrderAt_congr
      ((b4c_residue_normalizedForm_loc (Module.finrank_self ℂ) w p).filter_mono nhdsWithin_le_nhds),
      (w.property.2 p).meromorphicOrderAt_toMeromorphicNFAt]
    exact (RiemannRochAna_coe_divForm_apply (Module.finrank_self ℂ) w hfin p
      (b4c_meroForm_order_ne_top (Module.finrank_self ℂ) w hgw p)).symm
  change 0 ≤ meromorphicOrderAt (f * rf2_primitiveFamily C P p θ) 0
  by_cases hpole : D p < 0
  · have hps : p ∈ D.support := Finsupp.mem_support_iff.mpr (ne_of_lt hpole)
    let i : D.support := ⟨p, hps⟩
    have hπ : e (J θ) = 0 := LinearMap.mem_ker.mp hθ
    have hJ : J θ = 0 := e.injective (hπ.trans (map_zero e).symm)
    have hjet : θ ∈ (rf2_analyticJetMap (rf2_primitiveFamily C P p)
        (rf2_primitiveFamily_analytic C N hN P hP p hp) ((-D p).toNat)).ker := by
      exact congrFun hJ i
    have horder := rf2_analyticJetMap_order (rf2_primitiveFamily C P p)
      (rf2_primitiveFamily_analytic C N hN P hP p hp) ((-D p).toNat) θ hjet
    have hcast : -(((-D p).toNat : ℕ) : ℤ) = D p := by omega
    apply rf2_pole_cleared_by_jet ((-D p).toNat) f _ hm _ ha horder
    rw [hwOrder, hcast]
  · rw [meromorphicOrderAt_mul hm ha.meromorphicAt, hwOrder]
    exact add_nonneg (by exact_mod_cast (le_of_not_gt hpole)) ha.meromorphicOrderAt_nonneg

theorem rf2_linear_chart_coefficient_analytic (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (hθ : HurwitzPrymRR_IsLinear θ) (x : C) (z : (chartAt ℂ x).target)
    (hc : AnalyticAt ℂ (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ ((chartAt ℂ x).symm z)) 0) :
    AnalyticAt ℂ (rf2_extend C (fun y w ↦ θ (b3Forms_chartVec y (1 : ℂ) w)) x) z := by
  let p : C := (chartAt ℂ x).symm z
  let L := b4cov_lineEquiv (Module.finrank_self ℂ)
  let H := HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p
  let t : ℂ → ℂ := chartAt ℂ p ∘ (chartAt ℂ x).symm
  have ht : AnalyticAt ℂ t z :=
    rf2_chart_transition_analytic C x p z z.property (mem_chart_source ℂ p)
  have harg : AnalyticAt ℂ (fun u ↦ L.symm (t u - chartAt ℂ p p)) z :=
    (L.symm.toContinuousLinearMap.analyticAt _).comp (ht.sub analyticAt_const)
  have harg0 : L.symm (t z - chartAt ℂ p p) = 0 := by
    change L.symm (chartAt ℂ p p - chartAt ℂ p p) = 0
    rw [sub_self, map_zero]
  have hH : AnalyticAt ℂ H (L.symm (t z - chartAt ℂ p p)) := by
    rw [harg0]
    exact hc
  let G : ℂ → ℂ := fun u ↦ H (L.symm (t u - chartAt ℂ p p)) * L.symm 1 * deriv t u
  have hG : AnalyticAt ℂ G z := ((hH.comp
    (f := fun u : ℂ ↦ L.symm (t u - chartAt ℂ p p)) harg).mul analyticAt_const).mul ht.deriv
  apply hG.congr
  symm
  filter_upwards [(b3Forms_isOpen_trDom x p).mem_nhds
    (b3Forms_mem_trDom_self z.property)] with u hu
  have htu : t u ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source hu.2
  have hp : (chartAt ℂ x).symm u = (chartAt ℂ p).symm (t u) :=
    ((chartAt ℂ p).left_inv hu.2).symm
  change (if h : u ∈ (chartAt ℂ x).target then θ (b3Forms_chartVec x (1 : ℂ) u) else 0) = G u
  rw [dite_eq_left hu.1, rf2_linear_chart_transition C θ hθ x p ⟨u, hu.1⟩ ⟨t u, htu⟩ hp,
    rf2_linear_chart_coefficient C θ hθ p ⟨t u, htu⟩]

theorem rf2_linearField_chart_congr_on_open (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (U : Set C) (hU : IsOpen U)
    (θ η : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (he : ∀ p ∈ U, ∀ v : TangentSpace 𝓘(ℂ, ℂ) p, θ ⟨p, v⟩ = η ⟨p, v⟩)
    (x : C) (z : (chartAt ℂ x).target) (hz : (chartAt ℂ x).symm z ∈ U) :
    rf2_extend C (fun y w ↦ θ (b3Forms_chartVec y (1 : ℂ) w)) x =ᶠ[𝓝 (z : ℂ)]
      rf2_extend C (fun y w ↦ η (b3Forms_chartVec y (1 : ℂ) w)) x := by
  filter_upwards [((chartAt ℂ x).isOpen_inter_preimage_symm hU).mem_nhds
    (show (z : ℂ) ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' U from
      ⟨z.property, hz⟩)] with u hu
  simp only [rf2_extend, dite_eq_left hu.1]
  exact he ((chartAt ℂ x).symm u) hu.2 ((b3Forms_chartVec x (1 : ℂ) u).2)

theorem rf2_product_boundary_of_order (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ))
    (hgw : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) w p) 0 ≠ ⊤)
    (N : Set C) (hN : IsOpen N)
    (hZN : Function.support (b4c_ordForm (hE := Module.finrank_self ℂ) w) ⊆ N)
    (P : rf2_exactAway C N →ₗ[ℂ] b4c_SmoothFun ℂ C)
    (hP : ∀ θ, rf2_dbar00 C (P θ) = θ.val.val) (θ : rf2_exactAway C N)
    (ho : ∀ p ∈ N, 0 ≤ meromorphicOrderAt (fun τ ↦
      HurwitzPrymRR_loc (Module.finrank_self ℂ)
        (b4c_residue_normalizedForm (Module.finrank_self ℂ) w) p τ *
        rf2_primitiveFamily C P p θ τ) 0) :
    (fun x z ↦ rf2_meroCoeff C w x z * θ.val.val x z) ∈
      Submodule.span ℂ (rf2_dbar10 C '' (rf2_smoothForms C 1 0 : Set (rf2_Coeff C))) := by
  let Z := Function.support (b4c_ordForm (hE := Module.finrank_self ℂ) w)
  have hZ : IsClosed Z := (b4c_meroForm_orderSupport_finite (Module.finrank_self ℂ) w).isClosed
  let wNorm := b4c_residue_normalizedForm (Module.finrank_self ℂ) w
  let η : TangentBundle 𝓘(ℂ, ℂ) C → ℂ := fun v ↦ wNorm v * (P θ).val v.proj
  have hη : HurwitzPrymRR_IsLinear η := by
    intro p a v v'
    change wNorm ⟨p, a • v + v'⟩ * (P θ).val p =
      a * (wNorm ⟨p, v⟩ * (P θ).val p) + wNorm ⟨p, v'⟩ * (P θ).val p
    have he : wNorm ⟨p, a • v + v'⟩ = a * wNorm ⟨p, v⟩ + wNorm ⟨p, v'⟩ :=
      b4c_residue_normalizedForm_linear (Module.finrank_self ℂ) w p a v v'
    rw [he]
    ring
  have hloc (p : C) : HurwitzPrymRR_loc (Module.finrank_self ℂ) η p =
      (fun τ ↦ HurwitzPrymRR_loc (Module.finrank_self ℂ) wNorm p τ * rf2_primitiveFamily C P p θ τ) := by
    rfl
  have hm (p : C) (hp : p ∈ N) : MeromorphicAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) η p) 0 := by
    rw [hloc]
    exact ((b4c_residue_normalizedForm_mem (Module.finrank_self ℂ) w).2 p).mul
      (rf2_primitiveFamily_analytic C N hN P hP p hp θ).meromorphicAt
  have horder (p : C) (hp : p ∈ N) : 0 ≤ meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) η p) 0 := by
    rw [hloc]
    exact ho p hp
  have hwNorm (p : C) (hp : p ∉ Z) : AnalyticAt ℂ (HurwitzPrymRR_loc (Module.finrank_self ℂ) wNorm p) 0 := by
    have hp0 : b4c_ordForm (hE := Module.finrank_self ℂ) w p = 0 := by
      simpa only [Z, Function.mem_support, not_not] using hp
    exact (rf2_normalized_unit_at C w hgw p hp0).1
  have ha (p : C) (hp : p ∈ N) (hpZ : p ∉ Z) : AnalyticAt ℂ (HurwitzPrymRR_loc (Module.finrank_self ℂ) η p) 0 := by
    rw [hloc]
    exact (hwNorm p hpZ).mul (rf2_primitiveFamily_analytic C N hN P hP p hp θ)
  have hs (p : C) (hp : p ∉ Z) : ContDiffAt ℝ ∞ (HurwitzPrymRR_loc (Module.finrank_self ℂ) η p) 0 := by
    rw [hloc]
    exact ((hwNorm p hp).contDiffAt.restrict_scalars ℝ).mul (rf2_primitiveFamily_smooth C P p θ)
  let F := rf2_repairLinearField C Z η
  have hF : HurwitzPrymRR_IsLinear F := rf2_repairLinearField_linear C Z η hη
  let v : rf2_smoothForms C 1 0 := ⟨fun x z ↦ F (b3Forms_chartVec x (1 : ℂ) z),
    rf2_repairLinearField_smooth C Z N hZ hN hZN η hη hm horder ha hs⟩
  have hd (x : C) (z : (chartAt ℂ x).target) :
      wirtingerDbar (rf2_extend C v.val x) z = rf2_meroCoeff C w x z * θ.val.val x z := by
    by_cases hp : (chartAt ℂ x).symm z ∈ N
    · have he := (rf2_repairLinearField_loc_on C Z N hN η hη ha _ hp).trans
        (rf2_normalizeLinearField_loc C η hη _ (hm _ hp))
      have hA := (hm _ hp).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp (horder _ hp)
      have hc : AnalyticAt ℂ (HurwitzPrymRR_loc (Module.finrank_self ℂ) F ((chartAt ℂ x).symm z)) 0 :=
        hA.congr he.symm
      have hg := rf2_linear_chart_coefficient_analytic C F hF x z hc
      rw [θ.property.2 x z hp, mul_zero]
      exact rf2_wirtingerDbar_hol hg.differentiableAt
    · have hpZ : (chartAt ℂ x).symm z ∉ Z := fun hz ↦ hp (hZN hz)
      have he := rf2_linearField_chart_congr_on_open C Zᶜ hZ.isOpen_compl F η
        (fun p hp v ↦ if_neg hp) x z hpZ
      have he' : rf2_extend C (fun y w ↦ η (b3Forms_chartVec y (1 : ℂ) w)) x =ᶠ[𝓝 (z : ℂ)]
          (fun t ↦ rf2_extend C (rf2_meroCoeff C w) x t * ((P θ).val ∘ (chartAt ℂ x).symm) t) := by
        filter_upwards [(chartAt ℂ x).open_target.mem_nhds z.property] with t ht
        simp only [rf2_extend, dite_eq_left ht]
        change wNorm (b3Forms_chartVec x (1 : ℂ) t) * (P θ).val ((chartAt ℂ x).symm t) =
          wNorm ⟨(chartAt ℂ x).symm t, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ x).symm t (1 : ℂ)⟩ * _
        rw [rf2_inverse_chart_vector C x ⟨t, ht⟩ (1 : ℂ)]
        rfl
      have heq := he.trans he'
      have hder := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ antiLinearPart L 1) heq.fderiv_eq
      have hp0 : b4c_ordForm (hE := Module.finrank_self ℂ) w ((chartAt ℂ x).symm z) = 0 := by
        simpa only [Z, Function.mem_support, not_not] using hpZ
      have hmc := (rf2_meroCoeff_regular C w hgw x z hp0).1
      have hu := ((P θ).property.comp_contMDiffOn
        (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := x))).contDiffOn
      have hud := ((hu z z.property).contDiffAt ((chartAt ℂ x).open_target.mem_nhds z.property)).differentiableAt (by simp)
      change wirtingerDbar (rf2_extend C v.val x) z = _
      rw [show wirtingerDbar (rf2_extend C v.val x) z = wirtingerDbar
        (fun t ↦ rf2_extend C (rf2_meroCoeff C w) x t * ((P θ).val ∘ (chartAt ℂ x).symm) t) z from hder]
      rw [rf2_wirtingerDbar_mul (hmc.differentiableAt.restrictScalars ℝ) hud,
        rf2_wirtingerDbar_hol hmc.differentiableAt, mul_zero, add_zero]
      rw [show wirtingerDbar ((P θ).val ∘ (chartAt ℂ x).symm) z = θ.val.val x z from
        congrFun (congrFun (hP θ) x) z]
      simp only [rf2_extend, dite_eq_left z.property]
  apply Submodule.subset_span
  refine ⟨(-v).val, (-v).property, ?_⟩
  funext x z
  have he : rf2_extend C (-v).val x = (fun t ↦ -rf2_extend C v.val x t) := by
    funext t
    change (if h : t ∈ (chartAt ℂ x).target then -v.val x ⟨t, h⟩ else 0) =
      -(if h : t ∈ (chartAt ℂ x).target then v.val x ⟨t, h⟩ else 0)
    split_ifs <;> simp only [neg_zero]
  change -antiLinearPart (fderiv ℝ (rf2_extend C (-v).val x) z) 1 = _
  rw [he, fderiv_fun_neg]
  simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]
  exact hd x z

theorem rf2_principal_obstruction_aux (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ))
    (hw : (w : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) ≠ 0)
    (hgw : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) w x) 0 ≠ ⊤) (N : Set C) (hN : IsOpen N)
    (hZN : Function.support (b4c_ordForm (hE := Module.finrank_self ℂ) w) ⊆ N) :
    ∃ π : rf2_exactAway C N →ₗ[ℂ] (Fin (rf2_poleBudget C w) → ℂ),
      ∀ θ ∈ π.ker,
        (fun x z ↦ rf2_meroCoeff C w x z * θ.val.val x z) ∈
          Submodule.span ℂ (rf2_dbar10 C ''
            (rf2_smoothForms C 1 0 : Set (rf2_Coeff C))) := by
  obtain ⟨P, π, hP, hπ⟩ := rf2_poleJetMap C w hgw N hN hZN
  refine ⟨π, ?_⟩
  intro θ hθ
  exact rf2_product_boundary_of_order C w hgw N hN hZN P hP θ (hπ θ hθ)

theorem rf2_dimension_of_kernel_inclusion {V Q W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    (f : V →ₗ[ℂ] Q) (hf : Function.Surjective f) (g : V →ₗ[ℂ] W)
    (hker : g.ker ≤ f.ker) :
    Module.Finite ℂ Q ∧ Module.finrank ℂ Q ≤ Module.finrank ℂ W := by
  letI : Module.Finite ℂ (V ⧸ g.ker) := Module.Finite.of_surjective
    g.quotKerEquivRange.symm.toLinearMap g.quotKerEquivRange.symm.surjective
  let F : (V ⧸ g.ker) →ₗ[ℂ] Q := g.ker.liftQ f hker
  have hF : Function.Surjective F := by
    intro q
    obtain ⟨v, rfl⟩ := hf q
    exact ⟨g.ker.mkQ v, rfl⟩
  refine ⟨Module.Finite.of_surjective F hF, ?_⟩
  exact (LinearMap.finrank_le_finrank_of_surjective hF).trans
    (g.quotKerEquivRange.finrank_eq.trans_le (Submodule.finrank_le g.range))

theorem rf2_dimension_of_no_independent_family {Q : Type*} [AddCommGroup Q] [Module ℂ Q]
    (n : ℕ) (h : ∀ v : Fin (n + 1) → Q, ¬ LinearIndependent ℂ v) :
    Module.Finite ℂ Q ∧ Module.finrank ℂ Q ≤ n := by
  letI : Module.Free ℂ Q := Module.Free.of_divisionRing ℂ Q
  have hr : Module.rank ℂ Q < ((n + 1 : ℕ) : Cardinal) := by
    apply lt_of_not_ge
    intro hge
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank hge
    exact h v hv
  letI : Module.Finite ℂ Q := Module.rank_lt_aleph0_iff.mp
    (hr.trans Cardinal.natCast_lt_aleph0)
  refine ⟨inferInstance, ?_⟩
  by_contra hn
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank
    (show n + 1 ≤ Module.finrank ℂ Q by omega)
  exact h v hv

theorem rf2_vanishing_image_bound (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ))
    (hw : (w : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) ≠ 0)
    (hgw : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) w p) 0 ≠ ⊤)
    (N : Set C) (hN : IsOpen N)
    (hZN : Function.support (b4c_ordForm (hE := Module.finrank_self ℂ) w) ⊆ N) :
    ∃ T : rf2_vanishing C 0 1 N →ₗ[ℂ] ((rf2_smoothForms C 1 1) ⧸ rf2_boundaries C),
      Module.Finite ℂ T.range ∧
      Module.finrank ℂ T.range ≤ Module.finrank ℂ (b3_HolForm ℂ C) + rf2_poleBudget C w ∧
      ∀ τ : rf2_vanishing C 1 1 N, ∃ θ, T θ = (rf2_boundaries C).mkQ τ.val := by
  obtain ⟨e, he⟩ := rf2_divide_by_form_aux C w hw hgw N hN hZN
  obtain ⟨π, hπ⟩ := rf2_principal_obstruction_aux C w hw hgw N hN hZN
  let B := (rf2_smoothForms C 0 1) ⧸ rf2_boundaries01 C
  let E := rf2_exactAway C N
  let T := (rf2_boundaries C).mkQ.comp ((rf2_vanishing C 1 1 N).subtype.comp e.toLinearMap)
  let g := (rf2_boundaries01 C).mkQ.comp (rf2_vanishing C 0 1 N).subtype
  obtain ⟨R, hR⟩ := E.subtype.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr E.injective_subtype)
  let G := g.prod ((π.comp R).comp (rf2_vanishing C 0 1 N).subtype)
  have hker : G.ker ≤ T.rangeRestrict.ker := by
    intro θ hθ
    have hg := congrArg Prod.fst (LinearMap.mem_ker.mp hθ)
    have hj := congrArg Prod.snd (LinearMap.mem_ker.mp hθ)
    change (rf2_boundaries01 C).mkQ θ.val = 0 at hg
    have hb : θ.val ∈ rf2_boundaries01 C := (Submodule.Quotient.mk_eq_zero _).mp hg
    let ε : E := ⟨θ.val, hb, θ.property⟩
    have hr : R θ.val = ε := LinearMap.congr_fun hR ε
    change π (R θ.val) = 0 at hj
    rw [hr] at hj
    have hs := hπ ε (LinearMap.mem_ker.mpr hj)
    apply Subtype.ext
    change T θ = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change (e θ).val.val ∈ Submodule.span ℂ
      (rf2_dbar10 C '' (rf2_smoothForms C 1 0 : Set (rf2_Coeff C)))
    have hval : (e θ).val.val = fun x z ↦ rf2_meroCoeff C w x z * θ.val.val x z := by
      funext x z
      exact he θ x z
    rw [hval]
    exact hs
  have hsc := b4c_dolbeault_finite (E := ℂ) (C := C) (Module.finrank_self ℂ)
  letI : Module.Finite ℂ (b4c_Dolbeault01 ℂ C) := hsc.1
  obtain ⟨eB⟩ := rf2_dolbeault01_compare_aux C
  letI : Module.Finite ℂ B := Module.Finite.of_surjective eB.symm.toLinearMap eB.symm.surjective
  have hB : Module.finrank ℂ B = Module.finrank ℂ (b3_HolForm ℂ C) := eB.finrank_eq.trans hsc.2
  have hd := rf2_dimension_of_kernel_inclusion T.rangeRestrict T.surjective_rangeRestrict G hker
  refine ⟨T, hd.1, ?_, ?_⟩
  · calc
      Module.finrank ℂ T.range ≤ Module.finrank ℂ B + rf2_poleBudget C w := by
        simpa only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin,
          Module.finrank_self, mul_one] using hd.2
      _ = _ := by rw [hB]
  · intro τ
    refine ⟨e.symm τ, ?_⟩
    change (rf2_boundaries C).mkQ (e (e.symm τ)).val = (rf2_boundaries C).mkQ τ.val
    rw [e.apply_symm_apply]

theorem rf2_dbar_forms_aux (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] (w : b4c_MeroForm ℂ C (Module.finrank_self ℂ))
    (hw : (w : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) ≠ 0)
    (hgw : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) w x) 0 ≠ ⊤) :
    Module.Finite ℂ ((rf2_smoothForms C 1 1) ⧸ rf2_boundaries C) ∧
      Module.finrank ℂ ((rf2_smoothForms C 1 1) ⧸ rf2_boundaries C) ≤
        Module.finrank ℂ (b3_HolForm ℂ C) + rf2_poleBudget C w := by
  apply rf2_dimension_of_no_independent_family (Module.finrank ℂ (b3_HolForm ℂ C) + rf2_poleBudget C w)
  intro c hc
  choose τ hτ using (fun i ↦ (rf2_boundaries C).mkQ_surjective (c i))
  let Z := (b4c_divForm (hE := Module.finrank_self ℂ) w).support
  have hlocal (i) := rf2_dbar11_localize_aux C Z (τ i)
  choose U b hU hZU hloc using hlocal
  let N : Set C := ⋂ i, U i
  have hN : IsOpen N := isOpen_iInter_of_finite hU
  have hZN : Function.support (b4c_ordForm (hE := Module.finrank_self ℂ) w) ⊆ N := by
    intro p hp
    apply mem_iInter.mpr
    intro i
    apply hZU i
    change p ∈ (b4c_divForm (hE := Module.finrank_self ℂ) w).support
    apply Finsupp.mem_support_iff.mpr
    rw [RiemannRochAna_divForm_apply_of_finite (Module.finrank_self ℂ) w
      (b4c_meroForm_orderSupport_finite (Module.finrank_self ℂ) w)]
    exact hp
  let db (i) : rf2_smoothForms C 1 1 := ⟨rf2_dbar10 C (b i).val, rf2_dbar10_smooth_aux C (b i)⟩
  let a (i) : rf2_smoothForms C 1 1 := τ i - db i
  have ha (i) : a i ∈ rf2_vanishing C 1 1 N := by
    intro x z hz
    change (τ i).val x z - rf2_dbar10 C (b i).val x z = 0
    exact hloc i x z (mem_iInter.mp hz i)
  have hdb (i) : (rf2_boundaries C).mkQ (db i) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change rf2_dbar10 C (b i).val ∈ Submodule.span ℂ
      (rf2_dbar10 C '' (rf2_smoothForms C 1 0 : Set (rf2_Coeff C)))
    exact Submodule.subset_span ⟨(b i).val, (b i).property, rfl⟩
  have hclass (i) : (rf2_boundaries C).mkQ (a i) = c i := by
    change (rf2_boundaries C).mkQ (τ i - db i) = c i
    rw [map_sub, hdb, sub_zero, hτ]
  obtain ⟨T, hTfin, hTdim, hT⟩ := rf2_vanishing_image_bound C w hw hgw N hN hZN
  have hmem (i) : c i ∈ T.range := by
    obtain ⟨θ, hθ⟩ := hT ⟨a i, ha i⟩
    exact ⟨θ, hθ.trans (hclass i)⟩
  let v := fun i ↦ (⟨c i, hmem i⟩ : T.range)
  have hli : LinearIndependent ℂ v := LinearIndependent.of_comp T.range.subtype hc
  letI : Module.Finite ℂ T.range := hTfin
  have hcard := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

end HodgeLean.Foundations.Program
