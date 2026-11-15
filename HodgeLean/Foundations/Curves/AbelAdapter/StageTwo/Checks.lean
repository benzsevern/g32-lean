import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.Defs
import HodgeLean.Adapters.LatticeClassHQDefs
import HodgeLean.Adapters.HodgeDegreeOneAbelian
import HodgeLean.Foundations.IntegralHomology.StageThree.SurfaceIntegration
import HodgeLean.Foundations.IntegralHomology.Basic

/-! # Independent elliptic normalization tests for stage two

These tests import no stage-two interface bodies.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.Program HodgeLean.Foundations.IntegralHomology.StageThree
open scoped TensorProduct Manifold ContDiff CategoryTheory.MonObj
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
local instance abelS2Connected : ConnectedSpace b3_Elliptic := b3_elliptic_connectedSpace
private abbrev h := b3_ellipticModel_finrank
private abbrev Λ := b3_periodLattice b3_EllipticModel b3_Elliptic
private abbrev F := b3_periodF b3_EllipticModel b3_Elliptic
private abbrev J := b3_Jacobian b3_EllipticModel b3_Elliptic
private abbrev M := model (E := b3_EllipticModel) (C := b3_Elliptic) h
private abbrev a : Λ := b3_latticePeriod _ _ b3A_loopA
private abbrev b : Λ := b3_latticePeriod _ _ b3A_loopB
local instance abelS2Finite : Module.Finite ℤ Λ := b3_periodLattice_finite h
local instance abelS2Free : Module.Free ℤ Λ := b3_periodLattice_free
local instance abelS2Discrete : DiscreteTopology (b2_latticeMap Λ F).range :=
  b2_latticeMap_discrete F (b3_isWeightOne h)
private abbrev A := analyticAbel (E := b3_EllipticModel) (C := b3_Elliptic) h (0 : b3_Elliptic)
private theorem A_spec : b3_IsAbelJacobi _ _ (0 : b3_Elliptic) A :=
  (b3_exists_abelJacobi h (0 : b3_Elliptic)).choose_spec
private theorem A_cont : Continuous A := (b3_abelJacobi_holomorphic h _ A A_spec).continuous
private abbrev v := b2_coord (b3Rest2_QJ b3_EllipticModel b3_Elliptic)
  (b2_latticeMap Λ F a)

private theorem covector_value : periodCovector h b3A_dz v = (1 : ℂ) := by
  change b3Rest2_ellV b3A_dz v = 1
  rw [b3Rest2_ellV_coord]
  change b3_cplxPeriod _ _ ((1 : ℂ) ⊗ₜ[ℤ] a) b3A_dz = 1
  simpa only [Complex.ofReal_one, Complex.ofReal_zero, TensorProduct.zero_tmul,
    add_zero, zero_mul] using b3A_X_dz 1 0

private theorem integral_value :
    surfaceIntegrationLattice A A_cont (loopClass b3A_loopA) = a :=
  surfaceIntegration_loop h (0 : b3_Elliptic) A A_cont A_spec b3A_loopA

private theorem a_nonzero : a ≠ 0 := by
  intro hz
  have hh := covector_value
  simp only [v, hz, map_zero] at hh
  norm_num at hh

private theorem integralAbelSquare_falsification :
    modelPeriod h (surfaceIntegrationLattice A A_cont (loopClass b3A_loopA)) ≠
      modelPeriod h (2 • a) := by
  have hi : Function.Injective (modelPeriod (C := b3_Elliptic) h) :=
    (b5_periodMap_bijective Λ F (b3_isWeightOne (C := b3_Elliptic) h)
      (polarization (C := b3_Elliptic) h)
      (b3_intersectionForm_isRiemannForm (C := b3_Elliptic) h _ (b3_exists_intersectionForm (C := b3_Elliptic) h).choose_spec)).1
  intro he
  have he' := hi ((congrArg (modelPeriod (C := b3_Elliptic) h) integral_value).symm.trans he)
  have he'' : a + (0 : Λ) = a + a := by simpa only [add_zero, two_smul] using he'
  exact a_nonzero (add_left_cancel he'').symm

example : surfaceIntegrationLattice A A_cont (loopClass b3A_loopA) = a := integral_value

private theorem translate_point (B : Over (Spec ↧ℂ)) [GrpObj B]
    (t x : ComplexPoint B) : Point.map (translation B t).hom x = x * t := by
  change x ≫ (CategoryTheory.CartesianMonoidalCategory.lift (𝟙 B)
    (CategoryTheory.SemiCartesianMonoidalCategory.toUnit B ≫ t) ≫ MonObj.mul) =
      CategoryTheory.CartesianMonoidalCategory.lift x t ≫ MonObj.mul
  rw [← Category.assoc, CategoryTheory.CartesianMonoidalCategory.comp_lift]
  congr 1
  ext <;> simp

private abbrev q : J := QuotientAddGroup.mk (Submodule.Quotient.mk ((1 / 4 : ℂ) ⊗ₜ[ℤ] a))
private theorem q_nonzero : q ≠ 0 := by
  intro hz
  have hz' : q = QuotientAddGroup.mk (Submodule.Quotient.mk (0 : ℂ ⊗[ℤ] Λ)) := by
    simpa only [Submodule.Quotient.mk_zero, QuotientAddGroup.mk_zero] using hz
  obtain ⟨l, hl⟩ := b3A_jacobian_eq hz'
  obtain ⟨x, hx⟩ := b3A_lattice_dz l
  have hp : b3_cplxPeriod _ _ ((1 / 4 : ℂ) ⊗ₜ[ℤ] a) b3A_dz = (1 / 4 : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Complex.ofReal_zero, TensorProduct.zero_tmul, add_zero, zero_mul] using b3A_X_dz (1 / 4) 0
  have he := congrArg Complex.re ((congrFun hl b3A_dz).trans hx)
  simp only [Pi.sub_apply, map_zero, Pi.zero_apply, hp, zero_sub] at he
  have he' : -(1 / 4 : ℝ) = (x 0 : ℝ) := by simpa using he
  have hlo : (-1 : ℤ) < x 0 := by exact_mod_cast (show (-1 : ℝ) < (x 0 : ℝ) by linarith)
  have hhi : x 0 < (0 : ℤ) := by exact_mod_cast (show (x 0 : ℝ) < (0 : ℝ) by linarith)
  omega

private theorem theta_zero : theta (E := b3_EllipticModel) (C := b3_Elliptic) h (0 : J) =
    (1 : ComplexPoint M) :=
  (b5_group Λ F (b3_isWeightOne h) (polarization h)
    (b3_intersectionForm_isRiemannForm (C := b3_Elliptic) h _ (b3_exists_intersectionForm (C := b3_Elliptic) h).choose_spec)).1

private abbrev t : ComplexPoint M := theta h q
private theorem t_ne_one : t ≠ 1 := by
  intro he
  exact q_nonzero ((theta h).injective (he.trans theta_zero.symm))

private theorem translationPoint_falsification :
    Point.map (translation M t).hom (1 : ComplexPoint M) ≠ (1 : ComplexPoint M) := by
  intro he
  exact t_ne_one (((translate_point M t 1).trans (one_mul t)).symm.trans he)

example : Point.map (translation M t).hom (1 : ComplexPoint M) = t := by
  exact (translate_point M t 1).trans (one_mul t)

private theorem translation_h1_value (c : HQ M 1) :
    homPullback (translation M t).hom 1 c = c := ccm8_translation_pullback M t 1 c

example (c : HQ M 1) : homPullback (translation M t).hom 1 c = c := translation_h1_value c

private theorem polarization_value : polarization (C := b3_Elliptic) h a b = 1 :=
  ((b3_exists_intersectionForm (C := b3_Elliptic) h).choose_spec b3A_loopA b3A_loopB
    (b3_elliptic_transverse _ _ rfl rfl)).trans (b3_elliptic_intersection _ _ rfl rfl)

private def periodsEquiv : Λ ≃ₗ[ℤ] abelianPeriodLattice M :=
  LinearEquiv.ofBijective (modelPeriod h)
    (b5_periodMap_bijective Λ F (b3_isWeightOne (C := b3_Elliptic) h)
      (polarization (C := b3_Elliptic) h)
      (b3_intersectionForm_isRiemannForm (C := b3_Elliptic) h _ (b3_exists_intersectionForm (C := b3_Elliptic) h).choose_spec))
private def χ : abelianPeriodLattice M →+ ℚ :=
  (Int.castAddHom ℚ).comp (((polarization h a).toAddMonoidHom).comp
    periodsEquiv.symm.toAddMonoidHom)
private def c : HQ M 1 := (abelianPeriodEquiv M).symm χ
private theorem c_nonzero : c ≠ 0 := by
  have hv : χ (periodsEquiv b) = (1 : ℚ) := by
    change (polarization h a (periodsEquiv.symm (periodsEquiv b)) : ℚ) = 1
    exact congrArg (fun z : ℤ ↦ (z : ℚ))
      ((congrArg (polarization (C := b3_Elliptic) h a)
        (periodsEquiv.symm_apply_apply b)).trans polarization_value)
  intro hz
  have he : χ = 0 :=
    ((abelianPeriodEquiv M).apply_symm_apply χ).symm.trans
      ((congrArg (abelianPeriodEquiv M) hz).trans (map_zero _))
  have he' : χ (periodsEquiv b) = (0 : ℚ) := congrArg
    (fun f : abelianPeriodLattice M →+ ℚ ↦ f (periodsEquiv b)) he
  exact (by norm_num : (1 : ℚ) ≠ 0) (hv.symm.trans he')

private theorem translationH1_falsification : homPullback (translation M t).hom 1 c ≠ 0 := by
  intro he
  exact c_nonzero ((translation_h1_value c).symm.trans he)

private theorem factorH1_falsification :
    homPullback (translation M t).hom 1 c ≠
      (2 : ℚ) • homPullback (𝟙 M) 1 (homPullback (translation M t).hom 1 c) := by
  intro he
  have he : c = (2 : ℚ) • c :=
    (translation_h1_value c).symm.trans (he.trans
      (congrArg (fun y : HQ M 1 ↦ (2 : ℚ) • y)
        ((congrArg (fun f : HQ M 1 →ₗ[ℚ] HQ M 1 ↦ f
          (homPullback (translation M t).hom 1 c)) (spec_homPullback_id (X := M) 1)).trans
          (translation_h1_value c))))
  have hh : c + (0 : HQ M 1) = c + c := by simpa only [two_smul, add_zero] using he
  exact c_nonzero (add_left_cancel hh).symm

example : homPullback (translation M t).hom 1 c =
    homPullback (𝟙 M) 1 (homPullback (translation M t).hom 1 c) := by
  exact (congrArg (fun f : HQ M 1 →ₗ[ℚ] HQ M 1 ↦ f
    (homPullback (translation M t).hom 1 c)) (spec_homPullback_id (X := M) 1)).symm

private theorem model_dimension : TopologicalSpace.dim M.left = 1 := by
  let hQ := b3_intersectionForm_isRiemannForm (C := b3_Elliptic) h
    (polarization (C := b3_Elliptic) h) (b3_exists_intersectionForm (C := b3_Elliptic) h).choose_spec
  letI : IsIntegral (b5_model Λ F (b3_isWeightOne h) (polarization h)).left :=
    b5_integral Λ F (b3_isWeightOne h) (polarization h) hQ
  change TopologicalSpace.dim (b5_model Λ F (b3_isWeightOne h) (polarization h)).left = 1
  have hr := b2_two_mul_finrank F (b3_isWeightOne h)
  have hrank := b3_finrank_periodLattice (E := b3_EllipticModel) (C := b3_Elliptic) h
  have hg := b3_elliptic_finrank_holForm
  have hZ : Module.finrank ℤ Λ = 2 := hrank.trans (congrArg (fun n : ℕ ↦ 2 * n) hg)
  have hquot : Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F) = 1 :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hr.trans hZ)
  have hd := (b5_periodLinearEquiv Λ F (b3_isWeightOne h) (polarization h)
    (b3_intersectionForm_isRiemannForm (C := b3_Elliptic) h _
      (b3_exists_intersectionForm (C := b3_Elliptic) h).choose_spec)).finrank_eq
  simpa only [b5_V, Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
    smul_eq_mul, mul_one, hquot] using hd.symm

private def coordinateIndex : Fin (TopologicalSpace.dim M.left) :=
  ⟨0, by rw [model_dimension]; norm_num⟩
private def coordinate : (Fin (TopologicalSpace.dim M.left) → ℂ) →L[ℂ] ℂ :=
  ContinuousLinearMap.proj coordinateIndex
private def invariantForm : GlobalHolomorphicForm M 1 :=
  (spec_exists_closed_expPullback_eq M coordinate).choose
private theorem invariantForm_spec :
    expPullback M (TopologicalSpace.dim M.left) invariantForm 0 = coordinate :=
  (spec_exists_closed_expPullback_eq M coordinate).choose_spec.2
private def tangent : Fin (TopologicalSpace.dim M.left) → ℂ := fun _ ↦ 1
private def expTangent : Fin (TopologicalSpace.dim M.left) → ℂ :=
  mfderiv 𝓘(ℂ, Fin (TopologicalSpace.dim M.left) → ℂ)
    𝓘(ℂ, Fin (TopologicalSpace.dim M.left) → ℂ)
    (fun z ↦ (complexExponential M (TopologicalSpace.dim M.left) z).toMul) 0 tangent
private abbrev origin := (complexExponential M (TopologicalSpace.dim M.left) 0).toMul
private theorem scheme_value : schemeForm M invariantForm ⟨origin, expTangent⟩ = (1 : ℂ) := by
  change expPullback M (TopologicalSpace.dim M.left) invariantForm 0 tangent = 1
  exact congrArg (fun f : (Fin (TopologicalSpace.dim M.left) → ℂ) →L[ℂ] ℂ ↦ f tangent)
    invariantForm_spec

private theorem schemeCoordinates_falsification :
    schemeForm M invariantForm ⟨origin, expTangent⟩ ≠
      -schemeForm M invariantForm ⟨origin, expTangent⟩ := by
  intro he
  have hh : (1 : ℂ) = -(1 : ℂ) := scheme_value.symm.trans
    (he.trans (congrArg Neg.neg scheme_value))
  norm_num at hh

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 20000
private abbrev VJ := b3Rest2_VJ b3_EllipticModel b3_Elliptic
private abbrev VM := Fin (TopologicalSpace.dim M.left) → ℂ
set_option maxHeartbeats 20000 in
private def periodLinear : VJ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj b3A_dz).comp
      ((F.liftQ (b3_cplxPeriod _ _) le_rfl).comp
        (b2_coord (b3Rest2_QJ b3_EllipticModel b3_Elliptic)).symm.toLinearMap))
private theorem periodLinear_value : periodLinear v = (1 : ℂ) := covector_value
private def jacobianForm : TangentBundle 𝓘(ℂ, VJ) J → ℂ := b3A_invForm F periodLinear
private theorem theta_smooth :
    ContMDiff 𝓘(ℂ, VJ) 𝓘(ℂ, VM) ω (theta (E := b3_EllipticModel) (C := b3_Elliptic) h) :=
  (b5_theta_holomorphicFunctions Λ F (b3_isWeightOne (C := b3_Elliptic) h) (polarization (C := b3_Elliptic) h)
    (b3_intersectionForm_isRiemannForm (C := b3_Elliptic) h _
      (b3_exists_intersectionForm (C := b3_Elliptic) h).choose_spec)).1
private theorem theta_inverse_smooth :
    ContMDiff 𝓘(ℂ, VM) 𝓘(ℂ, VJ) ω (theta (E := b3_EllipticModel) (C := b3_Elliptic) h).symm :=
  (b5_theta_holomorphicFunctions Λ F (b3_isWeightOne (C := b3_Elliptic) h) (polarization (C := b3_Elliptic) h)
    (b3_intersectionForm_isRiemannForm (C := b3_Elliptic) h _
      (b3_exists_intersectionForm (C := b3_Elliptic) h).choose_spec)).2.1
private def thetaForm : TangentBundle 𝓘(ℂ, VM) (ComplexPoint M) → ℂ :=
  b3_pullback (C := ComplexPoint M) (C' := J) VM VJ (theta (E := b3_EllipticModel) (C := b3_Elliptic) h).symm jacobianForm
private theorem thetaForm_holomorphic : thetaForm ∈ b3_HolForm VM (ComplexPoint M) := by
  letI abelS2JacobianManifold : IsManifold 𝓘(ℂ, VJ) ω J := b2_torus_isManifold F
  exact b3_pullback_mem_holForm
    (theta (E := b3_EllipticModel) (C := b3_Elliptic) h).symm
    theta_inverse_smooth jacobianForm (b3A_invForm_mem F periodLinear)

private theorem pathIntegral_smul_check
    {U S : Type} [NormedAddCommGroup U] [NormedSpace ℂ U]
    [TopologicalSpace S] [ChartedSpace U S]
    (path : ℝ → S) (form : TangentBundle 𝓘(ℂ, U) S → ℂ) (c : ℂ) :
    b3_pathIntegral U S path (c • form) = c * b3_pathIntegral U S path form := by
  simp only [b3_pathIntegral, Pi.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]

private theorem pullback_comp_check
    {U V W : Type} [NormedAddCommGroup U] [NormedSpace ℂ U]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    {S T R : Type} [TopologicalSpace S] [ChartedSpace U S]
    [TopologicalSpace T] [ChartedSpace V T]
    [TopologicalSpace R] [ChartedSpace W R]
    (f : S → T) (hf : MDifferentiable 𝓘(ℂ, U) 𝓘(ℂ, V) f)
    (g : T → R) (hg : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, W) g)
    (form : TangentBundle 𝓘(ℂ, W) R → ℂ) :
    b3_pullback U W (g ∘ f) form = b3_pullback U V f (b3_pullback V W g form) := by
  funext p
  exact congrArg (fun w ↦ form ⟨g (f p.1), w⟩)
    (mfderiv_comp_apply p.1 (hg (f p.1)) (hf p.1) p.2)

private theorem pullback_inverse_check
    {U V : Type} [NormedAddCommGroup U] [NormedSpace ℂ U]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    {S T : Type} [TopologicalSpace S] [ChartedSpace U S]
    [TopologicalSpace T] [ChartedSpace V T]
    (f : S ≃ₜ T) (hf : MDifferentiable 𝓘(ℂ, U) 𝓘(ℂ, V) f)
    (hg : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, U) f.symm)
    (form : TangentBundle 𝓘(ℂ, U) S → ℂ) :
    b3_pullback U V f (b3_pullback V U f.symm form) = form := by
  rw [← pullback_comp_check f hf f.symm hg form]
  have hi : f.symm ∘ f = id := funext f.symm_apply_apply
  rw [hi]
  funext p
  change form ⟨p.1, mfderiv 𝓘(ℂ, U) 𝓘(ℂ, U) id p.1 p.2⟩ = form p
  rw [mfderiv_id]
  rfl

private theorem thetaForm_pullback :
    b3_pullback VJ VM (theta (E := b3_EllipticModel) (C := b3_Elliptic) h) thetaForm =
      jacobianForm :=
  pullback_inverse_check (theta (E := b3_EllipticModel) (C := b3_Elliptic) h)
    (theta_smooth.mdifferentiable (by simp))
    (theta_inverse_smooth.mdifferentiable (by simp)) jacobianForm
private theorem abel_pullback_comparison :
    b3_pullback b3_EllipticModel VM (modelAbel h (0 : b3_Elliptic)) thetaForm =
      b3_pullback b3_EllipticModel VJ A jacobianForm :=
  (pullback_comp_check A
    ((b3_abelJacobi_holomorphic h _ A A_spec).mdifferentiable (by simp))
    (theta (E := b3_EllipticModel) (C := b3_Elliptic) h)
    (theta_smooth.mdifferentiable (by simp)) thetaForm).trans
      (congrArg (b3_pullback b3_EllipticModel VJ A) thetaForm_pullback)
private theorem lattice_smul_check (L : Type) [AddCommGroup L]
    (G : Submodule ℂ (ℂ ⊗[ℤ] L)) (c : ℂ) (l : L) :
    c • b2_latticeMap L G l + 0 = G.mkQ (c ⊗ₜ[ℤ] l) := by
  change c • G.mkQ ((1 : ℂ) ⊗ₜ[ℤ] l) + 0 = _
  rw [add_zero, ← map_smul]
  exact congrArg G.mkQ (by simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one])

private theorem jacobian_pullback_period :
    b3_pathIntegral b3_EllipticModel b3_Elliptic b3_ellipticA
      (b3_pullback b3_EllipticModel VJ A jacobianForm) = (1 : ℂ) := by
  have hp : A ∘ b3_ellipticA = fun t : ℝ ↦
      (QuotientAddGroup.mk ((t : ℂ) • b2_latticeMap Λ F a + 0) : J) := by
    funext t
    have ht := b3_elliptic_abelJacobi_apply b3A_loopA b3A_loopB rfl rfl A A_spec t 0
    have ht' : A (b3_ellipticPoint t 0) =
        (QuotientAddGroup.mk (Submodule.Quotient.mk ((t : ℂ) ⊗ₜ[ℤ] a)) : J) := by
      simpa only [Complex.ofReal_zero, TensorProduct.zero_tmul, add_zero] using ht
    exact ht'.trans (congrArg
      (fun w : b3Rest2_QJ b3_EllipticModel b3_Elliptic ↦ (QuotientAddGroup.mk w : J))
      (lattice_smul_check Λ F (t : ℂ) a).symm)
  have hline : b3_pathIntegral VJ J
      (fun t : ℝ ↦ (QuotientAddGroup.mk ((t : ℂ) • b2_latticeMap Λ F a + 0) : J))
      jacobianForm = (1 : ℂ) := by
    simp only [b3_pathIntegral, jacobianForm, b3A_invForm,
      (b3A_torusLine F (b2_latticeMap Λ F a) 0).2, periodLinear_value,
      intervalIntegral.integral_const, sub_zero, one_smul]
  exact (b3A_pathIntegral_comp A (b3_abelJacobi_holomorphic h _ A A_spec)
    b3_ellipticA b3A_loopA.2.2 jacobianForm).symm.trans
      ((congrArg (fun (path : ℝ → J) ↦ b3_pathIntegral VJ J path jacobianForm) hp).trans hline)
private theorem abel_pullback_period :
    b3_pathIntegral b3_EllipticModel b3_Elliptic b3_ellipticA
      (b3_pullback b3_EllipticModel VM (modelAbel h (0 : b3_Elliptic)) thetaForm) =
        (1 : ℂ) :=
  (congrArg (fun form : TangentBundle 𝓘(ℂ, b3_EllipticModel) b3_Elliptic → ℂ ↦
    b3_pathIntegral b3_EllipticModel b3_Elliptic b3_ellipticA form)
      abel_pullback_comparison).trans jacobian_pullback_period
private theorem periodCovector_falsification :
    periodCovector h b3A_dz (v + v) ≠ (1 : ℂ) := by
  rw [map_add, covector_value]
  norm_num
private def quarterVector : VJ :=
  b2_coord (b3Rest2_QJ b3_EllipticModel b3_Elliptic)
    (Submodule.Quotient.mk ((1 / 4 : ℂ) ⊗ₜ[ℤ] a))
private theorem theta_cover_value :
    (theta (E := b3_EllipticModel) (C := b3_Elliptic) h ∘ b3Rest2_covHom (E := b3_EllipticModel) (C := b3_Elliptic)) quarterVector = t := by
  exact congrArg (theta (E := b3_EllipticModel) (C := b3_Elliptic) h) (b3Rest2_covHom_coord (E := b3_EllipticModel) (C := b3_Elliptic) _)
private theorem theta_cover_falsification :
    (theta (E := b3_EllipticModel) (C := b3_Elliptic) h ∘ b3Rest2_covHom (E := b3_EllipticModel) (C := b3_Elliptic)) (quarterVector + quarterVector) ≠ t := by
  intro he
  have hc : b3Rest2_covHom (E := b3_EllipticModel) (C := b3_Elliptic) quarterVector = q :=
    b3Rest2_covHom_coord (E := b3_EllipticModel) (C := b3_Elliptic) _
  have hs : b3Rest2_covHom (E := b3_EllipticModel) (C := b3_Elliptic)
      (quarterVector + quarterVector) = q + q :=
    (map_add (b3Rest2_covHom (E := b3_EllipticModel) (C := b3_Elliptic))
      quarterVector quarterVector).trans (congrArg₂ (· + ·) hc hc)
  have hh : q + q = q := (theta (E := b3_EllipticModel) (C := b3_Elliptic) h).injective
    ((congrArg (theta (E := b3_EllipticModel) (C := b3_Elliptic) h) hs).symm.trans he)
  exact q_nonzero (add_left_cancel (hh.trans (add_zero q).symm))
private theorem doubled_abel_pullback_period :
    b3_pathIntegral b3_EllipticModel b3_Elliptic b3_ellipticA
      (b3_pullback b3_EllipticModel VM (modelAbel h (0 : b3_Elliptic))
        ((2 : ℂ) • thetaForm)) = (2 : ℂ) := by
  have hs := (b3_pullback b3_EllipticModel VM (modelAbel h (0 : b3_Elliptic))).map_smul
    (2 : ℂ) thetaForm
  have hp := congrArg
    (fun form : TangentBundle 𝓘(ℂ, b3_EllipticModel) b3_Elliptic → ℂ ↦
      b3_pathIntegral b3_EllipticModel b3_Elliptic b3_ellipticA form) hs
  exact hp.trans ((pathIntegral_smul_check b3_ellipticA
    (b3_pullback b3_EllipticModel VM (modelAbel h (0 : b3_Elliptic)) thetaForm) (2 : ℂ)).trans
      ((congrArg (fun z : ℂ ↦ (2 : ℂ) * z) abel_pullback_period).trans (mul_one (2 : ℂ))))
private theorem abel_pullback_falsification :
    b3_pathIntegral b3_EllipticModel b3_Elliptic b3_ellipticA
      (b3_pullback b3_EllipticModel VM (modelAbel h (0 : b3_Elliptic)) thetaForm) ≠
      b3_pathIntegral b3_EllipticModel b3_Elliptic b3_ellipticA
        (b3_pullback b3_EllipticModel VM (modelAbel h (0 : b3_Elliptic))
          ((2 : ℂ) • thetaForm)) := by
  intro he
  have hh : (1 : ℂ) = 2 := abel_pullback_period.symm.trans (he.trans doubled_abel_pullback_period)
  norm_num at hh

private theorem invariantDifferential_falsification :
    ((theta (E := b3_EllipticModel) (C := b3_Elliptic) h ∘
      b3Rest2_covHom (E := b3_EllipticModel) (C := b3_Elliptic))
        (quarterVector + quarterVector) ≠ t) ∧
    (periodCovector h b3A_dz (v + v) ≠ (1 : ℂ)) ∧
    (b3_pathIntegral b3_EllipticModel b3_Elliptic b3_ellipticA
      (b3_pullback b3_EllipticModel VM (modelAbel h (0 : b3_Elliptic)) thetaForm) ≠
      b3_pathIntegral b3_EllipticModel b3_Elliptic b3_ellipticA
        (b3_pullback b3_EllipticModel VM (modelAbel h (0 : b3_Elliptic))
          ((2 : ℂ) • thetaForm))) :=
  ⟨theta_cover_falsification, periodCovector_falsification, abel_pullback_falsification⟩

example : (theta (E := b3_EllipticModel) (C := b3_Elliptic) h ∘ b3Rest2_covHom (E := b3_EllipticModel) (C := b3_Elliptic)) quarterVector = t := theta_cover_value
example : periodCovector h b3A_dz v = (1 : ℂ) := covector_value
example := abel_pullback_period
example := doubled_abel_pullback_period
example : thetaForm ∈ b3_HolForm VM (ComplexPoint M) := thetaForm_holomorphic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
private theorem scheme_tangent_scaling :
    schemeForm M invariantForm ⟨origin, (2 : ℂ) • expTangent⟩ ≠
      schemeForm M invariantForm ⟨origin, expTangent⟩ := by
  have hs : schemeForm M invariantForm ⟨origin, (2 : ℂ) • expTangent⟩ = (2 : ℂ) :=
    ((globalOneFormCovector M _ invariantForm origin).map_smul (2 : ℂ) expTangent).trans
      ((congrArg (fun z : ℂ ↦ (2 : ℂ) * z) scheme_value).trans (mul_one (2 : ℂ)))
  intro he
  exact (by norm_num : (2 : ℂ) ≠ 1) (hs.symm.trans (he.trans scheme_value))

example : schemeForm M invariantForm ⟨origin, expTangent⟩ = (1 : ℂ) := scheme_value

local instance abelS2TorusT2 : T2Space J := b2_torus_t2Space F

private def ellipticParametrization : b3_Elliptic ≃ₜ ComplexPoint M :=
  (A_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective A
    (b3_elliptic_abelJacobi_bijective A A_spec))).trans (theta h)
private def u : TopCat.of b3_Elliptic ⟶ TopCat.of (ComplexPoint M) :=
  TopCat.ofHom ⟨ellipticParametrization, ellipticParametrization.continuous⟩
private def uInv : TopCat.of (ComplexPoint M) ⟶ TopCat.of b3_Elliptic :=
  TopCat.ofHom ⟨ellipticParametrization.symm, ellipticParametrization.symm.continuous⟩
private abbrev modelCycle := IntegralHomology.mapLattice u (loopClass b3A_loopA)
private theorem modelCycle_period :
    surfaceIntegrationLattice A A_cont (IntegralHomology.mapLattice uInv modelCycle) = a := by
  have hu : u ≫ uInv = 𝟙 (TopCat.of b3_Elliptic) := by
    ext x
    exact ellipticParametrization.symm_apply_apply x
  have hcomp := (IntegralHomology.mapLattice_id_comp (TopCat.of b3_Elliptic)).2
    _ _ u uInv
  have hi := (IntegralHomology.mapLattice_id_comp (TopCat.of b3_Elliptic)).1
  have hval : IntegralHomology.mapLattice uInv modelCycle = loopClass b3A_loopA :=
    (congrArg (fun f : IntegralHomology.Lattice (TopCat.of b3_Elliptic) →ₗ[ℤ]
      IntegralHomology.Lattice (TopCat.of b3_Elliptic) ↦ f (loopClass b3A_loopA)) hcomp).symm.trans
      ((congrArg (fun f ↦ IntegralHomology.mapLattice f (loopClass b3A_loopA)) hu).trans
        (congrArg (fun f : IntegralHomology.Lattice (TopCat.of b3_Elliptic) →ₗ[ℤ]
          IntegralHomology.Lattice (TopCat.of b3_Elliptic) ↦ f (loopClass b3A_loopA)) hi))
  exact (congrArg (surfaceIntegrationLattice A A_cont) hval).trans integral_value
private theorem modelCycle_nonzero : modelCycle ≠ 0 := by
  intro hz
  have hv := (congrArg (fun z ↦ surfaceIntegrationLattice A A_cont
    (IntegralHomology.mapLattice uInv z)) hz)
  have h0 : surfaceIntegrationLattice A A_cont (IntegralHomology.mapLattice uInv 0) = 0 :=
    (congrArg (surfaceIntegrationLattice A A_cont) (map_zero _)).trans (map_zero _)
  exact a_nonzero (modelCycle_period.symm.trans (hv.trans h0))
private theorem identity_cycle :
    IntegralHomology.mapLattice (pointMap (𝟙 M)) modelCycle = modelCycle := by
  have hi : pointMap (𝟙 M) = 𝟙 (TopCat.of (ComplexPoint M)) := rfl
  exact (congrArg (fun f ↦ IntegralHomology.mapLattice f modelCycle) hi).trans
    (congrArg (fun f : IntegralHomology.Lattice (TopCat.of (ComplexPoint M)) →ₗ[ℤ]
      IntegralHomology.Lattice (TopCat.of (ComplexPoint M)) ↦ f modelCycle)
      (IntegralHomology.mapLattice_id_comp (TopCat.of (ComplexPoint M))).1)
private theorem integralAbelSquare_identity_falsification :
    IntegralHomology.mapLattice (pointMap (𝟙 M)) modelCycle ≠ 2 • modelCycle := by
  intro he
  have he' := identity_cycle.symm.trans he
  have hh : modelCycle + 0 = modelCycle + modelCycle := by
    simpa only [add_zero, two_smul] using he'
  exact modelCycle_nonzero (add_left_cancel hh).symm

local instance abelS2ModelConnected : ConnectedSpace (ComplexPoint M) :=
  HodgeLean.Foundations.connectedSpace_complexPoint M

set_option maxHeartbeats 20000 in
private theorem selected_abel_check :
    let hM : Module.finrank ℂ (Fin (TopologicalSpace.dim M.left) → ℂ) = 1 := by
      simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
        smul_eq_mul, mul_one] using model_dimension
    ∃ j : M ⟶ model (E := VM) (C := ComplexPoint M) hM,
      (∀ x, Point.map j x = modelAbel (E := VM) (C := ComplexPoint M) hM (1 : ComplexPoint M) x) ∧
      Point.map j (1 : ComplexPoint M) =
        theta (E := VM) (C := ComplexPoint M) hM (0 : b3_Jacobian VM (ComplexPoint M)) :=
  algebraicAbel M model_dimension (1 : ComplexPoint M)

example := selected_abel_check

private theorem elliptic_model_rank : Module.finrank ℂ VM = 1 := by
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
    smul_eq_mul, mul_one] using model_dimension

private def actualJ : M ⟶ model (E := VM) (C := ComplexPoint M) elliptic_model_rank :=
  selected_abel_check.choose
private theorem actualJ_formula (x : ComplexPoint M) :
    Point.map actualJ x =
      modelAbel (E := VM) (C := ComplexPoint M) elliptic_model_rank (1 : ComplexPoint M) x :=
  selected_abel_check.choose_spec.1 x
private def actualJ_top : TopCat.of (ComplexPoint M) ⟶
    TopCat.of (ComplexPoint (model (E := VM) (C := ComplexPoint M) elliptic_model_rank)) :=
  TopCat.ofHom ⟨modelAbel (E := VM) (C := ComplexPoint M) elliptic_model_rank (1 : ComplexPoint M),
    (holomorphicAbel elliptic_model_rank (1 : ComplexPoint M)).continuous⟩
private theorem actualJ_pointMap : pointMap actualJ = actualJ_top :=
  TopCat.ext actualJ_formula
private theorem actualJ_cycle_check : modelCycle ≠ 0 ∧
    IntegralHomology.mapLattice (pointMap actualJ) modelCycle =
      IntegralHomology.mapLattice actualJ_top modelCycle :=
  ⟨modelCycle_nonzero, congrArg (fun f ↦ IntegralHomology.mapLattice f modelCycle) actualJ_pointMap⟩

example := actualJ_cycle_check

/-- A nonzero integral class on the actual elliptic model and its algebraic identity morphism.
Source: Forster, §21; Hatcher, §2.1; surfaceIntegration_loop.
HC no distance; AV milestone no distance. -/
theorem integralAbelSquare_example :
    ∃ z : IntegralHomology.Lattice (TopCat.of (ComplexPoint M)), z ≠ 0 ∧
      IntegralHomology.mapLattice (pointMap (𝟙 M)) z = z :=
  ⟨modelCycle, modelCycle_nonzero, identity_cycle⟩

example := integralAbelSquare_example

/-- A nonidentity translation on the retained projective elliptic model.
Source: Mumford, Abelian Varieties, §1.
HC no distance; AV milestone no distance. -/
theorem translationPoint_example : ∃ t : ComplexPoint M, t ≠ 1 ∧
    Point.map (translation M t).hom (1 : ComplexPoint M) = t :=
  ⟨t, t_ne_one, (translate_point M t 1).trans (one_mul t)⟩

example := translationPoint_example

/-- A nonzero rational class fixed by a nonidentity scheme translation.
Source: Hatcher, Theorem 2.10; ccm8_translation_pullback.
HC no distance; AV milestone no distance. -/
theorem translationH1_example : ∃ t : ComplexPoint M, t ≠ 1 ∧
    ∃ c : HQ M 1, c ≠ 0 ∧ homPullback (translation M t).hom 1 c = c :=
  ⟨t, t_ne_one, c, c_nonzero, translation_h1_value c⟩

example := translationH1_example

/-- The H¹ composite evaluated on the nonzero intersection class.
Source: Hatcher, §3.1; spec_homPullback_id.
HC no distance; AV milestone no distance. -/
theorem factorH1_example : ∃ c : HQ M 1, c ≠ 0 ∧
    homPullback (translation M t).hom 1 c =
      homPullback (𝟙 M) 1 (homPullback (translation M t).hom 1 c) := by
  refine ⟨c, c_nonzero, ?_⟩
  exact (congrArg (fun f : HQ M 1 →ₗ[ℚ] HQ M 1 ↦ f
    (homPullback (translation M t).hom 1 c)) (spec_homPullback_id (X := M) 1)).symm

example := factorH1_example

/-- A genuine invariant global scheme form has the specified nonzero chart value.
Source: Birkenhake–Lange, §1.4; spec_exists_closed_expPullback_eq.
HC no distance; AV milestone no distance. -/
theorem schemeCoordinates_example : ∃ θ : GlobalHolomorphicForm M 1,
    ∃ w : TangentBundle 𝓘(ℂ, Fin (TopologicalSpace.dim M.left) → ℂ) (ComplexPoint M),
      schemeForm M θ w = (1 : ℂ) := ⟨invariantForm, ⟨origin, expTangent⟩, scheme_value⟩

example := schemeCoordinates_example

/-- Supplementary nonzero scheme-form tangent evaluation.
Source: Birkenhake–Lange, §1.4; globalOneFormCovector.
HC no distance; AV milestone no distance. -/
theorem invariantDifferential_example : ∃ θ : GlobalHolomorphicForm M 1,
    ∃ x : ComplexPoint M, ∃ w : Fin (TopologicalSpace.dim M.left) → ℂ,
      schemeForm M θ ⟨x, w⟩ = (1 : ℂ) ∧
      schemeForm M θ ⟨x, (2 : ℂ) • w⟩ ≠ schemeForm M θ ⟨x, w⟩ :=
  ⟨invariantForm, origin, expTangent, scheme_value, scheme_tangent_scaling⟩

example := invariantDifferential_example

#print axioms thetaForm_holomorphic
#print axioms doubled_abel_pullback_period
#print axioms thetaForm_pullback
#print axioms abel_pullback_comparison
#print axioms abel_pullback_period
#print axioms theta_cover_falsification
#print axioms periodCovector_falsification
#print axioms abel_pullback_falsification
#print axioms selected_abel_check
#print axioms actualJ_cycle_check
#print axioms integralAbelSquare_example
#print axioms translationPoint_example
#print axioms translationH1_example
#print axioms factorH1_example
#print axioms schemeCoordinates_example
#print axioms invariantDifferential_example
#print axioms integralAbelSquare_falsification
#print axioms integralAbelSquare_identity_falsification
#print axioms translationPoint_falsification
#print axioms translationH1_falsification
#print axioms factorH1_falsification
#print axioms schemeCoordinates_falsification
#print axioms invariantDifferential_falsification

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
