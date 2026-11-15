import HodgeLean.Foundations.OneParameter
import HodgeLean.Foundations.LatticeTorus
import HodgeLean.Foundations.GeometricIntegralitySchemes
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Uniformization of complex abelian varieties

Stage S12. HC no distance; AV milestone no distance. This retires nothing alone.
With S5 and S7, uniformization feeds S13 (C7 for abelian varieties).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj NNReal
open Filter Topology Set Metric

namespace HodgeLean.Foundations
noncomputable section

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
  [SmoothOfRelativeDimension d X.hom]

/-- The exponential is the time-one value of S11's one-parameter subgroup.

Source: Mumford, Abelian Varieties, §1; Birkenhake–Lange, Complex Abelian Varieties, §1.1. -/
def complexExponential (v : Fin d → ℂ) : Additive (ComplexPoint X) :=
  oneParameterSubgroup X d v 1

example (v : Fin d → ℂ) : complexExponential X d v = oneParameterSubgroup X d v 1 := rfl

/-- The zero velocity exponentiates to the identity.

Source: Mumford, Abelian Varieties, §1 (exponential at zero). -/
theorem complexExponential_zero : complexExponential X d 0 = 0 := by
  simp [complexExponential, oneParameterSubgroup_zero]

example : complexExponential X d 0 = 0 := complexExponential_zero X d

/-- Restricting the exponential to a real line recovers the prescribed subgroup.

Source: Mumford, Abelian Varieties, §1 (rescaling the exponential parameter). -/
theorem complexExponential_smul (a : ℝ) (v : Fin d → ℂ) :
    complexExponential X d (a • v) = oneParameterSubgroup X d v a := by
  simpa [complexExponential] using oneParameterSubgroup_smul X d a v 1

example (v : Fin d → ℂ) : Continuous (fun a : ℝ ↦ complexExponential X d (a • v)) := by
  simp_rw [complexExponential_smul]
  exact continuous_oneParameterSubgroup X d v

private theorem chart_one_source : (1 : ComplexPoint X) ∈ (identityChart X d).source :=
  mem_localChart_source X d 1

private theorem chart_zero_target : (0 : Fin d → ℂ) ∈ (identityChart X d).target := by
  rw [← identityChart_one X d]
  exact (identityChart X d).map_source (chart_one_source X d)

private theorem chart_symm_zero : (identityChart X d).symm 0 = 1 := by
  rw [← identityChart_one X d]
  exact (identityChart X d).left_inv (chart_one_source X d)

private theorem chart_symm_continuousAt : ContinuousAt (identityChart X d).symm 0 :=
  (identityChart X d).symm.continuousAt (chart_zero_target X d)

private theorem chart_product_source :
    ∀ᶠ p : (Fin d → ℂ) × (Fin d → ℂ) in 𝓝 (0, 0),
      (identityChart X d).symm p.1 * (identityChart X d).symm p.2 ∈
        (identityChart X d).source := by
  have h : ContinuousAt (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦
      (identityChart X d).symm p.1 * (identityChart X d).symm p.2) (0, 0) :=
    ((chart_symm_continuousAt X d).comp (f := Prod.fst) continuousAt_fst).mul
      ((chart_symm_continuousAt X d).comp (f := Prod.snd) continuousAt_snd)
  have h0 : (identityChart X d).symm 0 * (identityChart X d).symm 0 = 1 := by
    simp [chart_symm_zero]
  apply h.tendsto.eventually
  change (identityChart X d).source ∈
    𝓝 ((identityChart X d).symm 0 * (identityChart X d).symm 0)
  rw [h0]
  exact (identityChart X d).open_source.mem_nhds (chart_one_source X d)

private theorem chart_assoc_eventually :
    ∀ᶠ p : ((Fin d → ℂ) × (Fin d → ℂ)) × (Fin d → ℂ) in 𝓝 ((0, 0), 0),
      chartGroupLaw X d (chartGroupLaw X d p.1, p.2) =
        chartGroupLaw X d (p.1.1, chartGroupLaw X d (p.1.2, p.2)) := by
  have hab := (continuousAt_fst (p := (((0, 0) : (Fin d → ℂ) × (Fin d → ℂ)),
    (0 : Fin d → ℂ)))).tendsto.eventually (chart_product_source X d)
  have hbc := (continuousAt_fst.snd.prodMk continuousAt_snd
    (x := (((0, 0) : (Fin d → ℂ) × (Fin d → ℂ)), (0 : Fin d → ℂ)))).tendsto.eventually (chart_product_source X d)
  filter_upwards [hab, hbc] with p hab hbc
  simp only [chartGroupLaw, (identityChart X d).left_inv hab,
    (identityChart X d).left_inv hbc, mul_assoc]

private theorem chart_covariance (v : Fin d → ℂ) :
    ∀ᶠ p : (Fin d → ℂ) × (Fin d → ℂ) in 𝓝 (0, 0),
      fderiv ℂ (chartGroupLaw X d) p (0, chartVectorField X d v p.2) =
        chartVectorField X d v (chartGroupLaw X d p) := by
  let F := chartGroupLaw X d
  have hF0 : F (0, 0) = 0 := by
    simpa using chartGroupLaw_zero_right X d (chart_zero_target X d)
  have hF := (analyticAt_chartGroupLaw X d).eventually_analyticAt
  have hFprod : ContinuousAt (fun p ↦ (F p, (0 : Fin d → ℂ))) (0, 0) :=
    (analyticAt_chartGroupLaw X d).continuousAt.prodMk continuousAt_const
  have houter : ∀ᶠ p in 𝓝 (0, 0), AnalyticAt ℂ F (F p, 0) :=
    hFprod.tendsto.eventually (by
      change ∀ᶠ p in 𝓝 (F (0, 0), (0 : Fin d → ℂ)), AnalyticAt ℂ F p
      rw [hF0]
      exact hF)
  have hinner : ∀ᶠ p : (Fin d → ℂ) × (Fin d → ℂ) in 𝓝 (0, 0),
      AnalyticAt ℂ F (p.2, 0) :=
    (continuousAt_snd.prodMk continuousAt_const
      (x := ((0 : Fin d → ℂ), (0 : Fin d → ℂ)))).tendsto.eventually hF
  have hassoc : ∀ᶠ p : (Fin d → ℂ) × (Fin d → ℂ) in 𝓝 (0, 0),
      ∀ᶠ w in 𝓝 0, F (F p, w) = F (p.1, F (p.2, w)) := by
    have h := chart_assoc_eventually X d
    rw [nhds_prod_eq] at h
    exact h.curry
  have ht : ∀ᶠ p : (Fin d → ℂ) × (Fin d → ℂ) in 𝓝 (0, 0),
      p.2 ∈ (identityChart X d).target :=
    continuousAt_snd ((identityChart X d).open_target.mem_nhds (chart_zero_target X d))
  filter_upwards [hF, houter, hinner, hassoc, ht] with p hp ho hi ha ht
  have hz : F (p.2, 0) = p.2 := chartGroupLaw_zero_right X d ht
  have hright := hi.differentiableAt.hasFDerivAt.comp 0
    (hasFDerivAt_prodMk_right (𝕜 := ℂ) p.2 (0 : Fin d → ℂ))
  have hleft := ho.differentiableAt.hasFDerivAt.comp 0
    (hasFDerivAt_prodMk_right (𝕜 := ℂ) (F p) (0 : Fin d → ℂ))
  have hp' : HasFDerivAt F (fderiv ℂ F p) (p.1, F (p.2, 0)) := by
    simpa only [hz] using hp.differentiableAt.hasFDerivAt
  have hr := hp'.comp 0 ((hasFDerivAt_const p.1 0).prodMk hright)
  have he := hleft.unique (hr.congr_of_eventuallyEq ha)
  exact (DFunLike.congr_fun he v).symm

private theorem oneParameterSubgroup_lift (v : Fin d → ℂ) :
    (fun t ↦ (oneParameterSubgroup X d v t).toMul) =ᶠ[𝓝 0]
      (fun t ↦ (identityChart X d).symm (chartIntegralCurve X d v t)) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (chartLocalOneParameter X d v).radius_pos]
    with t ht
  exact (chartLocalOneParameter X d v).extend_eq t (by simpa [Real.dist_eq] using ht)


private theorem chartVectorField_add (v w u : Fin d → ℂ) :
    chartVectorField X d (v + w) u =
      chartVectorField X d v u + chartVectorField X d w u := by
  unfold chartVectorField
  rw [show ((0 : Fin d → ℂ), v + w) = (0, v) + (0, w) by simp, map_add]

section Commutative
variable [IsCommMonObj X]

private theorem chart_covariance_left (v : Fin d → ℂ) :
    ∀ᶠ p : (Fin d → ℂ) × (Fin d → ℂ) in 𝓝 (0, 0),
      fderiv ℂ (chartGroupLaw X d) p (chartVectorField X d v p.1, 0) =
        chartVectorField X d v (chartGroupLaw X d p) := by
  let F := chartGroupLaw X d
  have hc := (continuousAt_snd.prodMk continuousAt_fst
    (x := ((0 : Fin d → ℂ), (0 : Fin d → ℂ)))).tendsto
  have hv := hc.eventually (chart_covariance X d v)
  have hf := hc.eventually ((analyticAt_chartGroupLaw X d).eventually_analyticAt)
  filter_upwards [hv, hf] with p hv hf
  have he : (fun q : (Fin d → ℂ) × (Fin d → ℂ) ↦ F (q.2, q.1)) = F := by
    funext q
    exact chartGroupLaw_comm X d q.2 q.1
  have hd := hf.differentiableAt.hasFDerivAt.comp p
    ((ContinuousLinearMap.snd ℂ (Fin d → ℂ) (Fin d → ℂ)).hasFDerivAt.prodMk
      (ContinuousLinearMap.fst ℂ (Fin d → ℂ) (Fin d → ℂ)).hasFDerivAt)
  change HasFDerivAt (fun q : (Fin d → ℂ) × (Fin d → ℂ) ↦ F (q.2, q.1)) _ p at hd
  rw [he] at hd
  have h := DFunLike.congr_fun hd.fderiv (chartVectorField X d v p.1, 0)
  change fderiv ℂ F p (chartVectorField X d v p.1, 0) =
    fderiv ℂ F (p.2, p.1) (0, chartVectorField X d v p.1) at h
  rw [h, hv, chartGroupLaw_comm X d p.2 p.1]

private theorem chartIntegralCurve_add (v w : Fin d → ℂ) :
    chartIntegralCurve X d (v + w) =ᶠ[𝓝 0]
      (fun t ↦ chartGroupLaw X d (chartIntegralCurve X d v t, chartIntegralCurve X d w t)) := by
  let u := chartIntegralCurve X d v
  let z := chartIntegralCurve X d w
  let F := chartGroupLaw X d
  have hu : u 0 = 0 := chartIntegralCurve_zero X d v
  have hz : z 0 = 0 := chartIntegralCurve_zero X d w
  have hc : Tendsto (fun t ↦ (u t, z t)) (𝓝 0) (𝓝 (0, 0)) := by
    simpa only [chartIntegralCurve_zero] using
      ((hasDerivAt_chartIntegralCurve X d v).continuousAt.prodMk
        (hasDerivAt_chartIntegralCurve X d w).continuousAt).tendsto
  apply chartIntegralCurve_unique X d (v + w) (chartIntegralCurve_zero X d (v + w))
    (by simpa only [chartIntegralCurve_zero] using chartGroupLaw_zero_right X d (chart_zero_target X d))
    (chartIntegralCurve_ode X d (v + w))
  filter_upwards [chartIntegralCurve_ode X d v, chartIntegralCurve_ode X d w,
    hc.eventually (chart_covariance X d w), hc.eventually (chart_covariance_left X d v),
    hc.eventually ((analyticAt_chartGroupLaw X d).eventually_analyticAt)]
    with t hv hw hright hleft hf
  have hd := (hf.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (hv.prodMk hw)
  change HasDerivAt (fun t ↦ F (u t, z t))
    (fderiv ℂ F (u t, z t) (chartVectorField X d v (u t), chartVectorField X d w (z t))) t at hd
  have he : (chartVectorField X d v (u t), chartVectorField X d w (z t)) =
      (chartVectorField X d v (u t), 0) + (0, chartVectorField X d w (z t)) := by simp
  rw [he, map_add, hleft, hright, ← chartVectorField_add] at hd
  exact hd

/-- In a commutative complex group, the one-parameter subgroup is additive in its velocity.

Source: Mumford, Abelian Varieties, §1; proved by local ODE uniqueness and commutativity. -/
theorem oneParameterSubgroup_add (v w : Fin d → ℂ) :
    oneParameterSubgroup X d (v + w) =
      oneParameterSubgroup X d v + oneParameterSubgroup X d w := by
  apply real_addHom_ext_of_eventuallyEq
  have hc : Tendsto (fun t ↦ (chartIntegralCurve X d v t, chartIntegralCurve X d w t))
      (𝓝 0) (𝓝 (0, 0)) := by
    simpa only [chartIntegralCurve_zero] using
      ((hasDerivAt_chartIntegralCurve X d v).continuousAt.prodMk
        (hasDerivAt_chartIntegralCurve X d w).continuousAt).tendsto
  filter_upwards [oneParameterSubgroup_lift X d (v + w),
    oneParameterSubgroup_lift X d v, oneParameterSubgroup_lift X d w,
    chartIntegralCurve_add X d v w, hc.eventually (chart_product_source X d)]
    with t hs hv hw he hm
  apply Additive.toMul.injective
  change (oneParameterSubgroup X d (v + w) t).toMul =
    (oneParameterSubgroup X d v t).toMul * (oneParameterSubgroup X d w t).toMul
  rw [hs, hv, hw, he]
  exact (identityChart X d).left_inv hm

example (v w : Fin d → ℂ) (t : ℝ) :
    oneParameterSubgroup X d (v + w) t =
      oneParameterSubgroup X d v t + oneParameterSubgroup X d w t :=
  DFunLike.congr_fun (oneParameterSubgroup_add X d v w) t

/-- The exponential as an additive group homomorphism for a commutative group object.

Source: Mumford, Abelian Varieties, §1; Birkenhake–Lange, Complex Abelian Varieties, §1.1. -/
def complexExponentialHom : (Fin d → ℂ) →+ Additive (ComplexPoint X) where
  toFun := complexExponential X d
  map_zero' := complexExponential_zero X d
  map_add' v w := DFunLike.congr_fun (oneParameterSubgroup_add X d v w) 1

example (v : Fin d → ℂ) : complexExponentialHom X d v = oneParameterSubgroup X d v 1 := rfl

private theorem exponential_basis_sum {I : Type*} [Fintype I]
    (b : Module.Basis I ℝ (Fin d → ℂ)) (v : Fin d → ℂ) :
    complexExponential X d v = ∑ i, oneParameterSubgroup X d (b i) (b.equivFun v i) := by
  change complexExponentialHom X d v = _
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact complexExponential_smul X d _ _

/-- The exponential is continuous in the velocity, by its finite real-basis expansion.
This does not require a parameter-dependent ODE theorem.

Source: Mumford, Abelian Varieties, §1; Birkenhake–Lange, Complex Abelian Varieties, §1.1. -/
theorem continuous_complexExponential : Continuous (complexExponential X d) := by
  let b := Module.finBasis ℝ (Fin d → ℂ)
  have he : complexExponential X d =
      fun v ↦ ∑ i, oneParameterSubgroup X d (b i) (b.equivFun v i) := by
    funext v
    exact exponential_basis_sum X d b v
  rw [he]
  apply continuous_finsetSum
  intro i _
  exact (continuous_oneParameterSubgroup X d (b i)).comp
    ((continuous_apply i).comp (continuous_equivFun_basis b))

example : Continuous (complexExponentialHom X d) := continuous_complexExponential X d

private theorem chart_add_jet
    (f g : (Fin d → ℂ) → Additive (ComplexPoint X))
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (A B : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ))
    (hfc : ContDiffAt ℝ 1 (fun v ↦ identityChart X d (f v).toMul) 0)
    (hgc : ContDiffAt ℝ 1 (fun v ↦ identityChart X d (g v).toMul) 0)
    (hfd : HasFDerivAt (fun v ↦ identityChart X d (f v).toMul) A 0)
    (hgd : HasFDerivAt (fun v ↦ identityChart X d (g v).toMul) B 0) :
    ContDiffAt ℝ 1 (fun v ↦ identityChart X d (f v + g v).toMul) 0 ∧
      HasFDerivAt (fun v ↦ identityChart X d (f v + g v).toMul) (A + B) 0 := by
  have hfmem : ∀ᶠ v in 𝓝 0, (f v).toMul ∈ (identityChart X d).source := by
    apply hf.tendsto.eventually
    change (identityChart X d).source ∈ 𝓝 (f 0).toMul
    rw [hf0]
    exact (identityChart X d).open_source.mem_nhds (chart_one_source X d)
  have hgmem : ∀ᶠ v in 𝓝 0, (g v).toMul ∈ (identityChart X d).source := by
    apply hg.tendsto.eventually
    change (identityChart X d).source ∈ 𝓝 (g 0).toMul
    rw [hg0]
    exact (identityChart X d).open_source.mem_nhds (chart_one_source X d)
  have he : (fun v ↦ identityChart X d (f v + g v).toMul) =ᶠ[𝓝 0]
      (fun v ↦ chartGroupLaw X d (identityChart X d (f v).toMul,
        identityChart X d (g v).toMul)) := by
    filter_upwards [hfmem, hgmem] with v hfv hgv
    simp only [chartGroupLaw, (identityChart X d).left_inv hfv,
      (identityChart X d).left_inv hgv]
    rfl
  have h0 : (identityChart X d (f 0).toMul, identityChart X d (g 0).toMul) = (0, 0) := by
    simp only [hf0, hg0, toMul_zero, identityChart_one]
  have hc : ContDiffAt ℝ 1 (chartGroupLaw X d)
      (identityChart X d (f 0).toMul, identityChart X d (g 0).toMul) := by
    rw [h0]
    exact (analyticAt_chartGroupLaw X d).contDiffAt.restrict_scalars ℝ
  have hd : HasFDerivAt (chartGroupLaw X d)
      ((ContinuousLinearMap.fst ℂ (Fin d → ℂ) (Fin d → ℂ) +
        ContinuousLinearMap.snd ℂ (Fin d → ℂ) (Fin d → ℂ)).restrictScalars ℝ)
      (identityChart X d (f 0).toMul, identityChart X d (g 0).toMul) := by
    rw [h0]
    have h := (analyticAt_chartGroupLaw X d).differentiableAt.hasFDerivAt
    rw [fderiv_chartGroupLaw] at h
    exact h.restrictScalars ℝ
  refine ⟨(hc.comp (f := fun v ↦ (identityChart X d (f v).toMul, identityChart X d (g v).toMul)) 0 (hfc.prodMk hgc)).congr_of_eventuallyEq he, ?_⟩
  have h := hd.comp 0 (hfd.prodMk hgd)
  have heq : ((ContinuousLinearMap.fst ℂ (Fin d → ℂ) (Fin d → ℂ) +
      ContinuousLinearMap.snd ℂ (Fin d → ℂ) (Fin d → ℂ)).restrictScalars ℝ).comp
      (A.prod B) = A + B := by ext v i; rfl
  rw [heq] at h
  exact h.congr_of_eventuallyEq he

private theorem chart_sum_jet {I : Type*} (s : Finset I)
    (f : I → (Fin d → ℂ) → Additive (ComplexPoint X))
    (A : I → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ))
    (hf : ∀ i, ContinuousAt (f i) 0) (hf0 : ∀ i, f i 0 = 0)
    (hc : ∀ i, ContDiffAt ℝ 1 (fun v ↦ identityChart X d (f i v).toMul) 0)
    (hd : ∀ i, HasFDerivAt (fun v ↦ identityChart X d (f i v).toMul) (A i) 0) :
    ContDiffAt ℝ 1 (fun v ↦ identityChart X d (∑ i ∈ s, f i v).toMul) 0 ∧
      HasFDerivAt (fun v ↦ identityChart X d (∑ i ∈ s, f i v).toMul) (∑ i ∈ s, A i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using And.intro (contDiffAt_const (c := identityChart X d (1 : ComplexPoint X)))
      (hasFDerivAt_const (𝕜 := ℝ) (identityChart X d (1 : ComplexPoint X)) (0 : Fin d → ℂ))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact chart_add_jet X d (f i) (fun v ↦ ∑ j ∈ s, f j v) (hf i)
      (by fun_prop) (hf0 i) (by simp [hf0])
      (A i) (∑ j ∈ s, A j) (hc i) ih.1 (hd i) ih.2

private theorem exponential_chart_jet :
    ContDiffAt ℝ 1 (fun v ↦ identityChart X d (complexExponential X d v).toMul) 0 ∧
      HasFDerivAt (fun v ↦ identityChart X d (complexExponential X d v).toMul)
        (ContinuousLinearMap.id ℝ (Fin d → ℂ)) 0 := by
  let b := Module.finBasis ℝ (Fin d → ℂ)
  let c (i : Fin (Module.finrank ℝ (Fin d → ℂ))) : (Fin d → ℂ) →L[ℝ] ℝ :=
    (b.coord i).toContinuousLinearMap
  let f i v := oneParameterSubgroup X d (b i) (c i v)
  let A i := (ContinuousLinearMap.toSpanSingleton ℝ (b i)).comp (c i)
  have hf i : ContinuousAt (f i) 0 :=
    ((continuous_oneParameterSubgroup X d (b i)).comp (c i).continuous).continuousAt
  have hf0 i : f i 0 = 0 := by simp [f]
  have hc i : ContDiffAt ℝ 1 (fun v ↦ identityChart X d (f i v).toMul) 0 := by
    have h := contDiffAt_oneParameterSubgroup_chart X d (b i)
    rw [← map_zero (c i)] at h
    exact h.comp 0 (c i).contDiff.contDiffAt
  have hd i : HasFDerivAt (fun v ↦ identityChart X d (f i v).toMul) (A i) 0 := by
    have h := (hasDerivAt_oneParameterSubgroup_chart X d (b i)).hasFDerivAt
    rw [← map_zero (c i)] at h
    exact h.comp 0 (c i).hasFDerivAt
  have h := chart_sum_jet X d Finset.univ f A hf hf0 hc hd
  have he : (fun v ↦ ∑ i, f i v) = complexExponential X d := by
    funext v
    exact (exponential_basis_sum X d b v).symm
  have hA : ∑ i, A i = ContinuousLinearMap.id ℝ (Fin d → ℂ) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [sum_apply, ContinuousLinearMap.id_apply]
    exact b.sum_repr v
  simp_rw [show ∀ v, ∑ i, f i v = complexExponential X d v from fun v ↦ congrFun he v, hA] at h
  exact h

/-- The exponential is continuously differentiable near zero in the identity chart.

Source: Mumford, Abelian Varieties, §1; finite products of S11's real one-parameter curves. -/
theorem contDiffAt_complexExponential_chart :
    ContDiffAt ℝ 1 (fun v ↦ identityChart X d (complexExponential X d v).toMul) 0 :=
  (exponential_chart_jet X d).1

example : ContDiffAt ℝ 1 (fun v ↦ identityChart X d (complexExponential X d v).toMul) 0 :=
  contDiffAt_complexExponential_chart X d

/-- The real derivative of the exponential at zero, in the normalized chart, is the identity.

Source: Mumford, Abelian Varieties, §1; Birkenhake–Lange, Complex Abelian Varieties, §1.1. -/
theorem hasFDerivAt_complexExponential_chart :
    HasFDerivAt (fun v ↦ identityChart X d (complexExponential X d v).toMul)
      (ContinuousLinearMap.id ℝ (Fin d → ℂ)) 0 := (exponential_chart_jet X d).2

example : HasFDerivAt (fun v ↦ identityChart X d (complexExponential X d v).toMul)
    (ContinuousLinearMap.id ℝ (Fin d → ℂ)) 0 := hasFDerivAt_complexExponential_chart X d

/-- Near zero, the exponential agrees with an open partial homeomorphism.
The source contains zero; the equality is an equality of germs, so no behavior of
chart inverses outside their domains is asserted.

Source: Mumford, Abelian Varieties, §1; the real inverse function theorem. -/
theorem complexExponential_localHomeomorph :
    ∃ e : OpenPartialHomeomorph (Fin d → ℂ) (ComplexPoint X),
      0 ∈ e.source ∧ (fun v ↦ (complexExponential X d v).toMul) =ᶠ[𝓝 0] e := by
  let h := contDiffAt_complexExponential_chart X d
  let hd : HasFDerivAt (fun v ↦ identityChart X d (complexExponential X d v).toMul)
      (ContinuousLinearEquiv.refl ℝ (Fin d → ℂ)).toContinuousLinearMap 0 :=
    hasFDerivAt_complexExponential_chart X d
  let e₀ := h.toOpenPartialHomeomorph _ hd (by simp)
  let e := e₀.trans (identityChart X d).symm
  have h0 : e₀ 0 = 0 := by
    change identityChart X d (complexExponential X d 0).toMul = 0
    rw [complexExponential_zero]
    exact identityChart_one X d
  refine ⟨e, ?_, ?_⟩
  · refine ⟨h.mem_toOpenPartialHomeomorph_source hd (by simp), ?_⟩
    change e₀ 0 ∈ (identityChart X d).target
    rw [h0]
    exact chart_zero_target X d
  · have hm : ∀ᶠ v in 𝓝 0, (complexExponential X d v).toMul ∈ (identityChart X d).source := by
      apply (continuous_complexExponential X d).continuousAt.tendsto.eventually
      change (identityChart X d).source ∈ 𝓝 (complexExponential X d 0).toMul
      rw [complexExponential_zero]
      exact (identityChart X d).open_source.mem_nhds (chart_one_source X d)
    filter_upwards [hm] with v hv
    exact ((identityChart X d).left_inv hv).symm

example : ∃ e : OpenPartialHomeomorph (Fin d → ℂ) (ComplexPoint X),
    0 ∈ e.source ∧ (fun v ↦ (complexExponential X d v).toMul) =ᶠ[𝓝 0] e :=
  complexExponential_localHomeomorph X d

/-- The exponential is open globally, by translation of its local inverse at zero.

Source: Mumford, Abelian Varieties, §1; the open-homomorphism neighborhood criterion. -/
theorem isOpenMap_complexExponential : IsOpenMap (complexExponential X d) := by
  change IsOpenMap (complexExponentialHom X d)
  apply IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr
  obtain ⟨e, he0, he⟩ := complexExponential_localHomeomorph X d
  have hm := e.map_nhds_eq he0
  rw [← Filter.map_congr he] at hm
  have hz : e 0 = 1 := by
    rw [← he.self_of_nhds]
    change (complexExponential X d 0).toMul = 1
    rw [complexExponential_zero]
    rfl
  rw [hz] at hm
  exact le_of_eq hm.symm

example : IsOpenMap (complexExponentialHom X d) := isOpenMap_complexExponential X d

/-- The period subgroup, viewed as an integer submodule of the real tangent space.

Source: Mumford, Abelian Varieties, §1; Birkenhake–Lange, Complex Abelian Varieties, §1.1. -/
def complexExponentialLattice : Submodule ℤ (Fin d → ℂ) :=
  (complexExponentialHom X d).ker.toIntSubmodule

example (v : Fin d → ℂ) : v ∈ complexExponentialLattice X d ↔ complexExponential X d v = 0 :=
  Iff.rfl

/-- Periods are discrete because the exponential is injective on a neighborhood of zero.

Source: Mumford, Abelian Varieties, §1; discreteness of the kernel of a local isomorphism. -/
instance discrete_complexExponentialLattice : DiscreteTopology (complexExponentialLattice X d) := by
  obtain ⟨e, he0, he⟩ := complexExponential_localHomeomorph X d
  have hn := he.and (e.open_source.mem_nhds he0)
  obtain ⟨U, hU, hUopen, hU0⟩ := _root_.mem_nhds_iff.mp hn
  have hinj : Set.InjOn (complexExponential X d) U := by
    intro v hv w hw hvw
    apply e.injOn (hU hv).2 (hU hw).2
    rw [← (hU hv).1, ← (hU hw).1]
    exact congrArg Additive.toMul hvw
  apply discreteTopology_of_isOpen_singleton_zero
  have hset : (Subtype.val : complexExponentialLattice X d → (Fin d → ℂ)) ⁻¹' U = {0} := by
    ext v
    constructor
    · intro hv
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      exact hinj hv hU0 (v.property.trans (complexExponential_zero X d).symm)
    · intro hv
      rw [Set.mem_singleton_iff.mp hv]
      exact hU0
  rw [← hset]
  exact hUopen.preimage continuous_subtype_val

example : DiscreteTopology (complexExponentialLattice X d) := discrete_complexExponentialLattice X d

variable [IsIntegral X.left] [IsProjective X.hom]

/-- The exponential is onto: its image is an open and closed subgroup of the connected group.

Source: Mumford, Abelian Varieties, §1; Birkenhake–Lange, Complex Abelian Varieties, §1.1. -/
theorem surjective_complexExponential : Function.Surjective (complexExponential X d) := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  let : ConnectedSpace (Additive (ComplexPoint X)) := connectedSpace_complexPoint X
  let H := (complexExponentialHom X d).range
  have ho : IsOpen (H : Set (Additive (ComplexPoint X))) :=
    (isOpenMap_complexExponential X d).isOpen_range
  have hc : IsClosed (H : Set (Additive (ComplexPoint X))) := H.isClosed_of_isOpen ho
  have he := (IsClopen.eq_univ ⟨hc, ho⟩ ⟨0, H.zero_mem⟩)
  exact Set.range_eq_univ.mp he

example : Function.Surjective (complexExponentialHom X d) := surjective_complexExponential X d

/-- The exponential induces a topological additive-group isomorphism from its kernel quotient.

Source: Mumford, Abelian Varieties, §1; the first isomorphism theorem for an open homomorphism. -/
def complexExponentialQuotientEquiv :
    ContinuousAddEquiv ((Fin d → ℂ) ⧸ (complexExponentialLattice X d).toAddSubgroup)
      (Additive (ComplexPoint X)) := by
  let e := QuotientAddGroup.liftEquiv (complexExponentialHom X d).ker
    (surjective_complexExponential X d) rfl
  have hc : Continuous e :=
    QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp (continuous_complexExponential X d)
  have ho : IsOpenMap e :=
    QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap_iff.mpr (isOpenMap_complexExponential X d)
  exact { e with
    continuous_toFun := hc
    continuous_invFun := e.toEquiv.continuous_symm_iff.mpr ho }

example (v : Fin d → ℂ) : complexExponentialQuotientEquiv X d (QuotientAddGroup.mk v) =
    complexExponential X d v := rfl

/-- The quotient by the period subgroup is compact, transported from projective complex points.

Source: Mumford, Abelian Varieties, §1; projective analytic compactness and the quotient isomorphism. -/
theorem compact_complexExponentialQuotient :
    CompactSpace ((Fin d → ℂ) ⧸ (complexExponentialLattice X d).toAddSubgroup) :=
  (complexExponentialQuotientEquiv X d).toHomeomorph.symm.compactSpace

example : CompactSpace ((Fin d → ℂ) ⧸ (complexExponentialLattice X d).toAddSubgroup) :=
  compact_complexExponentialQuotient X d

/-- The period subgroup is a full integer lattice, by discreteness and compact quotient.

Source: Mumford, Abelian Varieties, §1; Birkenhake–Lange, Complex Abelian Varieties, §1.1. -/
theorem isZLattice_complexExponentialLattice : IsZLattice ℝ (complexExponentialLattice X d) := by
  let := compact_complexExponentialQuotient X d
  exact LatticeTorus.isZLattice_of_compact_quotient (complexExponentialLattice X d)

example : IsZLattice ℝ (complexExponentialLattice X d) := isZLattice_complexExponentialLattice X d

end Commutative

/-- The complex coordinate space of dimension `d` has real dimension `2*d`.
The scalar-field contribution is `Complex.finrank_real_complex`, proved using
`Complex.basisOneI`; it must not be replaced by the complex dimension `d`.

Source: Birkenhake–Lange, Complex Abelian Varieties, §1.1 (real dimension of a complex vector space). -/
theorem finrank_real_complexCoordinates (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, Nat.mul_comm]

example : Module.finrank ℝ (Fin 1 → ℂ) = 2 := by rw [finrank_real_complexCoordinates]

/-- Complex points of a smooth projective integral complex group of relative dimension `d`
are the real torus of dimension `2*d`, as a topological additive group.
Commutativity is derived from properness and integrality; it is not an additional assumption.
This is S12, feeding S13 with S5 and S7, and retires nothing alone.
HC no distance; AV milestone no distance.

Source: Mumford, Abelian Varieties, §1; Birkenhake–Lange, Complex Abelian Varieties, §1.1. -/
def complexPointUniformization [IsIntegral X.left] [IsProjective X.hom] :
    ContinuousAddEquiv (Additive (ComplexPoint X)) (UnitAddTorus (Fin (2 * d))) := by
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  letI := isZLattice_complexExponentialLattice X d
  let L := complexExponentialLattice X d
  letI := ZLattice.module_free ℝ L
  letI := ZLattice.module_finite ℝ L
  exact (complexExponentialQuotientEquiv X d).symm.trans
    (LatticeTorus.quotientEquivOfBasis L
      (Module.finBasisOfFinrankEq ℤ L ((ZLattice.rank ℝ L).trans
        (finrank_real_complexCoordinates d))))

example [IsIntegral X.left] [IsProjective X.hom] (x y : Additive (ComplexPoint X)) :
    complexPointUniformization X d (x + y) =
      complexPointUniformization X d x + complexPointUniformization X d y := map_add _ x y

/-- The underlying uniformization homeomorphism of complex points with a real torus.
Its additive-group compatibility is supplied by `complexPointUniformization`.
HC no distance; AV milestone no distance.

Source: Mumford, Abelian Varieties, §1; Birkenhake–Lange, Complex Abelian Varieties, §1.1. -/
def complexPointTorusHomeomorph [IsIntegral X.left] [IsProjective X.hom] :
    ComplexPoint X ≃ₜ UnitAddTorus (Fin (2 * d)) :=
  (complexPointUniformization X d).toHomeomorph

example [IsIntegral X.left] [IsProjective X.hom] :
    ComplexPoint X ≃ₜ UnitAddTorus (Fin (2 * d)) := complexPointTorusHomeomorph X d


/-- The period lattice has integer rank exactly twice the relative complex dimension.

Source: Birkenhake–Lange, Complex Abelian Varieties, §1.1 (rank of the period lattice). -/
theorem finrank_complexExponentialLattice [IsCommMonObj X]
    [IsIntegral X.left] [IsProjective X.hom] :
    Module.finrank ℤ (complexExponentialLattice X d) = 2 * d := by
  let := isZLattice_complexExponentialLattice X d
  exact (ZLattice.rank ℝ (complexExponentialLattice X d)).trans
    (finrank_real_complexCoordinates d)

example [IsCommMonObj X] [IsIntegral X.left] [IsProjective X.hom] :
    Module.finrank ℤ (complexExponentialLattice X d) = 2 * d :=
  finrank_complexExponentialLattice X d

/-- A full integer basis of the actual exponential kernel, with precisely `2*d` elements.

Source: Birkenhake–Lange, Complex Abelian Varieties, §1.1 (a basis of the period lattice). -/
def complexExponentialLatticeBasis [IsCommMonObj X]
    [IsIntegral X.left] [IsProjective X.hom] :
    Module.Basis (Fin (2 * d)) ℤ (complexExponentialLattice X d) := by
  letI := isZLattice_complexExponentialLattice X d
  letI := ZLattice.module_free ℝ (complexExponentialLattice X d)
  letI := ZLattice.module_finite ℝ (complexExponentialLattice X d)
  exact Module.finBasisOfFinrankEq ℤ _ (finrank_complexExponentialLattice X d)

example [IsCommMonObj X] [IsIntegral X.left] [IsProjective X.hom]
    (v : complexExponentialLattice X d) :
    ∑ i, (complexExponentialLatticeBasis X d).repr v i • complexExponentialLatticeBasis X d i = v :=
  (complexExponentialLatticeBasis X d).sum_repr v

example : Module.finrank ℝ (Fin 0 → ℂ) = 0 := finrank_real_complexCoordinates 0
example : Module.finrank ℝ (Fin 2 → ℂ) = 4 := finrank_real_complexCoordinates 2

end

/-- In relative dimension zero, uniformization forces every complex point to be the identity.
This tests the degenerate torus without any positive-dimension assumption.

Source: Mumford, Abelian Varieties, §1; the zero-dimensional case of uniformization. -/
theorem complexPoint_eq_one_of_relativeDimension_zero (X : Over (Spec ↧ℂ))
    [GrpObj X] [SmoothOfRelativeDimension 0 X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (x : ComplexPoint X) : x = 1 := by
  apply (complexPointTorusHomeomorph X 0).injective
  funext i
  exact Fin.elim0 i

example (X : Over (Spec ↧ℂ)) [GrpObj X] [SmoothOfRelativeDimension 0 X.hom]
    [IsIntegral X.left] [IsProjective X.hom] (x : ComplexPoint X) : x = 1 :=
  complexPoint_eq_one_of_relativeDimension_zero X x

noncomputable section

private abbrev trivialUniformizationGroup : Over (Spec ↧ℂ) := 𝟙_ (Over (Spec ↧ℂ))

private instance : SmoothOfRelativeDimension 0 trivialUniformizationGroup.hom := by
  change SmoothOfRelativeDimension 0 (𝟙 (Spec ↧ℂ))
  infer_instance

private instance : IsIntegral trivialUniformizationGroup.left := by
  change IsIntegral (Spec (.of ℂ))
  infer_instance

private instance : IsProjective trivialUniformizationGroup.hom := by
  change IsProjective (𝟙 (Spec ↧ℂ))
  let v : ComplexProjectiveSpace.CoordinateSpace 0 := fun _ ↦ 1
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num [v] at h0
  let i := ComplexProjectiveSpace.vectorToProjectiveSpace v hv
  let q := ProjectiveSpace.toBase (Fin 1) (Spec ↧ℂ)
  have hi : i ≫ q = 𝟙 _ := ComplexProjectiveSpace.vectorToProjectiveSpace_toBase v hv
  let : IsClosedImmersion (i ≫ q) := by rw [hi]; infer_instance
  let : IsClosedImmersion i := IsClosedImmersion.of_comp i q
  exact ⟨⟨{ ambientDimension := 0, immersion := i, immersion_toBase := hi }⟩⟩

example : ComplexPoint trivialUniformizationGroup ≃ₜ UnitAddTorus (Fin 0) :=
  complexPointTorusHomeomorph trivialUniformizationGroup 0

example (x : ComplexPoint trivialUniformizationGroup) : x = 1 :=
  complexPoint_eq_one_of_relativeDimension_zero trivialUniformizationGroup x

end
end HodgeLean.Foundations


#print axioms HodgeLean.Foundations.complexExponential
#print axioms HodgeLean.Foundations.complexExponential_zero
#print axioms HodgeLean.Foundations.complexExponential_smul
#print axioms HodgeLean.Foundations.oneParameterSubgroup_add
#print axioms HodgeLean.Foundations.complexExponentialHom
#print axioms HodgeLean.Foundations.continuous_complexExponential

#print axioms HodgeLean.Foundations.contDiffAt_complexExponential_chart
#print axioms HodgeLean.Foundations.hasFDerivAt_complexExponential_chart
#print axioms HodgeLean.Foundations.complexExponential_localHomeomorph
#print axioms HodgeLean.Foundations.isOpenMap_complexExponential

#print axioms HodgeLean.Foundations.complexExponentialLattice
#print axioms HodgeLean.Foundations.discrete_complexExponentialLattice
#print axioms HodgeLean.Foundations.surjective_complexExponential
#print axioms HodgeLean.Foundations.complexExponentialQuotientEquiv
#print axioms HodgeLean.Foundations.compact_complexExponentialQuotient
#print axioms HodgeLean.Foundations.isZLattice_complexExponentialLattice

#print axioms HodgeLean.Foundations.finrank_real_complexCoordinates
#print axioms HodgeLean.Foundations.complexPointUniformization
#print axioms HodgeLean.Foundations.complexPointTorusHomeomorph

#print axioms HodgeLean.Foundations.finrank_complexExponentialLattice
#print axioms HodgeLean.Foundations.complexExponentialLatticeBasis
#print axioms HodgeLean.Foundations.complexPoint_eq_one_of_relativeDimension_zero
