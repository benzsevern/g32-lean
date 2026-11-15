import HodgeLean.Adapters.HolomorphicFormsPullback

/-! # Proof obligations for holomorphic translations and the holomorphic exponential

One obligation per statement of `HodgeLean.Adapters.ExpHolomorphic`. All seven are proved, by three parallel provers. -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint
open HodgeLean.Foundations
open Filter Topology
open scoped Manifold ContDiff CategoryTheory.MonObj

namespace HodgeLean.Adapters

theorem spec_contMDiff_pointMap_aux (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom] (f : X ⟶ Y) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ω (Point.map f : ComplexPoint X → ComplexPoint Y) := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨(Point.continuous_map f).continuousAt, ?_⟩
  have hx := mem_localChart_source X d x
  have h := analyticAt_localChart_symm_map X Y f d e x
    ((localChart X d x).map_source hx)
    (by rw [(localChart X d x).left_inv hx]; exact mem_localChart_source Y e _)
  simp only [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe, Set.range_id,
    PartialEquiv.coe_trans, PartialEquiv.coe_trans_symm,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm, OpenPartialHomeomorph.coe_toPartialEquiv]
  exact h.contDiffAt.contDiffWithinAt

open CartesianMonoidalCategory in
private theorem pointMap_mul_left (X : Over (Spec ↧ℂ)) [GrpObj X] (a x : ComplexPoint X) :
    Point.map (lift (toUnit X ≫ a) (𝟙 X) ≫ MonObj.mul) x = a * x := by
  have h : x ≫ toUnit X = 𝟙 _ := Subsingleton.elim _ _
  simp only [Point.map, Hom.mul_def]
  rw [← Category.assoc, comp_lift, reassoc_of% h, Category.comp_id]

theorem spec_contMDiff_mul_left_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] (a : ComplexPoint X) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (fun x : ComplexPoint X ↦ a * x) := by
  have := spec_contMDiff_pointMap_aux X X d d
    (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.toUnit X ≫ a) (𝟙 X) ≫
      MonObj.mul)
  convert this using 1
  funext x
  exact (pointMap_mul_left X a x).symm

open MonoidalCategory CartesianMonoidalCategory in
private theorem analyticAt_localChart_mul (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] (x y : ComplexPoint X) :
    AnalyticAt ℂ (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦
      localChart X d (x * y) ((localChart X d x).symm p.1 * (localChart X d y).symm p.2))
      (localChart X d x x, localChart X d y y) := by
  let z : ComplexPoint (X ⊗ X) := lift x y
  let a := localChart (X ⊗ X) (d + d) z
  let H := productChartComparison X X d d z
  have hfst : Point.map (fst X X) z = x := by simp [z, Point.map]
  have hsnd : Point.map (snd X X) z = y := by simp [z, Point.map]
  have hza := mem_localChart_source (X ⊗ X) (d + d) z
  have he : H (a z) = (localChart X d x x, localChart X d y y) := by
    change (localChart X d (Point.map (fst X X) z)
      (Point.map (fst X X) (a.symm (a z))),
      localChart X d (Point.map (snd X X) z)
      (Point.map (snd X X) (a.symm (a z)))) = _
    rw [a.left_inv hza, hfst, hsnd]
  have hz : a z ∈ H.source := by
    refine ⟨a.map_source hza, trivial, ?_, ?_⟩
    · change Point.map (fst X X) (a.symm (a z)) ∈ _
      rw [a.left_inv hza]
      exact mem_localChart_source X d _
    · change Point.map (snd X X) (a.symm (a z)) ∈ _
      rw [a.left_inv hza]
      exact mem_localChart_source X d _
  have ht : (localChart X d x x, localChart X d y y) ∈ H.target := he ▸ H.map_source hz
  have hv : H.symm (localChart X d x x, localChart X d y y) = a z := by
    rw [← he]; exact H.left_inv hz
  have hH : AnalyticAt ℂ H.symm (localChart X d x x, localChart X d y y) := by
    simpa only [hfst, hsnd] using analyticAt_productChartComparison_symm X X d d z
  have hm : Point.map (MonObj.mul : X ⊗ X ⟶ X) z = x * y := rfl
  have hM : AnalyticAt ℂ (fun u ↦ localChart X d (x * y)
      (Point.map (MonObj.mul : X ⊗ X ⟶ X) (a.symm u))) (a z) := by
    rw [← hm]
    apply analyticAt_localChart_symm_map
    · exact a.map_source hza
    · rw [a.left_inv hza]
      exact mem_localChart_source X d _
  apply (hM.comp_of_eq hH hv).congr
  filter_upwards [H.open_target.mem_nhds ht] with p hp
  have hp' : lift ((localChart X d x).symm p.1) ((localChart X d y).symm p.2) ∈ a.source := by
    have hp2 := hp.2
    change lift ((localChart X d (Point.map (fst X X) z)).symm p.1)
      ((localChart X d (Point.map (snd X X) z)).symm p.2) ∈ a.source at hp2
    simpa only [hfst, hsnd] using hp2
  change localChart X d (x * y) (Point.map (MonObj.mul : X ⊗ X ⟶ X)
    (a.symm (H.symm p))) = _
  have hval : H.symm p = a (lift ((localChart X d x).symm p.1) ((localChart X d y).symm p.2)) := by
    change a (lift ((localChart X d (Point.map (fst X X) z)).symm p.1)
      ((localChart X d (Point.map (snd X X) z)).symm p.2)) = _
    rw [hfst, hsnd]
  rw [hval, a.left_inv hp']
  rfl

theorem spec_lieGroup_complexPoint_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] :
    LieGroup 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X) where
  contMDiff_mul := by
    rintro ⟨x, y⟩
    rw [contMDiffAt_iff]
    refine ⟨(continuous_complexPoint_mul X).continuousAt, ?_⟩
    simp only [extChartAt_prod, ModelWithCorners.range_prod, modelWithCornersSelf_coe,
      Set.range_id, Set.univ_prod_univ, contDiffWithinAt_univ]
    exact (analyticAt_localChart_mul X d x y).contDiffAt
  contMDiff_inv := by
    exact spec_contMDiff_pointMap_aux X X d d (GrpObj.inv : X ⟶ X)

theorem spec_mdifferentiable_complexExponential_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] :
    MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ)
      (fun v ↦ (complexExponential X d v).toMul) := by
  set E : (Fin d → ℂ) → ComplexPoint X := fun v ↦ (complexExponential X d v).toMul with hE
  have hE0 : E 0 = 1 := by
    simp only [hE, complexExponential_zero]
    rfl
  have h0 : MDifferentiableAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) E 0 := by
    rw [mdifferentiableAt_iff]
    refine ⟨(continuous_complexExponential X d).continuousAt, ?_⟩
    have hd := (spec_eventually_differentiableAt_complexExponential_chart X d).self_of_nhds
    have heq : writtenInExtChartAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) 0 E =
        fun w ↦ identityChart X d (E w) + localChart X d 1 1 := by
      funext w
      simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
        chartAt_self_eq, Function.comp_apply, hE0]
      change localChart X d 1 (E w) = (localChart X d 1 (E w) - localChart X d 1 1) + _
      abel
    rw [heq]
    exact (hd.add_const _).differentiableWithinAt
  intro v₀
  have htr : ∀ v, E v = E v₀ * E (v - v₀) := by
    intro v
    have := (complexExponentialHom X d).map_add v₀ (v - v₀)
    rw [add_sub_cancel] at this
    exact congrArg Additive.toMul this
  have hcomp : MDifferentiableAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ)
      ((fun x : ComplexPoint X ↦ E v₀ * x) ∘ E ∘ (fun v ↦ v - v₀)) v₀ := by
    have hs : MDifferentiableAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ)
        (fun v : Fin d → ℂ ↦ v - v₀) v₀ :=
      (differentiableAt_id.sub_const v₀).mdifferentiableAt
    have h0' : MDifferentiableAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) E (v₀ - v₀) := by
      simpa using h0
    have ht : MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ)
        (fun x : ComplexPoint X ↦ E v₀ * x) :=
      (spec_contMDiff_mul_left_aux X d (E v₀)).mdifferentiable (by simp)
    have hc := MDifferentiableAt.comp (f := fun v : Fin d → ℂ ↦ v - v₀) v₀ h0' hs
    exact (ht _).comp v₀ hc
  have hfun : E = (fun x : ComplexPoint X ↦ E v₀ * x) ∘ E ∘ (fun v ↦ v - v₀) := by
    funext v
    exact htr v
  rw [hfun]
  exact hcomp

/-- If `exp ∘ L₁` and `exp ∘ L₂` are analytic in the identity chart at `0`, for maps `L₁`, `L₂`
continuous at `0` and vanishing there, then so is `exp ∘ (L₁ + L₂)`, through the group law. -/
private theorem analyticAt_complexExponential_chart_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] {L₁ L₂ : E → Fin d → ℂ}
    (h₁0 : L₁ 0 = 0) (h₁c : ContinuousAt L₁ 0)
    (h₁ : AnalyticAt ℂ (fun z ↦ identityChart X d (complexExponential X d (L₁ z)).toMul) 0)
    (h₂0 : L₂ 0 = 0) (h₂c : ContinuousAt L₂ 0)
    (h₂ : AnalyticAt ℂ (fun z ↦ identityChart X d (complexExponential X d (L₂ z)).toMul) 0) :
    AnalyticAt ℂ
      (fun z ↦ identityChart X d (complexExponential X d (L₁ z + L₂ z)).toMul) 0 := by
  set φ : (Fin d → ℂ) → (Fin d → ℂ) :=
    fun w ↦ identityChart X d (complexExponential X d w).toMul with hφ
  have hφ0 : φ 0 = 0 := by
    simp only [hφ, complexExponential_zero]
    exact identityChart_one X d
  have hE : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ),
      (complexExponential X d v).toMul ∈ (identityChart X d).source := by
    apply (continuous_complexExponential X d).continuousAt.tendsto.eventually
    change (identityChart X d).source ∈ 𝓝 (complexExponential X d 0).toMul
    rw [complexExponential_zero]
    exact (identityChart X d).open_source.mem_nhds (mem_localChart_source X d 1)
  have hE₁ : ∀ᶠ z in 𝓝 (0 : E), (complexExponential X d (L₁ z)).toMul ∈
      (identityChart X d).source := by
    have := h₁c.tendsto
    rw [h₁0] at this
    exact this.eventually hE
  have hE₂ : ∀ᶠ z in 𝓝 (0 : E), (complexExponential X d (L₂ z)).toMul ∈
      (identityChart X d).source := by
    have := h₂c.tendsto
    rw [h₂0] at this
    exact this.eventually hE
  have hμ : AnalyticAt ℂ (chartGroupLaw X d) (φ (L₁ 0), φ (L₂ 0)) := by
    rw [h₁0, h₂0, hφ0]
    exact analyticAt_chartGroupLaw X d
  apply (hμ.comp (f := fun z ↦ (φ (L₁ z), φ (L₂ z))) (h₁.prod h₂)).congr
  filter_upwards [hE₁, hE₂] with z hz₁ hz₂
  simp only [Function.comp_apply, chartGroupLaw, hφ]
  rw [(identityChart X d).left_inv hz₁, (identityChart X d).left_inv hz₂]
  congr 1
  change _ = (complexExponentialHom X d (L₁ z + L₂ z)).toMul
  rw [map_add, toMul_add]
  rfl

theorem spec_analyticAt_complexExponential_chart_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] :
    AnalyticAt ℂ (fun w ↦ identityChart X d (complexExponential X d w).toMul) 0 := by
  set φ : (Fin d → ℂ) → (Fin d → ℂ) :=
    fun w ↦ identityChart X d (complexExponential X d w).toMul with hφ
  let P : ((Fin d → ℂ) → (Fin d → ℂ)) → Prop := fun L ↦
    L 0 = 0 ∧ ContinuousAt L 0 ∧ AnalyticAt ℂ (fun z ↦ φ (L z)) 0
  have hD := spec_eventually_differentiableAt_complexExponential_chart X d
  have hsingle : ∀ i, P (fun z ↦ z i • Pi.single i (1 : ℂ)) := by
    intro i
    refine ⟨by simp, ((continuous_apply i).smul continuous_const).continuousAt, ?_⟩
    let g : ℂ → Fin d → ℂ := fun t ↦ φ (t • Pi.single i (1 : ℂ))
    have hg : AnalyticAt ℂ g 0 := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      have ht : Tendsto (fun t : ℂ ↦ t • Pi.single i (1 : ℂ)) (𝓝 0) (𝓝 0) := by
        have : Continuous (fun t : ℂ ↦ t • Pi.single i (1 : ℂ)) := by fun_prop
        simpa using this.tendsto 0
      filter_upwards [ht.eventually hD] with t ht
      exact DifferentiableAt.comp (g := φ) t ht (by fun_prop)
    exact hg.comp_of_eq ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i).analyticAt 0) rfl
  have hzero : P (fun _ ↦ 0) := by
    refine ⟨rfl, continuousAt_const, analyticAt_const⟩
  have hadd : ∀ L₁ L₂, P L₁ → P L₂ → P (L₁ + L₂) := by
    rintro L₁ L₂ ⟨h₁0, h₁c, h₁⟩ ⟨h₂0, h₂c, h₂⟩
    refine ⟨by simp [h₁0, h₂0], h₁c.add h₂c, ?_⟩
    exact analyticAt_complexExponential_chart_add X d h₁0 h₁c h₁ h₂0 h₂c h₂
  have hsum : P (∑ i, fun z : Fin d → ℂ ↦ z i • Pi.single i (1 : ℂ)) :=
    Finset.sum_induction _ P hadd hzero (fun i _ ↦ hsingle i)
  have hid : (∑ i, fun z : Fin d → ℂ ↦ z i • Pi.single i (1 : ℂ)) = id := by
    funext z
    rw [Finset.sum_apply]
    exact (pi_eq_sum_univ' z).symm
  rw [hid] at hsum
  exact hsum.2.2

theorem spec_contMDiff_complexExponential_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      (fun v ↦ (complexExponential X d v).toMul) := by
  have h1 : (complexExponential X d 0).toMul = 1 := by
    rw [complexExponential_zero, toMul_zero]
  have hA : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      (fun v ↦ (complexExponential X d v).toMul) 0 := by
    rw [contMDiffAt_iff]
    refine ⟨(continuous_complexExponential X d).continuousAt, ?_⟩
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
      Function.comp_id, extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp,
      Set.range_id, id_eq, h1]
    have h : AnalyticAt ℂ (fun w ↦ identityChart X d (complexExponential X d w).toMul +
        localChart X d 1 1) 0 := (spec_analyticAt_complexExponential_chart_aux X d).add analyticAt_const
    refine (h.contDiffAt.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards with w
    change localChart X d 1 _ = (localChart X d 1 _ - localChart X d 1 1) + localChart X d 1 1
    rw [sub_add_cancel]
  intro v₀
  have hsub : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (fun v ↦ v - v₀) v₀ :=
    (contDiff_id.sub contDiff_const).contMDiff v₀
  have hc := (spec_contMDiff_mul_left_aux X d (complexExponential X d v₀).toMul _).comp_of_eq
    (hA.comp_of_eq hsub (sub_self v₀)) rfl
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards with v
  change (complexExponentialHom X d v).toMul =
    (complexExponentialHom X d v₀).toMul * (complexExponentialHom X d (v - v₀)).toMul
  rw [← toMul_add, ← map_add, add_sub_cancel]

theorem spec_conj_not_mdifferentiable_aux :
    (∀ z w : ℂ, starRingEnd ℂ (z + w) = starRingEnd ℂ z + starRingEnd ℂ w) ∧
      ContDiff ℝ ω (starRingEnd ℂ : ℂ → ℂ) ∧
      ¬ MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (starRingEnd ℂ : ℂ → ℂ) 0 := by
  refine ⟨fun z w ↦ map_add _ z w, Complex.conjCLE.contDiff, fun h ↦ ?_⟩
  rw [mdifferentiableAt_iff_differentiableAt] at h
  set L := fderiv ℂ (starRingEnd ℂ : ℂ → ℂ) 0
  have hR := h.hasFDerivAt.restrictScalars ℝ
  have hC : HasFDerivAt (starRingEnd ℂ : ℂ → ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) 0 :=
    Complex.conjCLE.hasFDerivAt
  have he := hR.unique hC
  have hI := DFunLike.congr_fun he Complex.I
  have h1 := DFunLike.congr_fun he 1
  simp only [ContinuousLinearMap.coe_restrictScalars'] at hI h1
  have hL : L Complex.I = Complex.I * L 1 := by
    rw [← smul_eq_mul, ← L.map_smul, smul_eq_mul, mul_one]
  rw [hI, h1] at hL
  have := congrArg Complex.im hL
  norm_num at this

end HodgeLean.Adapters
