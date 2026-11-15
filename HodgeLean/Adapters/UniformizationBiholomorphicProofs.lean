import HodgeLean.Adapters.ExpHolomorphic

/-! # Proof obligations for the uniformization as complex manifolds

One obligation per statement of `HodgeLean.Adapters.UniformizationBiholomorphic`. All nine are proved, by two parallel provers and the amendment. -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint
open HodgeLean.Foundations
open Filter Topology
open scoped Manifold ContDiff CategoryTheory.MonObj

namespace HodgeLean.Adapters

/-- The identity chart is holomorphic on its source. -/
private theorem contMDiffOn_identityChart (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] :
    ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (identityChart X d)
      (identityChart X d).source := by
  have h : ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      (chartAt (Fin d → ℂ) (1 : ComplexPoint X)) (chartAt (Fin d → ℂ) (1 : ComplexPoint X)).source :=
    contMDiffOn_chart
  have hs : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      (fun p : Fin d → ℂ ↦ p - localChart X d 1 1) :=
    (contDiff_id.sub contDiff_const).contMDiff
  exact hs.comp_contMDiffOn h

/-- The complex derivative at `0` of `exp` in the identity chart is the identity. -/
private theorem hasFDerivAt_complexExponential_chart_complex (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] :
    HasFDerivAt (fun w ↦ identityChart X d (complexExponential X d w).toMul)
      (ContinuousLinearMap.id ℂ (Fin d → ℂ)) 0 := by
  have hA := spec_analyticAt_complexExponential_chart X d
  have hC := hA.differentiableAt.hasFDerivAt
  have hR := hC.restrictScalars ℝ
  have he := hR.unique (hasFDerivAt_complexExponential_chart X d)
  convert hC using 1
  ext w : 1
  exact (DFunLike.congr_fun he w).symm

/-- Near `0`, `exp` agrees with an open partial homeomorphism with holomorphic inverse. -/
private theorem complexExponential_localBiholomorph_zero (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] :
    ∃ e : OpenPartialHomeomorph (Fin d → ℂ) (ComplexPoint X),
      0 ∈ e.source ∧ Set.EqOn (fun w ↦ (complexExponential X d w).toMul) e e.source ∧
        ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω e.symm e.target := by
  set φ : (Fin d → ℂ) → (Fin d → ℂ) :=
    fun w ↦ identityChart X d (complexExponential X d w).toMul with hφ
  have hA : AnalyticAt ℂ φ 0 := spec_analyticAt_complexExponential_chart X d
  have hd : HasFDerivAt φ
      ((ContinuousLinearEquiv.refl ℂ (Fin d → ℂ) : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ)) :
        (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0 :=
    hasFDerivAt_complexExponential_chart_complex X d
  have hφ0 : φ 0 = 0 := by
    simp only [hφ, complexExponential_zero]
    exact identityChart_one X d
  have hinv : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), (fderiv ℂ φ w).IsInvertible := by
    have h0 : (fderiv ℂ φ 0).IsInvertible := by
      rw [hd.fderiv]
      exact ⟨ContinuousLinearEquiv.refl ℂ _, rfl⟩
    exact hA.fderiv.continuousAt.eventually h0.eventually_nhds
  have hsrc : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      (complexExponential X d w).toMul ∈ (identityChart X d).source := by
    apply (continuous_complexExponential X d).continuousAt.tendsto.eventually
    change (identityChart X d).source ∈ 𝓝 (complexExponential X d 0).toMul
    rw [complexExponential_zero]
    exact (identityChart X d).open_source.mem_nhds (mem_localChart_source X d 1)
  obtain ⟨U, hU, hUo, hU0⟩ := _root_.mem_nhds_iff.mp
    (hA.eventually_analyticAt.and (hinv.and hsrc))
  have hcd : ContDiffAt ℂ ω φ 0 := hA.contDiffAt
  let e₀ := hcd.toOpenPartialHomeomorph φ hd (by simp)
  let e₁ := e₀.restrOpen U hUo
  let e := e₁.trans (identityChart X d).symm
  have he₁ : (e₁ : (Fin d → ℂ) → (Fin d → ℂ)) = φ := rfl
  have he₁s : e₁.source ⊆ U := fun w hw ↦ hw.2
  refine ⟨e, ⟨⟨hcd.mem_toOpenPartialHomeomorph_source hd (by simp), hU0⟩, ?_⟩,
    ?_, ?_⟩
  · change φ 0 ∈ (identityChart X d).target
    rw [hφ0]
    rw [← identityChart_one X d]
    exact (identityChart X d).map_source (mem_localChart_source X d 1)
  · intro w hw
    have hwU := (hU (he₁s hw.1)).2.2
    change _ = (identityChart X d).symm (φ w)
    exact ((identityChart X d).left_inv hwU).symm
  · have hto : IsOpen e.target := e.open_target
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    have hyc : y ∈ (identityChart X d).source := by
      have := hy.1
      simpa using this
    have hz : identityChart X d y ∈ e₁.target := by
      have := hy.2
      simpa using this
    have hzU : e₁.symm (identityChart X d y) ∈ U := he₁s (e₁.map_target hz)
    obtain ⟨hAn, ⟨L, hL⟩, -⟩ := hU hzU
    have hs : ContDiffAt ℂ ω e₁.symm (identityChart X d y) := by
      apply e₁.contDiffAt_symm hz (f₀' := L)
      · rw [he₁, hL]
        exact hAn.differentiableAt.hasFDerivAt
      · rw [he₁]
        exact hAn.contDiffAt
    have hc : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (identityChart X d) y :=
      (contMDiffOn_identityChart X d).contMDiffAt
        ((identityChart X d).open_source.mem_nhds hyc)
    exact hs.contMDiffAt.comp y hc

/-- Every `v` has a neighbourhood on which `exp` agrees with an open partial homeomorphism with
holomorphic inverse: translate the one at `0`. -/
private theorem complexExponential_localBiholomorph_at (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] (v : Fin d → ℂ) :
    ∃ e : OpenPartialHomeomorph (Fin d → ℂ) (ComplexPoint X),
      v ∈ e.source ∧ Set.EqOn (fun w ↦ (complexExponential X d w).toMul) e e.source ∧
        ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω e.symm e.target := by
  obtain ⟨e, he0, heq, hsm⟩ := complexExponential_localBiholomorph_zero X d
  set a : ComplexPoint X := (complexExponential X d v).toMul with ha
  let f := (Homeomorph.addRight (-v)).transOpenPartialHomeomorph
    (e.transHomeomorph (Homeomorph.mulLeft a))
  have hfs : f.source = (· + -v) ⁻¹' e.source := rfl
  have hft : f.target = (a⁻¹ * ·) ⁻¹' e.target := rfl
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [hfs]
    simpa using he0
  · intro w hw
    rw [hfs] at hw
    change _ = a * e (w + -v)
    rw [← heq hw, ha]
    change (complexExponentialHom X d w).toMul =
      (complexExponentialHom X d v).toMul * (complexExponentialHom X d (w + -v)).toMul
    rw [← toMul_add, ← map_add]
    congr 2
    abel
  · intro y hy
    rw [hft] at hy
    apply ContMDiffAt.contMDiffWithinAt
    have h1 : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω e.symm (a⁻¹ * y) :=
      hsm.contMDiffAt (e.open_target.mem_nhds hy)
    have h2 : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (fun p : Fin d → ℂ ↦ p + -(-v)) :=
      (contDiff_id.add contDiff_const).contMDiff
    have h3 := spec_contMDiff_mul_left X d a⁻¹
    exact (h2 _).comp y (h1.comp y (h3 y))

/-- A map with a two-sided local inverse, both differentiable, has invertible derivative. -/
private theorem isInvertible_mfderiv_of_localInverse {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
    [ChartedSpace E N] {f : M → N} {g : N → M} {x : M} (hgx : g (f x) = x)
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) f x) (hg : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) g (f x))
    (h1 : g ∘ f =ᶠ[𝓝 x] id) (h2 : f ∘ g =ᶠ[𝓝 (f x)] id) :
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) f x).IsInvertible := by
  have hf' : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) f (g (f x)) := by rw [hgx]; exact hf
  have c1 := mfderiv_comp x hg hf
  rw [h1.mfderiv_eq, mfderiv_id] at c1
  have c2 := mfderiv_comp (f x) hf' hg
  rw [h2.mfderiv_eq, mfderiv_id, hgx] at c2
  let L : E →L[ℂ] E := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) f x
  let K : E →L[ℂ] E := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) g (f x)
  have hl : ∀ w, K (L w) = w := fun w ↦ (DFunLike.congr_fun c1 w).symm
  have hr : ∀ w, L (K w) = w := fun w ↦ (DFunLike.congr_fun c2 w).symm
  exact ⟨ContinuousLinearEquiv.equivOfInverse L K hl hr, rfl⟩

theorem spec_isInvertible_mfderiv_complexExponential_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] (v : Fin d → ℂ) :
    (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ)
      (fun w ↦ (complexExponential X d w).toMul) v).IsInvertible := by
  obtain ⟨e, hv, heq, hsm⟩ := complexExponential_localBiholomorph_at X d v
  set E : (Fin d → ℂ) → ComplexPoint X := fun w ↦ (complexExponential X d w).toMul with hE
  have hEv : E v = e v := heq hv
  have hEt : E v ∈ e.target := hEv ▸ e.map_source hv
  have hsv : e.symm (E v) = v := by rw [hEv, e.left_inv hv]
  have hdE : MDifferentiableAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) E v :=
    spec_mdifferentiable_complexExponential X d v
  have hdS : MDifferentiableAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) e.symm (E v) :=
    (hsm.contMDiffAt (e.open_target.mem_nhds hEt)).mdifferentiableAt (by simp)
  have h1 : e.symm ∘ E =ᶠ[𝓝 v] id := by
    filter_upwards [e.open_source.mem_nhds hv] with w hw
    simp only [Function.comp_apply, heq hw, e.left_inv hw, id]
  have h2 : E ∘ e.symm =ᶠ[𝓝 (E v)] id := by
    filter_upwards [e.open_target.mem_nhds hEt] with y hy
    simp only [Function.comp_apply, heq (e.map_target hy), e.right_inv hy, id]
  exact isInvertible_mfderiv_of_localInverse hsv hdE hdS h1 h2

theorem spec_complexExponential_localBiholomorph_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] (v : Fin d → ℂ) :
    ∃ e : OpenPartialHomeomorph (Fin d → ℂ) (ComplexPoint X),
      v ∈ e.source ∧ Set.EqOn (fun w ↦ (complexExponential X d w).toMul) e e.source ∧
        ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω e.symm e.target :=
  complexExponential_localBiholomorph_at X d v

theorem spec_isAddQuotientCoveringMap_complexExponential_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    [IsIntegral X.left] [IsProjective X.hom] :
    IsAddQuotientCoveringMap (fun v ↦ (complexExponential X d v).toMul)
      (complexExponentialLattice X d).toAddSubgroup := by
  have hq : IsQuotientMap (fun v ↦ (complexExponential X d v).toMul) :=
    (IsOpenQuotientMap.mk (surjective_complexExponential X d)
      (continuous_complexExponential X d) (isOpenMap_complexExponential X d)).isQuotientMap
  refine hq.isAddQuotientCoveringMap_of_addSubgroup _
    (isDiscrete_iff_discreteTopology.mpr (discrete_complexExponentialLattice X d)) ?_
  intro e₁ e₂
  change _ ↔ complexExponentialHom X d (e₂ + -e₁) = 0
  rw [map_add, map_neg, add_neg_eq_zero, eq_comm]
  rfl

theorem spec_contMDiff_iff_contDiff_comp_complexExponential_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    [IsIntegral X.left] [IsProjective X.hom] (F : ComplexPoint X → ℂ) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω F ↔
      ContDiff ℂ ω (fun v ↦ F (complexExponential X d v).toMul) := by
  constructor
  · intro hF
    exact contMDiff_iff_contDiff.mp (hF.comp (spec_contMDiff_complexExponential X d))
  · intro hf x
    obtain ⟨v, hv⟩ := surjective_complexExponential X d (Additive.ofMul x)
    obtain ⟨e, hve, heq, hs⟩ := spec_complexExponential_localBiholomorph_aux X d v
    have hx : e v = x := by rw [← heq hve]; simp [hv]
    have hxt : x ∈ e.target := hx ▸ e.map_source hve
    have hcomp : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω
        ((fun v ↦ F (complexExponential X d v).toMul) ∘ e.symm) x :=
      (contMDiff_iff_contDiff.mpr hf).contMDiffAt.comp x
        (hs.contMDiffAt (e.open_target.mem_nhds hxt))
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [e.open_target.mem_nhds hxt] with y hy
    simp only [Function.comp_apply]
    have h' := heq (e.map_target hy)
    simp only at h'
    rw [h', e.right_inv hy]

theorem spec_existsUnique_contMDiff_descent_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    [IsIntegral X.left] [IsProjective X.hom] (f : (Fin d → ℂ) → ℂ) (hf : ContDiff ℂ ω f)
    (hper : ∀ l ∈ complexExponentialLattice X d, ∀ v, f (v + l) = f v) :
    ∃! F : ComplexPoint X → ℂ, ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω F ∧
      ∀ v, F (complexExponential X d v).toMul = f v := by
  have hsurj := surjective_complexExponential X d
  let F : ComplexPoint X → ℂ := fun x ↦ f (hsurj (Additive.ofMul x)).choose
  have hF : ∀ v, F (complexExponential X d v).toMul = f v := by
    intro v
    have hw := (hsurj (Additive.ofMul (complexExponential X d v).toMul)).choose_spec
    set w := (hsurj (Additive.ofMul (complexExponential X d v).toMul)).choose
    have hl : w - v ∈ complexExponentialLattice X d := by
      change complexExponentialHom X d (w - v) = 0
      rw [map_sub]
      change complexExponential X d w - complexExponential X d v = 0
      rw [hw]; exact sub_self _
    change f w = f v
    simpa using hper _ hl v
  refine ⟨F, ⟨(spec_contMDiff_iff_contDiff_comp_complexExponential_aux X d F).mpr ?_, hF⟩, ?_⟩
  · simpa only [hF] using hf
  · rintro G ⟨-, hG⟩
    funext x
    obtain ⟨v, rfl⟩ := hsurj (Additive.ofMul x)
    exact (hG v).trans (hF v).symm

theorem spec_rat_quotient_not_t2Space_aux :
    ¬ T2Space (ℂ ⧸ (Rat.castHom ℂ).toAddMonoidHom.range) := by
  intro h
  set S := (Rat.castHom ℂ).toAddMonoidHom.range
  have hS : IsClosed (S : Set ℂ) := by
    have : (QuotientAddGroup.mk : ℂ → ℂ ⧸ S) ⁻¹' {0} = S := by
      ext z; simp [QuotientAddGroup.eq_zero_iff]
    rw [← this]
    exact (isClosed_singleton).preimage QuotientAddGroup.continuous_mk
  have hmem : ((Real.sqrt 2 : ℝ) : ℂ) ∈ S :=
    Rat.denseRange_cast.induction_on (p := fun r : ℝ ↦ (r : ℂ) ∈ S) (Real.sqrt 2)
      (hS.preimage Complex.continuous_ofReal) (fun q ↦ ⟨q, by simp⟩)
  obtain ⟨q, hq⟩ := hmem
  refine irrational_sqrt_two ⟨q, ?_⟩
  have : ((q : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := by simpa using hq
  exact_mod_cast this

theorem spec_int_quotient_discrete_not_compact_aux :
    DiscreteTopology (Int.castAddHom ℂ).range ∧ ¬ CompactSpace (ℂ ⧸ (Int.castAddHom ℂ).range) := by
  set S := (Int.castAddHom ℂ).range
  constructor
  · apply discreteTopology_of_isOpen_singleton_zero
    have : ({0} : Set S) = Subtype.val ⁻¹' Metric.ball (0 : ℂ) 1 := by
      ext ⟨z, m, rfl⟩
      simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
      constructor
      · intro h; have : (m : ℂ) = 0 := congrArg Subtype.val h
        simp [this]
      · intro h
        have h1 : |(m : ℝ)| < 1 := by simpa [Complex.norm_intCast] using h
        have : m = 0 := by
          have : |m| < 1 := by exact_mod_cast h1
          exact Int.abs_lt_one_iff.mp this
        ext; simp [this]
    rw [this]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  · intro h
    let g : ℂ ⧸ S →+ ℝ := QuotientAddGroup.lift S Complex.imAddGroupHom (by
      rintro _ ⟨m, rfl⟩; simp)
    have hg : Continuous g :=
      (QuotientAddGroup.isQuotientMap_mk S).continuous_iff.mpr Complex.continuous_im
    have hc := isCompact_range hg
    have : Set.range g = Set.univ := by
      refine Set.eq_univ_of_forall fun r ↦ ⟨QuotientAddGroup.mk (r * Complex.I), ?_⟩
      simp [g]
    rw [this] at hc
    exact noncompact_univ ℝ hc

theorem spec_contMDiff_iff_contMDiff_comp_complexExponential_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    [IsIntegral X.left] [IsProjective X.hom]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {H' : Type*} [TopologicalSpace H']
    (I' : ModelWithCorners ℂ E' H') {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y]
    (F : ComplexPoint X → Y) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) I' ω F ↔
      ContMDiff 𝓘(ℂ, Fin d → ℂ) I' ω (fun v ↦ F (complexExponential X d v).toMul) := by
  refine ⟨fun hF ↦ hF.comp (spec_contMDiff_complexExponential X d), fun hG x ↦ ?_⟩
  obtain ⟨v, hvx⟩ := surjective_complexExponential X d (Additive.ofMul x)
  obtain rfl : x = (complexExponential X d v).toMul := by rw [hvx]; rfl
  obtain ⟨e, hv, he, hs⟩ := spec_complexExponential_localBiholomorph_aux X d v
  have hx : (complexExponential X d v).toMul ∈ e.target := by
    rw [show (complexExponential X d v).toMul = e v from he hv]; exact e.map_source hv
  have hon : ContMDiffOn 𝓘(ℂ, Fin d → ℂ) I' ω
      ((fun w ↦ F (complexExponential X d w).toMul) ∘ e.symm) e.target :=
    hG.contMDiffOn.comp (t := Set.univ) hs (fun _ _ ↦ Set.mem_univ _)
  have heq : Set.EqOn F ((fun w ↦ F (complexExponential X d w).toMul) ∘ e.symm) e.target := by
    intro y hy
    simp only [Function.comp_apply]
    rw [show (complexExponential X d (e.symm y)).toMul = e (e.symm y) from he (e.map_target hy),
      e.right_inv hy]
  exact ((hon.congr heq).contMDiffAt (e.open_target.mem_nhds hx))

theorem spec_existsUnique_contMDiff_descent_manifold_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    [IsIntegral X.left] [IsProjective X.hom]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {H' : Type*} [TopologicalSpace H']
    (I' : ModelWithCorners ℂ E' H') {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y]
    (f : (Fin d → ℂ) → Y) (hf : ContMDiff 𝓘(ℂ, Fin d → ℂ) I' ω f)
    (hper : ∀ l ∈ complexExponentialLattice X d, ∀ v, f (v + l) = f v) :
    ∃! F : ComplexPoint X → Y, ContMDiff 𝓘(ℂ, Fin d → ℂ) I' ω F ∧
      ∀ v, F (complexExponential X d v).toMul = f v := by
  have hs := surjective_complexExponential X d
  let s : ComplexPoint X → (Fin d → ℂ) := fun x ↦ (hs (Additive.ofMul x)).choose
  have hsx : ∀ x, complexExponential X d (s x) = Additive.ofMul x :=
    fun x ↦ (hs (Additive.ofMul x)).choose_spec
  have hfac : ∀ v, f (s (complexExponential X d v).toMul) = f v := by
    intro v
    have hmem : v - s (complexExponential X d v).toMul ∈ complexExponentialLattice X d := by
      change complexExponentialHom X d _ = 0
      rw [map_sub]
      change complexExponential X d v - complexExponential X d _ = 0
      rw [hsx]; exact sub_self _
    have := hper _ hmem (s (complexExponential X d v).toMul)
    rw [add_sub_cancel] at this; exact this.symm
  refine ⟨fun x ↦ f (s x), ⟨?_, hfac⟩, ?_⟩
  · exact (spec_contMDiff_iff_contMDiff_comp_complexExponential_aux X d I' _).mpr (by simpa only [hfac] using hf)
  · rintro G ⟨-, hG⟩
    funext x
    obtain ⟨v, hvx⟩ := hs (Additive.ofMul x)
    obtain rfl : x = (complexExponential X d v).toMul := by rw [hvx]; rfl
    rw [hG, hfac]

end HodgeLean.Adapters
