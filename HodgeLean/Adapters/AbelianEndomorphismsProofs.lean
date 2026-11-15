import HodgeLean.Adapters.AbelianEndomorphismsDefs
import HodgeLean.Adapters.ExpHolomorphic

/-! # Proof obligations for the endomorphisms of an abelian variety acting on `HQ X 1`

One obligation per statement of `HodgeLean.Adapters.AbelianEndomorphisms`. All twelve are proved, by three parallel provers. -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

omit [IsCommMonObj X] in
/-- The period map of `X` is injective (`spec_abelianPeriod_equiv`). -/
theorem abelianPeriod_injective : Function.Injective (abelianPeriod X) := by
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv X
  intro x y hxy
  apply e.injective
  refine DFunLike.ext _ _ fun l => ?_
  rw [he, he, hxy]

omit [IsCommMonObj X] in
/-- Two endomorphisms of `HQ X 1` with the same periods everywhere are equal. -/
theorem linearMap_ext_abelianPeriod {T T' : Module.End ℚ (HQ X 1)}
    (h : ∀ x l, abelianPeriod X (T x) l = abelianPeriod X (T' x) l) : T = T' :=
  LinearMap.ext fun x => abelianPeriod_injective X (funext (h x))

omit [IsCommMonObj X] in
/-- The periods of a pullback are the periods along the image loops. -/
theorem abelianPeriod_complexPointPullback (f : X ⟶ X) (x : HQ X 1)
    (l : abelianPeriodLattice X) :
    abelianPeriod X (complexPointPullback X f 1 x) l =
      loopPeriod ((Point.continuousMap f).comp (abelianLatticeLoop X l))
        (cupComparison X 1 x) := by
  rw [loopPeriod_comp]
  simp [abelianPeriod, complexPointPullback]

omit [GrpObj X] [IsCommMonObj X] in
/-- The comparison carries the pullback to the singular pullback. -/
theorem cupComparison_complexPointPullback (f : X ⟶ X) (x : HQ X 1) :
    cupComparison X 1 (complexPointPullback X f 1 x) =
      cohomologyMap ℚ 1 (TopCat.ofHom (Point.continuousMap f)) (cupComparison X 1 x) := by
  simp [complexPointPullback]

omit [GrpObj X] [IsCommMonObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- A loop of `X(ℂ)` as a loop of the additive group `Additive X(ℂ)`. -/
private def additiveLoop (p : C(UnitAddCircle, ComplexPoint X)) :
    C(UnitAddCircle, Additive (ComplexPoint X)) :=
  ⟨fun t => Additive.ofMul (p t), p.continuous⟩

omit [GrpObj X] [IsCommMonObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
private theorem loopPeriod_additiveLoop (p : C(UnitAddCircle, ComplexPoint X)) :
    loopPeriod (additiveLoop X p) = loopPeriod p := rfl

/-- Periods along the image of a loop under a pointwise product of maps add up. -/
theorem loopPeriod_comp_mul (f g : X ⟶ X) (p : C(UnitAddCircle, ComplexPoint X)) :
    loopPeriod ((Point.continuousMap (f * g)).comp p) =
      loopPeriod ((Point.continuousMap f).comp p) +
        loopPeriod ((Point.continuousMap g).comp p) := by
  have : PathConnectedSpace (Additive (ComplexPoint X)) := pathConnectedSpace_complexPoint X
  have h : additiveLoop X ((Point.continuousMap (f * g)).comp p) =
      additiveLoop X ((Point.continuousMap f).comp p) +
        additiveLoop X ((Point.continuousMap g).comp p) := by
    refine ContinuousMap.ext fun t => ?_
    show Additive.ofMul (p t ≫ (f * g)) = Additive.ofMul ((p t ≫ f) * (p t ≫ g))
    rw [MonObj.comp_mul]
  rw [← loopPeriod_additiveLoop, h, loopPeriod_add]
  rfl

theorem spec_abelianEndAction_one_aux : abelianEndAction X 1 = 1 := by
  refine linearMap_ext_abelianPeriod X fun x l => ?_
  rw [abelianEndAction, abelianPeriod_complexPointPullback]
  rfl

theorem spec_abelianEndAction_mul_aux (f g : AbelianEnd X) :
    abelianEndAction X (f * g) = abelianEndAction X g * abelianEndAction X f := by
  refine linearMap_ext_abelianPeriod X fun x l => ?_
  rw [Module.End.mul_apply, abelianEndAction, abelianEndAction, abelianEndAction,
    abelianPeriod_complexPointPullback, abelianPeriod_complexPointPullback,
    cupComparison_complexPointPullback, ← loopPeriod_comp]
  rfl

theorem spec_abelianEndAction_zero_aux : abelianEndAction X 0 = 0 := by
  refine linearMap_ext_abelianPeriod X fun x l => ?_
  have h : (Point.continuousMap (0 : AbelianEnd X).hom).comp (abelianLatticeLoop X l) =
      ContinuousMap.const UnitAddCircle 1 := by
    refine ContinuousMap.ext fun t => ?_
    show (abelianLatticeLoop X l t ≫ (1 : X ⟶ X)) = 1
    rw [MonObj.comp_one]
  rw [abelianEndAction, abelianPeriod_complexPointPullback, h, loopPeriod_const]
  simp only [LinearMap.zero_apply, map_zero, Pi.zero_apply]

theorem spec_abelianEndAction_add_aux (f g : AbelianEnd X) :
    abelianEndAction X (f + g) = abelianEndAction X f + abelianEndAction X g := by
  refine linearMap_ext_abelianPeriod X fun x l => ?_
  rw [LinearMap.add_apply, map_add, Pi.add_apply, abelianEndAction, abelianEndAction,
    abelianEndAction, abelianPeriod_complexPointPullback, abelianPeriod_complexPointPullback,
    abelianPeriod_complexPointPullback, AbelianEnd.add_hom, loopPeriod_comp_mul]
  rfl

theorem spec_abelianEndAction_ringHom_aux :
    ∃ ρ : AbelianEnd X →+* (Module.End ℚ (HQ X 1))ᵐᵒᵖ,
      ∀ f, ρ f = MulOpposite.op (abelianEndAction X f) := by
  refine ⟨{ toFun := fun f => MulOpposite.op (abelianEndAction X f)
            map_one' := by rw [spec_abelianEndAction_one_aux, MulOpposite.op_one]
            map_mul' := fun f g => by
              rw [spec_abelianEndAction_mul_aux, MulOpposite.op_mul]
            map_zero' := by rw [spec_abelianEndAction_zero_aux, MulOpposite.op_zero]
            map_add' := fun f g => by
              rw [spec_abelianEndAction_add_aux, MulOpposite.op_add] }, fun f => rfl⟩

omit [GrpObj X] [IsCommMonObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Periods are `ℤ`-linear in the loop, for a path-connected topological abelian group. -/
theorem loopPeriod_zsmul {T : Type} [AddCommGroup T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] [PathConnectedSpace T] (n : ℤ) (p : C(UnitAddCircle, T)) :
    loopPeriod (n • p) = n • loopPeriod p :=
  map_zsmul (AddMonoidHom.mk' (fun q : C(UnitAddCircle, T) => loopPeriod q)
    spec_loopPeriod_add) n p

omit [IsCommMonObj X] in
theorem spec_complexPointPullback_zpow_aux (n : ℤ) :
    complexPointPullback X (𝟙 X ^ n) 1 = (n : ℚ) • LinearMap.id := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  have : PathConnectedSpace (Additive (ComplexPoint X)) := pathConnectedSpace_complexPoint X
  refine linearMap_ext_abelianPeriod X fun x l => ?_
  have h : additiveLoop X ((Point.continuousMap (𝟙 X ^ n)).comp (abelianLatticeLoop X l)) =
      n • additiveLoop X (abelianLatticeLoop X l) := by
    refine ContinuousMap.ext fun t => ?_
    show Additive.ofMul (abelianLatticeLoop X l t ≫ 𝟙 X ^ n) =
      n • Additive.ofMul (abelianLatticeLoop X l t)
    rw [GrpObj.comp_zpow, Category.comp_id, ofMul_zpow]
  rw [abelianPeriod_complexPointPullback, ← loopPeriod_additiveLoop, h, loopPeriod_zsmul,
    loopPeriod_additiveLoop, LinearMap.smul_apply, LinearMap.id_apply, map_smul, Pi.smul_apply]
  change n • abelianPeriod X x l = _
  rw [zsmul_eq_mul, smul_eq_mul]

section AnalyticRepresentation

open Filter Topology

variable {Y : Over (Spec ↧ℂ)} {d : ℕ} [GrpObj Y] [IsCommMonObj Y]
  [SmoothOfRelativeDimension d Y.hom]

private theorem exists_nsmul_eq_small (v : Fin d → ℂ) {t : ℝ} (ht : 0 < t) :
    ∃ (n : ℕ) (w : Fin d → ℂ), 0 < n ∧ ‖w‖ < t ∧ (n : ℝ) * ‖w‖ = ‖v‖ ∧ n • w = v := by
  obtain ⟨n, hn⟩ := exists_nat_gt (‖v‖ / t)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (norm_nonneg _) ht.le) hn
  refine ⟨n, (n : ℝ)⁻¹ • v, by exact_mod_cast hn0, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_eq_div, div_lt_iff₀ hn0]
    rwa [div_lt_iff₀ ht, mul_comm] at hn
  · rw [norm_smul, norm_inv, Real.norm_natCast, ← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul]
  · rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]

private theorem eventually_mem_identityChart_source {k : (Fin d → ℂ) → ComplexPoint Y}
    (hk : ContinuousAt k 0) (hk0 : k 0 = 1) :
    ∀ᶠ v in 𝓝 0, k v ∈ (identityChart Y d).source := by
  apply hk.tendsto.eventually
  rw [hk0]
  exact (identityChart Y d).open_source.mem_nhds (mem_localChart_source Y d 1)

/-- A continuous homomorphism `ℂ^d → X(ℂ)` whose expression in the identity chart has real
derivative `D` at `0` is `exp ∘ D`. -/
private theorem eq_complexExponential_of_hasFDerivAt
    (g : (Fin d → ℂ) →+ Additive (ComplexPoint Y)) (hg : ContinuousAt g 0)
    (D : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ))
    (hD : HasFDerivAt (fun v ↦ identityChart Y d (g v).toMul) D 0) (v : Fin d → ℂ) :
    g v = complexExponential Y d (D v) := by
  set E : (Fin d → ℂ) → (Fin d → ℂ) :=
    fun v ↦ identityChart Y d (complexExponential Y d v).toMul with hEdef
  set F : (Fin d → ℂ) → (Fin d → ℂ) := fun v ↦ identityChart Y d (g v).toMul with hFdef
  have hE0 : E 0 = 0 := by
    simp only [hEdef, complexExponential_zero, toMul_zero, identityChart_one]
  have hF0 : F 0 = 0 := by
    simp only [hFdef, map_zero, toMul_zero, identityChart_one]
  have hEd : HasFDerivAt E
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℂ)) : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ)) 0 :=
    hasFDerivAt_complexExponential_chart Y d
  have hs : HasStrictFDerivAt E
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℂ)) : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ)) 0 :=
    (contDiffAt_complexExponential_chart Y d).hasStrictFDerivAt' hEd one_ne_zero
  set L := hs.localInverse E _ 0 with hLdef
  have hL : HasStrictFDerivAt L
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℂ)).symm : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ)) (E 0) :=
    hs.to_localInverse
  have hLE : ∀ᶠ x in 𝓝 0, L (E x) = x := hs.eventually_left_inverse
  have hEL : ∀ᶠ y in 𝓝 (E 0), E (L y) = y := hs.eventually_right_inverse
  have hL0 : L 0 = 0 := by
    have := hLE.self_of_nhds
    rwa [hE0] at this
  set h : (Fin d → ℂ) → (Fin d → ℂ) := fun v ↦ L (F v) with hhdef
  have hh0 : h 0 = 0 := by simp only [hhdef, hF0, hL0]
  have hhd : HasFDerivAt h D 0 := by
    have hL' : HasFDerivAt L
        ((ContinuousLinearEquiv.refl ℝ (Fin d → ℂ)).symm : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ))
        (F 0) := by
      rw [hF0, ← hE0]
      exact hL.hasFDerivAt
    have := hL'.comp 0 hD
    simpa using this
  -- `exp ∘ h = g` near `0`
  have hgv : ∀ᶠ v in 𝓝 0, complexExponential Y d (h v) = g v := by
    have hexp : ContinuousAt (fun v ↦ (complexExponential Y d (h v)).toMul) 0 :=
      (continuous_toMul.comp (continuous_complexExponential Y d)).continuousAt.comp
        hhd.continuousAt
    have h1 := eventually_mem_identityChart_source hexp
      (by simp only [hh0, complexExponential_zero, toMul_zero])
    have h2 := eventually_mem_identityChart_source (k := fun v ↦ (g v).toMul)
      (continuous_toMul.continuousAt.comp hg) (by simp)
    have h3 : ∀ᶠ v in 𝓝 0, E (L (F v)) = F v := by
      refine hD.continuousAt.tendsto.eventually (p := fun y ↦ E (L y) = y) ?_
      rw [hF0, ← hE0]
      exact hEL
    filter_upwards [h1, h2, h3] with v h1 h2 h3
    exact Additive.toMul.injective ((identityChart Y d).injOn h1 h2 h3)
  -- local injectivity of `exp`
  obtain ⟨r, hr, hrN⟩ := Metric.eventually_nhds_iff_ball.mp hLE
  have hexpinj : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) r, ∀ y ∈ Metric.ball (0 : Fin d → ℂ) r,
      complexExponential Y d x = complexExponential Y d y → x = y := by
    intro x hx y hy hxy
    rw [← hrN x hx, ← hrN y hy]
    simp only [hEdef, hxy]
  have hsmall : ∀ᶠ v in 𝓝 0, h v ∈ Metric.ball (0 : Fin d → ℂ) (r / 2) := by
    refine hhd.continuousAt.tendsto.eventually (p := fun y ↦ y ∈ Metric.ball 0 (r / 2)) ?_
    rw [hh0]
    exact Metric.ball_mem_nhds _ (half_pos hr)
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff_ball.mp (hgv.and hsmall)
  have hδ : 0 < ε / 2 := half_pos hε
  -- local additivity of `h`
  have hadd : ∀ u, ‖u‖ < ε / 2 → ∀ w, ‖w‖ < ε / 2 → h (u + w) = h u + h w := by
    intro u hu w hw
    have huw : u + w ∈ Metric.ball (0 : Fin d → ℂ) ε := by
      rw [mem_ball_zero_iff]
      calc ‖u + w‖ ≤ ‖u‖ + ‖w‖ := norm_add_le _ _
        _ < ε / 2 + ε / 2 := add_lt_add hu hw
        _ = ε := add_halves ε
    have hu' : u ∈ Metric.ball (0 : Fin d → ℂ) ε := by
      rw [mem_ball_zero_iff]; linarith
    have hw' : w ∈ Metric.ball (0 : Fin d → ℂ) ε := by
      rw [mem_ball_zero_iff]; linarith
    have h1 := (hεP _ huw).2
    have h2 := (hεP _ hu').2
    have h3 := (hεP _ hw').2
    rw [mem_ball_zero_iff] at h1 h2 h3
    apply hexpinj
    · rw [mem_ball_zero_iff]; linarith
    · rw [mem_ball_zero_iff]
      calc ‖h u + h w‖ ≤ ‖h u‖ + ‖h w‖ := norm_add_le _ _
        _ < r / 2 + r / 2 := add_lt_add h2 h3
        _ = r := add_halves r
    · have hm : complexExponential Y d (h u + h w) =
          complexExponential Y d (h u) + complexExponential Y d (h w) :=
        (complexExponentialHom Y d).map_add _ _
      rw [(hεP _ huw).1, hm, (hεP _ hu').1, (hεP _ hw').1, map_add]
  have hmul : ∀ u, ‖u‖ < ε / 2 → ∀ k : ℕ, (k : ℝ) * ‖u‖ < ε / 2 → h (k • u) = k • h u := by
    intro u hu k
    induction k with
    | zero => intro _; simp [hh0]
    | succ k ih =>
      intro hk
      have hk' : (k : ℝ) * ‖u‖ < ε / 2 := by
        refine lt_of_le_of_lt ?_ hk
        gcongr
        simp
      rw [succ_nsmul, succ_nsmul, hadd _ (by rw [RCLike.norm_nsmul ℝ, nsmul_eq_mul]; exact hk') u hu,
        ih hk']
  -- `h` agrees with `D` near `0`
  have hlo : (fun u ↦ h u - D u) =o[𝓝 0] fun u ↦ u := by
    have := hasFDerivAt_iff_isLittleO_nhds_zero.mp hhd
    simpa [hh0] using this
  have hlin : ∀ u, ‖u‖ < ε / 2 → h u = D u := by
    intro u hu
    have key : ∀ c : ℝ, 0 < c → ‖h u - D u‖ ≤ c * ‖u‖ := by
      intro c hc
      obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff_ball.mp (hlo.def hc)
      obtain ⟨n, w, hn, hw, hnw, hwu⟩ := exists_nsmul_eq_small u (lt_min hρ hδ)
      have hwρ : w ∈ Metric.ball (0 : Fin d → ℂ) ρ :=
        mem_ball_zero_iff.mpr (lt_of_lt_of_le hw (min_le_left _ _))
      have hwδ : ‖w‖ < ε / 2 := lt_of_lt_of_le hw (min_le_right _ _)
      have he : h u - D u = n • (h w - D w) := by
        rw [← hwu, hmul w hwδ n (by rw [hnw]; exact hu), map_nsmul, nsmul_sub]
      rw [he, RCLike.norm_nsmul ℝ, nsmul_eq_mul, ← hnw]
      have := hρP _ hwρ
      calc (n : ℝ) * ‖h w - D w‖ ≤ n * (c * ‖w‖) := by gcongr
        _ = c * (n * ‖w‖) := by ring
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    by_contra hne
    replace hne := not_le.mp hne
    have h1 := key (‖h u - D u‖ / (‖u‖ + 1)) (div_pos hne (by positivity))
    have h2 : ‖h u - D u‖ / (‖u‖ + 1) * ‖u‖ < ‖h u - D u‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg u]
    linarith
  -- globalize by subdivision
  obtain ⟨n, w, hn, hw, hnw, hwv⟩ := exists_nsmul_eq_small v hδ
  have hwε : w ∈ Metric.ball (0 : Fin d → ℂ) ε := by
    rw [mem_ball_zero_iff]; linarith
  have hexp : complexExponential Y d (D w) = g w := by
    rw [← hlin w hw]
    exact (hεP _ hwε).1
  rw [← hwv, map_nsmul, map_nsmul, ← hexp]
  exact ((complexExponentialHom Y d).map_nsmul _ _).symm

end AnalyticRepresentation

omit [IsCommMonObj X] in
theorem spec_abelianEnd_analyticRepresentation_aux (f : AbelianEnd X) :
    ∃ A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ), ∀ v,
      Additive.toMul (complexExponential X (dim X.left) (A v)) =
        Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)) := by
  have : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  set d := dim X.left
  have hf1 : Point.map f.hom (1 : ComplexPoint X) = 1 := MonObj.one_comp f.hom
  let g : (Fin d → ℂ) →+ Additive (ComplexPoint X) :=
    { toFun := fun v ↦ Additive.ofMul (Point.map f.hom (complexExponential X d v).toMul)
      map_zero' := by
        rw [complexExponential_zero, toMul_zero, hf1]
        rfl
      map_add' := fun v w ↦ by
        have hm : complexExponential X d (v + w) =
            complexExponential X d v + complexExponential X d w :=
          (complexExponentialHom X d).map_add _ _
        rw [hm, toMul_add]
        exact MonObj.mul_comp _ _ f.hom }
  have hg : Continuous g :=
    continuous_ofMul.comp ((Point.continuous_map f.hom).comp
      (continuous_toMul.comp (continuous_complexExponential X d)))
  set G : (Fin d → ℂ) → (Fin d → ℂ) := fun w ↦ identityChart X d (g w).toMul with hGdef
  have hG : AnalyticAt ℂ G 0 := by
    set c := localChart X d 1 1
    have hc : c ∈ (localChart X d 1).target :=
      (localChart X d 1).map_source (mem_localChart_source X d 1)
    have hH := analyticAt_localChart_symm_map X X f.hom d d 1 hc (by
      rw [(localChart X d 1).left_inv (mem_localChart_source X d 1)]
      exact mem_localChart_source X d _)
    rw [hf1] at hH
    have hE := spec_analyticAt_complexExponential_chart X d
    have hE0 : identityChart X d (complexExponential X d 0).toMul + c = c := by
      rw [complexExponential_zero, toMul_zero, identityChart_one, zero_add]
    have hcomp := (hH.comp_of_eq (hE.add (analyticAt_const (v := c))) hE0).sub (analyticAt_const (v := c))
    apply hcomp.congr
    have hmem := eventually_mem_identityChart_source
      (k := fun v ↦ (complexExponential X d v).toMul)
      (continuous_toMul.comp (continuous_complexExponential X d)).continuousAt
      (by rw [complexExponential_zero, toMul_zero])
    filter_upwards [hmem] with v hv
    simp only [hGdef]
    change localChart X d 1 (Point.map f.hom ((localChart X d 1).symm
      (localChart X d 1 (complexExponential X d v).toMul - c + c))) - c =
        localChart X d 1 (Point.map f.hom (complexExponential X d v).toMul) - c
    rw [sub_add_cancel, (localChart X d 1).left_inv hv]
  have hD : HasFDerivAt G ((fderiv ℂ G 0).restrictScalars ℝ) 0 :=
    hG.differentiableAt.hasFDerivAt.restrictScalars ℝ
  refine ⟨(fderiv ℂ G 0).toLinearMap, fun v ↦ ?_⟩
  have := eq_complexExponential_of_hasFDerivAt g hg.continuousAt _ hD v
  rw [ContinuousLinearMap.coe_restrictScalars'] at this
  exact (congrArg Additive.toMul this).symm

omit [IsCommMonObj X] in
theorem spec_abelianEndAction_period_aux (f : AbelianEnd X) :
    ∃ φ : abelianPeriodLattice X →+ abelianPeriodLattice X, ∀ x l,
      abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l) := by
  obtain ⟨A, hA⟩ := spec_abelianEnd_analyticRepresentation_aux X f
  have hf1 : Point.map f.hom (1 : ComplexPoint X) = 1 := MonObj.one_comp f.hom
  let φ : abelianPeriodLattice X →+ abelianPeriodLattice X :=
    { toFun := fun l ↦ ⟨A l, by
        change complexExponential X (dim X.left) (A l) = 0
        apply Additive.toMul.injective
        rw [hA, show complexExponential X (dim X.left) (l : Fin (dim X.left) → ℂ) = 0 from l.2]
        exact hf1⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun l m ↦ Subtype.ext (by simp) }
  refine ⟨φ, fun x l ↦ ?_⟩
  have hloop : (Point.continuousMap f.hom).comp (abelianLatticeLoop X l) =
      abelianLatticeLoop X (φ l) := by
    refine ContinuousMap.ext fun z ↦ ?_
    induction z using QuotientAddGroup.induction_on with
    | H t =>
      change Point.map f.hom (Additive.toMul
          (oneParameterSubgroup X _ (l : Fin (dim X.left) → ℂ) t)) =
        Additive.toMul (oneParameterSubgroup X _ (A l) t)
      rw [← complexExponential_smul, ← complexExponential_smul, ← hA, A.map_smul_of_tower]
  have e1 : ∀ y m, abelianPeriod X y m =
      loopPeriod (abelianLatticeLoop X m) (cupComparison X 1 y) := fun _ _ ↦ rfl
  have e2 : cupComparison X 1 (abelianEndAction X f x) =
      cohomologyMap ℚ 1 (TopCat.ofHom (Point.continuousMap f.hom)) (cupComparison X 1 x) := by
    simp [abelianEndAction, complexPointPullback]
  rw [e1, e1, e2, ← hloop, loopPeriod_comp]

omit [IsCommMonObj X] in
/-- A complex-linear `A` intertwining the exponential with `f` maps periods to periods. -/
private theorem analyticRepresentation_mem_lattice (f : AbelianEnd X)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)))
    (l : abelianPeriodLattice X) : A l ∈ abelianPeriodLattice X := by
  have hl : complexExponential X (dim X.left) (l : Fin (dim X.left) → ℂ) = 0 := l.2
  change complexExponential X (dim X.left) (A l) = 0
  apply Additive.toMul.injective
  rw [hA, hl]
  change (1 : ComplexPoint X) ≫ f.hom = 1
  exact MonObj.one_comp f.hom

omit [IsCommMonObj X] in
private theorem analyticRepresentation_loop (f : AbelianEnd X)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)))
    (l : abelianPeriodLattice X) :
    (Point.continuousMap f.hom).comp (abelianLatticeLoop X l) =
      abelianLatticeLoop X ⟨A l, analyticRepresentation_mem_lattice X f A hA l⟩ := by
  refine ContinuousMap.ext fun z => ?_
  induction z using QuotientAddGroup.induction_on with
  | H t =>
    change Point.map f.hom (Additive.toMul (oneParameterSubgroup X (dim X.left)
        (l : Fin (dim X.left) → ℂ) t)) =
      Additive.toMul (oneParameterSubgroup X (dim X.left) (A l) t)
    rw [← complexExponential_smul, ← complexExponential_smul, ← hA,
      LinearMap.map_smul_of_tower]

omit [IsCommMonObj X] in
private theorem abelianPeriod_analyticRepresentation (f : AbelianEnd X)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)))
    (x : HQ X 1) (l : abelianPeriodLattice X) :
    abelianPeriod X (abelianEndAction X f x) l =
      abelianPeriod X x ⟨A l, analyticRepresentation_mem_lattice X f A hA l⟩ := by
  rw [abelianPeriod, LinearMap.pi_apply, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, abelianEndAction, complexPointPullback, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, ← loopPeriod_comp, analyticRepresentation_loop X f A hA]

omit [IsCommMonObj X] in
private theorem complexAbelianPeriod_tmul (c : ℂ) (x : HQ X 1) (l : abelianPeriodLattice X) :
    complexAbelianPeriod X (c ⊗ₜ x) l = c * (abelianPeriod X x l : ℂ) := by
  simp [complexAbelianPeriod]

omit [IsCommMonObj X] in
private theorem complexAbelianPeriod_analyticRepresentation (f : AbelianEnd X)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)))
    (ω : ℂ ⊗[ℚ] HQ X 1) (l : abelianPeriodLattice X) :
    complexAbelianPeriod X ((abelianEndAction X f).baseChange ℂ ω) l =
      complexAbelianPeriod X ω ⟨A l, analyticRepresentation_mem_lattice X f A hA l⟩ := by
  induction ω using TensorProduct.inductionOn with
  | tmul c x =>
    rw [LinearMap.baseChange_tmul, complexAbelianPeriod_tmul, complexAbelianPeriod_tmul,
      abelianPeriod_analyticRepresentation X f A hA]
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

omit [IsCommMonObj X] in
theorem spec_abelianEndAction_hodge_of_analyticRepresentation_aux (f : AbelianEnd X)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v))) :
    (complexHolomorphicH1 X).map ((abelianEndAction X f).baseChange ℂ) ≤
        complexHolomorphicH1 X ∧
      (complexAntiholomorphicH1 X).map ((abelianEndAction X f).baseChange ℂ) ≤
        complexAntiholomorphicH1 X := by
  have key : ∀ (ω : ℂ ⊗[ℚ] HQ X 1) (F : DegreeOneLatticeDual (dim X.left)),
      latticeRestriction X F = complexAbelianPeriod X ω →
        latticeRestriction X (F ∘ₗ A.restrictScalars ℝ) =
          complexAbelianPeriod X ((abelianEndAction X f).baseChange ℂ ω) := by
    intro ω F hF
    funext l
    rw [complexAbelianPeriod_analyticRepresentation X f A hA, ← hF]
    rfl
  constructor
  · rw [Submodule.map_le_iff_le_comap]
    rintro ω ⟨F, hF, hFω⟩
    refine ⟨F ∘ₗ A.restrictScalars ℝ, fun v => ?_, key ω F hFω⟩
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, map_smul]
    exact hF (A v)
  · rw [Submodule.map_le_iff_le_comap]
    rintro ω ⟨F, hF, hFω⟩
    refine ⟨F ∘ₗ A.restrictScalars ℝ, fun v => ?_, key ω F hFω⟩
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, map_smul]
    exact hF (A v)

omit [IsCommMonObj X] in
theorem spec_abelianEndAction_hodge_aux (f : AbelianEnd X) :
    (complexHolomorphicH1 X).map ((abelianEndAction X f).baseChange ℂ) ≤
        complexHolomorphicH1 X ∧
      (complexAntiholomorphicH1 X).map ((abelianEndAction X f).baseChange ℂ) ≤
        complexAntiholomorphicH1 X := by
  obtain ⟨A, hA⟩ := spec_abelianEnd_analyticRepresentation_aux X f
  exact spec_abelianEndAction_hodge_of_analyticRepresentation_aux X f A hA

omit [IsCommMonObj X] in
/-- Two points of the period lattice with the same rational periods are equal. -/
private theorem abelianPeriodLattice_eq_of_period {a b : abelianPeriodLattice X}
    (h : ∀ x, abelianPeriod X x a = abelianPeriod X x b) : a = b := by
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv X
  refine (abelianLatticeBasis X).ext_elem fun i => ?_
  let χ : abelianPeriodLattice X →+ ℚ :=
    (Int.castAddHom ℚ).comp ((abelianLatticeBasis X).coord i).toAddMonoidHom
  have hχ := h (e.symm χ)
  rw [← he, ← he, LinearEquiv.apply_symm_apply] at hχ
  have h2 : ((abelianLatticeBasis X).repr a i : ℚ) = (abelianLatticeBasis X).repr b i := hχ
  exact_mod_cast h2

omit [GrpObj X] [IsCommMonObj X] in
/-- Morphisms of `X` over `Spec ℂ` are determined by their maps of complex points. -/
private theorem over_hom_ext_of_point_map {f g : X ⟶ X} (h : Point.map f = Point.map g) :
    f = g := by
  refine Over.OverMorphism.ext ?_
  have hf : f.left ≫ X.hom = X.hom := Over.w f
  have hg : g.left ≫ X.hom = X.hom := Over.w g
  have : LocallyOfFiniteType (f.left ≫ X.hom) := by rw [hf]; infer_instance
  refine ext_of_apply_eq (K := ℂ) X.hom Set.univ isOpen_univ.isLocallyClosed dense_univ ?_
    (hf.trans hg.symm)
  intro x _ hx
  obtain ⟨a⟩ : Nonempty (Spec ↧ℂ) := inferInstance
  rw [← pointOfClosedPoint_apply X.hom x hx a]
  have := congrArg (fun z => z.left)
    (congrFun h (Over.homMk (pointOfClosedPoint X.hom x hx) (by simp) :
      Over.mk (𝟙 (Spec ↧ℂ)) ⟶ X))
  change (pointOfClosedPoint X.hom x hx ≫ f.left) a = (pointOfClosedPoint X.hom x hx ≫ g.left) a
  exact congrArg (fun φ : Spec ↧ℂ ⟶ X.left => φ a) this

omit [IsCommMonObj X] in
theorem spec_abelianEndAction_injective_aux : Function.Injective (abelianEndAction X) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  intro f f' hff'
  obtain ⟨A, hA⟩ := spec_abelianEnd_analyticRepresentation_aux X f
  obtain ⟨A', hA'⟩ := spec_abelianEnd_analyticRepresentation_aux X f'
  have hΛ : ∀ l : abelianPeriodLattice X, A l = A' l := fun l => by
    have := abelianPeriodLattice_eq_of_period X (a := ⟨A l, analyticRepresentation_mem_lattice X f A hA l⟩)
      (b := ⟨A' l, analyticRepresentation_mem_lattice X f' A' hA' l⟩) fun x => by
        rw [← abelianPeriod_analyticRepresentation X f A hA,
          ← abelianPeriod_analyticRepresentation X f' A' hA', hff']
    exact congrArg Subtype.val this
  have hAA' : A.restrictScalars ℝ = A'.restrictScalars ℝ := by
    let := isZLattice_complexExponentialLattice X (dim X.left)
    refine LinearMap.ext_on (IsZLattice.span_top (L := abelianPeriodLattice X)) ?_
    intro w hw
    exact hΛ ⟨w, hw⟩
  have hmap : Point.map f.hom = Point.map f'.hom := by
    funext p
    obtain ⟨v, hv⟩ := surjective_complexExponential X (dim X.left) (Additive.ofMul p)
    have hp : p = Additive.toMul (complexExponential X (dim X.left) v) := by rw [hv]; rfl
    rw [hp, ← hA, ← hA']
    exact congrArg (fun w => Additive.toMul (complexExponential X (dim X.left) w))
      (LinearMap.congr_fun hAA' v)
  exact AbelianEnd.ext (over_hom_ext_of_point_map X hmap)

theorem spec_abelianEnd0Action_aux :
    ∃ ρ : AbelianEnd0 X →ₐ[ℚ] (Module.End ℚ (HQ X 1))ᵐᵒᵖ,
      (∀ f, ρ (1 ⊗ₜ f) = MulOpposite.op (abelianEndAction X f)) ∧ Function.Injective ρ := by
  obtain ⟨ρ, hρ⟩ := spec_abelianEndAction_ringHom_aux X
  let ρ0 : AbelianEnd0 X →ₐ[ℚ] (Module.End ℚ (HQ X 1))ᵐᵒᵖ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℚ _) ρ.toIntAlgHom
      fun q _ => by rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left q _
  have hρ0 : ∀ f, ρ0 (1 ⊗ₜ f) = MulOpposite.op (abelianEndAction X f) := fun f => by
    dsimp only [ρ0]
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact hρ f
  refine ⟨ρ0, hρ0, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  let j := TensorProduct.mk ℤ ℚ (AbelianEnd X) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ j).mpr
      (TensorProduct.isBaseChange ℤ (AbelianEnd X) ℚ)
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (nonZeroDivisors ℤ) j x
  change ρ0 (IsLocalizedModule.mk' j m s) = 0 at hx
  have hcancel := IsLocalizedModule.mk'_cancel' j m s
  have hm : abelianEndAction X m = abelianEndAction X 0 := by
    rw [spec_abelianEndAction_zero_aux X]
    apply MulOpposite.op_injective
    rw [← hρ0, MulOpposite.op_zero]
    change ρ0 (j m) = 0
    rw [← hcancel, Submonoid.smul_def, map_zsmul]
    rw [hx, smul_zero]
  change IsLocalizedModule.mk' j m s = 0
  rw [spec_abelianEndAction_injective_aux X hm]
  exact IsLocalizedModule.mk'_zero j s

end HodgeLean.Adapters
