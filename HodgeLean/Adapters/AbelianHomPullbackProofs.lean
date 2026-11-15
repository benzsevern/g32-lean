import HodgeLean.Adapters.AbelianHomPullbackDefs
import HodgeLean.Adapters.AbelianEndomorphisms
import HodgeLean.Adapters.HodgeDegreeOneAbelian

/-! # Proof obligations for pullback along homomorphisms of abelian varieties

One obligation per statement of `HodgeLean.Adapters.AbelianHomPullback`. All are open. -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

section Functoriality

variable {X Y Z : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
  [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom] in
/-- The map of complex points of the identity is the identity. -/
theorem ofHom_continuousMap_id :
    TopCat.ofHom (Point.continuousMap (𝟙 X)) = 𝟙 (TopCat.of (ComplexPoint X)) := by
  refine TopCat.hom_ext (ContinuousMap.ext fun z => ?_)
  exact Category.comp_id z

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom] in
/-- The map of complex points of a composite is the composite of the maps. -/
theorem ofHom_continuousMap_comp (g : Z ⟶ Y) (f : Y ⟶ X) :
    TopCat.ofHom (Point.continuousMap (g ≫ f)) =
      TopCat.ofHom (Point.continuousMap g) ≫ TopCat.ofHom (Point.continuousMap f) := by
  refine TopCat.hom_ext (ContinuousMap.ext fun z => ?_)
  exact (Category.assoc z g f).symm

theorem spec_homPullback_id_aux (n : ℕ) : homPullback (𝟙 X) n = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [homPullback, LinearMap.comp_apply, ofHom_continuousMap_id, cohomologyMap_id,
    LinearEquiv.coe_coe, LinearMap.id_apply, LinearEquiv.symm_apply_apply]

theorem spec_homPullback_comp_aux (g : Z ⟶ Y) (f : Y ⟶ X) (n : ℕ) :
    homPullback (g ≫ f) n = homPullback g n ∘ₗ homPullback f n := by
  refine LinearMap.ext fun x => ?_
  simp only [homPullback, LinearMap.comp_apply, ofHom_continuousMap_comp, cohomologyMap_comp,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

theorem spec_homPullback_section_aux (p : Y ⟶ X) (s : X ⟶ Y) (hps : s ≫ p = 𝟙 X) (n : ℕ) :
    homPullback s n ∘ₗ homPullback p n = LinearMap.id := by
  rw [← spec_homPullback_comp_aux, hps, spec_homPullback_id_aux]

theorem spec_homPullback_unit_aux (f : Y ⟶ X) :
    homPullback f 0 (cupUnit X) = cupUnit Y := by
  apply (cupComparison Y 0).injective
  simp only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, cupComparison_unit, Foundations.Singular.cohomologyMap_unit]

end Functoriality

section Abelian

variable {X Y : Over (Spec ↧ℂ)} [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom] [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

omit [GrpObj X] in
/-- The periods of a pullback along `f : Y ⟶ X` are the periods along the image loops. -/
private theorem abelianPeriod_homPullback (f : Y ⟶ X) (x : HQ X 1)
    (l : abelianPeriodLattice Y) :
    abelianPeriod Y (homPullback f 1 x) l =
      loopPeriod ((Point.continuousMap f).comp (abelianLatticeLoop Y l))
        (cupComparison X 1 x) := by
  rw [loopPeriod_comp]
  simp [abelianPeriod, homPullback]

omit [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Two linear maps `HQ X 1 → HQ Y 1` with the same periods everywhere are equal. -/
private theorem linearMap_ext_abelianPeriod_hom {T T' : HQ X 1 →ₗ[ℚ] HQ Y 1}
    (h : ∀ x l, abelianPeriod Y (T x) l = abelianPeriod Y (T' x) l) : T = T' :=
  LinearMap.ext fun x => abelianPeriod_injective Y (funext (h x))

omit [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] in
/-- Periods along the image of a loop under a pointwise product of maps `Y ⟶ X` add up. -/
private theorem loopPeriod_comp_mul_hom (f g : Y ⟶ X) (p : C(UnitAddCircle, ComplexPoint Y)) :
    loopPeriod ((Point.continuousMap (f * g)).comp p) =
      loopPeriod ((Point.continuousMap f).comp p) +
        loopPeriod ((Point.continuousMap g).comp p) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  have : PathConnectedSpace (Additive (ComplexPoint X)) := pathConnectedSpace_complexPoint X
  let addLoop : C(UnitAddCircle, ComplexPoint X) → C(UnitAddCircle, Additive (ComplexPoint X)) :=
    fun q => ⟨fun t => Additive.ofMul (q t), q.continuous⟩
  have hadd : ∀ q, loopPeriod (addLoop q) = loopPeriod q := fun _ => rfl
  have h : addLoop ((Point.continuousMap (f * g)).comp p) =
      addLoop ((Point.continuousMap f).comp p) + addLoop ((Point.continuousMap g).comp p) := by
    refine ContinuousMap.ext fun t => ?_
    show Additive.ofMul (p t ≫ (f * g)) = Additive.ofMul ((p t ≫ f) * (p t ≫ g))
    rw [MonObj.comp_mul]
  rw [← hadd, h, spec_loopPeriod_add]
  rfl

theorem spec_homPullback_mul_aux (f g : Y ⟶ X) :
    homPullback (f * g) 1 = homPullback f 1 + homPullback g 1 := by
  refine linearMap_ext_abelianPeriod_hom fun x l => ?_
  rw [LinearMap.add_apply, map_add, Pi.add_apply, abelianPeriod_homPullback,
    abelianPeriod_homPullback, abelianPeriod_homPullback, loopPeriod_comp_mul_hom]
  rfl

theorem spec_homPullback_one_aux : homPullback (1 : Y ⟶ X) 1 = 0 := by
  refine linearMap_ext_abelianPeriod_hom fun x l => ?_
  have h : (Point.continuousMap (1 : Y ⟶ X)).comp (abelianLatticeLoop Y l) =
      ContinuousMap.const UnitAddCircle 1 := by
    refine ContinuousMap.ext fun t => ?_
    show (abelianLatticeLoop Y l t ≫ (1 : Y ⟶ X)) = 1
    rw [MonObj.comp_one]
  rw [abelianPeriod_homPullback, h, loopPeriod_const]
  simp only [LinearMap.zero_apply, map_zero, Pi.zero_apply]

theorem spec_homPullback_zpow_aux (f : Y ⟶ X) (n : ℤ) :
    homPullback (f ^ n) 1 = (n : ℚ) • homPullback f 1 := by
  let φ : (Y ⟶ X) →* Multiplicative (HQ X 1 →ₗ[ℚ] HQ Y 1) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (homPullback g 1)) fun g g' => by
      rw [spec_homPullback_mul_aux, ofAdd_add]
  have h := map_zpow φ f n
  rw [Int.cast_smul_eq_zsmul]
  exact congrArg Multiplicative.toAdd h

section HomAnalyticRepresentation

open Filter Topology

private theorem homPullback_exists_nsmul_eq_small {e : ℕ} (v : Fin e → ℂ) {t : ℝ} (ht : 0 < t) :
    ∃ (n : ℕ) (w : Fin e → ℂ), 0 < n ∧ ‖w‖ < t ∧ (n : ℝ) * ‖w‖ = ‖v‖ ∧ n • w = v := by
  obtain ⟨n, hn⟩ := exists_nat_gt (‖v‖ / t)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (norm_nonneg _) ht.le) hn
  refine ⟨n, (n : ℝ)⁻¹ • v, by exact_mod_cast hn0, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_eq_div, div_lt_iff₀ hn0]
    rwa [div_lt_iff₀ ht, mul_comm] at hn
  · rw [norm_smul, norm_inv, Real.norm_natCast, ← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul]
  · rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]

private theorem homPullback_eventually_mem_identityChart_source {W : Over (Spec ↧ℂ)} {d e : ℕ}
    [GrpObj W] [SmoothOfRelativeDimension d W.hom] {k : (Fin e → ℂ) → ComplexPoint W}
    (hk : ContinuousAt k 0) (hk0 : k 0 = 1) :
    ∀ᶠ v in 𝓝 0, k v ∈ (identityChart W d).source := by
  apply hk.tendsto.eventually
  rw [hk0]
  exact (identityChart W d).open_source.mem_nhds (mem_localChart_source W d 1)

/-- A continuous homomorphism `ℂ^e → W(ℂ)` whose expression in the identity chart of `W` has real
derivative `D` at `0` is `exp_W ∘ D`. -/
private theorem homPullback_eq_complexExponential_of_hasFDerivAt {W : Over (Spec ↧ℂ)} {d e : ℕ}
    [GrpObj W] [IsCommMonObj W] [SmoothOfRelativeDimension d W.hom]
    (g : (Fin e → ℂ) →+ Additive (ComplexPoint W)) (hg : ContinuousAt g 0)
    (D : (Fin e → ℂ) →L[ℝ] (Fin d → ℂ))
    (hD : HasFDerivAt (fun v ↦ identityChart W d (g v).toMul) D 0) (v : Fin e → ℂ) :
    g v = complexExponential W d (D v) := by
  set E : (Fin d → ℂ) → (Fin d → ℂ) :=
    fun v ↦ identityChart W d (complexExponential W d v).toMul with hEdef
  set F : (Fin e → ℂ) → (Fin d → ℂ) := fun v ↦ identityChart W d (g v).toMul with hFdef
  have hE0 : E 0 = 0 := by
    simp only [hEdef, complexExponential_zero, toMul_zero, identityChart_one]
  have hF0 : F 0 = 0 := by
    simp only [hFdef, map_zero, toMul_zero, identityChart_one]
  have hEd : HasFDerivAt E
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℂ)) : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ)) 0 :=
    hasFDerivAt_complexExponential_chart W d
  have hs : HasStrictFDerivAt E
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℂ)) : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ)) 0 :=
    (contDiffAt_complexExponential_chart W d).hasStrictFDerivAt' hEd one_ne_zero
  set L := hs.localInverse E _ 0 with hLdef
  have hL : HasStrictFDerivAt L
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℂ)).symm : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ)) (E 0) :=
    hs.to_localInverse
  have hLE : ∀ᶠ x in 𝓝 0, L (E x) = x := hs.eventually_left_inverse
  have hEL : ∀ᶠ y in 𝓝 (E 0), E (L y) = y := hs.eventually_right_inverse
  have hL0 : L 0 = 0 := by
    have := hLE.self_of_nhds
    rwa [hE0] at this
  set h : (Fin e → ℂ) → (Fin d → ℂ) := fun v ↦ L (F v) with hhdef
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
  have hgv : ∀ᶠ v in 𝓝 0, complexExponential W d (h v) = g v := by
    have hexp : ContinuousAt (fun v ↦ (complexExponential W d (h v)).toMul) 0 :=
      (continuous_toMul.comp (continuous_complexExponential W d)).continuousAt.comp
        hhd.continuousAt
    have h1 := homPullback_eventually_mem_identityChart_source (d := d) hexp
      (by simp only [hh0, complexExponential_zero, toMul_zero])
    have h2 := homPullback_eventually_mem_identityChart_source (d := d)
      (k := fun v ↦ (g v).toMul) (continuous_toMul.continuousAt.comp hg) (by simp)
    have h3 : ∀ᶠ v in 𝓝 0, E (L (F v)) = F v := by
      refine hD.continuousAt.tendsto.eventually (p := fun y ↦ E (L y) = y) ?_
      rw [hF0, ← hE0]
      exact hEL
    filter_upwards [h1, h2, h3] with v h1 h2 h3
    exact Additive.toMul.injective ((identityChart W d).injOn h1 h2 h3)
  -- local injectivity of `exp`
  obtain ⟨r, hr, hrN⟩ := Metric.eventually_nhds_iff_ball.mp hLE
  have hexpinj : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) r, ∀ y ∈ Metric.ball (0 : Fin d → ℂ) r,
      complexExponential W d x = complexExponential W d y → x = y := by
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
  have hadd : ∀ u : Fin e → ℂ, ‖u‖ < ε / 2 → ∀ w : Fin e → ℂ, ‖w‖ < ε / 2 →
      h (u + w) = h u + h w := by
    intro u hu w hw
    have huw : u + w ∈ Metric.ball (0 : Fin e → ℂ) ε := by
      rw [mem_ball_zero_iff]
      calc ‖u + w‖ ≤ ‖u‖ + ‖w‖ := norm_add_le _ _
        _ < ε / 2 + ε / 2 := add_lt_add hu hw
        _ = ε := add_halves ε
    have hu' : u ∈ Metric.ball (0 : Fin e → ℂ) ε := by
      rw [mem_ball_zero_iff]; linarith
    have hw' : w ∈ Metric.ball (0 : Fin e → ℂ) ε := by
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
    · have hm : complexExponential W d (h u + h w) =
          complexExponential W d (h u) + complexExponential W d (h w) :=
        (complexExponentialHom W d).map_add _ _
      rw [(hεP _ huw).1, hm, (hεP _ hu').1, (hεP _ hw').1, map_add]
  have hmul : ∀ u : Fin e → ℂ, ‖u‖ < ε / 2 → ∀ k : ℕ, (k : ℝ) * ‖u‖ < ε / 2 →
      h (k • u) = k • h u := by
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
  have hlin : ∀ u : Fin e → ℂ, ‖u‖ < ε / 2 → h u = D u := by
    intro u hu
    have key : ∀ c : ℝ, 0 < c → ‖h u - D u‖ ≤ c * ‖u‖ := by
      intro c hc
      obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff_ball.mp (hlo.def hc)
      obtain ⟨n, w, hn, hw, hnw, hwu⟩ := homPullback_exists_nsmul_eq_small u (lt_min hρ hδ)
      have hwρ : w ∈ Metric.ball (0 : Fin e → ℂ) ρ :=
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
  obtain ⟨n, w, hn, hw, hnw, hwv⟩ := homPullback_exists_nsmul_eq_small v hδ
  have hwε : w ∈ Metric.ball (0 : Fin e → ℂ) ε := by
    rw [mem_ball_zero_iff]; linarith
  have hexp : complexExponential W d (D w) = g w := by
    rw [← hlin w hw]
    exact (hεP _ hwε).1
  rw [← hwv, map_nsmul, map_nsmul, ← hexp]
  exact ((complexExponentialHom W d).map_nsmul _ _).symm

end HomAnalyticRepresentation

theorem spec_abelianHom_analyticRepresentation_aux (f : Y ⟶ X) [IsMonHom f] :
    ∃ A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ), ∀ v,
      Additive.toMul (complexExponential X (dim X.left) (A v)) =
        Point.map f (Additive.toMul (complexExponential Y (dim Y.left) v)) := by
  have : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  have : IsCommMonObj Y := isCommMonObj_of_complexSelfProductIntegral Y
    (complexSelfProductIntegral_of_isIntegral Y)
  set d := dim X.left
  set e := dim Y.left
  have hf1 : Point.map f (1 : ComplexPoint Y) = 1 := MonObj.one_comp f
  let g : (Fin e → ℂ) →+ Additive (ComplexPoint X) :=
    { toFun := fun v ↦ Additive.ofMul (Point.map f (complexExponential Y e v).toMul)
      map_zero' := by
        rw [complexExponential_zero, toMul_zero, hf1]
        rfl
      map_add' := fun v w ↦ by
        have hm : complexExponential Y e (v + w) =
            complexExponential Y e v + complexExponential Y e w :=
          (complexExponentialHom Y e).map_add _ _
        rw [hm, toMul_add]
        exact MonObj.mul_comp _ _ f }
  have hg : Continuous g :=
    continuous_ofMul.comp ((Point.continuous_map f).comp
      (continuous_toMul.comp (continuous_complexExponential Y e)))
  set G : (Fin e → ℂ) → (Fin d → ℂ) := fun w ↦ identityChart X d (g w).toMul with hGdef
  have hG : AnalyticAt ℂ G 0 := by
    set c := localChart Y e 1 1
    set c' := localChart X d 1 1
    have hc : c ∈ (localChart Y e 1).target :=
      (localChart Y e 1).map_source (mem_localChart_source Y e 1)
    have hH := analyticAt_localChart_symm_map Y X f e d 1 hc (by
      rw [(localChart Y e 1).left_inv (mem_localChart_source Y e 1)]
      exact mem_localChart_source X d _)
    rw [hf1] at hH
    have hE := spec_analyticAt_complexExponential_chart Y e
    have hE0 : identityChart Y e (complexExponential Y e 0).toMul + c = c := by
      rw [complexExponential_zero, toMul_zero, identityChart_one, zero_add]
    have hcomp := (hH.comp_of_eq (hE.add (analyticAt_const (v := c))) hE0).sub
      (analyticAt_const (v := c'))
    apply hcomp.congr
    have hmem := homPullback_eventually_mem_identityChart_source (d := e)
      (k := fun v ↦ (complexExponential Y e v).toMul)
      (continuous_toMul.comp (continuous_complexExponential Y e)).continuousAt
      (by rw [complexExponential_zero, toMul_zero])
    filter_upwards [hmem] with v hv
    simp only [hGdef]
    change localChart X d 1 (Point.map f ((localChart Y e 1).symm
      (localChart Y e 1 (complexExponential Y e v).toMul - c + c))) - c' =
        localChart X d 1 (Point.map f (complexExponential Y e v).toMul) - c'
    rw [sub_add_cancel, (localChart Y e 1).left_inv hv]
  have hD : HasFDerivAt G ((fderiv ℂ G 0).restrictScalars ℝ) 0 :=
    hG.differentiableAt.hasFDerivAt.restrictScalars ℝ
  refine ⟨(fderiv ℂ G 0).toLinearMap, fun v ↦ ?_⟩
  have := homPullback_eq_complexExponential_of_hasFDerivAt g hg.continuousAt _ hD v
  rw [ContinuousLinearMap.coe_restrictScalars'] at this
  exact (congrArg Additive.toMul this).symm

/-- A complex-linear `A` intertwining the exponentials with `f` maps periods of `Y` to periods
of `X`. -/
private theorem homPullback_analyticRepresentation_mem_lattice (f : Y ⟶ X)
    (A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f (Additive.toMul (complexExponential Y (dim Y.left) v)))
    (l : abelianPeriodLattice Y) : A l ∈ abelianPeriodLattice X := by
  have hl : complexExponential Y (dim Y.left) (l : Fin (dim Y.left) → ℂ) = 0 := l.2
  have h0 := hA 0
  rw [map_zero, complexExponential_zero, complexExponential_zero] at h0
  change complexExponential X (dim X.left) (A l) = 0
  apply Additive.toMul.injective
  rw [hA, hl, ← h0]

private theorem homPullback_analyticRepresentation_loop (f : Y ⟶ X)
    (A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f (Additive.toMul (complexExponential Y (dim Y.left) v)))
    (l : abelianPeriodLattice Y) :
    (Point.continuousMap f).comp (abelianLatticeLoop Y l) =
      abelianLatticeLoop X ⟨A l, homPullback_analyticRepresentation_mem_lattice f A hA l⟩ := by
  refine ContinuousMap.ext fun z => ?_
  induction z using QuotientAddGroup.induction_on with
  | H t =>
    change Point.map f (Additive.toMul (oneParameterSubgroup Y (dim Y.left)
        (l : Fin (dim Y.left) → ℂ) t)) =
      Additive.toMul (oneParameterSubgroup X (dim X.left) (A l) t)
    rw [← complexExponential_smul, ← complexExponential_smul, ← hA,
      LinearMap.map_smul_of_tower]

private theorem abelianPeriod_homPullback_analyticRepresentation (f : Y ⟶ X)
    (A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f (Additive.toMul (complexExponential Y (dim Y.left) v)))
    (x : HQ X 1) (l : abelianPeriodLattice Y) :
    abelianPeriod Y (homPullback f 1 x) l =
      abelianPeriod X x ⟨A l, homPullback_analyticRepresentation_mem_lattice f A hA l⟩ := by
  have hc : cupComparison Y 1 (homPullback f 1 x) =
      cohomologyMap ℚ 1 (TopCat.ofHom (Point.continuousMap f)) (cupComparison X 1 x) := by
    simp [homPullback]
  change loopPeriod (abelianLatticeLoop Y l) (cupComparison Y 1 (homPullback f 1 x)) =
    loopPeriod (abelianLatticeLoop X _) (cupComparison X 1 x)
  rw [hc, ← loopPeriod_comp, homPullback_analyticRepresentation_loop f A hA]

theorem spec_homPullback_period_aux (f : Y ⟶ X) [IsMonHom f] :
    ∃ φ : abelianPeriodLattice Y →+ abelianPeriodLattice X, ∀ x l,
      abelianPeriod Y (homPullback f 1 x) l = abelianPeriod X x (φ l) := by
  obtain ⟨A, hA⟩ := spec_abelianHom_analyticRepresentation_aux f
  let φ : abelianPeriodLattice Y →+ abelianPeriodLattice X :=
    { toFun := fun l ↦ ⟨A l, homPullback_analyticRepresentation_mem_lattice f A hA l⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun l m ↦ Subtype.ext (by simp) }
  exact ⟨φ, fun x l ↦ abelianPeriod_homPullback_analyticRepresentation f A hA x l⟩

private theorem homPullback_complexAbelianPeriod_tmul {W : Over (Spec ↧ℂ)} [GrpObj W]
    [IsIntegral W.left] [Smooth W.hom] [IsProjective W.hom]
    (c : ℂ) (x : HQ W 1) (l : abelianPeriodLattice W) :
    complexAbelianPeriod W (c ⊗ₜ x) l = c * (abelianPeriod W x l : ℂ) := by
  simp [complexAbelianPeriod]

private theorem complexAbelianPeriod_homPullback_analyticRepresentation (f : Y ⟶ X)
    (A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f (Additive.toMul (complexExponential Y (dim Y.left) v)))
    (ω : ℂ ⊗[ℚ] HQ X 1) (l : abelianPeriodLattice Y) :
    complexAbelianPeriod Y ((homPullback f 1).baseChange ℂ ω) l =
      complexAbelianPeriod X ω ⟨A l, homPullback_analyticRepresentation_mem_lattice f A hA l⟩ := by
  induction ω using TensorProduct.inductionOn with
  | tmul c x =>
    rw [LinearMap.baseChange_tmul, homPullback_complexAbelianPeriod_tmul,
      homPullback_complexAbelianPeriod_tmul, abelianPeriod_homPullback_analyticRepresentation f A hA]
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

theorem spec_homPullback_hodge_of_analyticRepresentation_aux (f : Y ⟶ X)
    (A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f (Additive.toMul (complexExponential Y (dim Y.left) v))) :
    (complexHolomorphicH1 X).map ((homPullback f 1).baseChange ℂ) ≤ complexHolomorphicH1 Y ∧
      (complexAntiholomorphicH1 X).map ((homPullback f 1).baseChange ℂ) ≤
        complexAntiholomorphicH1 Y := by
  have key : ∀ (ω : ℂ ⊗[ℚ] HQ X 1) (F : DegreeOneLatticeDual (dim X.left)),
      latticeRestriction X F = complexAbelianPeriod X ω →
        latticeRestriction Y (F ∘ₗ A.restrictScalars ℝ) =
          complexAbelianPeriod Y ((homPullback f 1).baseChange ℂ ω) := by
    intro ω F hF
    funext l
    rw [complexAbelianPeriod_homPullback_analyticRepresentation f A hA, ← hF]
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

theorem spec_homPullback_hodge_aux (f : Y ⟶ X) [IsMonHom f] :
    (complexHolomorphicH1 X).map ((homPullback f 1).baseChange ℂ) ≤ complexHolomorphicH1 Y ∧
      (complexAntiholomorphicH1 X).map ((homPullback f 1).baseChange ℂ) ≤
        complexAntiholomorphicH1 Y := by
  obtain ⟨A, hA⟩ := spec_abelianHom_analyticRepresentation_aux f
  exact spec_homPullback_hodge_of_analyticRepresentation_aux f A hA

theorem spec_homPullback_hodgeFiltration_aux (f : Y ⟶ X) [IsMonHom f] :
    ((F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1)).map
        ((homPullback f 1).baseChange ℂ) ≤
      (F^1 H_dR^((1 : ℕ) : ℤ)(Y)).comap (bettiDeRhamHQ Y 1) := by
  rw [spec_comap_hodgeFiltration_one_eq X, spec_comap_hodgeFiltration_one_eq Y]
  exact (spec_homPullback_hodge_aux f).1

end Abelian

end HodgeLean.Adapters
