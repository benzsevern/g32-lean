import HodgeLean.Foundations.Curves.CurveDivisorsDefs
import HodgeLean.Foundations.Curves.ChartStalks

/-! # The divisor of `x` on the fixed cubic

Local computation of `Scheme.ord cubicX` at every point of `y²z = x³ + xz²`. At `(0,0)` the stalk is
a DVR with uniformizer `y` and `x = y²/(x²+1)`; at infinity it is a DVR with uniformizer
`u = x/y` and `x = u/v` with `v = u³/(1-uv)`; elsewhere `x` is a unit.
HC no distance; AV milestone no distance.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Polynomial
noncomputable section
namespace HodgeLean.Foundations.Curves.CubicDivisor

open ChartStalks

theorem ker_le_span (f : ℂ[X][X]) (φ : AdjoinRoot f →+* ℂ)
    (hc : ∀ c, φ (AdjoinRoot.of f (C c)) = c) (hX : φ (AdjoinRoot.of f X) = 0)
    (hR : φ (AdjoinRoot.root f) = 0) :
    RingHom.ker φ ≤ Ideal.span {AdjoinRoot.of f X, AdjoinRoot.root f} := by
  intro a ha
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  have hq : q = C (C ((q.coeff 0).coeff 0) + X * (q.coeff 0).divX) + X * q.divX := by
    conv_lhs => rw [← X_mul_divX_add q, ← X_mul_divX_add (q.coeff 0)]
    simp only [map_add, map_mul]; ring
  have hmk : AdjoinRoot.mk f q = AdjoinRoot.of f (C ((q.coeff 0).coeff 0)) +
      AdjoinRoot.of f X * AdjoinRoot.of f (q.coeff 0).divX +
      AdjoinRoot.root f * AdjoinRoot.mk f q.divX := by
    conv_lhs => rw [hq]
    simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  rw [RingHom.mem_ker, hmk] at ha
  simp only [map_add, map_mul, hc, hX, hR, zero_mul, add_zero] at ha
  rw [hmk, ha]
  simp only [map_zero, zero_add]
  apply Ideal.add_mem
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem finitePointCoordinates_algebraMap (c : ℂ) :
    finitePointCoordinates (algebraMap ℂ W.toAffine.CoordinateRing c) = c := by
  have h := finitePoint_over
  rw [← finitePoint_chart, Category.assoc, zChartMap_over, ← Spec.map_comp] at h
  have h' := Spec.map_injective (h.trans (Spec.map_id _).symm)
  exact congrArg (fun ψ : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ ↦ ψ c) h'

theorem infinityCoordinates_algebraMap (c : ℂ) :
    infinityCoordinates (algebraMap ℂ YCoordinateRing c) = c := by
  have h := infinity_over
  rw [← infinity_chart, Category.assoc, yChartMap_over, ← Spec.map_comp] at h
  have h' := Spec.map_injective (h.trans (Spec.map_id _).symm)
  exact congrArg (fun ψ : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ ↦ ψ c) h'

theorem z_relation :
    (AdjoinRoot.root W.toAffine.polynomial)^2 =
      (AdjoinRoot.of W.toAffine.polynomial X)^3 + AdjoinRoot.of W.toAffine.polynomial X := by
  have hp : W.toAffine.polynomial = X ^ 2 - (C X ^ 3 + C X) := by
    simp [WeierstrassCurve.Affine.polynomial, W, WeierstrassCurve.ofJ1728]
  have h : AdjoinRoot.mk W.toAffine.polynomial (X ^ 2 - (C X ^ 3 + C X)) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr (dvd_of_eq hp)
  simp only [map_sub, map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  linear_combination h

private abbrev A := W.toAffine.CoordinateRing
private abbrev B := YCoordinateRing
private abbrev ax : A := AdjoinRoot.of W.toAffine.polynomial X
private abbrev ay : A := AdjoinRoot.root W.toAffine.polynomial
private abbrev bu : B := AdjoinRoot.of yAffinePolynomial X
private abbrev bv : B := AdjoinRoot.root yAffinePolynomial

/-- A complex point of the Weierstrass chart with `x = 1`. -/
private def zEval (s : ℂ) (hs : s ^ 2 = 2) : A →+* ℂ :=
  AdjoinRoot.lift (Polynomial.evalRingHom 1) s (by
    rw [Polynomial.eval₂_evalRingHom, WeierstrassCurve.Affine.evalEval_polynomial]
    norm_num [W, WeierstrassCurve.ofJ1728, hs])

private theorem exists_sqrt_two : ∃ s : ℂ, s ^ 2 = 2 :=
  IsAlgClosed.exists_pow_nat_eq (2 : ℂ) (by decide : 0 < 2)

private theorem ax_ne_zero : ax ≠ 0 := by
  obtain ⟨s, hs⟩ := exists_sqrt_two
  intro h
  have := congrArg (zEval s hs) h
  simp [zEval] at this

private theorem ay_ne_zero : ay ≠ 0 := by
  obtain ⟨s, hs⟩ := exists_sqrt_two
  intro h
  have := congrArg (zEval s hs) h
  simp only [zEval, AdjoinRoot.lift_root, map_zero] at this
  rw [this] at hs
  norm_num at hs

private theorem bu_ne_zero : bu ≠ 0 := by
  obtain ⟨s, hs⟩ := exists_sqrt_two
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  let φ : B →+* ℂ := AdjoinRoot.lift (Polynomial.evalRingHom s⁻¹) s⁻¹ (by
    rw [Polynomial.eval₂_evalRingHom]
    simp [yAffinePolynomial, evalEval]
    field_simp
    linear_combination hs)
  intro h
  have := congrArg φ h
  simp [φ, hs0] at this

private theorem finitePointCoordinates_C (c : ℂ) :
    finitePointCoordinates (AdjoinRoot.of W.toAffine.polynomial (C c)) = c := by
  have h := finitePoint_over
  rw [← finitePoint_chart, Category.assoc, zChartMap_over, ← Spec.map_comp] at h
  have h' := Spec.map_injective (h.trans (Spec.map_id _).symm)
  exact congrArg (fun ψ : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ ↦ ψ c) h'

private theorem infinityCoordinates_C (c : ℂ) :
    infinityCoordinates (AdjoinRoot.of yAffinePolynomial (C c)) = c := by
  have h := infinity_over
  rw [← infinity_chart, Category.assoc, yChartMap_over, ← Spec.map_comp] at h
  have h' := Spec.map_injective (h.trans (Spec.map_id _).symm)
  exact congrArg (fun ψ : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ ↦ ψ c) h'

private theorem ker_z_le : RingHom.ker finitePointCoordinates ≤ Ideal.span {ax, ay} :=
  ker_le_span _ _ finitePointCoordinates_C finitePointCoordinates_values.1
    finitePointCoordinates_values.2

private theorem ker_y_le : RingHom.ker infinityCoordinates ≤ Ideal.span {bu, bv} :=
  ker_le_span _ _ infinityCoordinates_C infinityCoordinates_values.1
    infinityCoordinates_values.2

private theorem ker_z_isMaximal : (RingHom.ker finitePointCoordinates).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨_, finitePointCoordinates_C c⟩

private theorem ker_y_isMaximal : (RingHom.ker infinityCoordinates).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨_, infinityCoordinates_C c⟩

private theorem specMap_point_asIdeal {R : CommRingCat} (φ : R ⟶ CommRingCat.of ℂ)
    (p : Spec ↧ℂ) : ((Spec.map φ).base p).asIdeal = RingHom.ker φ.hom := by
  have := p.isPrime
  have h : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  change Ideal.comap φ.hom p.asIdeal = _
  rw [h, RingHom.ker_eq_comap_bot]

/-- The prime of `(0,0)` in the Weierstrass chart. -/
private def t₀ : Spec (CommRingCat.of A) :=
  (Spec.map (CommRingCat.ofHom finitePointCoordinates)).base default

/-- The prime of infinity in the `y` chart. -/
private def tInf : Spec (CommRingCat.of B) :=
  (Spec.map (CommRingCat.ofHom infinityCoordinates)).base default

private theorem t₀_asIdeal : t₀.asIdeal = RingHom.ker finitePointCoordinates :=
  specMap_point_asIdeal _ _

private theorem tInf_asIdeal : tInf.asIdeal = RingHom.ker infinityCoordinates :=
  specMap_point_asIdeal _ _

private theorem zChartMap_t₀ : zChartMap t₀ = finitePoint.base default := by
  rw [← finitePoint_chart]
  rfl

private theorem yChartMap_tInf : yChartMap tInf = infinity.base default := by
  rw [← infinity_chart]
  rfl

private theorem eq_t₀ (t : Spec (CommRingCat.of A)) (h : ax ∈ t.asIdeal) : t = t₀ := by
  have hy : ay ∈ t.asIdeal := by
    apply t.isPrime.mem_of_pow_mem 2
    rw [z_relation]
    exact t.asIdeal.add_mem (t.asIdeal.pow_mem_of_mem h 3 (by norm_num)) h
  have hle : RingHom.ker finitePointCoordinates ≤ t.asIdeal := by
    refine ker_z_le.trans ?_
    rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact h
    · exact hy
  apply PrimeSpectrum.ext
  rw [t₀_asIdeal]
  exact (ker_z_isMaximal.eq_of_le t.isPrime.ne_top hle).symm

private theorem eq_tInf (q : Spec (CommRingCat.of B)) (h : bv ∈ q.asIdeal) : q = tInf := by
  have hu : bu ∈ q.asIdeal := by
    apply q.isPrime.mem_of_pow_mem 3
    have he := yChart_equation
    have : bu ^ 3 = bv - bu * bv ^ 2 := by linear_combination -he
    rw [this]
    exact q.asIdeal.sub_mem h (q.asIdeal.mul_mem_left _ (q.asIdeal.pow_mem_of_mem h 2 (by norm_num)))
  have hle : RingHom.ker infinityCoordinates ≤ q.asIdeal := by
    refine ker_y_le.trans ?_
    rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact hu
    · exact h
  apply PrimeSpectrum.ext
  rw [tInf_asIdeal]
  exact (ker_y_isMaximal.eq_of_le q.isPrime.ne_top hle).symm

private def zSec : A →+* Γ(E.left, zChart) := chartSection zChart zChartIso

private def ySec : B →+* Γ(E.left, yChart) := chartSection yChart yChartIso

private instance : IsOpenImmersion zChartMap := by unfold zChartMap; infer_instance

private instance : IsOpenImmersion yChartMap := by unfold yChartMap; infer_instance

private theorem zChartMap_mem (p : Spec (CommRingCat.of A)) : zChartMap p ∈ zChart := by
  change zChart.ι (zChartIso.inv p) ∈ zChart
  exact (zChartIso.inv p).property

private theorem yChartMap_mem (q : Spec (CommRingCat.of B)) : yChartMap q ∈ yChart := by
  change yChart.ι (yChartIso.inv q) ∈ yChart
  exact (yChartIso.inv q).property

private instance : Nonempty zChart := ⟨⟨_, zChartMap_mem t₀⟩⟩

private instance : Nonempty yChart := ⟨⟨_, yChartMap_mem tInf⟩⟩

private theorem cubicX_eq : cubicX = E.left.germToFunctionField zChart (zSec ax) := rfl

private theorem zSec_app (r : A) : zChartMap.app zChart (zSec r) =
    (Spec (CommRingCat.of A)).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso _).inv r) :=
  chartSection_app zChart zChartIso r

private theorem ySec_app (r : B) : yChartMap.app yChart (ySec r) =
    (Spec (CommRingCat.of B)).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso _).inv r) :=
  chartSection_app yChart yChartIso r

/-- The rational functions `u = x/y` and `v = 1/y` of the infinity chart. -/
private def funU : E.left.functionField := E.left.germToFunctionField yChart (ySec bu)

private def funV : E.left.functionField := E.left.germToFunctionField yChart (ySec bv)

private theorem overlap_relation : funU = cubicX * funV := by
  let L := CommRingCat.of (Localization.Away ay)
  let h : Spec L ⟶ E.left := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away ay))) ≫
    zChartMap
  have hh : Spec.map (CommRingCat.ofHom zToYCoordinates) ≫ yChartMap = h :=
    transition_agreement_z
  have : IsOpenImmersion h := by dsimp only [h]; infer_instance
  have : IsDomain (Localization.Away ay) := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors ay_ne_zero)
  obtain ⟨t⟩ : Nonempty (PrimeSpectrum (Localization.Away ay)) := inferInstance
  let t' : Spec L := t
  have htz : h t' ∈ zChart := zChartMap_mem _
  have hty : h t' ∈ yChart := by
    rw [← hh]
    exact yChartMap_mem _
  have HX := app_comp_specMap zChartMap (CommRingCat.ofHom (algebraMap A (Localization.Away ay)))
    (zSec ax) ax (zSec_app ax)
  have HU := app_comp_specMap yChartMap (CommRingCat.ofHom zToYCoordinates) (ySec bu) bu
    (ySec_app bu)
  have HV := app_comp_specMap yChartMap (CommRingCat.ofHom zToYCoordinates) (ySec bv) bv
    (ySec_app bv)
  rw [hh] at HU HV
  let ψ : Localization.Away ay →+* E.left.functionField :=
    (algebraMap (E.left.presheaf.stalk (h t')) E.left.functionField).comp
      (@algebraMap L _ _ _ (chartStalkAlgebra h t'))
  have eX : cubicX = ψ (algebraMap A _ ax) := germToFunctionField_eq h _ _ HX t' htz
  have eU : funU = ψ (zToYCoordinates bu) := germToFunctionField_eq h _ _ HU t' hty
  have eV : funV = ψ (zToYCoordinates bv) := germToFunctionField_eq h _ _ HV t' hty
  rw [eX, eU, eV, zToYCoordinates_u, zToYCoordinates_v, map_mul]

private theorem ord_finitePoint_aux :
    cubicX ≠ 0 ∧ E.left.ord cubicX (finitePoint.base default) = 2 := by
  let S := E.left.presheaf.stalk (zChartMap t₀)
  let := chartStalkAlgebra zChartMap t₀
  have := t₀.isPrime
  have := chartStalk_isLocalization zChartMap t₀
  have eX : cubicX = algebraMap S E.left.functionField (algebraMap A S ax) :=
    cubicX_eq.trans
      (germToFunctionField_eq zChartMap (zSec ax) ax (zSec_app ax) t₀ (zChartMap_mem t₀))
  have hw : IsUnit (algebraMap A S (ax ^ 2 + 1)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff S t₀.asIdeal, Ideal.mem_primeCompl_iff,
      t₀_asIdeal, RingHom.mem_ker]
    simp [finitePointCoordinates_values.1]
  have hrel : algebraMap A S ax = algebraMap A S ay ^ 2 * ↑hw.unit⁻¹ := by
    have h2 : algebraMap A S ax * algebraMap A S (ax ^ 2 + 1) = algebraMap A S ay ^ 2 := by
      rw [← map_mul, ← map_pow (algebraMap A S) ay 2]
      congr 1
      rw [z_relation]
      ring
    rw [Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec]
    exact h2
  have hinj : Function.Injective (algebraMap A S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors t₀.asIdeal)
  have hπ0 : algebraMap A S ay ≠ 0 := fun h ↦ ay_ne_zero (hinj (h.trans (map_zero _).symm))
  obtain ⟨hdvr, hirr⟩ := dvr_of_span t₀.asIdeal S ay ax
    (by rw [t₀_asIdeal]; exact ker_z_le)
    (by rw [t₀_asIdeal, RingHom.mem_ker]; exact finitePointCoordinates_values.2)
    (Ideal.mem_span_singleton'.mpr ⟨algebraMap A S ay * ↑hw.unit⁻¹, by rw [hrel]; ring⟩) hπ0
  have hX0 : cubicX ≠ 0 := by
    rw [eX, hrel]
    refine (map_ne_zero_iff _ (IsFractionRing.injective S _)).mpr ?_
    exact mul_ne_zero (pow_ne_zero _ hπ0) (Units.ne_zero _)
  refine ⟨hX0, ?_⟩
  rw [← zChartMap_t₀]
  apply ord_eq_of_dvr _ hX0
  rw [eX, hrel, map_mul, map_mul, map_pow, map_pow, Ring.ordFrac_irreducible hirr,
    Ring.ordFrac_of_isUnit (Units.isUnit _), mul_one, ← WithZero.exp_nsmul]
  rfl

theorem cubicX_ne_zero : cubicX ≠ 0 := ord_finitePoint_aux.1

theorem ord_cubicX_finitePoint : E.left.ord cubicX (finitePoint.base default) = 2 :=
  ord_finitePoint_aux.2

theorem ord_cubicX_infinity : E.left.ord cubicX (infinity.base default) = -2 := by
  let S := E.left.presheaf.stalk (yChartMap tInf)
  let := chartStalkAlgebra yChartMap tInf
  have := tInf.isPrime
  have := chartStalk_isLocalization yChartMap tInf
  have eU : funU = algebraMap S E.left.functionField (algebraMap B S bu) :=
    germToFunctionField_eq yChartMap (ySec bu) bu (ySec_app bu) tInf (yChartMap_mem tInf)
  have eV : funV = algebraMap S E.left.functionField (algebraMap B S bv) :=
    germToFunctionField_eq yChartMap (ySec bv) bv (ySec_app bv) tInf (yChartMap_mem tInf)
  have hw : IsUnit (algebraMap B S (1 - bu * bv)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff S tInf.asIdeal, Ideal.mem_primeCompl_iff,
      tInf_asIdeal, RingHom.mem_ker]
    simp [infinityCoordinates_values.1]
  have hrel : algebraMap B S bv = algebraMap B S bu ^ 3 * ↑hw.unit⁻¹ := by
    have h2 : algebraMap B S bv * algebraMap B S (1 - bu * bv) = algebraMap B S bu ^ 3 := by
      rw [← map_mul, ← map_pow (algebraMap B S) bu 3]
      congr 1
      have he := yChart_equation
      linear_combination he
    rw [Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec]
    exact h2
  have := yCoordinateRing_isDomain
  have hinj : Function.Injective (algebraMap B S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors tInf.asIdeal)
  have hπ0 : algebraMap B S bu ≠ 0 := fun h ↦ bu_ne_zero (hinj (h.trans (map_zero _).symm))
  obtain ⟨hdvr, hirr⟩ := dvr_of_span tInf.asIdeal S bu bv
    (by rw [tInf_asIdeal, Set.pair_comm]; exact ker_y_le)
    (by rw [tInf_asIdeal, RingHom.mem_ker]; exact infinityCoordinates_values.1)
    (Ideal.mem_span_singleton'.mpr ⟨algebraMap B S bu ^ 2 * ↑hw.unit⁻¹, by rw [hrel]; ring⟩) hπ0
  have hV0 : funV ≠ 0 := by
    rw [eV, hrel]
    refine (map_ne_zero_iff _ (IsFractionRing.injective S _)).mpr ?_
    exact mul_ne_zero (pow_ne_zero _ hπ0) (Units.ne_zero _)
  have hX : cubicX = funU / funV := by
    rw [overlap_relation, mul_div_cancel_right₀ _ hV0]
  rw [← yChartMap_tInf]
  apply ord_eq_of_dvr _ cubicX_ne_zero
  rw [hX, map_div₀, eU, eV, hrel, map_mul, map_mul, map_pow, map_pow,
    Ring.ordFrac_irreducible hirr, Ring.ordFrac_of_isUnit (Units.isUnit _), mul_one,
    ← WithZero.exp_nsmul, ← WithZero.exp_sub]
  rfl

private theorem infinity_not_mem_zChart : infinity.base default ∉ zChart := by
  intro h
  have h' : (default : Spec ↧ℂ) ∈ infinity ⁻¹ᵁ zChart := h
  rw [infinity_zChart] at h'
  exact h'

private theorem finitePoint_mem_zChart : finitePoint.base default ∈ zChart := by
  rw [← zChartMap_t₀]
  exact zChartMap_mem t₀

/-- The two marked points of the cubic are distinct scheme points.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1. -/
theorem finitePoint_ne_infinity : finitePoint.base default ≠ infinity.base default :=
  fun h ↦ infinity_not_mem_zChart (h ▸ finitePoint_mem_zChart)

private theorem ord_cubicX_of_unit (t : Spec (CommRingCat.of A)) (hx : ax ∉ t.asIdeal) :
    E.left.ord cubicX (zChartMap t) = 0 := by
  by_cases hP : Order.coheight (zChartMap t) = 1
  · let S := E.left.presheaf.stalk (zChartMap t)
    let := chartStalkAlgebra zChartMap t
    have := t.isPrime
    have := chartStalk_isLocalization zChartMap t
    have : Ring.KrullDimLE 1 S := krullDimLE_of_coheight_le hP.le
    have eX : cubicX = algebraMap S E.left.functionField (algebraMap A S ax) :=
      cubicX_eq.trans
        (germToFunctionField_eq zChartMap (zSec ax) ax (zSec_app ax) t (zChartMap_mem t))
    have hu : IsUnit (algebraMap A S ax) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff S t.asIdeal ax).mpr hx
    rw [Scheme.ord_eq_iff hP cubicX_ne_zero]
    change Ring.ordFrac S cubicX = _
    rw [eX, Ring.ordFrac_of_isUnit hu]
    rfl
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hP _

private theorem iso_inv_hom_apply {X Y : Scheme} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

open Classical in
/-- The order of `x` at every point of the cubic.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1 and II.1. -/
theorem ord_cubicX (P : E.left) : E.left.ord cubicX P =
    if P = finitePoint.base default then 2 else if P = infinity.base default then -2 else 0 := by
  by_cases hz : P ∈ zChart
  · let x : zChart.toScheme := ⟨P, hz⟩
    let t : Spec (CommRingCat.of A) := zChartIso.hom x
    have ht : zChartMap t = P := by
      change zChart.ι (zChartIso.inv (zChartIso.hom x)) = P
      rw [iso_inv_hom_apply]
      rfl
    have hinf : P ≠ infinity.base default := fun h ↦ infinity_not_mem_zChart (h ▸ hz)
    by_cases hx : ax ∈ t.asIdeal
    · have hP : P = finitePoint.base default := by
        rw [← ht, eq_t₀ t hx, zChartMap_t₀]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hP), hP, ord_cubicX_finitePoint]
    · have hP : P ≠ finitePoint.base default := by
        intro h
        apply hx
        have h' : zChartMap t = zChartMap t₀ := by rw [ht, h, zChartMap_t₀]
        rw [zChartMap.isOpenEmbedding.injective h', t₀_asIdeal, RingHom.mem_ker]
        exact finitePointCoordinates_values.1
      rw [ite_eq_right_of_eq_false _ _ (eq_false hP), ite_eq_right_of_eq_false _ _ (eq_false hinf), ← ht]
      exact ord_cubicX_of_unit t hx
  · have hy : P ∈ yChart := by
      have h : P ∈ zChart ⊔ yChart := by rw [charts_cover]; trivial
      rcases h with h | h
      · exact absurd h hz
      · exact h
    let x : yChart.toScheme := ⟨P, hy⟩
    let q : Spec (CommRingCat.of B) := yChartIso.hom x
    have hq : yChartMap q = P := by
      change yChart.ι (yChartIso.inv (yChartIso.hom x)) = P
      rw [iso_inv_hom_apply]
      rfl
    have hv : bv ∈ q.asIdeal := by
      by_contra hv
      apply hz
      have : q ∈ yChartMap ⁻¹ᵁ zChart := by
        rw [yChartMap_preimage_z]
        exact hv
      rw [← hq]
      exact this
    have hP : P = infinity.base default := by
      rw [← hq, eq_tInf q hv, yChartMap_tInf]
    have hP0 : P ≠ finitePoint.base default := fun h ↦ hz (h ▸ finitePoint_mem_zChart)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hP0), ite_eq_left_of_eq_true _ _ (eq_true hP), hP,
      ord_cubicX_infinity]

end HodgeLean.Foundations.Curves.CubicDivisor
