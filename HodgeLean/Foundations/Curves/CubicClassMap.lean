import HodgeLean.Foundations.Curves.CurveDivisorClassesLemmas
import HodgeLean.Foundations.Curves.DedekindValuation
import HodgeLean.Foundations.Curves.CurveDivisors
import HodgeLean.Foundations.Curves.CurveProductFormula

/-! # From divisors on the cubic to the class group of its affine coordinate ring

Restricting a divisor on `E` to the affine chart `zChart ≅ Spec A` and taking the product of the
corresponding prime ideals gives a fractional ideal of the Dedekind domain `A`. The order of a
rational function at a point of the chart is the exponent of its prime in the principal ideal, so
principal divisors go to principal ideals, and a divisor of degree zero with trivial ideal is zero.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors

namespace HodgeLean.Foundations.Curves.CubicClassMap

open ChartStalks

local notation "𝒜" => W.toAffine.CoordinateRing
local notation "KE" => E.left.functionField

instance : IsOpenImmersion zChartMap := by unfold zChartMap; infer_instance

theorem zChartMap_mem (p : Spec (CommRingCat.of 𝒜)) : zChartMap p ∈ zChart := by
  change zChart.ι (zChartIso.inv p) ∈ zChart
  exact (zChartIso.inv p).property

instance : Nonempty zChart := ⟨⟨_, zChartMap_mem ⟨⊥, Ideal.isPrime_bot⟩⟩⟩

/-- Sections over the chart coming from the coordinate ring. -/
def zSec : 𝒜 →+* Γ(E.left, zChart) := chartSection zChart zChartIso

theorem zSec_app (r : 𝒜) : zChartMap.app zChart (zSec r) =
    (Spec (CommRingCat.of 𝒜)).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso _).inv r) :=
  chartSection_app zChart zChartIso r

/-- The coordinate ring maps to the function field of `E`. -/
instance algebraFunctionField : Algebra 𝒜 KE :=
  ((E.left.germToFunctionField zChart).hom.comp zSec).toAlgebra

/-- Through any chart stalk, the map `𝒜 → K(E)` factors as `𝒜 → 𝒪_{E,t} → K(E)`. -/
theorem algebraMap_eq_stalk (t : Spec (CommRingCat.of 𝒜)) (r : 𝒜) :
    algebraMap 𝒜 KE r = algebraMap (E.left.presheaf.stalk (zChartMap t)) KE
      (@algebraMap 𝒜 _ _ _ (chartStalkAlgebra zChartMap t) r) :=
  germToFunctionField_eq zChartMap (zSec r) r (zSec_app r) t (zChartMap_mem t)

theorem isScalarTower_stalk (t : Spec (CommRingCat.of 𝒜)) :
    @IsScalarTower 𝒜 (E.left.presheaf.stalk (zChartMap t)) KE
      (@Algebra.toSMul _ _ _ _ (chartStalkAlgebra zChartMap t)) _ _ := by
  let := chartStalkAlgebra zChartMap t
  exact IsScalarTower.of_algebraMap_eq (algebraMap_eq_stalk t)

/-- The function field of `E` is the fraction field of the coordinate ring.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 3.6. -/
instance isFractionRing : IsFractionRing 𝒜 KE := by
  let t : Spec (CommRingCat.of 𝒜) := ⟨⊥, Ideal.isPrime_bot⟩
  let S := E.left.presheaf.stalk (zChartMap t)
  let := chartStalkAlgebra zChartMap t
  have := chartStalk_isLocalization zChartMap t
  have := isScalarTower_stalk t
  have hinjS : Function.Injective (algebraMap 𝒜 S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors t.asIdeal)
  have hinj : Function.Injective (algebraMap 𝒜 KE) := by
    rw [IsScalarTower.algebraMap_eq 𝒜 S KE]
    exact (IsFractionRing.injective S KE).comp hinjS
  have : FaithfulSMul 𝒜 KE := (faithfulSMul_iff_algebraMap_injective 𝒜 KE).mpr hinj
  have hmk : ∀ (a : 𝒜) (b : t.asIdeal.primeCompl),
      algebraMap S KE (IsLocalization.mk' S a b) = algebraMap 𝒜 KE a / algebraMap 𝒜 KE b := by
    intro a b
    have hb : algebraMap 𝒜 KE b ≠ 0 := fun h ↦
      nonZeroDivisors.ne_zero (Ideal.primeCompl_le_nonZeroDivisors t.asIdeal b.2)
        (hinj (h.trans (map_zero _).symm))
    rw [eq_div_iff hb, IsScalarTower.algebraMap_apply 𝒜 S KE, IsScalarTower.algebraMap_apply 𝒜 S KE,
      ← map_mul, IsLocalization.mk'_spec]
  refine IsFractionRing.of_field 𝒜 KE fun z ↦ ?_
  obtain ⟨s₁, s₂, hs₂, rfl⟩ := IsFractionRing.div_surjective (A := S) z
  obtain ⟨⟨a₁, b₁⟩, rfl⟩ := IsLocalization.mk'_surjective t.asIdeal.primeCompl s₁
  obtain ⟨⟨a₂, b₂⟩, rfl⟩ := IsLocalization.mk'_surjective t.asIdeal.primeCompl s₂
  refine ⟨a₁ * b₂, b₁ * a₂, ?_⟩
  rw [hmk, hmk, map_mul, map_mul, div_div_div_eq]

/-- The point of `E` given by a height-one prime of the coordinate ring. -/
def pt (v : HeightOneSpectrum 𝒜) : E.left :=
  zChartMap (⟨v.asIdeal, v.isPrime⟩ : Spec (CommRingCat.of 𝒜))

theorem pt_mem_zChart (v : HeightOneSpectrum 𝒜) : pt v ∈ zChart := zChartMap_mem _

theorem pt_injective : Function.Injective pt := by
  intro v w h
  have h' := zChartMap.isOpenEmbedding.injective h
  ext1
  exact congrArg PrimeSpectrum.asIdeal h'

/-- The stalk of `E` at a nonzero prime of the chart is a DVR. -/
theorem stalk_dvr (t : Spec (CommRingCat.of 𝒜)) (ht : t.asIdeal ≠ ⊥) :
    IsDiscreteValuationRing (E.left.presheaf.stalk (zChartMap t)) := by
  let := chartStalkAlgebra zChartMap t
  have := t.isPrime
  have := chartStalk_isLocalization zChartMap t
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain 𝒜 ht _

instance (v : HeightOneSpectrum 𝒜) : IsDiscreteValuationRing (E.left.presheaf.stalk (pt v)) :=
  stalk_dvr _ v.ne_bot

theorem coheight_pt (v : HeightOneSpectrum 𝒜) : Order.coheight (pt v) = 1 := by
  have h1 := ringKrullDim_stalk_eq_coheight (pt v)
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h1
  exact_mod_cast h1.symm

/-- The order of a rational function at the point of `v` is the exponent of `v` in `(f)`.
Source: Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.2. -/
theorem ord_pt (v : HeightOneSpectrum 𝒜) (f : KE) (hf : f ≠ 0) :
    E.left.ord f (pt v) = count KE v (spanSingleton 𝒜⁰ f) := by
  let t : Spec (CommRingCat.of 𝒜) := ⟨v.asIdeal, v.isPrime⟩
  change E.left.ord f (zChartMap t) = _
  have := stalk_dvr t v.ne_bot
  let := chartStalkAlgebra zChartMap t
  have := chartStalk_isLocalization zChartMap t
  have := isScalarTower_stalk t
  exact ord_eq_of_dvr _ hf _ (DedekindValuation.ordFrac_eq_exp_count v f hf)

theorem iso_inv_hom_apply {X Y : Scheme} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-- Every coheight-one point of the chart comes from a height-one prime. -/
theorem exists_pt {z : E.left} (hz : z ∈ zChart) (hc : Order.coheight z = 1) :
    ∃ v, pt v = z := by
  let x : zChart.toScheme := ⟨z, hz⟩
  let t : Spec (CommRingCat.of 𝒜) := zChartIso.hom x
  have ht : zChartMap t = z := by
    change zChart.ι (zChartIso.inv (zChartIso.hom x)) = z
    rw [iso_inv_hom_apply]
    rfl
  have hne : t.asIdeal ≠ ⊥ := by
    intro h0
    have h1 := idealHeight_eq_coheight (CommRingCat.of 𝒜) t
    rw [← coheight_eq_of_isOpenImmersion zChartMap, ht, hc, h0, Ideal.height_bot] at h1
    exact zero_ne_one h1
  exact ⟨⟨t.asIdeal, t.isPrime, hne⟩, ht⟩

section Infinity

open Polynomial

theorem infinityCoordinates_C (c : ℂ) :
    infinityCoordinates (AdjoinRoot.of yAffinePolynomial (C c)) = c := by
  have h := infinity_over
  rw [← infinity_chart, Category.assoc, yChartMap_over, ← Spec.map_comp] at h
  have h' := Spec.map_injective (h.trans (Spec.map_id _).symm)
  exact congrArg (fun ψ : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ ↦ ψ c) h'

/-- The prime of infinity in the `y` chart. -/
def tInf : Spec (CommRingCat.of YCoordinateRing) :=
  (Spec.map (CommRingCat.ofHom infinityCoordinates)).base default

theorem tInf_asIdeal : tInf.asIdeal = RingHom.ker infinityCoordinates := by
  have := (default : Spec ↧ℂ).isPrime
  have h : (default : Spec ↧ℂ).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  change Ideal.comap _ (default : Spec ↧ℂ).asIdeal = _
  rw [h, RingHom.ker_eq_comap_bot]
  rfl

theorem eq_tInf (q : Spec (CommRingCat.of YCoordinateRing))
    (h : AdjoinRoot.root yAffinePolynomial ∈ q.asIdeal) : q = tInf := by
  have hu : AdjoinRoot.of yAffinePolynomial X ∈ q.asIdeal := by
    apply q.isPrime.mem_of_pow_mem 3
    have he := yChart_equation
    have : AdjoinRoot.of yAffinePolynomial X ^ 3 = AdjoinRoot.root yAffinePolynomial -
        AdjoinRoot.of yAffinePolynomial X * AdjoinRoot.root yAffinePolynomial ^ 2 := by
      linear_combination -he
    rw [this]
    exact q.asIdeal.sub_mem h (q.asIdeal.mul_mem_left _ (q.asIdeal.pow_mem_of_mem h 2 (by norm_num)))
  have hle : RingHom.ker infinityCoordinates ≤ q.asIdeal := by
    refine (CubicDivisor.ker_le_span _ _ infinityCoordinates_C infinityCoordinates_values.1
      infinityCoordinates_values.2).trans ?_
    rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact hu
    · exact h
  have hmax : (RingHom.ker infinityCoordinates).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨_, infinityCoordinates_C c⟩
  apply PrimeSpectrum.ext
  rw [tInf_asIdeal]
  exact (hmax.eq_of_le q.isPrime.ne_top hle).symm

/-- The only point of `E` outside the affine chart is the point at infinity.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1. -/
theorem eq_infinity_of_not_mem {z : E.left} (hz : z ∉ zChart) : z = cubicInfinity := by
  have hy : z ∈ yChart := by
    have h : z ∈ zChart ⊔ yChart := by rw [charts_cover]; trivial
    rcases h with h | h
    · exact absurd h hz
    · exact h
  let x : yChart.toScheme := ⟨z, hy⟩
  let q : Spec (CommRingCat.of YCoordinateRing) := yChartIso.hom x
  have hq : yChartMap q = z := by
    change yChart.ι (yChartIso.inv (yChartIso.hom x)) = z
    rw [iso_inv_hom_apply]
    rfl
  have hv : AdjoinRoot.root yAffinePolynomial ∈ q.asIdeal := by
    by_contra hv
    apply hz
    have : q ∈ yChartMap ⁻¹ᵁ zChart := by
      rw [yChartMap_preimage_z]
      exact hv
    rw [← hq]
    exact this
  rw [← hq, eq_tInf q hv, cubicInfinity, ← infinity_chart]
  rfl

end Infinity

section IdealMap

/-- The invertible fractional ideal of a height-one prime. -/
def idealUnit (v : HeightOneSpectrum 𝒜) : (FractionalIdeal 𝒜⁰ KE)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal 𝒜⁰ KE) (by rw [ne_eq, coeIdeal_eq_zero]; exact v.ne_bot)

theorem support_finite (D : Divisor E.left) :
    {v : HeightOneSpectrum 𝒜 | (D : AlgebraicCycle E.left ℤ) (pt v) ≠ 0}.Finite :=
  (divisor_support_finite D).preimage pt_injective.injOn

theorem mulSupport_finite (D : Divisor E.left) :
    (Function.mulSupport fun v ↦ idealUnit v ^ (D : AlgebraicCycle E.left ℤ) (pt v)).Finite := by
  refine (support_finite D).subset fun v hv h0 ↦ hv ?_
  simp only [h0, zpow_zero]

/-- The fractional ideal of the affine part of a divisor. -/
def divisorIdeal (D : Divisor E.left) : (FractionalIdeal 𝒜⁰ KE)ˣ :=
  ∏ᶠ v, idealUnit v ^ (D : AlgebraicCycle E.left ℤ) (pt v)

theorem divisorIdeal_add (D D' : Divisor E.left) :
    divisorIdeal (D + D') = divisorIdeal D * divisorIdeal D' := by
  rw [divisorIdeal, divisorIdeal, divisorIdeal,
    ← finprod_mul_distrib (mulSupport_finite D) (mulSupport_finite D')]
  refine finprod_congr fun v ↦ ?_
  rw [← zpow_add]
  rfl

theorem divisorIdeal_zero : divisorIdeal 0 = 1 := by
  have h := divisorIdeal_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem coe_divisorIdeal (D : Divisor E.left) :
    (divisorIdeal D : FractionalIdeal 𝒜⁰ KE) =
      ∏ᶠ v : HeightOneSpectrum 𝒜, (v.asIdeal : FractionalIdeal 𝒜⁰ KE) ^
        (D : AlgebraicCycle E.left ℤ) (pt v) := by
  rw [divisorIdeal, ← Units.coeHom_apply, MonoidHom.map_finprod _ (mulSupport_finite D)]
  refine finprod_congr fun v ↦ ?_
  rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val]
  rfl

theorem count_divisorIdeal (D : Divisor E.left) (v : HeightOneSpectrum 𝒜) :
    count KE v (divisorIdeal D) = (D : AlgebraicCycle E.left ℤ) (pt v) := by
  rw [coe_divisorIdeal, count_finprod KE v _ (Filter.eventually_cofinite.mpr (support_finite D))]

/-- Invertible fractional ideals are determined by their exponents.
Source: Mathlib `FractionalIdeal.finprod_heightOneSpectrum_factorization'`. -/
theorem units_ext_count {I J : (FractionalIdeal 𝒜⁰ KE)ˣ}
    (h : ∀ v, count KE v (I : FractionalIdeal 𝒜⁰ KE) = count KE v (J : FractionalIdeal 𝒜⁰ KE)) :
    I = J := by
  apply Units.ext
  rw [← finprod_heightOneSpectrum_factorization' (K := KE) I.ne_zero,
    ← finprod_heightOneSpectrum_factorization' (K := KE) J.ne_zero]
  simp_rw [h]

/-- Principal divisors go to principal fractional ideals.
Source: Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.2. -/
theorem divisorIdeal_principal (f : KE) (hf : f ≠ 0) :
    divisorIdeal (principalDivisor E.left f) = toPrincipalIdeal 𝒜 KE (Units.mk0 f hf) := by
  apply units_ext_count
  intro v
  rw [count_divisorIdeal, coe_toPrincipalIdeal, Units.val_mk0, ← ord_pt v f hf]
  exact principalDivisor_apply f hf (pt v)

theorem divisorIdeal_pt (v : HeightOneSpectrum 𝒜) :
    divisorIdeal (pointDivisor E.left (pt v)) = idealUnit v := by
  classical
  apply units_ext_count
  intro w
  rw [count_divisorIdeal, pointDivisor_apply, idealUnit, Units.val_mk0, count_maximal,
    pt_injective.eq_iff]
  simp only [coheight_pt, true_and, eq_comm]

theorem pt_ne_infinity (v : HeightOneSpectrum 𝒜) : pt v ≠ cubicInfinity := by
  intro h
  have h' : (default : Spec ↧ℂ) ∈ infinity ⁻¹ᵁ zChart := by
    change cubicInfinity ∈ zChart
    rw [← h]
    exact pt_mem_zChart v
  rw [infinity_zChart] at h'
  exact h'

theorem divisorIdeal_infinity : divisorIdeal (pointDivisor E.left cubicInfinity) = 1 := by
  classical
  apply units_ext_count
  intro w
  rw [count_divisorIdeal, pointDivisor_apply, Units.val_one, count_one]
  simp [pt_ne_infinity]

/-- A divisor of degree zero whose fractional ideal is trivial is zero. -/
theorem eq_zero_of_divisorIdeal_eq_one (D : Divisor E.left) (h1 : divisorIdeal D = 1)
    (h2 : divisorDegree E D = 0) : D = 0 := by
  have hz : ∀ z, z ≠ cubicInfinity → (D : AlgebraicCycle E.left ℤ) z = 0 := by
    intro z hz
    by_cases hc : Order.coheight z = 1
    · by_cases hm : z ∈ zChart
      · obtain ⟨v, rfl⟩ := exists_pt hm hc
        rw [← count_divisorIdeal, h1, Units.val_one, count_one]
      · exact absurd (eq_infinity_of_not_mem hm) hz
    · by_contra h
      exact hc (D.2 (Function.mem_support.mpr h))
  have hinf : (D : AlgebraicCycle E.left ℤ) cubicInfinity = 0 := by
    rw [divisorDegree, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
      AlgebraicCycle.degree_apply, finsum_eq_single _ cubicInfinity
        (fun z hz' ↦ by rw [hz z hz', smul_zero]),
      residueDegree_eq_one cubicInfinity_isClosed, one_smul] at h2
    exact h2
  apply Subtype.ext
  ext z
  by_cases h : z = cubicInfinity
  · rw [h, hinf]
    rfl
  · rw [hz z h]
    rfl

end IdealMap

section ClassMap

/-- Divisors on `E` to the class group of the affine coordinate ring. -/
def classMap : Divisor E.left →+ Additive (ClassGroup 𝒜) where
  toFun D := Additive.ofMul (ClassGroup.mk KE (divisorIdeal D))
  map_zero' := by rw [divisorIdeal_zero, map_one, ofMul_one]
  map_add' D D' := by rw [divisorIdeal_add, map_mul, ofMul_mul]

theorem classMap_apply (D : Divisor E.left) :
    classMap D = Additive.ofMul (ClassGroup.mk KE (divisorIdeal D)) := rfl

theorem classMap_principal (f : KE) (hf : f ≠ 0) : classMap (principalDivisor E.left f) = 0 := by
  rw [classMap_apply, divisorIdeal_principal f hf, ofMul_eq_zero, ClassGroup.mk_eq_one_iff,
    coe_toPrincipalIdeal, coe_spanSingleton]
  exact ⟨⟨f, rfl⟩⟩

theorem principalDivisors_le_ker : principalDivisors E.left ≤ classMap.ker := by
  rw [principalDivisors, AddSubgroup.closure_le]
  rintro _ ⟨f, hf, rfl⟩
  exact classMap_principal f hf

/-- The induced map on divisor classes. -/
def classMapQ : DivisorClass E.left →+ Additive (ClassGroup 𝒜) :=
  QuotientAddGroup.lift _ classMap principalDivisors_le_ker

theorem classMapQ_mk (D : Divisor E.left) : classMapQ (DivisorClass.mk E.left D) = classMap D :=
  rfl

/-- A degree-zero divisor with principal ideal class is principal: `Cl⁰(E)` injects into the
class group of the affine coordinate ring. This uses the product formula.
Source: Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.5. -/
theorem mk_eq_zero_of_classMap_eq_zero (D : Divisor E.left) (h1 : classMap D = 0)
    (h2 : divisorDegree E D = 0) : DivisorClass.mk E.left D = 0 := by
  have h : ClassGroup.mk KE (divisorIdeal D) = 1 := h1
  rw [ClassGroup.mk_eq_one_iff] at h
  obtain ⟨g, hg⟩ := h.principal
  have hI : (divisorIdeal D : FractionalIdeal 𝒜⁰ KE) = spanSingleton 𝒜⁰ g := by
    apply Subtype.coe_injective
    simp only [val_eq_coe, hg, coe_spanSingleton]
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [spanSingleton_zero] at hI
    exact (divisorIdeal D).ne_zero hI
  have hD : divisorIdeal D = toPrincipalIdeal 𝒜 KE (Units.mk0 g hg0) := by
    apply Units.ext
    rw [hI, coe_toPrincipalIdeal, Units.val_mk0]
  have hneg : ∀ D' : Divisor E.left, divisorIdeal (-D') = (divisorIdeal D')⁻¹ := by
    intro D'
    rw [eq_inv_iff_mul_eq_one, ← divisorIdeal_add, neg_add_cancel, divisorIdeal_zero]
  have hdiff : divisorIdeal (D - principalDivisor E.left g) = 1 := by
    rw [sub_eq_add_neg, divisorIdeal_add, hneg, divisorIdeal_principal g hg0, hD, mul_inv_cancel]
  have hdeg : divisorDegree E (D - principalDivisor E.left g) = 0 := by
    rw [map_sub, h2, degree_principalDivisor g hg0, sub_zero]
  have h0 := eq_zero_of_divisorIdeal_eq_one _ hdiff hdeg
  rw [sub_eq_zero] at h0
  rw [h0]
  exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.subset_closure ⟨g, hg0, rfl⟩)

open Polynomial in
/-- An affine point of Mathlib's group goes to the point of `E` of the prime `⟨X - x, Y - y⟩`. -/
theorem exists_pt_cubicPointOf {x y : ℂ} (h : W.toAffine.Nonsingular x y) :
    ∃ v : HeightOneSpectrum 𝒜, pt v = cubicPointOf (.some x y h) ∧
      v.asIdeal = WeierstrassCurve.Affine.CoordinateRing.XYIdeal W.toAffine x (C y) := by
  let t : Spec (CommRingCat.of 𝒜) := (Spec.map (CommRingCat.ofHom (equationEval h.1))).base default
  have ht : t.asIdeal = WeierstrassCurve.Affine.CoordinateRing.XYIdeal W.toAffine x (C y) := by
    rw [← ker_equationEval h.1]
    have := (default : Spec ↧ℂ).isPrime
    have h0 : (default : Spec ↧ℂ).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    change Ideal.comap _ (default : Spec ↧ℂ).asIdeal = _
    rw [h0, RingHom.ker_eq_comap_bot]
    rfl
  have hne : t.asIdeal ≠ ⊥ := by
    rw [ht]
    intro h0
    apply WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero (W' := W.toAffine) x
    rw [← Ideal.mem_bot, ← h0]
    exact Ideal.subset_span (Set.mem_insert _ _)
  exact ⟨⟨t.asIdeal, t.isPrime, hne⟩, rfl, ht⟩

/-- The class map sends the Abel class of a point to Mathlib's `Point.toClass`.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.3.4; Mathlib
`WeierstrassCurve.Affine.Point.toClass`. -/
theorem classMap_abel (P : W.toAffine.Point) :
    classMap (pointDivisor E.left (cubicPointOf P) - pointDivisor E.left cubicInfinity) =
      WeierstrassCurve.Affine.Point.toClass P := by
  cases P with
  | zero =>
    rw [show (WeierstrassCurve.Affine.Point.zero : W.toAffine.Point) = 0 from rfl,
      WeierstrassCurve.Affine.Point.toClass_zero]
    change classMap (pointDivisor E.left cubicInfinity - pointDivisor E.left cubicInfinity) = 0
    rw [sub_self, map_zero]
  | some x y h =>
    obtain ⟨v, hv, hI⟩ := exists_pt_cubicPointOf h
    rw [← hv, map_sub, classMap_apply, classMap_apply, divisorIdeal_pt, divisorIdeal_infinity,
      map_one, ofMul_one, sub_zero, WeierstrassCurve.Affine.Point.toClass_some,
      ← ClassGroup.mk_canonicalEquiv W.toAffine.FunctionField KE]
    apply congrArg Additive.ofMul
    apply congrArg (ClassGroup.mk KE)
    apply Units.ext
    rw [idealUnit, Units.val_mk0, Units.coe_map, MonoidHom.coe_ofClass,
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal'_eq, canonicalEquiv_coeIdeal, hI]

end ClassMap

end HodgeLean.Foundations.Curves.CubicClassMap
