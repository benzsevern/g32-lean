import HodgeLean.Foundations.Curves.CurveDivisorClassesDefs
import HodgeLean.Foundations.Curves.ChartStalks
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Jacobson.Ring

/-! # The affine coordinate ring of the cubic is a Dedekind domain

Every maximal ideal of `ℂ[x,y]/(y² - x³ - x)` is the ideal `⟨x - x₀, y - y₀⟩` of a point, and its
localization is a DVR with uniformizer `x - x₀` (when `y₀ ≠ 0`) or `y` (when `y₀ = 0`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial WeierstrassCurve.Affine

namespace HodgeLean.Foundations.Curves

local notation "A" => W.toAffine.CoordinateRing

/-- The coordinate `x` of the affine chart. -/
abbrev cx : A := AdjoinRoot.of W.toAffine.polynomial X

/-- The coordinate `y` of the affine chart. -/
abbrev cy : A := AdjoinRoot.root W.toAffine.polynomial

/-- The cubic relation `y² = x³ + x` in the coordinate ring.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1. -/
theorem cy_sq : cy ^ 2 = cx ^ 3 + cx := by
  have hp : W.toAffine.polynomial = X ^ 2 - (C X ^ 3 + C X) := by
    simp [WeierstrassCurve.Affine.polynomial, W, WeierstrassCurve.ofJ1728]
  have h : AdjoinRoot.mk W.toAffine.polynomial (X ^ 2 - (C X ^ 3 + C X)) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr (dvd_of_eq hp)
  simp only [map_sub, map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  linear_combination h

/-- Ring maps out of the coordinate ring agree once they agree on constants, `x` and `y`.
Source: Mathlib `AdjoinRoot.ringHom_ext`. -/
theorem coordinateRing_ringHom_ext {T : Type*} [CommRing T] {f g : A →+* T}
    (hc : ∀ c : ℂ, f (algebraMap ℂ A c) = g (algebraMap ℂ A c)) (hx : f cx = g cx)
    (hy : f cy = g cy) : f = g := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      exact hc c
    · exact hx
  · exact hy

/-- `equationEval` is a `ℂ`-algebra map. -/
theorem equationEval_algebraMap {x y : ℂ} (h : W.toAffine.Equation x y) (c : ℂ) :
    equationEval h (algebraMap ℂ A c) = c := by
  simp only [equationEval, RingHom.comp_apply, Ideal.Quotient.mk_algebraMap]
  exact (CoordinateRing.quotientXYIdealEquiv (W' := W.toAffine) h).commutes c

/-- The kernel of `equationEval` is the ideal `⟨X - x, Y - y⟩`. -/
theorem ker_equationEval {x y : ℂ} (h : W.toAffine.Equation x y) :
    RingHom.ker (equationEval h) = CoordinateRing.XYIdeal W.toAffine x (C y) := by
  ext a
  simp only [RingHom.mem_ker, equationEval, RingHom.comp_apply]
  change (CoordinateRing.quotientXYIdealEquiv (W' := W.toAffine) h).toRingEquiv _ = 0 ↔ _
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

/-- `equationEval` vanishes on the ideal `⟨X - x, Y - y⟩`. -/
theorem equationEval_mem {x y : ℂ} (h : W.toAffine.Equation x y) (a : A)
    (ha : a ∈ CoordinateRing.XYIdeal W.toAffine x (C y)) : equationEval h a = 0 := by
  rwa [← RingHom.mem_ker, ker_equationEval]

theorem XClass_eq (x : ℂ) : CoordinateRing.XClass W.toAffine x = cx - algebraMap ℂ A x := by
  simp only [CoordinateRing.XClass, map_sub, CoordinateRing.mk, AdjoinRoot.mk_C]
  rfl

theorem YClass_eq (y : ℂ) : CoordinateRing.YClass W.toAffine (C y) = cy - algebraMap ℂ A y := by
  simp only [CoordinateRing.YClass, map_sub, CoordinateRing.mk, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  rfl

/-- `equationEval` sends the coordinate `x` to `x`. -/
theorem equationEval_x {x y : ℂ} (h : W.toAffine.Equation x y) : equationEval h cx = x := by
  have := equationEval_mem h _ (Ideal.subset_span (Set.mem_insert _ _))
  rw [XClass_eq, map_sub, equationEval_algebraMap, sub_eq_zero] at this
  exact this

/-- `equationEval` sends the coordinate `y` to `y`. -/
theorem equationEval_y {x y : ℂ} (h : W.toAffine.Equation x y) : equationEval h cy = y := by
  have := equationEval_mem h _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [YClass_eq, map_sub, equationEval_algebraMap, sub_eq_zero] at this
  exact this

/-- The equation of `W` at a point, in the form `y² = x³ + x`. -/
theorem W_equation_iff (x y : ℂ) : W.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [W, WeierstrassCurve.ofJ1728]

instance : Module.Finite ℂ[X] A := Module.Finite.of_basis (CoordinateRing.basis W.toAffine)

instance : Algebra.FiniteType ℂ A := Algebra.FiniteType.trans (S := ℂ[X]) inferInstance inferInstance

/-- Every maximal ideal of the coordinate ring is the kernel of evaluation at a point (weak
Nullstellensatz).
Source: Atiyah–Macdonald, Corollary 5.24; Mathlib `finite_of_finite_type_of_isJacobsonRing`. -/
theorem exists_eq_ker_equationEval (m : Ideal A) [hm : m.IsMaximal] :
    ∃ x y : ℂ, ∃ h : W.toAffine.Equation x y, m = RingHom.ker (equationEval h) := by
  let := Ideal.Quotient.field m
  have : Module.Finite ℂ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  let φ : (A ⧸ m) →ₐ[ℂ] ℂ := IsAlgClosed.lift
  let ψ : A →+* ℂ := (φ.comp (Ideal.Quotient.mkₐ ℂ m)).toRingHom
  have hψc : ∀ c, ψ (algebraMap ℂ A c) = c := fun c ↦ (φ.comp _).commutes c
  have h : W.toAffine.Equation (ψ cx) (ψ cy) := by
    rw [W_equation_iff]
    have := congrArg ψ cy_sq
    simpa only [map_pow, map_add] using this
  refine ⟨_, _, h, ?_⟩
  have hψ : ψ = equationEval h := coordinateRing_ringHom_ext
    (fun c ↦ by rw [hψc, equationEval_algebraMap]) (equationEval_x h).symm (equationEval_y h).symm
  rw [← hψ]
  refine hm.eq_of_le (RingHom.ker_ne_top ψ) fun a ha ↦ ?_
  rw [RingHom.mem_ker]
  change φ (Ideal.Quotient.mk m a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

instance ker_equationEval_isPrime {x y : ℂ} (h : W.toAffine.Equation x y) :
    (RingHom.ker (equationEval h)).IsPrime :=
  RingHom.ker_isPrime _

/-- The local ring of the coordinate ring at a point is a DVR.
Source: Silverman, *The Arithmetic of Elliptic Curves*, II.1.1 and III.1; Mathlib
`IsDiscreteValuationRing.TFAE`. -/
theorem isDiscreteValuationRing_of_point {x y : ℂ} (h : W.toAffine.Equation x y) (S : Type*)
    [CommRing S] [IsDomain S] [Algebra A S] [IsLocalization.AtPrime S (RingHom.ker (equationEval h))] :
    IsDiscreteValuationRing S := by
  set m := RingHom.ker (equationEval h)
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing m.primeCompl S inferInstance
  have hinj : Function.Injective (algebraMap A S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors m)
  have hunit : ∀ u, equationEval h u ≠ 0 → IsUnit (algebraMap A S u) := fun u hu ↦
    (IsLocalization.AtPrime.isUnit_to_map_iff S m u).mpr (by simpa [m, RingHom.mem_ker] using hu)
  let c := algebraMap ℂ A
  have hc : ∀ r, equationEval h (c r) = r := equationEval_algebraMap h
  set X' := cx - c x
  set Y' := cy - c y
  set w := cx ^ 2 + c x * cx + c (x ^ 2 + 1)
  have hxy : y ^ 2 = x ^ 3 + x := (W_equation_iff x y).mp h
  have hrel : Y' * (cy + c y) = X' * w := by
    have hc : c (y ^ 2) = c (x ^ 3 + x) := by rw [hxy]
    simp only [map_pow, map_add] at hc
    simp only [X', Y', w, map_add, map_pow, map_one]
    linear_combination cy_sq - hc
  have hm : m ≤ Ideal.span {X', Y'} := by
    change RingHom.ker (equationEval h) ≤ _
    rw [ker_equationEval]
    simp only [CoordinateRing.XYIdeal, XClass_eq, YClass_eq]
    exact le_rfl
  have hX0 : algebraMap A S X' ≠ 0 := fun h0 ↦ CoordinateRing.XClass_ne_zero (W' := W.toAffine) x
    (by rw [XClass_eq]; exact hinj (h0.trans (map_zero _).symm))
  have hY0 : algebraMap A S Y' ≠ 0 := fun h0 ↦ CoordinateRing.YClass_ne_zero (W' := W.toAffine)
    (C y) (by rw [YClass_eq]; exact hinj (h0.trans (map_zero _).symm))
  have hXm : X' ∈ m := by
    rw [RingHom.mem_ker, map_sub, equationEval_x, hc, sub_self]
  have hYm : Y' ∈ m := by
    rw [RingHom.mem_ker, map_sub, equationEval_y, hc, sub_self]
  by_cases hy : y = 0
  · have hw : equationEval h w ≠ 0 := by
      simp only [w, map_add, map_mul, map_pow, equationEval_x, hc]
      intro h0
      rw [hy] at hxy
      have hx : x * (x ^ 2 + 1) = 0 := by linear_combination -hxy
      rcases mul_eq_zero.mp hx with hx | hx
      · rw [hx] at h0; norm_num at h0
      · have : (-2 : ℂ) = 0 := by linear_combination h0 - 3 * hx
        norm_num at this
    have hu := hunit w hw
    refine (ChartStalks.dvr_of_span m S Y' X' hm hYm ?_ hY0).1
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap A S (cy + c y) * ↑hu.unit⁻¹, ?_⟩
    rw [mul_comm, ← mul_assoc, ← map_mul, hrel, map_mul, mul_assoc,
      IsUnit.mul_val_inv, mul_one]
  · have hu : IsUnit (algebraMap A S (cy + c y)) := hunit _ (by
      rw [map_add, equationEval_y, hc]
      intro h0
      exact hy (by linear_combination h0 / 2))
    refine (ChartStalks.dvr_of_span m S X' Y' (by rwa [Set.pair_comm]) hXm ?_ hX0).1
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap A S w * ↑hu.unit⁻¹, ?_⟩
    rw [mul_comm, ← mul_assoc, ← map_mul, ← hrel, map_mul, mul_assoc,
      IsUnit.mul_val_inv, mul_one]

/-- The affine coordinate ring of the cubic is a Dedekind domain.
Source: Silverman, *The Arithmetic of Elliptic Curves*, II.1 and III.1; Mathlib
`isDedekindDomain_iff_isDiscreteValuationRing_atPrime`. -/
instance coordinateRing_isDedekindDomain : IsDedekindDomain A := by
  refine isDedekindDomain_iff_isDiscreteValuationRing_atPrime.mpr ⟨inferInstance, ?_⟩
  intro P hP hPp
  have : Algebra.IsIntegral ℂ[X] A := Algebra.IsIntegral.of_finite ℂ[X] A
  have : Ring.DimensionLEOne A := Ring.DimensionLEOne.of_isIntegral (R := ℂ[X]) A
  have : P.IsMaximal := hPp.isMaximal hP
  obtain ⟨x, y, h, rfl⟩ := exists_eq_ker_equationEval P
  exact isDiscreteValuationRing_of_point h (Localization.AtPrime (RingHom.ker (equationEval h)))

end HodgeLean.Foundations.Curves
