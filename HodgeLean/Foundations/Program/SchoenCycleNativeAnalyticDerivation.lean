import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Differentiation of native analytic germs -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- Differentiating analytic representatives in a fixed direction defines
an operation on native analytic germs.
Source: Mathlib, AnalyticAt.fderiv and Filter.EventuallyEq.fderiv. -/
def s2e_nativeAnalytic_derivative (d : ℕ) (v : Fin d → ℂ)
    (g : s2e_nativeAnalyticGermRing d) : s2e_nativeAnalyticGermRing d := by
  refine ⟨Filter.Germ.liftOn g.val
    (fun f => Filter.Germ.ofFun (fun z => fderiv ℂ f z v))
    (fun f h he => Filter.Germ.coe_eq.mpr (he.fderiv.mono fun z hz =>
      congrArg (fun D : (Fin d → ℂ) →L[ℂ] ℂ => D v) hz)), ?_⟩
  obtain ⟨f, hf, he⟩ := g.property
  rw [← he]
  refine ⟨fun z => fderiv ℂ f z v, ?_, rfl⟩
  exact ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt (fderiv ℂ f 0)).comp hf.fderiv

#print axioms s2e_nativeAnalytic_derivative
/-- Native analytic germ differentiation is additive.
Source: Mathlib, fderiv_add and AnalyticAt.eventually_analyticAt. -/
theorem s2e_nativeAnalytic_derivative_add (d : ℕ) (v : Fin d → ℂ)
    (a b : s2e_nativeAnalyticGermRing d) :
    s2e_nativeAnalytic_derivative d v (a + b) =
      s2e_nativeAnalytic_derivative d v a + s2e_nativeAnalytic_derivative d v b := by
  obtain ⟨f, hf, he⟩ := a.property
  obtain ⟨g, hg, he'⟩ := b.property
  apply Subtype.ext
  change Filter.Germ.liftOn (a.val + b.val) _ _ =
    Filter.Germ.liftOn a.val _ _ + Filter.Germ.liftOn b.val _ _
  rw [← he, ← he']
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with z hfz hgz
  change fderiv ℂ (f + g) z v = fderiv ℂ f z v + fderiv ℂ g z v
  rw [fderiv_add hfz.differentiableAt hgz.differentiableAt]
  rfl

#print axioms s2e_nativeAnalytic_derivative_add
/-- Native analytic germ differentiation satisfies the product rule.
Source: Mathlib, fderiv_mul and AnalyticAt.eventually_analyticAt. -/
theorem s2e_nativeAnalytic_derivative_mul (d : ℕ) (v : Fin d → ℂ)
    (a b : s2e_nativeAnalyticGermRing d) :
    s2e_nativeAnalytic_derivative d v (a * b) =
      a * s2e_nativeAnalytic_derivative d v b + b * s2e_nativeAnalytic_derivative d v a := by
  obtain ⟨f, hf, he⟩ := a.property
  obtain ⟨g, hg, he'⟩ := b.property
  apply Subtype.ext
  change Filter.Germ.liftOn (a.val * b.val) _ _ =
    a.val * Filter.Germ.liftOn b.val _ _ + b.val * Filter.Germ.liftOn a.val _ _
  rw [← he, ← he']
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with z hfz hgz
  change fderiv ℂ (f * g) z v = f z * fderiv ℂ g z v + g z * fderiv ℂ f z v
  rw [fderiv_mul hfz.differentiableAt hgz.differentiableAt]
  rfl

#print axioms s2e_nativeAnalytic_derivative_mul
/-- Native directional differentiation is an algebraic derivation over the
integers, retaining the native analytic derivative as its underlying map.
Source: Mathlib, Derivation.mk'. -/
def s2e_nativeAnalytic_derivation (d : ℕ) (v : Fin d → ℂ) :
    Derivation ℤ (s2e_nativeAnalyticGermRing d) (s2e_nativeAnalyticGermRing d) := by
  let D : s2e_nativeAnalyticGermRing d →+ s2e_nativeAnalyticGermRing d :=
    { toFun := s2e_nativeAnalytic_derivative d v
      map_zero' := by
        apply Subtype.ext
        apply Filter.Germ.coe_eq.mpr
        filter_upwards [] with z
        change fderiv ℂ (fun _ : Fin d → ℂ => (0 : ℂ)) z v = 0
        simp
      map_add' := s2e_nativeAnalytic_derivative_add d v }
  exact Derivation.mk' D.toIntLinearMap (s2e_nativeAnalytic_derivative_mul d v)

#print axioms s2e_nativeAnalytic_derivation
/-- A derivation lowers the order in any ideal by at most one.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
Mathlib, Derivation.leibniz. -/
theorem s2e_derivation_ideal_power
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (I : Ideal A) (N : ℕ) {a : A}
    (ha : a ∈ I ^ (N + 1)) : D a ∈ I ^ N := by
  induction N generalizing a with
  | zero => simp
  | succ N ih =>
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      rw [D.leibniz]
      change x * D y + y * D x ∈ I ^ (N + 1)
      apply Ideal.add_mem
      · exact Ideal.mul_mem_right _ _ hx
      · rw [mul_comm, pow_succ]
        exact Ideal.mul_mem_mul (ih hx) hy
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy

#print axioms s2e_derivation_ideal_power
/-- The native derivative of a constant germ is zero.
Source: Mathlib, fderiv_const. -/
theorem s2e_nativeAnalytic_derivation_constant (d : ℕ) (v : Fin d → ℂ) (c : ℂ) :
    s2e_nativeAnalytic_derivation d v (s2e_nativeAnalytic_constant d c) = 0 := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [] with z
  change fderiv ℂ (fun _ : Fin d → ℂ => c) z v = 0
  simp

#print axioms s2e_nativeAnalytic_derivation_constant
/-- The native derivative of a coordinate germ is its directional component.
Source: Mathlib, ContinuousLinearMap.fderiv. -/
theorem s2e_nativeAnalytic_derivation_coordinate (d : ℕ) (v : Fin d → ℂ) (i : Fin d) :
    s2e_nativeAnalytic_derivation d v (s2e_nativeAnalytic_coordinate d i) =
      s2e_nativeAnalytic_constant d (v i) := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [] with z
  change fderiv ℂ (fun w : Fin d → ℂ => w i) z v = v i
  have h : fderiv ℂ (fun w : Fin d → ℂ => w i) z = ContinuousLinearMap.proj i :=
    (ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ).fderiv
  exact congrArg (fun D : (Fin d → ℂ) →L[ℂ] ℂ => D v) h

#print axioms s2e_nativeAnalytic_derivation_coordinate
/-- Native partial differentiation commutes with polynomial evaluation.
Source: Mathlib, MvPolynomial.pderiv and Derivation.leibniz. -/
theorem s2e_nativeAnalytic_derivation_polynomial (d : ℕ) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    s2e_nativeAnalytic_derivation d (Pi.single i 1) (s2e_nativeAnalytic_polynomial d p) =
      s2e_nativeAnalytic_polynomial d (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.pderiv_C, map_zero, s2e_nativeAnalytic_polynomial,
      MvPolynomial.eval₂Hom_C, s2e_nativeAnalytic_derivation_constant]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, Derivation.leibniz, MvPolynomial.pderiv_mul, map_add, hp, smul_eq_mul]
    have hX : s2e_nativeAnalytic_polynomial d (MvPolynomial.X j) =
        s2e_nativeAnalytic_coordinate d j := MvPolynomial.eval₂Hom_X' _ _ _
    rw [hX, s2e_nativeAnalytic_derivation_coordinate]
    by_cases h : j = i
    · subst j
      simp [MvPolynomial.pderiv_X_self, add_comm, mul_comm, Pi.single_apply]
    · simp [MvPolynomial.pderiv_X_of_ne h, Pi.single_eq_of_ne h, mul_comm]

#print axioms s2e_nativeAnalytic_derivation_polynomial
/-- Vanishing constant coefficient and partial derivatives of order at
least N force polynomial order at least N+1.
Source: Hartshorne, Algebraic Geometry, II.8;
Mathlib, MvPolynomial.coeff_pderiv and mem_pow_idealOfVars_iff'. -/
theorem s2e_polynomial_order_of_partial_derivatives (d N : ℕ)
    (p : MvPolynomial (Fin d) ℂ) (h0 : MvPolynomial.constantCoeff p = 0)
    (hD : ∀ i, MvPolynomial.pderiv i p ∈ MvPolynomial.idealOfVars (Fin d) ℂ ^ N) :
    p ∈ MvPolynomial.idealOfVars (Fin d) ℂ ^ (N + 1) := by
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro m hm
  by_cases hz : m = 0
  · simpa only [hz, MvPolynomial.constantCoeff_eq] using h0
  · have hex : ∃ i, m i ≠ 0 := by
      by_contra h
      apply hz
      ext i
      exact not_ne_iff.mp (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hex
    let e := m - Finsupp.single i 1
    have he : e + Finsupp.single i 1 = m := Finsupp.sub_add_single_one_cancel hi
    have hdeg : e.degree < N := by
      have h := congrArg Finsupp.degree he
      simp only [map_add, Finsupp.degree_single] at h
      omega
    have hc := (MvPolynomial.mem_pow_idealOfVars_iff' N _).mp (hD i) e hdeg
    rw [MvPolynomial.coeff_pderiv, he] at hc
    apply (mul_eq_zero.mp hc).resolve_right
    exact_mod_cast Nat.succ_ne_zero (e i)

#print axioms s2e_polynomial_order_of_partial_derivatives
/-- Polynomial evaluation in native analytic germs preserves the constant
coefficient as evaluation at the origin.
Source: Mathlib, MvPolynomial.constantCoeff. -/
theorem s2e_nativeAnalytic_polynomial_value (d : ℕ) (p : MvPolynomial (Fin d) ℂ) :
    s2e_nativeAnalyticGerm_value d (s2e_nativeAnalytic_polynomial d p) =
      MvPolynomial.constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [s2e_nativeAnalytic_polynomial, MvPolynomial.eval₂Hom_C,
      MvPolynomial.constantCoeff_C]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.constantCoeff_X, mul_zero]
    have hX : s2e_nativeAnalytic_polynomial d (MvPolynomial.X i) =
        s2e_nativeAnalytic_coordinate d i := MvPolynomial.eval₂Hom_X' _ _ _
    rw [hX]
    change MvPolynomial.constantCoeff p * 0 = 0
    exact mul_zero _

#print axioms s2e_nativeAnalytic_polynomial_value
/-- Polynomial evaluation reflects every power of the maximal ideal in
the native analytic germ ring.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6. -/
theorem s2e_nativeAnalytic_polynomial_order_iff (d N : ℕ)
    (p : MvPolynomial (Fin d) ℂ) :
    s2e_nativeAnalytic_polynomial d p ∈
        IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d) ^ N ↔
      p ∈ MvPolynomial.idealOfVars (Fin d) ℂ ^ N := by
  constructor
  · intro hp
    induction N generalizing p with
    | zero => simp
    | succ N ih =>
      apply s2e_polynomial_order_of_partial_derivatives d N p
      · have hm := Ideal.pow_le_self (Nat.succ_ne_zero N) hp
        have hn : ¬ IsUnit (s2e_nativeAnalytic_polynomial d p) := hm
        have hv : s2e_nativeAnalyticGerm_value d (s2e_nativeAnalytic_polynomial d p) = 0 := by
          simpa only [s2e_nativeAnalyticGerm_isUnit_iff_value_ne_zero, not_not] using hn
        rwa [s2e_nativeAnalytic_polynomial_value] at hv
      · intro i
        apply ih
        rw [← s2e_nativeAnalytic_derivation_polynomial]
        exact s2e_derivation_ideal_power
          (s2e_nativeAnalytic_derivation d (Pi.single i 1)) _ N hp
  · intro hp
    have h := Ideal.mem_map_of_mem (s2e_nativeAnalytic_polynomial d) hp
    rwa [Ideal.map_pow, s2e_nativeAnalytic_map_variableIdeal] at h

#print axioms s2e_nativeAnalytic_polynomial_order_iff
end HodgeLean.Foundations.Program
