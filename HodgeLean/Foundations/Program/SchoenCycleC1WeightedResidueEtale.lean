import HodgeLean.Foundations.Program.SchoenCycleC1ResidueEtale
import Mathlib.RingTheory.Ideal.Operations

/-! # Etale normalization from weighted branch ideals -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A weighted branch ideal which is a degree-th power has zero prime residues. -/
theorem s2e_c1_weighted_residues_zero_of_ideal_power
    {R J : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Fintype J] (g : J → R) (n : J → ℕ) (hg : ∀ j, g j ≠ 0)
    (m : ℕ) (E : R)
    (hI : (∏ j, (Ideal.span {g j}) ^ n j) = (Ideal.span {E}) ^ m)
    (p : R) (hp : Prime p) :
    Int.ModEq (m : ℤ)
      (∑ j, (n j : ℤ) * ((emultiplicity p (g j)).toNat : ℤ)) 0 := by
  simp only [Ideal.span_singleton_pow, Ideal.prod_span_singleton] at hI
  have he := emultiplicity_eq_of_associated_right (a := p)
    (Ideal.span_singleton_eq_span_singleton.mp hI : Associated (∏ j, g j ^ n j) (E ^ m))
  rw [← s2v_l1b_divisor_weighted_product_order g n hg p hp, he,
    s2v_l1b_kval_prime_order_pow hp]
  apply Int.modEq_zero_iff_dvd.mpr
  exact dvd_mul_right _ _

/-- Weighted branch residues and a degree-th-power ideal identity suffice for
etaleness of the actual integral closure. -/
theorem s2e_c1_integralClosure_etale_of_weighted_ideal_power
    {R K L J : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [IsIntegrallyClosed R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [Algebra.IsSeparable K L] [Fintype J]
    (P : PowerBasis K L) (m : ℕ) (hm : 0 < m)
    (hdim : Module.finrank K L = m) (d : Rˣ) (hd : (d : R) = (m : R))
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hz : P.gen ^ m = algebraMap R L a / algebraMap R L b)
    (g : J → R) (n : J → ℕ) (hg : ∀ j, g j ≠ 0)
    (hv : ∀ p : R, Prime p → Int.ModEq (m : ℤ)
      (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ))
      (∑ j, (n j : ℤ) * ((emultiplicity p (g j)).toNat : ℤ)))
    (E : R) (hI : (∏ j, (Ideal.span {g j}) ^ n j) = (Ideal.span {E}) ^ m) :
    Algebra.Etale R (integralClosure R L) := by
  apply s2e_c1_integralClosure_etale_of_zero_residues P m hm hdim d hd a b ha hb hz
  intro p hp
  exact (hv p hp).trans (s2e_c1_weighted_residues_zero_of_ideal_power g n hg m E hI p hp)

end HodgeLean.Foundations.Program
