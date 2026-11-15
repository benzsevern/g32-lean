import HodgeLean.Foundations.Program.SchoenTowerT11bEffectiveDegree

/-! Polynomial coefficient reductions without division by parameter functions.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Cancel the leading spatial term using only polynomial coefficient operations.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, polynomial remainder construction step. -/
def s2v_t11b_pseudoStep {A : Type*} [CommRing A] (P Q : Polynomial A) : Polynomial A :=
  Polynomial.C Q.leadingCoeff * P -
    (Polynomial.C P.leadingCoeff * Q) * Polynomial.X ^ (P.natDegree - Q.natDegree)


/-- Leading-term cancellation strictly decreases spatial degree over a parameter domain.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, polynomial remainder termination step. -/
theorem s2v_t11b_pseudoStep_degree {A : Type*} [CommRing A] [IsDomain A]
    (P Q : Polynomial A) (hP : P ≠ 0) (hQ : Q ≠ 0) (hd : Q.natDegree ≤ P.natDegree) :
    (s2v_t11b_pseudoStep P Q).degree < P.degree := by
  have hp := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hq := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have he : (Polynomial.C Q.leadingCoeff * P).degree =
      ((Polynomial.C P.leadingCoeff * Q) * Polynomial.X ^ (P.natDegree - Q.natDegree)).degree := by
    rw [Polynomial.degree_C_mul hq, Polynomial.degree_mul_X_pow, Polynomial.degree_C_mul hp,
      Polynomial.degree_eq_natDegree hP, Polynomial.degree_eq_natDegree hQ, ← Nat.cast_add,
      Nat.add_sub_of_le hd]
  have hn : Polynomial.C Q.leadingCoeff * P ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hq) hP
  have hl : (Polynomial.C Q.leadingCoeff * P).leadingCoeff =
      ((Polynomial.C P.leadingCoeff * Q) * Polynomial.X ^ (P.natDegree - Q.natDegree)).leadingCoeff := by
    simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_X_pow, mul_one, one_mul, mul_comm]
  have h := Polynomial.degree_sub_lt_left he hn hl
  simpa only [s2v_t11b_pseudoStep, Polynomial.degree_C_mul hq] using h


/-- Polynomial division over a parameter domain needs only a power of the divisor's leading coefficient.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, scaled polynomial division step. -/
theorem s2v_t11b_pseudoDivision_exists {A : Type*} [CommRing A] [IsDomain A]
    (P Q : Polynomial A) (hQ : Q ≠ 0) :
    ∃ k : ℕ, ∃ S R : Polynomial A,
      Polynomial.C (Q.leadingCoeff ^ k) * P = Q * S + R ∧ R.degree < Q.degree := by
  by_cases hsmall : P.degree < Q.degree
  · exact ⟨0, 0, P, by simp, hsmall⟩
  have hP : P ≠ 0 := by
    intro hz
    apply hsmall
    rw [hz, Polynomial.degree_zero]
    rw [Polynomial.degree_eq_natDegree hQ]
    exact WithBot.bot_lt_coe _
  have hd : Q.natDegree ≤ P.natDegree := Polynomial.natDegree_le_natDegree (le_of_not_gt hsmall)
  let T := s2v_t11b_pseudoStep P Q
  obtain ⟨k, S, R, he, hr⟩ := s2v_t11b_pseudoDivision_exists T Q hQ
  refine ⟨k + 1, S + Polynomial.C (Q.leadingCoeff ^ k) *
    (Polynomial.C P.leadingCoeff * Polynomial.X ^ (P.natDegree - Q.natDegree)), R, ?_, hr⟩
  calc
    Polynomial.C (Q.leadingCoeff ^ (k + 1)) * P =
        Polynomial.C (Q.leadingCoeff ^ k) * T + Q *
          (Polynomial.C (Q.leadingCoeff ^ k) *
            (Polynomial.C P.leadingCoeff * Polynomial.X ^ (P.natDegree - Q.natDegree))) := by
      dsimp [T, s2v_t11b_pseudoStep]
      rw [pow_succ, Polynomial.C_mul]
      ring
    _ = Q * (S + Polynomial.C (Q.leadingCoeff ^ k) *
          (Polynomial.C P.leadingCoeff * Polynomial.X ^ (P.natDegree - Q.natDegree))) + R := by
      rw [he]
      ring
termination_by P.degree
decreasing_by exact s2v_t11b_pseudoStep_degree P Q hP hQ hd


/-- A scaled remainder retains exactly the common roots at every specialization avoiding the divisor's leading coefficient.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, specialized remainder root step. -/
theorem s2v_t11b_pseudoDivision_common_roots {A : Type*} [CommRing A]
    (P Q S R : Polynomial A) (k : ℕ)
    (he : Polynomial.C (Q.leadingCoeff ^ k) * P = Q * S + R)
    (φ : A →+* ℝ) (hlead : φ Q.leadingCoeff ≠ 0) (x : ℝ) :
    (P.eval₂ φ x = 0 ∧ Q.eval₂ φ x = 0) ↔
      (Q.eval₂ φ x = 0 ∧ R.eval₂ φ x = 0) := by
  have hv := congrArg (fun W : Polynomial A => W.eval₂ φ x) he
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_add, Polynomial.eval₂_pow, map_pow] at hv
  constructor
  · rintro ⟨hp, hq⟩
    refine ⟨hq, ?_⟩
    simpa only [hp, hq, mul_zero, zero_mul, zero_add] using hv.symm
  · rintro ⟨hq, hr⟩
    refine ⟨?_, hq⟩
    rw [hq, hr, zero_mul, zero_add] at hv
    exact (mul_eq_zero.mp hv).resolve_left (pow_ne_zero k hlead)


/-- Scaled remainder reduction preserves every common polynomial divisor after regular specialization.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, specialized polynomial divisor step. -/
theorem s2v_t11b_pseudoDivision_common_divisors {A : Type*} [CommRing A]
    (P Q S R : Polynomial A) (k : ℕ)
    (he : Polynomial.C (Q.leadingCoeff ^ k) * P = Q * S + R)
    (φ : A →+* ℝ) (hlead : φ Q.leadingCoeff ≠ 0) (D : Polynomial ℝ) :
    (D ∣ P.map φ ∧ D ∣ Q.map φ) ↔ (D ∣ Q.map φ ∧ D ∣ R.map φ) := by
  have hv := congrArg (Polynomial.map φ) he
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_add, map_pow] at hv
  have hu : IsUnit (Polynomial.C (φ Q.leadingCoeff ^ k)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero k hlead))
  have heq : Polynomial.C (φ Q.leadingCoeff ^ k) * P.map φ = Q.map φ * S.map φ + R.map φ := by
    simpa only [Polynomial.C_pow] using hv
  constructor
  · rintro ⟨hp, hq⟩
    refine ⟨hq, ?_⟩
    have h := dvd_sub ((hu.dvd_mul_left).mpr hp) (dvd_mul_of_dvd_left hq (S.map φ))
    rwa [heq, add_sub_cancel_left] at h
  · rintro ⟨hq, hr⟩
    refine ⟨hu.dvd_mul_left.mp ?_, hq⟩
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_left hq (S.map φ)) hr


/-- A scaled remainder vanishes identically at every degree-preserving specialization where the divisor divides the dividend.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, specialized exact division step. -/
theorem s2v_t11b_pseudoDivision_remainder_zero {A : Type*} [CommRing A]
    (P Q S R : Polynomial A) (k : ℕ)
    (he : Polynomial.C (Q.leadingCoeff ^ k) * P = Q * S + R) (hr : R.degree < Q.degree)
    (φ : A →+* ℝ) (hlead : φ Q.leadingCoeff ≠ 0) (hdiv : Q.map φ ∣ P.map φ) :
    R.map φ = 0 := by
  have hv := congrArg (Polynomial.map φ) he
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_add, map_pow] at hv
  have heq : Polynomial.C (φ Q.leadingCoeff ^ k) * P.map φ = Q.map φ * S.map φ + R.map φ := by
    simpa only [Polynomial.C_pow] using hv
  have hd : Q.map φ ∣ R.map φ := by
    have h := dvd_sub (dvd_mul_of_dvd_right hdiv (Polynomial.C (φ Q.leadingCoeff ^ k)))
      (dvd_mul_right (Q.map φ) (S.map φ))
    rwa [heq, add_sub_cancel_left] at h
  apply Polynomial.eq_zero_of_dvd_of_degree_lt hd
  rw [Polynomial.degree_map_eq_of_leadingCoeff_ne_zero φ hlead]
  exact Polynomial.degree_map_le.trans_lt hr

end HodgeLean.Foundations.Program
