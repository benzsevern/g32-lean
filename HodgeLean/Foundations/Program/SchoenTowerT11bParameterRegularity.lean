import HodgeLean.Foundations.Program.SchoenTowerT11bParameterResultants

/-! Polynomial tests for regular specialized fibers over arbitrary parameter rings.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A common real root under a coefficient specialization forces the resultant to vanish there.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, specialized resultant step. -/
theorem s2v_t11b_parameter_common_root_resultant {A : Type*} [CommRing A]
    (P Q : Polynomial A) (φ : A →+* ℝ)
    (hdegree : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) (x : ℝ)
    (hP : P.eval₂ φ x = 0) (hQ : Q.eval₂ φ x = 0) :
    φ (P.resultant Q) = 0 := by
  obtain ⟨U, V, _, _, h⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant P Q
    le_rfl le_rfl hdegree
  have he := congrArg (fun S : Polynomial A => S.eval₂ φ x) h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    hP, hQ, zero_mul, zero_add] at he
  exact he.symm


/-- Nonvanishing leading coefficient and derivative resultant ensure simple real fibers in every spatial degree.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, regular specialization step. -/
theorem s2v_t11b_parameter_simple_roots_of_projection {A : Type*} [CommRing A]
    (P : Polynomial A) (φ : A →+* ℝ)
    (hlead : φ P.leadingCoeff ≠ 0) (hres : φ (P.resultant P.derivative) ≠ 0) :
    ∀ x : ℝ, P.eval₂ φ x = 0 → (P.map φ).derivative.eval x ≠ 0 := by
  by_cases hd : P.natDegree ≠ 0
  · intro x hx hdx
    have hder : P.derivative.eval₂ φ x = 0 := by
      simpa only [Polynomial.eval₂_eq_eval_map, Polynomial.derivative_map] using hdx
    exact hres (s2v_t11b_parameter_common_root_resultant P P.derivative φ (Or.inl hd) x hx hder)
  · have hz : P.natDegree = 0 := not_ne_iff.mp hd
    have hC : P = Polynomial.C P.leadingCoeff := by
      simpa only [Polynomial.leadingCoeff, hz] using Polynomial.eq_C_of_natDegree_eq_zero hz
    intro x hx
    have he := congrArg (fun Q : Polynomial A => Q.eval₂ φ x) hC
    rw [Polynomial.eval₂_C] at he
    exact (hlead (he.symm.trans hx)).elim


/-- One nonzero coefficient polynomial detects every failure of simple degree-preserving specialization of a radical carrier.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, exceptional polynomial construction step. -/
theorem s2v_t11b_parameter_exceptional_polynomial {A : Type*} [CommRing A]
    [IsDomain A] [CharZero A] [UniqueFactorizationMonoid A]
    [NormalizationMonoid (Polynomial A)] (P : Polynomial A) :
    ∃ D : A, D ≠ 0 ∧ ∀ φ : A →+* ℝ, φ D ≠ 0 →
      φ (UniqueFactorizationMonoid.radical P).leadingCoeff ≠ 0 ∧
      ∀ x : ℝ, (UniqueFactorizationMonoid.radical P).eval₂ φ x = 0 →
        ((UniqueFactorizationMonoid.radical P).map φ).derivative.eval x ≠ 0 := by
  let R := UniqueFactorizationMonoid.radical P
  refine ⟨R.leadingCoeff * R.resultant R.derivative, mul_ne_zero ?_ ?_, ?_⟩
  · exact Polynomial.leadingCoeff_ne_zero.mpr UniqueFactorizationMonoid.radical_ne_zero
  · exact s2v_t11b_parameter_radical_derivative_resultant P
  · intro φ hD
    rw [map_mul] at hD
    obtain ⟨hl, hr⟩ := mul_ne_zero_iff.mp hD
    exact ⟨hl, s2v_t11b_parameter_simple_roots_of_projection R φ hl hr⟩

end HodgeLean.Foundations.Program
