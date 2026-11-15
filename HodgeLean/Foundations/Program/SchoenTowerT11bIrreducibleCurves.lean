import HodgeLean.Foundations.Program.SchoenTowerT11bIrreducibleResultants
import HodgeLean.Foundations.Program.SchoenTowerT11bCurveTriviality

/-! Inequality-compatible finite charts on irreducible plane curves.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Polynomial divisibility forces vanishing on every specialized zero set.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, common-component step. -/
theorem s2v_t11b_family_eval_zero_of_dvd (P Q : Polynomial (Polynomial ℝ))
    (hdiv : P ∣ Q) (t x : ℝ) (hx : P.eval₂ (Polynomial.evalRingHom t) x = 0) :
    Q.eval₂ (Polynomial.evalRingHom t) x = 0 := by
  obtain ⟨S, rfl⟩ := hdiv
  rw [Polynomial.eval₂_mul, hx, zero_mul]

/-- An inequality on an irreducible plane curve has finite Boolean base charts, including shared components.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, irreducible plane curve case. -/
theorem s2v_t11b_irreducible_nonneg_curve_triviality
    (P Q : Polynomial (Polynomial ℝ)) (hP : Irreducible P) (hdegree : P.natDegree ≠ 0) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula 1, ∃ b : Fin m → ℝ,
      (∀ t : ℝ, ∃! i, WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize) ∧
      ∀ i, ∃ e :
        ({x : ℝ | P.eval₂ (Polynomial.evalRingHom (b i)) x = 0 ∧
          0 ≤ Q.eval₂ (Polynomial.evalRingHom (b i)) x} ×
          {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize}) ≃ₜ
        {z : {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize} × ℝ |
          P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0 ∧
          0 ≤ Q.eval₂ (Polynomial.evalRingHom z.1.val) z.2},
        ∀ y, (e y).val.1 = y.2 := by
  classical
  have hres := s2v_t11b_irreducible_derivative_resultant P hP hdegree
  by_cases hdiv : P ∣ Q
  · obtain ⟨m, c, b, hcover, hcharts⟩ :=
      s2v_t11b_finite_base_triviality_of_resultant P hP.ne_zero hdegree hres
    refine ⟨m, c, b, hcover, ?_⟩
    intro i
    obtain ⟨e, he⟩ := hcharts i
    let K : Set ℝ := {t | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize}
    have hf : {x : ℝ | P.eval₂ (Polynomial.evalRingHom (b i)) x = 0 ∧
        0 ≤ Q.eval₂ (Polynomial.evalRingHom (b i)) x} =
        {x : ℝ | P.eval₂ (Polynomial.evalRingHom (b i)) x = 0} := by
      ext x
      constructor
      · exact fun h => h.1
      · intro hx
        exact ⟨hx, (s2v_t11b_family_eval_zero_of_dvd P Q hdiv (b i) x hx).symm ▸ le_refl 0⟩
    have ht : {z : K × ℝ | P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0 ∧
        0 ≤ Q.eval₂ (Polynomial.evalRingHom z.1.val) z.2} =
        {z : K × ℝ | P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0} := by
      ext z
      constructor
      · exact fun h => h.1
      · intro hz
        exact ⟨hz, (s2v_t11b_family_eval_zero_of_dvd P Q hdiv z.1.val z.2 hz).symm ▸ le_refl 0⟩
    let A := (Homeomorph.setCongr hf).prodCongr (Homeomorph.refl K)
    let E := (A.trans e).trans (Homeomorph.setCongr ht).symm
    exact ⟨E, fun y => he (A y)⟩
  · exact s2v_t11b_nonneg_curve_finite_base_triviality P Q hP.ne_zero hdegree hres
      (s2v_t11b_irreducible_test_resultant P Q hP hdegree hdiv)

end HodgeLean.Foundations.Program
