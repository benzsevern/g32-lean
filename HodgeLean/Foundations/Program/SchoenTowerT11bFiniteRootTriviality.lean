import HodgeLean.Foundations.Program.SchoenTowerT11bResultantTriviality

/-! Finite Boolean base pieces for squarefree monic real polynomial families.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A monic family with nonzero derivative resultant has finitely many Boolean base charts.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, monic plane zero-set case. -/
theorem s2v_t11b_monic_finite_base_triviality
    (P : Polynomial (Polynomial ℝ)) (hP : P.Monic) (hdegree : P.natDegree ≠ 0)
    (hres : P.resultant P.derivative ≠ 0) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula 1, ∃ b : Fin m → ℝ,
      (∀ t : ℝ, ∃! i, WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize) ∧
      ∀ i, ∃ e :
        ({x : ℝ | P.eval₂ (Polynomial.evalRingHom (b i)) x = 0} ×
          {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize}) ≃ₜ
        {z : {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize} × ℝ |
          P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0},
        ∀ y, (e y).val.1 = y.2 := by
  exact s2v_t11b_finite_base_triviality_of_resultant P hP.ne_zero hdegree hres

end HodgeLean.Foundations.Program
