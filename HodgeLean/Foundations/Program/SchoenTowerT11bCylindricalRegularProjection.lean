import HodgeLean.Foundations.Program.SchoenTowerT11bCylindricalFormulaCoordinates
import HodgeLean.Foundations.Program.SchoenTowerT11bParameterRegularity
import Mathlib.RingTheory.MvPolynomial.Basic

/-! Actual Boolean projection charts away from a specified polynomial exceptional locus.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
attribute [local instance] s2v_t11b_mvParameterNormalization

/-- Every Boolean formula has actual-fiber cylindrical charts on connected base regions avoiding one nonzero polynomial.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, regular cylindrical decomposition step. -/
theorem s2v_t11b_cylindrical_formula_off_exceptional {n : ℕ}
    (f : s2v_t11b_Formula (n + 1)) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ (K : Set (EuclideanSpace ℝ (Fin n))), IsPreconnected K → ∀ a : K,
      (∀ t ∈ K, MvPolynomial.eval (fun i => t i) D ≠ 0) →
      ∃ F : ({x : ℝ | WithLp.toLp 2 (Fin.cons x (fun i => a.val i)) ∈ f.realize} × K) ≃ₜ
          {z : K × ℝ | WithLp.toLp 2 (Fin.cons z.2 (fun i => z.1.val i)) ∈ f.realize},
        ∀ y, (F y).val.1 = y.2 := by
  let P := MvPolynomial.finSuccEquiv ℝ n (s2v_t11b_boundaryPolynomial f)
  obtain ⟨D, hD, hregular⟩ := s2v_t11b_parameter_exceptional_polynomial P
  refine ⟨D, hD, ?_⟩
  intro K hK a havoid
  exact s2v_t11b_cylindrical_formula_regular_chart f P
    (s2v_t11b_finSucc_carrier_ne_zero f) (s2v_t11b_finSucc_atom_dvd_carrier f) K hK a
    (fun t ht => (hregular (MvPolynomial.eval (fun i => t i)) (havoid t ht)).1)
    (fun t ht => (hregular (MvPolynomial.eval (fun i => t i)) (havoid t ht)).2)

end HodgeLean.Foundations.Program
