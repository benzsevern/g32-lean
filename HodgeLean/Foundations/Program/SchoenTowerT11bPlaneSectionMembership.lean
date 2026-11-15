import HodgeLean.Foundations.Program.SchoenTowerT11bPlaneEncoding
import HodgeLean.Foundations.Program.SchoenTowerT11bBooleanSections

/-! Actual Boolean membership along plane polynomial root sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Divisibility and common-root resultants give constant membership of a plane Boolean formula along a root section.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, sign-invariant section step. -/
theorem s2v_t11b_plane_formula_constant_on_root_section
    (P : Polynomial (Polynomial ℝ)) (hdegree : P.natDegree ≠ 0)
    (f : s2v_t11b_Formula 2) (K : Set ℝ) (hK : IsPreconnected K)
    (ψ : K → ℝ) (hψ : Continuous ψ)
    (hroot : ∀ t : K, P.eval₂ (Polynomial.evalRingHom t.val) (ψ t) = 0)
    (hres : ∀ q ∈ f.atoms, ¬ P ∣ s2v_t11b_planeFamilyPolynomial q →
      ∀ t ∈ K, (P.resultant (s2v_t11b_planeFamilyPolynomial q)).eval t ≠ 0)
    (a b : K) :
    WithLp.toLp 2 ![ψ a, a.val] ∈ f.realize ↔
      WithLp.toLp 2 ![ψ b, b.val] ∈ f.realize := by
  let Ψ : K → EuclideanSpace ℝ (Fin 2) := fun t => WithLp.toLp 2 ![ψ t, t.val]
  have hΨ : Continuous Ψ := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact hψ
    · exact continuous_subtype_val
  apply s2v_t11b_formula_constant_on_section f K hK Ψ hΨ ?_ a b
  intro q hq
  by_cases hd : P ∣ s2v_t11b_planeFamilyPolynomial q
  · left
    intro t
    have hzero := s2v_t11b_family_eval_zero_of_dvd P (s2v_t11b_planeFamilyPolynomial q)
      hd t.val (ψ t) (hroot t)
    exact (s2v_t11b_eval_planeFamilyPolynomial q (Ψ t)).symm.trans hzero
  · right
    intro t hz
    have hzero := (s2v_t11b_eval_planeFamilyPolynomial q (Ψ t)).trans hz
    exact hres q hq hd t.val t.property
      (s2v_t11b_family_common_root_resultant P (s2v_t11b_planeFamilyPolynomial q)
        (Or.inl hdegree) t.val (ψ t) (hroot t) hzero)

end HodgeLean.Foundations.Program
