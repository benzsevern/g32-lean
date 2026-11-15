import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairComplexPolynomialFormula
import HodgeLean.Foundations.Program.SchoenTowerHardtCad3FormulaTools
import Mathlib.RingTheory.Polynomial.Basic

/-! Finite Boolean descriptions of complex ideal zero loci.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace HodgeLean.WitnessSelection.StageTwo

/-- A complex polynomial ideal has an exact real Boolean zero-locus description.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_complex_ideal_formula {ι : Type*} [Fintype ι] {n : ℕ}
    (I : Ideal (MvPolynomial ι ℂ)) (r s : ι → MvPolynomial (Fin n) ℝ) :
    ∃ f : s2v_t11b_Formula n, ∀ x : EuclideanSpace ℝ (Fin n),
      x ∈ f.realize ↔ ∀ p ∈ I, MvPolynomial.eval (fun i =>
        (MvPolynomial.eval (fun j => x j) (r i) : ℂ) +
          (MvPolynomial.eval (fun j => x j) (s i) : ℂ) * Complex.I) p = 0 := by
  classical
  obtain ⟨G, hG⟩ := I.fg_of_isNoetherianRing
  have hex (g : G) := s2e_pair_complex_polynomial_formula g.val r s
  choose f hf using hex
  obtain ⟨F, hF⟩ := s2v_hardt_cad3_finite_inter f
  refine ⟨F, ?_⟩
  intro x
  rw [hF]
  constructor
  · intro hx
    let z : ι → ℂ := fun i =>
      (MvPolynomial.eval (fun j => x j) (r i) : ℂ) +
        (MvPolynomial.eval (fun j => x j) (s i) : ℂ) * Complex.I
    have hle : I ≤ RingHom.ker (MvPolynomial.eval z) := by
      rw [← hG]
      apply Ideal.span_le.mpr
      intro p hp
      exact (hf ⟨p, hp⟩ x).mp (hx ⟨p, hp⟩)
    intro p hp
    exact hle hp
  · intro hx g
    apply (hf g x).mpr
    apply hx g.val
    rw [← hG]
    exact Ideal.subset_span g.property

end HodgeLean.WitnessSelection.StageTwo
