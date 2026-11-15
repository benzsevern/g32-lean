import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairComplexIdealFormula
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! Boolean descriptions of polynomially parametrized affine Zariski loci.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace HodgeLean.WitnessSelection.StageTwo

/-- A Zariski closed affine locus has an exact Boolean description under complex polynomial coordinates.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_affine_closed_formula {ι : Type*} [Fintype ι] {n : ℕ}
    (C : Set (PrimeSpectrum (MvPolynomial ι ℂ))) (hC : IsClosed C)
    (r s : ι → MvPolynomial (Fin n) ℝ) :
    ∃ f : s2v_t11b_Formula n, ∀ x : EuclideanSpace ℝ (Fin n),
      x ∈ f.realize ↔
        PrimeSpectrum.comap (MvPolynomial.eval (fun i =>
          (MvPolynomial.eval (fun j => x j) (r i) : ℂ) +
            (MvPolynomial.eval (fun j => x j) (s i) : ℂ) * Complex.I))
          (⟨⊥, inferInstance⟩ : PrimeSpectrum ℂ) ∈ C := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal C).mp hC
  obtain ⟨f, hf⟩ := s2e_pair_complex_ideal_formula I r s
  refine ⟨f, ?_⟩
  intro x
  rw [hf]
  rfl

end HodgeLean.WitnessSelection.StageTwo
