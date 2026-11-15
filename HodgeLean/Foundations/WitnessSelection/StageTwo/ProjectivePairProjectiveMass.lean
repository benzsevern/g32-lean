import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Field

/-! Positive homogeneous mass of a finite complex coordinate vector.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.WitnessSelection.StageTwo

/-- Sum of squared coordinate norms used to normalize a projective representative.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
def s2e_pair_vectorMass {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

/-- A nonzero vector has positive homogeneous mass.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_vectorMass_pos {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (hv : v ≠ 0) : 0 < s2e_pair_vectorMass v := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  change v i ≠ 0 at hi
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
    (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i))

/-- Homogeneous mass scales by the squared norm of the scalar.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_vectorMass_smul {ι : Type*} [Fintype ι]
    (c : ℂ) (v : ι → ℂ) :
    s2e_pair_vectorMass (c • v) = Complex.normSq c * s2e_pair_vectorMass v := by
  simp only [s2e_pair_vectorMass, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Finset.mul_sum]

end HodgeLean.WitnessSelection.StageTwo
