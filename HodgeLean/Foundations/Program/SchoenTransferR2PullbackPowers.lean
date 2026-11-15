import HodgeLean.Foundations.Program.SchoenTransferR2ExceptionalRestriction

/-! # Pullbacks of actual endomorphism powers

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Actual endomorphism powers pull back to powers of the cohomology operator.
Source: Hatcher, Algebraic Topology, §3.1, functoriality of singular cohomology.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_pullback_pow
    (R : Type) [CommRing R] {W : Over (Spec ↧ℂ)} (d : W ⟶ W) (n i : ℕ) :
    s2e_pullback R (End.of d ^ i).asHom n = (s2e_pullback R d n) ^ i := by
  induction i with
  | zero =>
    change cohomologyMap R n (𝟙 (TopCat.of (ComplexPoint W))) = 1
    rw [cohomologyMap_id]
    rfl
  | succ i hi =>
    have he : (End.of d ^ (i + 1)).asHom = (End.of d ^ i).asHom ≫ d := by
      rw [pow_succ']
      rfl
    rw [he, s4_assembly_pullback_comp, hi, pow_succ]
    rfl

#print axioms s4_assembly_pullback_pow
end HodgeLean.Foundations.Program
