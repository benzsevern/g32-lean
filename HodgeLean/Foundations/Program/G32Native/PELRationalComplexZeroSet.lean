import HodgeLean.Foundations.HodgeGroupAlgebraicDefs
import HodgeLean.Foundations.MatrixAlgGroupLieIdentityComponent

noncomputable section
namespace HodgeLean.Foundations
open MvPolynomial HodgeLean.Foundations.Program

/-- Extending coefficients identifies the rational and complex polynomial loci. -/
theorem pel_ratZeroSet_eq_complexZeroSet {n : ℕ}
    (S : Set (MvPolynomial (Fin n × Fin n) ℚ)) :
    g2_ratZeroSet S = g1_zeroSet (MvPolynomial.map (algebraMap ℚ ℂ) '' S) := by
  ext g
  change (∀ p ∈ S, aeval (g1_coords g) p = 0) ↔ _
  simp only [g1_zeroSet, Set.mem_ofPred_eq, Set.forall_mem_image,
    aeval_def, eval₂_eq_eval_map]

#print axioms pel_ratZeroSet_eq_complexZeroSet
end HodgeLean.Foundations
