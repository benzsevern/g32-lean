import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.CompactModel
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.TruncationTransfer

/-! Pointed bases on actual finite real polynomial equation carriers.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
open Topology TopologicalSpace
namespace HodgeLean.Foundations.ComplexTopology

lemma realPolynomial_basis {n m : ℕ} (a b : Fin m → MvPolynomial (Fin n) ℝ)
    (x : realPolynomialCarrier a b) (U : Opens (realPolynomialCarrier a b)) (hxU : x ∈ U) :
    ∃ V : Opens (realPolynomialCarrier a b),
      x ∈ V ∧ ContractibleSpace V ∧ V ≤ U := by
  obtain ⟨K, hK, ⟨h⟩⟩ := polynomial_truncation_triangulation a b x.val (r := 1) zero_le_one
  exact basis_of_triangulated_truncation (realPolynomialCarrier a b) x zero_lt_one K hK h U hxU

end HodgeLean.Foundations.ComplexTopology
