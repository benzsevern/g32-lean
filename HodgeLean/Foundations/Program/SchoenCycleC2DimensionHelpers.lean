import HodgeLean.Adapters.NormalConeB3Height
import HodgeLean.Adapters.KleimanExpectedCoheight
import HodgeLean.RealDefs.DegreeZero

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The point dimension formula uses the canonical dimension of a smooth
integral complex scheme. -/
theorem s2e_height_add_coheight_eq_dim
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (x : X.left) :
    Order.height x + Order.coheight x = dim X.left := by
  have hdim : dim X.left = (Order.height (genericPoint X.left)).toNat := by
    rw [TopologicalSpace.dim_eq_krullDim, ← Order.height_top_eq_krullDim]
    rfl
  rw [hdim]
  exact a3b3_height_add_coheight X.hom x

/-- An integral smooth subscheme of dimension `n` in a smooth integral
scheme of dimension `n + k` has generic-point coheight `k`. -/
theorem s2e_immersion_generic_coheight_of_dimensions
    {Q B : Over (Spec ↧ℂ)} [IsIntegral Q.left] [Smooth Q.hom]
    [IsIntegral B.left] [Smooth B.hom]
    (ι : Q ⟶ B) [IsClosedImmersion ι.left] (n k : ℕ)
    (hQ : dim Q.left = n) (hB : dim B.left = n + k) :
    Order.coheight (ι.left (genericPoint Q.left)) = k := by
  have h := s2e_height_add_coheight_eq_dim B (ι.left (genericPoint Q.left))
  have hheight := s2e_height_add_coheight_eq_dim Q (genericPoint Q.left)
  rw [HodgeLean.RealDefs.coheight_genericPoint, add_zero, hQ] at hheight
  rw [hc9k8_height_eq_of_isEmbedding ι.left ι.left.isClosedEmbedding.isEmbedding
    ι.left.isClosedEmbedding.isClosed_range, hheight, hB, Nat.cast_add] at h
  exact WithTop.add_left_cancel (ENat.natCast_ne_top n) h

end HodgeLean.Foundations.Program
