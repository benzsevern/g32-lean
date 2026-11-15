import HodgeLean.Adapters.NormalConeB4aGysinSupportRemainderDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.ClosedFiltration
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.SingularLocusDimension

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- Every smooth layer after the first in the actual support filtration has
dimension strictly below the original support bound. -/
theorem a3b4a_gysin_lower_smooth_stratum_dimension_lt
    {Z : Scheme.{0}} [IsNoetherian Z]
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    (S : Closeds Z) (n : ℕ)
    (hdim : topologicalKrullDim (reducedClosedSubscheme S) ≤ (n : ℕ)) (k : ℕ) :
    topologicalKrullDim (reducedClosedSmoothPiece q
      (reducedSmoothClosedFiltration q S (k + 1))) < (n : ℕ) := by
  have hT : reducedSmoothClosedFiltration q S (k + 1) ≤ reducedClosedSingularRemainder q S := by
    rw [reducedSmoothClosedFiltration_succ_start]
    exact reducedSmoothClosedFiltration_le q _ k
  have hs := a3b4a_gysin_support_remainder_dimension_lt q S n hdim
  rw [a3b4a_gysin_reduced_closed_dimension_eq] at hs
  exact (topologicalKrullDim_reducedClosedSmoothPiece_le q hT).trans_lt hs

/-- Every lower support stratum has smooth affine coordinate regions with
relative dimension strictly below the parameter dimension bound. -/
theorem a3b4a_gysin_lower_stratum_affine_dimension_bound
    {Z : Scheme.{0}} [IsNoetherian Z]
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    (S : Closeds Z) (n : ℕ)
    (hdim : topologicalKrullDim (reducedClosedSubscheme S) ≤ (n : ℕ)) (k : ℕ)
    (z : reducedClosedSmoothPiece q (reducedSmoothClosedFiltration q S (k + 1))) :
    ∃ (U : (reducedClosedSmoothPiece q
      (reducedSmoothClosedFiltration q S (k + 1))).Opens) (_ : IsAffineOpen U), z ∈ U ∧
      ∃ m : ℕ, m < n ∧ SmoothOfRelativeDimension m
        (U.ι ≫ reducedClosedSmoothPieceι q (reducedSmoothClosedFiltration q S (k + 1)) ≫ q) := by
  have hlt := a3b4a_gysin_lower_smooth_stratum_dimension_lt q S n hdim k
  obtain ⟨U, hU, hzU, m, hm, hstd⟩ :=
    Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
      (reducedClosedSmoothPieceι q (reducedSmoothClosedFiltration q S (k + 1)) ≫ q) hlt z
  refine ⟨U, hU, hzU, m, hm, ?_⟩
  exact smoothOfRelativeDimension_affineOpen_of_isStandardSmooth
    (reducedClosedSmoothPieceι q (reducedSmoothClosedFiltration q S (k + 1)) ≫ q) hU hstd

end HodgeLean.Adapters
