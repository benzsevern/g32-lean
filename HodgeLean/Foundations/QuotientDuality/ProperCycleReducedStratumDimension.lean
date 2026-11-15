import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.ClosedFiltration
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.SingularLocusDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.AffineRelativeDimension

/-! # Dimension bounds on actual reduced smooth strata without ambient smoothness -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Every actual reduced smooth stratum of a dimension-bounded closed support has affine complex charts of bounded relative dimension.
Source: EGA IV, 17.11.1, local standard smooth presentations;
Hartshorne, Algebraic Geometry, II.3, dimension of locally closed subschemes.
HC no distance; AV milestone no distance. -/
lemma properCycle_reduced_stratum_affine_relativeDimension_le
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (S : Closeds X.left) (d : ℕ) (hdim : topologicalKrullDim S ≤ d) (k : ℕ)
    (z : reducedClosedSmoothPiece X.hom (reducedSmoothClosedFiltration X.hom S k)) :
    ∃ (U : (reducedClosedSmoothPiece X.hom (reducedSmoothClosedFiltration X.hom S k)).Opens)
      (_ : IsAffineOpen U), z ∈ U ∧ ∃ m : ℕ, m ≤ d ∧
        SmoothOfRelativeDimension m
          (U.ι ≫ reducedClosedSmoothPieceι X.hom (reducedSmoothClosedFiltration X.hom S k) ≫ X.hom) := by
  have hpiece : topologicalKrullDim
      (reducedClosedSmoothPiece X.hom (reducedSmoothClosedFiltration X.hom S k)) < (d + 1 : ℕ) := by
    calc
      _ ≤ topologicalKrullDim S := topologicalKrullDim_reducedClosedSmoothPiece_le X.hom
        (reducedSmoothClosedFiltration_le X.hom S k)
      _ ≤ (d : ℕ) := hdim
      _ < (d + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self d
  obtain ⟨U, hU, hzU, m, hm, hstd⟩ :=
    Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
      (reducedClosedSmoothPieceι X.hom (reducedSmoothClosedFiltration X.hom S k) ≫ X.hom) hpiece z
  exact ⟨U, hU, hzU, m, by omega,
    smoothOfRelativeDimension_affineOpen_of_isStandardSmooth _ hU hstd⟩

end HodgeLean.Foundations.QuotientDuality
