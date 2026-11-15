import HodgeLean.Foundations.Program.SchoenCommonDegreeProjective
import HodgeLean.Foundations.Program.SchoenGradingUniqueness

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

/-- Every graded subalgebra over the ambient degree zero retains that actual coefficient ring. -/
def s2_subalgebraDegreeZeroEquiv {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (R : Subalgebra (𝒜 0) A)
    [GradedRing (s2_subringGradedPiece 𝒜 R.toSubring)] :
    𝒜 0 ≃+* s2_subringGradedPiece 𝒜 R.toSubring 0 where
  toFun a := ⟨⟨a.val, R.algebraMap_mem a⟩, a.property⟩
  invFun a := ⟨a.val.val, a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite generators in one positive ambient degree give projectivity for the actual graded subalgebra. -/
theorem s2_subalgebra_projective_of_commonDegree {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (R : Subalgebra (𝒜 0) A)
    [g : GradedRing (s2_subringGradedPiece 𝒜 R.toSubring)]
    (M : ℕ) (hM : 0 < M) (n : ℕ) (w : Fin (n + 1) → A)
    (hw : ∀ i, w i ∈ 𝒜 M) (hgen : Algebra.adjoin (𝒜 0) (Set.range w) = R) :
    IsProjective (Proj.toSpecZero (s2_subringGradedPiece 𝒜 R.toSubring) ≫
      Spec.map (CommRingCat.ofHom (s2_subalgebraDegreeZeroEquiv 𝒜 R).toRingHom)) := by
  subst R
  have hg : g = s2_homogeneousAdjoinGrading 𝒜 (Set.range w)
      (by rintro _ ⟨i, rfl⟩; exact ⟨M, hw i⟩) := s2_gradedRing_eq _ _ _
  cases hg
  exact s2_commonDegreeAdjoin_original_projective 𝒜 M hM n w hw

end HodgeLean.Foundations.Program
