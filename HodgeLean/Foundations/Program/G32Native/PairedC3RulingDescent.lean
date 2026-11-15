import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Descent of a smooth marked ruling along its residual cover -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Compatible local ruling maps descend over the original base scheme. -/
def pairedC3RulingOfCover {S : Scheme} (X C : Over S)
    (U : X.left.OpenCover) (f : ∀ j, U.X j ⟶ C.left)
    (hf : ∀ j k, pullback.fst (U.f j) (U.f k) ≫ f j = pullback.snd _ _ ≫ f k)
    (hbase : ∀ j, f j ≫ C.hom = U.f j ≫ X.hom) : X ⟶ C :=
  Over.homMk (U.glueMorphisms f hf) (by
    apply U.hom_ext
    intro j
    rw [← Category.assoc, U.ι_glueMorphisms]
    exact hbase j)

/-- Smoothness of the chart maps gives smoothness of their descended ruling. -/
theorem pairedC3_ruling_of_cover_smooth {S : Scheme} (X C : Over S)
    (U : X.left.OpenCover) (f : ∀ j, U.X j ⟶ C.left)
    (hf : ∀ j k, pullback.fst (U.f j) (U.f k) ≫ f j = pullback.snd _ _ ≫ f k)
    (hbase : ∀ j, f j ≫ C.hom = U.f j ≫ X.hom)
    (hs : ∀ j, Smooth (f j)) : Smooth (pairedC3RulingOfCover X C U f hf hbase).left := by
  apply IsZariskiLocalAtSource.of_openCover U
  intro j
  change Smooth (U.f j ≫ U.glueMorphisms f hf)
  rw [U.ι_glueMorphisms]
  exact hs j

/-- The marked fibre squares descend along the same cover as the ruling.
The maps from the original intersection scheme are retained. -/
theorem pairedC3_ruling_of_cover_marked_square
    {S : Scheme} (X C : Over S) (U : X.left.OpenCover)
    (f : ∀ j, U.X j ⟶ C.left)
    (hf : ∀ j k, pullback.fst (U.f j) (U.f k) ≫ f j = pullback.snd _ _ ≫ f k)
    (hbase : ∀ j, f j ≫ C.hom = U.f j ≫ X.hom)
    {D T : Scheme} (a : D ⟶ T) (b : D ⟶ X.left) (c : T ⟶ C.left)
    (H : ∀ j, IsPullback (U.pullbackHom b j) ((U.pullback₁ b).f j ≫ a) (f j) c) :
    IsPullback a b c (pairedC3RulingOfCover X C U f hf hbase).left := by
  apply IsPullback.flip
  apply Scheme.isPullback_of_openCover b a _ c U
  intro j
  change IsPullback _ _ (U.f j ≫ U.glueMorphisms f hf) c
  rw [U.ι_glueMorphisms]
  exact H j

#print axioms pairedC3RulingOfCover
#print axioms pairedC3_ruling_of_cover_smooth
#print axioms pairedC3_ruling_of_cover_marked_square
end HodgeLean.Foundations.Program.G32Native
