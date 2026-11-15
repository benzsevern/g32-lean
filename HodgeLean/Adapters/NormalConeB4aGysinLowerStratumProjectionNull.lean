import HodgeLean.Adapters.NormalConeB4aGysinLowerStrata
import HodgeLean.Adapters.NormalConeB4aGysinSmoothDimensionProjectionNull

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- Every canonical lower smooth stratum of the support has null parameter
image in the supplied ambient holomorphic chart. -/
theorem a3b4a_gysin_lower_stratum_parameter_image_null
    (Y : Over (Spec (CommRingCat.of ℂ))) [IsNoetherian Y.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (S : TopologicalSpace.Closeds Y.left) (n c : ℕ)
    (hdim : topologicalKrullDim (reducedClosedSubscheme S) ≤ (n : ℕ)) (k : ℕ)
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ) :
    let T := reducedSmoothClosedFiltration Y.hom S (k + 1)
    let A := Over.mk (reducedClosedSmoothPieceι Y.hom T ≫ Y.hom)
    let f : A ⟶ Y := Over.homMk (reducedClosedSmoothPieceι Y.hom T) rfl
    MeasureTheory.volume ((fun x => (Φ (Point.map f x)).1) ''
      (Point.map f ⁻¹' Φ.source)) = 0 := by
  let T := reducedSmoothClosedFiltration Y.hom S (k + 1)
  let A := Over.mk (reducedClosedSmoothPieceι Y.hom T ≫ Y.hom)
  let f : A ⟶ Y := Over.homMk (reducedClosedSmoothPieceι Y.hom T) rfl
  change MeasureTheory.volume ((fun x => (Φ (Point.map f x)).1) ''
    (Point.map f ⁻¹' Φ.source)) = 0
  letI : NoetherianSpace (reducedClosedSubscheme T) :=
    (reducedClosedSubschemeι T).isClosedEmbedding.isInducing.noetherianSpace
  letI : NoetherianSpace (reducedClosedSmoothPiece Y.hom T) :=
    (reducedClosedStructureMap Y.hom T).smoothLocus.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : NoetherianSpace A.left :=
    inferInstanceAs (NoetherianSpace (reducedClosedSmoothPiece Y.hom T))
  letI : Smooth A.hom :=
    inferInstanceAs (Smooth (reducedClosedSmoothPieceι Y.hom T ≫ Y.hom))
  letI : LocallyOfFiniteType A.hom :=
    inferInstanceAs (LocallyOfFiniteType (reducedClosedSmoothPieceι Y.hom T ≫ Y.hom))
  letI : QuasiCompact A.hom := inferInstance
  letI : IsSeparated A.hom :=
    inferInstanceAs (IsSeparated (reducedClosedSmoothPieceι Y.hom T ≫ Y.hom))
  exact a3b4a_gysin_smooth_dimension_parameter_image_null A Y n c f Φ hΦ
    (a3b4a_gysin_lower_smooth_stratum_dimension_lt Y.hom S n hdim k)

end HodgeLean.Adapters
