import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionLimit

/-! Actual ambient chain projection as a morphism of supported presheaves.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Ambient singular chains project naturally to the relative chains supported on each open set.
Source: Bredon, Sheaf Theory, second edition, VI.12; the supported-chain presheaf.
HC no distance; AV milestone no distance.
-/
def ambientChainPresheafProjection (X : TopCat.{0}) (n : ℕ) :
    (Functor.const (Opens X)ᵒᵖ).obj
      ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj ((SingularChainComplex ℚ X).X n)) ⟶
      (singularChainPresheafComplex ℚ X).X n where
  app U := (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
    ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U.unop : Set X)ᶜ)).f n)
  naturality {U V} f := by
    let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
    let P := TopPair.ofSubset (X := X) (U.unop : Set X)ᶜ
    let Q := TopPair.ofSubset (X := X) (V.unop : Set X)ᶜ
    let a := supportInclusionPairMap X (leOfHom f.unop)
    change F.map ((relativeChainProjection ℚ Q).f n) =
      F.map ((relativeChainProjection ℚ P).f n) ≫ F.map (((relativeChainFunctor ℚ).map a).f n)
    rw [← F.map_comp]
    have h := TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) a
    change relativeChainProjection ℚ P ≫ (relativeChainFunctor ℚ).map a =
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map (𝟙 X)) ≫
        relativeChainProjection ℚ Q at h
    rw [(((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ))).map_id, Category.id_comp] at h
    have hn := congrArg (fun f => f.f n) h
    change (relativeChainProjection ℚ P).f n ≫ ((relativeChainFunctor ℚ).map a).f n =
      (relativeChainProjection ℚ Q).f n at hn
    exact congrArg F.map hn.symm

#print axioms ambientChainPresheafProjection
end HodgeLean.Foundations.RationalHomologyManifold
