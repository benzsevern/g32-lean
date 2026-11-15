import HodgeLean.Foundations.RationalHomologyManifold.AmbientChainPresheaf

/-! Scalar multiples of an actual ambient chain in supported presheaves.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Project scalar multiples of a specified actual chain into the original supported-chain presheaf.
Source: Bredon, Sheaf Theory, second edition, VI.12; actual relative chain projection on each open support.
HC no distance; AV milestone no distance.
-/
def scalarChainPresheafMap (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X n) :
    TopCat.Presheaf.const X (AddCommGrpCat.of ℚ) ⟶ (singularChainPresheafComplex ℚ X).X n :=
  (Functor.const (Opens X)ᵒᵖ).map
    (AddCommGrpCat.ofHom (LinearMap.toSpanSingleton ℚ _ z).toAddMonoidHom) ≫
      ambientChainPresheafProjection X n

#print axioms scalarChainPresheafMap
/-- The original supported-chain differential sends the scalar chain section to the section of its actual ambient boundary.
Source: Hatcher, Algebraic Topology, section 2.1; naturality of relative chain projection.
HC no distance; AV milestone no distance.
-/
theorem scalarChainPresheafMap_boundary (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1)) :
    scalarChainPresheafMap X (n + 1) z ≫ (singularChainPresheafComplex ℚ X).d (n + 1) n =
      scalarChainPresheafMap X n ((SingularChainComplex ℚ X).d (n + 1) n z) := by
  apply NatTrans.ext
  funext U
  ext r
  change ℚ at r
  rw [singularChainPresheafComplex_d]
  let P := TopPair.ofSubset (X := X) (U.unop : Set X)ᶜ
  change ((relativeChainFunctor ℚ).obj P).d (n + 1) n
    ((relativeChainProjection ℚ P).f (n + 1) (r • z)) =
      (relativeChainProjection ℚ P).f n (r • (SingularChainComplex ℚ X).d (n + 1) n z)
  have h := ConcreteCategory.congr_hom ((relativeChainProjection ℚ P).comm (n + 1) n) (r • z)
  simp only [ConcreteCategory.comp_apply, map_smul] at h ⊢
  exact h

#print axioms scalarChainPresheafMap_boundary
end HodgeLean.Foundations.RationalHomologyManifold
