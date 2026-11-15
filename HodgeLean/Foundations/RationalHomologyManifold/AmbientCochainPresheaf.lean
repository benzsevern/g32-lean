import HodgeLean.Foundations.Program.SingularGlobalPullback
import HodgeLean.Foundations.RationalHomologyManifold.LocalZeroCochains

/-! The actual presheaf restriction from ambient singular cochains to local singular cochains.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Restrict actual ambient cochains to each open subset in the existing singular cochain presheaf.
Source: Bredon, Sheaf Theory, second edition, VI.12; the constant-ambient to local singular cochain morphism.
HC no distance; AV milestone no distance.
-/
def ambientCochainPresheafRestriction (X : TopCat.{0}) (p : ℕ) :
    (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (Cochain ℚ (TopCat.toSSet.obj X) p)) ⟶
      singularCochainPresheaf ℚ X p where
  app U := AddCommGrpCat.ofHom
    (((singularChainComplexMap ℚ (Opens.inclusion' U.unop)).f p).hom.dualMap.toAddMonoidHom)
  naturality {U V} i := by
    ext φ
    change Cochain ℚ (TopCat.toSSet.obj X) p at φ
    apply LinearMap.ext
    intro c
    let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
    change φ (((F.map (Opens.inclusion' V.unop)).f p).hom c) =
      φ (((F.map (Opens.inclusion' U.unop)).f p).hom
        (((F.map ((Opens.toTopCat X).map i.unop)).f p).hom c))
    exact congrArg (fun f => φ ((f.f p).hom c))
      (F.map_comp ((Opens.toTopCat X).map i.unop) (Opens.inclusion' U.unop))

#print axioms ambientCochainPresheafRestriction
/-- Restriction from actual ambient cochains commutes with the existing local coboundary.
Source: Hatcher, Algebraic Topology, section 3.1; naturality of the singular coboundary.
HC no distance; AV milestone no distance.
-/
theorem ambientCochainPresheafRestriction_coboundary (X : TopCat.{0}) (p : ℕ) :
    (Functor.const (Opens X)ᵒᵖ).map (AddCommGrpCat.ofHom ((coboundary ℚ p).toAddMonoidHom)) ≫
        ambientCochainPresheafRestriction X (p + 1) =
      ambientCochainPresheafRestriction X p ≫ singularCochainCoboundary ℚ X p := by
  apply NatTrans.ext
  funext U
  ext φ
  change Cochain ℚ (TopCat.toSSet.obj X) p at φ
  apply LinearMap.ext
  intro c
  have h := (singularChainComplexMap ℚ (Opens.inclusion' U.unop)).comm (p + 1) p
  exact congrArg (fun f => φ (f.hom c)) h

#print axioms ambientCochainPresheafRestriction_coboundary
end HodgeLean.Foundations.RationalHomologyManifold
