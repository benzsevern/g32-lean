import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainGlobalUnit

/-! Actual global ambient restriction is the original singular sheaf comparison.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual constant ambient section followed by local restriction is exactly the original singular-to-global-cochain-sheaf comparison.
Source: Bredon, Sheaf Theory, second edition, VI.12; normalization of actual singular sheafification on the whole space.
HC no distance; AV milestone no distance.
-/
theorem ambientCochainGlobalUnit_restriction (X : TopCat.{0}) :
    ambientCochainGlobalUnit X ≫
      ((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map
        (ambientCochainSheafRestriction X) =
      HodgeLean.Foundations.Program.singularGlobalComparison X := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  change AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p at φ
  have h₀ := congrArg (fun f => f.app (op (⊤ : Opens X)))
    (toSheafify_naturality (Opens.grothendieckTopology X) (ambientCochainPresheafRestriction X p))
  have h := congrArg (fun g => AddCommGrpCat.Hom.hom g φ) h₀
  exact h.symm.trans (HodgeLean.Foundations.Program.singularGlobalComparison_apply X p φ).symm

#print axioms ambientCochainGlobalUnit_restriction
end HodgeLean.Foundations.RationalHomologyManifold
