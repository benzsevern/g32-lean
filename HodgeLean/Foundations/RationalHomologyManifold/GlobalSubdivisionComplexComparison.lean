import HodgeLean.Foundations.RationalHomologyManifold.GlobalSubdivisionComparison

/-! Canonical global chain-complex comparison for the supported subdivision limit.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Actual sheafification on the global sections of the supported subdivision-limit chain complex.
Source: Bredon, Sheaf Theory, second edition, VI.12; the canonical global supported-chain comparison.
HC no distance; AV milestone no distance.
-/
def subdivisionGlobalSheafificationMap (X : TopCat.{0}) :
    (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op ⊤)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (subdivisionLimitPresheafComplex X) ⟶
    (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op ⊤)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (subdivisionLimitSheafComplex X)) where
  f n := (toSheafify (Opens.grothendieckTopology X)
    ((subdivisionLimitPresheafComplex X).X n)).app (Opposite.op ⊤)
  comm' i j hij := by
    have h := congrArg (fun f => f.app (Opposite.op ⊤))
      (toSheafify_naturality (Opens.grothendieckTopology X)
        ((subdivisionLimitPresheafComplex X).d i j))
    exact h.symm

#print axioms subdivisionGlobalSheafificationMap
/-- Canonical global sheafification of the actual supported subdivision-limit chain complex is an isomorphism on compact Hausdorff spaces.
Source: Bredon, Sheaf Theory, second edition, VI.12; the actual global supported-chain comparison.
HC no distance; AV milestone no distance.
-/
theorem subdivisionGlobalSheafificationMap_isIso (X : TopCat.{0})
    [CompactSpace X] [T2Space X] : IsIso (subdivisionGlobalSheafificationMap X) := by
  letI : ∀ n, IsIso ((subdivisionGlobalSheafificationMap X).f n) :=
    fun n => subdivisionLimit_global_sheafification_isIso X n
  exact HomologicalComplex.Hom.isIso_of_components _

#print axioms subdivisionGlobalSheafificationMap_isIso
end HodgeLean.Foundations.RationalHomologyManifold
