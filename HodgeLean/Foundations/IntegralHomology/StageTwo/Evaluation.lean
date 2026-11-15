import HodgeLean.Foundations.IntegralHomology.StageTwo.Defs
import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality

/-! Quotient evaluation and its functoriality over commutative rings.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

def shortPairing {R : Type} [CommRing R] (S : ShortComplex (ModuleCat R)) :
    S.linearDual.homology →ₗ[R] Module.Dual R S.homology :=
  S.moduleCatHomologyIso.toLinearEquiv.dualMap.toLinearMap.comp
    (S.dualHomologyComparisonExplicit.comp S.linearDual.moduleCatHomologyIso.hom.hom)

theorem shortPairing_classes {R : Type} [CommRing R] (S : ShortComplex (ModuleCat R))
    (u : LinearMap.ker S.f.hom.dualMap) (a : LinearMap.ker S.g.hom) :
    shortPairing S (S.linearDual.moduleCatHomologyClass u)
      (S.moduleCatHomologyClass a) = u.val a.val := by
  change S.dualHomologyComparisonExplicit
    (S.linearDual.moduleCatHomologyIso.hom
      (S.linearDual.moduleCatHomologyIso.inv (Submodule.Quotient.mk u)))
    (S.moduleCatHomologyIso.hom
      (S.moduleCatHomologyIso.inv (Submodule.Quotient.mk a))) = u.val a.val
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  rfl

theorem shortPairing_natural {R : Type} [CommRing R]
    {S T : ShortComplex (ModuleCat R)} (f : S ⟶ T)
    (u : T.linearDual.homology) (a : S.homology) :
    shortPairing S ((ShortComplex.homologyMap (ShortComplex.linearDualMap f)).hom u) a =
      shortPairing T u ((ShortComplex.homologyMap f).hom a) := by
  obtain ⟨u, rfl⟩ := T.linearDual.moduleCatHomologyClass_surjective u
  obtain ⟨a, rfl⟩ := S.moduleCatHomologyClass_surjective a
  rw [ShortComplex.moduleCatHomologyClass_naturality,
    ShortComplex.moduleCatHomologyClass_naturality,
    shortPairing_classes, shortPairing_classes]
  rfl

theorem evaluation_natural (R : Type) [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (u : Cohomology R Y 1) (a : Homology R X 1) :
    evaluation R X (cohomologyMap R 1 f u) a =
      evaluation R Y u (homologyMap R 1 f a) := by
  have h := congrArg (ShortComplex.homologyFunctor (ModuleCat R)).map
    (HomologicalComplex.linearDualCochainComplexScIso_naturality
      (singularChainComplexMap R f) 1)
  rw [Functor.map_comp, Functor.map_comp] at h
  have hu := ConcreteCategory.congr_hom h u
  change shortPairing ((SingularChainComplex R X).sc 1)
    (ShortComplex.homologyMap
      (HomologicalComplex.linearDualCochainComplexScIso (SingularChainComplex R X) 1).hom
      (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap
        (singularChainComplexMap R f)) 1 u)) a = _
  rw [show ShortComplex.homologyMap
      (HomologicalComplex.linearDualCochainComplexScIso (SingularChainComplex R X) 1).hom
      (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap
        (singularChainComplexMap R f)) 1 u) =
    ShortComplex.homologyMap
      (ShortComplex.linearDualMap ((HomologicalComplex.shortComplexFunctor (ModuleCat R)
        (.down ℕ) 1).map (singularChainComplexMap R f)))
      (ShortComplex.homologyMap
        (HomologicalComplex.linearDualCochainComplexScIso (SingularChainComplex R Y) 1).hom u)
    from hu]
  exact shortPairing_natural _ _ _
end HodgeLean.Foundations.IntegralHomology.StageTwo
