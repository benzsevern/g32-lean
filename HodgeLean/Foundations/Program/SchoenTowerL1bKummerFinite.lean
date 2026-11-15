import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A dominant map induces the pullback between the actual generic stalks. -/
def s2v_l1b_functionFieldPullback {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : Y.functionField ⟶ X.functionField :=
  eqToHom (congrArg (fun y => Y.presheaf.stalk y) (s2_dominant_genericPoint f).symm) ≫
    f.stalkMap (genericPoint X)

example {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] :
    Function.Injective (s2v_l1b_functionFieldPullback f).hom :=
  (s2v_l1b_functionFieldPullback f).hom.injective

/-- A dominant locally quasi-finite morphism gives a finite extension of the actual function fields. -/
theorem s2v_l1b_functionFieldPullback_finite
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [LocallyQuasiFinite f] :
    letI := (s2v_l1b_functionFieldPullback f).hom.toAlgebra
    Module.Finite Y.functionField X.functionField := by
  let e : Y.functionField ⟶ Y.presheaf.stalk (f (genericPoint X)) :=
    eqToHom (congrArg (fun y => Y.presheaf.stalk y) (s2_dominant_genericPoint f).symm)
  have he : e.hom.QuasiFinite := RingHom.QuasiFinite.of_finite
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso e).surjective)
  have hq : (s2v_l1b_functionFieldPullback f).hom.QuasiFinite :=
    (f.quasiFiniteAt (genericPoint X)).comp he
  letI := (s2v_l1b_functionFieldPullback f).hom.toAlgebra
  haveI : Algebra.QuasiFinite Y.functionField X.functionField := hq
  exact Module.Finite.of_quasiFinite

/-- The actual field pullback recovers the original morphism on generic spectra. -/
theorem s2v_l1b_functionFieldPullback_generic_square
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] :
    Spec.map (s2v_l1b_functionFieldPullback f) ≫
      Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk (genericPoint X) ≫ f := by
  have ht (z : Y) (hz : z = genericPoint Y) :
      Spec.map (eqToHom (congrArg (fun y => Y.presheaf.stalk y) hz.symm)) ≫
        Y.fromSpecStalk (genericPoint Y) = Y.fromSpecStalk z := by
    subst z
    simp only [eqToHom_refl, Spec.map_id, Category.id_comp]
  dsimp only [s2v_l1b_functionFieldPullback]
  rw [Spec.map_comp, Category.assoc, ht _ (s2_dominant_genericPoint f)]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk f

end HodgeLean.Foundations.Program
