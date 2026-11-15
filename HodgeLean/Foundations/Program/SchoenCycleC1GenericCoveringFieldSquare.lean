import HodgeLean.Foundations.Program.SchoenCycleC1DominantGenericPoint
import HodgeLean.Foundations.Program.SchoenCycleC1GenericStalkActionHelpers

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A commuting actual field-source square identifies the composite of the
specified generic pullback with the original covering-field embedding. -/
theorem s2e_c1_generic_covering_field_square
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f]
    (L : Type) [Field L] (ηX : Spec (CommRingCat.of L) ⟶ X)
    (ηY : Spec (CommRingCat.of L) ⟶ Y) (hη : ηX ≫ f = ηY)
    (φX : X.functionField →+* L) (φY : Y.functionField →+* L)
    (hX : Spec.map (CommRingCat.ofHom φX) ≫ X.fromSpecStalk (genericPoint X) = ηX)
    (hY : Spec.map (CommRingCat.ofHom φY) ≫ Y.fromSpecStalk (genericPoint Y) = ηY) :
    let hg := s2e_c1_dominant_generic_point f
    φX.comp (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
      f.stalkMap (genericPoint X)).hom = φY := by
  let hg := s2e_c1_dominant_generic_point f
  let ψ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
    f.stalkMap (genericPoint X)).hom
  have hsq : Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f := s2e_c1_genericStalkMap_square f hg
  have hc : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom φX = CommRingCat.ofHom φY := by
    apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecStalk (genericPoint Y))]
    rw [Spec.map_comp, Category.assoc, hsq,
      ← Category.assoc, hX, hη, hY]
  exact congrArg CommRingCat.Hom.hom hc

end HodgeLean.Foundations.Program
