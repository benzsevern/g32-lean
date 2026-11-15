import HodgeLean.Foundations.Program.G32Native.OriginalIdealSectionTransport
import HodgeLean.Foundations.Program.G32Native.AffineIdealSectionInclusion

/-! # Original equation sections in affine source and ambient coordinates -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.Algebraic

/-- Transport of a family of arrows into a fixed object.
Source: equality elimination in a category. -/
theorem familyArrow_eqToIso_comp {C : Type*} [Category C] {I : Type*}
    (M : I → C) (N : C) (f : ∀ i, M i ⟶ N) {i k : I} (h : i = k) :
    (eqToIso (congrArg M h)).hom ≫ f k = f i := by
  subst k
  exact Category.id_comp _

/-- Equality of immersion maps preserves the actual ideal inclusion.
Source: transport along equality of the original morphism. -/
theorem originalIdeal_hom_eq_inclusion {Q W : Scheme.{0}}
    (j k : Q ⟶ W) (h : j = k) :
    (eqToIso (congrArg Conormal.idealModule h)).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) := by
  exact familyArrow_eqToIso_comp (fun f : Q ⟶ W => Conormal.idealModule f)
    (SheafOfModules.unit W.ringCatSheaf)
    (fun f => kernel.ι (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) h

#print axioms originalIdeal_hom_eq_inclusion
end HodgeLean.Foundations.TubularEuler
