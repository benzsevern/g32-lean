import HodgeLean.Foundations.Program.G32Native.UnionConormalOpenPushforwardValue

/-! # Direct image composition in the ambient restriction square -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The two composed direct images in an ambient restriction square agree. -/
def unionConormalOpenDirectImageSquareIso {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
    (Scheme.Modules.pushforwardComp (f ∣_ U) U.ι).symm

end HodgeLean.Foundations.Program.G32Native
