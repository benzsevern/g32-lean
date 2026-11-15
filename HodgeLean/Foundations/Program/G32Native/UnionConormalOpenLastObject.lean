import HodgeLean.Foundations.Program.G32Native.UnionConormalOpenPushforwardIso
import HodgeLean.Foundations.Program.G32Native.UnionConormalResLEConormal

/-! # The actual last object on compatible open charts -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Open direct image restriction and conormal restriction identify the last object. -/
def unionConormalOpenLastObjectIso
    {S Q W : Scheme.{0}} (f : S ⟶ Q) (i : S ⟶ W)
    (U : Q.Opens) (V : W.Opens) (hle : f ⁻¹ᵁ U ≤ i ⁻¹ᵁ V)
    (he : f ⁻¹ᵁ U = i ⁻¹ᵁ V) :
    (Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.pushforward f).obj (s2c_conormal i)) ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj
        (s2c_conormal (i.resLE V (f ⁻¹ᵁ U) hle)) :=
  unionConormalOpenPushforwardIso f U (s2c_conormal i) ≪≫
    (Scheme.Modules.pushforward (f ∣_ U)).mapIso
      (unionConormalResLEConormalIso i V (f ⁻¹ᵁ U) hle he)

end HodgeLean.Foundations.Program.G32Native
