import HodgeLean.Foundations.Program.SchoenCycleC2OpenConormalRestrictionHelpers

/-! # Conormal restriction with an explicitly specified inverse image open -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Equality with the inverse image open identifies conormal restriction for resLE. -/
def unionConormalResLEConormalIso
    {Q W : Scheme.{0}} (i : Q ⟶ W) (U : W.Opens) (V : Q.Opens)
    (hle : V ≤ i ⁻¹ᵁ U) (he : V = i ⁻¹ᵁ U) :
    Scheme.Modules.restrict (s2c_conormal i) V.ι ≅ s2c_conormal (i.resLE U V hle) := by
  subst V
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact s2e_conormal_restrict_ambient_open_iso i U

end HodgeLean.Foundations.Program.G32Native
