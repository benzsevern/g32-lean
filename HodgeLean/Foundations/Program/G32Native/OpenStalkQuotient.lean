import HodgeLean.Ported.Hironaka.Scheme.IdealSheaf.StalkIdeal

/-! Actual quotient-stalk comparison for restriction of an ideal to an open. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Restriction to an open retains the quotient stalk as a ring. -/
def g32l4_comap_open_stalk_quotient_equiv {X : Scheme}
    (I : X.IdealSheafData) (U : X.Opens) (y : U.toScheme) :
    (X.presheaf.stalk (U.ι y) ⧸ I.stalkIdeal (U.ι y)) ≃+*
      (U.toScheme.presheaf.stalk y ⧸ (I.comap U.ι).stalkIdeal y) := by
  let e := (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv
  exact Ideal.quotientEquiv _ _ e (I.stalkIdeal_comap U.ι y)

/-- Quotient-stalk dimension drops are unchanged by restriction to an ambient open. -/
theorem g32l4_comap_open_stalk_dimension_drop_iff {X : Scheme}
    (I : X.IdealSheafData) (U : X.Opens) (y : U.toScheme) (r : ℕ) :
    (ringKrullDim (U.toScheme.presheaf.stalk y ⧸ (I.comap U.ι).stalkIdeal y) + r =
      ringKrullDim (U.toScheme.presheaf.stalk y)) ↔
    (ringKrullDim (X.presheaf.stalk (U.ι y) ⧸ I.stalkIdeal (U.ι y)) + r =
      ringKrullDim (X.presheaf.stalk (U.ι y))) := by
  have hq := ringKrullDim_eq_of_ringEquiv (g32l4_comap_open_stalk_quotient_equiv I U y)
  have ha := ringKrullDim_eq_of_ringEquiv
    (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv
  rw [← hq, ← ha]

end HodgeLean.Foundations.Program
