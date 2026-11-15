import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIdealGerm
import Mathlib.RingTheory.Localization.AtPrime.Basic

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Outside ideal support, its extension to the actual stalk is the unit ideal. -/
theorem s2v_l1b_divisor_ideal_germ_top
    (X : Scheme) (I : X.IdealSheafData) (U : X.affineOpens)
    (x : X) (hx : x ∈ U.1) (hn : x ∉ I.support) :
    (I.ideal U).map (X.presheaf.germ U.1 x hx).hom = ⊤ := by
  let P := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) P := U.2.isLocalization_stalk ⟨x, hx⟩
  apply IsLocalization.AtPrime.map_eq_top_of_not_le (S := X.presheaf.stalk x) (p := P)
  intro hle
  apply hn
  rw [I.mem_support_iff_of_mem hx]
  rw [X.mem_zeroLocus_iff]
  intro a ha hb
  have hPa : a ∈ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := hle ha
  rw [U.2.primeIdealOf_eq_map_closedPoint] at hPa
  change ¬ IsUnit ((X.presheaf.germ U.1 x hx).hom a) at hPa
  exact hPa ((X.mem_basicOpen a x hx).mp hb)

end HodgeLean.Foundations.Program
