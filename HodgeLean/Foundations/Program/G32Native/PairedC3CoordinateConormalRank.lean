import HodgeLean.Foundations.Program.G32Native.PairedC3PolynomialInclusionFrames

/-! # The number of discarded projective conormal coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Removing the retained projective coordinates leaves exactly the
codimension number of normal labels. -/
theorem paired_c3_coordinate_normal_card {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) :
    Fintype.card {j : Fin (n + 1) // j ∉ Set.range e} = n - k := by
  classical
  rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin,
    Fintype.card_fin]
  omega

/-- The standard-open conormal frame has the literal codimension rank. -/
def pairedC3PolynomialInclusionRankFrame {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    (Scheme.Modules.pullback (ProjSpace.standardOpen ℂ k i).ι).obj
        (s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)) ≅
      (SheafOfModules.free (R := (ProjSpace.standardOpen ℂ k i).toScheme.ringCatSheaf)
        (Fin (n - k)) : (ProjSpace.standardOpen ℂ k i).toScheme.Modules) := by
  classical
  exact pairedC3PolynomialInclusionOpenFrame e i ≪≫
    SheafOfModules.freeFunctor.mapIso
      (Fintype.equivFinOfCardEq (paired_c3_coordinate_normal_card e)).toIso

end HodgeLean.Foundations.Program.G32Native
