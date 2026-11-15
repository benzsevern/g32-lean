import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateConormalRank

/-! # Standard-open frames for the original initial coordinate inclusion -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Coordinate conormal frames allow an arbitrary nonempty ambient
coordinate count, retaining the original polynomial projective morphism. -/
def pairedC3PolynomialInclusionCountFrame {m k : ℕ}
    (e : Fin (k + 1) ↪ Fin m) (i : Fin (k + 1)) :
    (Scheme.Modules.pullback (ProjSpace.standardOpen ℂ k i).ι).obj
        (s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)) ≅
      (SheafOfModules.free (R := (ProjSpace.standardOpen ℂ k i).toScheme.ringCatSheaf)
        (Fin (m - (k + 1))) : (ProjSpace.standardOpen ℂ k i).toScheme.Modules) := by
  cases m with
  | zero => exact Fin.elim0 (e 0)
  | succ n =>
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_add_right] using
      pairedC3PolynomialInclusionRankFrame e i

/-- On every literal source standard open the initial coordinate
inclusion has an actual conormal frame of rank r minus one. -/
def pairedC3InitialCoordinateOpenFrame (k r : ℕ) (hr : 0 < r) (i : Fin (k + 1)) :
    (Scheme.Modules.pullback (ProjSpace.standardOpen ℂ k i).ι).obj
        (s2c_conormal (pairedC3InitialCoordinateInclusion k r hr)) ≅
      (SheafOfModules.free (R := (ProjSpace.standardOpen ℂ k i).toScheme.ringCatSheaf)
        (Fin (r - 1)) : (ProjSpace.standardOpen ℂ k i).toScheme.Modules) := by
  let e := pairedC3InitialCoordinateEmbedding k r hr
  let p := pairedC3PolynomialCoordinateInclusion (A := ℂ) e
  let a := s2_polynomialProjectiveSpaceIso ℂ (Fin (k + r))
  have h : k + r - (k + 1) = r - 1 := by omega
  exact (Scheme.Modules.pullback (ProjSpace.standardOpen ℂ k i).ι).mapIso
      (s2e_ambientIsoConormalIso p a.hom) ≪≫
    pairedC3PolynomialInclusionCountFrame e i ≪≫
    SheafOfModules.freeFunctor.mapIso (Equiv.cast (congrArg Fin h)).toIso

end HodgeLean.Foundations.Program.G32Native
