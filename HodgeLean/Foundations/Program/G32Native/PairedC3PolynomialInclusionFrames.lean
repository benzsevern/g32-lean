import HodgeLean.Foundations.Program.G32Native.PairedC3NormalizedCoordinateChart
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateChartConormal
import HodgeLean.Foundations.AlgebraicGeometry.ConormalBaseChange

/-! # Frames of the original projective conormal on its standard source charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Restricting the actual projective conormal to a standard source
affine chart gives the discarded-coordinate frame by flat chart base change. -/
def pairedC3PolynomialInclusionChartFrame {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    let b := Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)
      (isHomogeneous_X ℂ i) zero_lt_one
    (Scheme.Modules.pullback b).obj (s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)) ≅
      (SheafOfModules.free (R := (Spec (CommRingCat.of
        (Away (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)))).ringCatSheaf)
          {j : Fin (n + 1) // j ∉ Set.range e} :
            (Spec (CommRingCat.of (Away (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)))).Modules) := by
  let f := pairedC3PolynomialCoordinateInclusion (A := ℂ) e
  let φ := Spec.map (CommRingCat.ofHom (pairedC3CoordinateChartMap e i))
  let a := Proj.awayι (homogeneousSubmodule (Fin (n + 1)) ℂ) (X (e i))
    (isHomogeneous_X ℂ (e i)) zero_lt_one
  let b := Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)
    (isHomogeneous_X ℂ i) zero_lt_one
  letI : IsClosedImmersion f := paired_c3_polynomial_coordinate_inclusion_immersion e
  letI : IsClosedImmersion φ := IsClosedImmersion.spec_of_surjective _
    (paired_c3_coordinate_chart_map_surjective e i)
  exact Conormal.flatBaseChangeIso f φ a b
    (paired_c3_normalized_coordinate_chart_isPullback e i).flip ≪≫
      pairedC3CoordinateChartConormalFrame e i

/-- The same frame on the literal standard open of the source scheme,
rather than only on its isomorphic affine spectrum. -/
def pairedC3PolynomialInclusionOpenFrame {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    (Scheme.Modules.pullback (ProjSpace.standardOpen ℂ k i).ι).obj
        (s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)) ≅
      (SheafOfModules.free (R := (ProjSpace.standardOpen ℂ k i).toScheme.ringCatSheaf)
        {j : Fin (n + 1) // j ∉ Set.range e} : (ProjSpace.standardOpen ℂ k i).toScheme.Modules) := by
  let G := homogeneousSubmodule (Fin (k + 1)) ℂ
  let U := ProjSpace.standardOpen ℂ k i
  let E := Proj.basicOpenIsoSpec G (X i) (isHomogeneous_X ℂ i) zero_lt_one
  let M := s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)
  let H : (Scheme.Modules.pullback E.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅
      SheafOfModules.free (R := (Spec (CommRingCat.of (Away G (X i)))).ringCatSheaf)
        {j : Fin (n + 1) // j ∉ Set.range e} :=
    (Scheme.Modules.pullbackComp E.inv U.ι).app M ≪≫ pairedC3PolynomialInclusionChartFrame e i
  exact s2e_freeOfPullbackIso E.symm _ _ H

end HodgeLean.Foundations.Program.G32Native
