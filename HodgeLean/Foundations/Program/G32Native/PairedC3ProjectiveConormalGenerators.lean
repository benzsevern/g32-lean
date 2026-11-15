import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveIdealTransitions
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Frames.PullbackFrame

/-! # Original conormal generator sections and their denominator transitions -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme.Modules.FramePullback
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The original ideal generator induces a section of the original
conormal by the pullback-pushforward adjunction unit. -/
def pairedC3ProjectiveConormalGenerator {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (j : Fin (n + 1)) (hj : j ∉ Set.range e) :
    Γ(s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e),
      pairedC3PolynomialCoordinateInclusion (A := ℂ) e ⁻¹ᵁ ProjSpace.standardOpen ℂ n (e i)) :=
  eta (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)
    (s2c_idealModule (pairedC3PolynomialCoordinateInclusion (A := ℂ) e))
    (ProjSpace.standardOpen ℂ n (e i)) (pairedC3ProjectiveIdealGenerator e i j hj)

/-- The actual conormal generators change by the pullback of the
original denominator ratio on every common ambient subopen. -/
theorem paired_c3_projective_conormal_generator_transition {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i l : Fin (k + 1))
    (j : Fin (n + 1)) (hj : j ∉ Set.range e)
    (V : (pairedC3Proj n).Opens)
    (hi : V ≤ ProjSpace.standardOpen ℂ n (e i))
    (hl : V ≤ ProjSpace.standardOpen ℂ n (e l)) :
    let p := pairedC3PolynomialCoordinateInclusion (A := ℂ) e
    pairedC3ModuleRestrict (s2c_conormal p) (p.preimage_mono hi)
        (pairedC3ProjectiveConormalGenerator e i j hj) =
      p.app V ((pairedC3Proj n).presheaf.map (homOfLE hi).op
        (ProjSpace.coordinateRatioSection ℂ n (e i) (e l))) •
      pairedC3ModuleRestrict (s2c_conormal p) (p.preimage_mono hl)
        (pairedC3ProjectiveConormalGenerator e l j hj) := by
  dsimp only
  let p := pairedC3PolynomialCoordinateInclusion (A := ℂ) e
  let M := s2c_idealModule p
  let a := (pairedC3Proj n).presheaf.map (homOfLE hi).op
    (ProjSpace.coordinateRatioSection ℂ n (e i) (e l))
  exact (res_eta p M hi (pairedC3ProjectiveIdealGenerator e i j hj)).trans
    ((congrArg (eta p M V)
      (paired_c3_projective_ideal_generator_transition e i l j hj V hi hl)).trans
      ((eta_smul p M V a (res M hl (pairedC3ProjectiveIdealGenerator e l j hj))).trans
        (congrArg (fun s => p.app V a • s)
          (res_eta p M hl (pairedC3ProjectiveIdealGenerator e l j hj)).symm)))

end HodgeLean.Foundations.Program.G32Native
