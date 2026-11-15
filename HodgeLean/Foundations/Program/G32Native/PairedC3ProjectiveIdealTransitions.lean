import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveIdealGenerators
import HodgeLean.Foundations.Program.G32Native.PairedC3IdealKernelSections
import HodgeLean.Foundations.Program.G32Native.PairedC3LocalModuleComparison

/-! # Original projective ideal generators on common subopens -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The categorical projective ideal generators change by the original
homogeneous denominator ratio on every common ambient subopen. -/
theorem paired_c3_projective_ideal_generator_transition {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i l : Fin (k + 1))
    (j : Fin (n + 1)) (hj : j ∉ Set.range e)
    (V : (pairedC3Proj n).Opens)
    (hi : V ≤ ProjSpace.standardOpen ℂ n (e i))
    (hl : V ≤ ProjSpace.standardOpen ℂ n (e l)) :
    pairedC3ModuleRestrict (s2c_idealModule (pairedC3PolynomialCoordinateInclusion (A := ℂ) e))
        hi (pairedC3ProjectiveIdealGenerator e i j hj) =
      (pairedC3Proj n).presheaf.map (homOfLE hi).op
        (ProjSpace.coordinateRatioSection ℂ n (e i) (e l)) •
      pairedC3ModuleRestrict (s2c_idealModule (pairedC3PolynomialCoordinateInclusion (A := ℂ) e))
        hl (pairedC3ProjectiveIdealGenerator e l j hj) := by
  apply (s2e_idealModule_sections_equiv (pairedC3PolynomialCoordinateInclusion (A := ℂ) e) V).injective
  rw [map_smul]
  apply Subtype.ext
  change ((s2e_idealModule_sections_equiv _ V)
    (pairedC3ModuleRestrict _ hi (pairedC3ProjectiveIdealGenerator e i j hj)) : Γ(pairedC3Proj n, V)) =
      (pairedC3Proj n).presheaf.map (homOfLE hi).op
        (ProjSpace.coordinateRatioSection ℂ n (e i) (e l)) *
      ((s2e_idealModule_sections_equiv _ V)
        (pairedC3ModuleRestrict _ hl (pairedC3ProjectiveIdealGenerator e l j hj)) : Γ(pairedC3Proj n, V))
  dsimp only [pairedC3ModuleRestrict, Scheme.Modules.presheaf]
  erw [s2e_idealModule_sections_equiv_restrict, s2e_idealModule_sections_equiv_restrict]
  simp only [pairedC3ProjectiveIdealGenerator, LinearEquiv.apply_symm_apply]
  exact (ProjSpace.coordinateRatioSection_mul ℂ n (e i) (e l) j hi hl).symm

end HodgeLean.Foundations.Program.G32Native
