import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalSourceTransitions

/-! # Actual conormal generators on literal source standard opens -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The intrinsic conormal generator on its literal original source open. -/
def pairedC3ConormalStandardGenerator {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (j : Fin (n + 1)) (hj : j ∉ Set.range e) :
    Γ(s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e),
      ProjSpace.standardOpen ℂ k i) :=
  pairedC3ModuleRestrict _ (paired_c3_coordinate_inclusion_preimage_basicOpen (A := ℂ) e i).ge
    (pairedC3ProjectiveConormalGenerator e i j hj)

/-- The original conormal classes have the native negative-line
transition, on every literal source subopen where both frames are available. -/
theorem paired_c3_conormal_standard_generator_transition {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i l : Fin (k + 1))
    (j : Fin (n + 1)) (hj : j ∉ Set.range e)
    (T : (pairedC3Proj k).Opens)
    (hi : T ≤ ProjSpace.standardOpen ℂ k i)
    (hl : T ≤ ProjSpace.standardOpen ℂ k l) :
    pairedC3ModuleRestrict (s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)) hi
        (pairedC3ConormalStandardGenerator e i j hj) =
      (pairedC3Proj k).presheaf.map (homOfLE hi).op
        (ProjSpace.coordinateRatioSection ℂ k i l) •
      pairedC3ModuleRestrict (s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)) hl
        (pairedC3ConormalStandardGenerator e l j hj) := by
  let p := pairedC3PolynomialCoordinateInclusion (A := ℂ) e
  let hi' := hi.trans (paired_c3_coordinate_inclusion_preimage_basicOpen (A := ℂ) e i).ge
  let hl' := hl.trans (paired_c3_coordinate_inclusion_preimage_basicOpen (A := ℂ) e l).ge
  have h := paired_c3_projective_conormal_source_transition e i l j hj T hi' hl'
  have hc := congrArg ((pairedC3Proj k).presheaf.map (homOfLE hi).op)
    (paired_c3_projective_inclusion_retained_section e i l)
  change (p.appLE _ _ _ ≫ (pairedC3Proj k).presheaf.map (homOfLE hi).op)
      (ProjSpace.coordinateRatioSection ℂ n (e i) (e l)) = _ at hc
  rw [Scheme.Hom.appLE_map] at hc
  dsimp only [pairedC3ConormalStandardGenerator]
  rw [paired_c3_module_restrict_comp, paired_c3_module_restrict_comp]
  dsimp only at h
  dsimp only [p] at hc
  rw [hc] at h
  exact h

end HodgeLean.Foundations.Program.G32Native
