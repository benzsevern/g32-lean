import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveConormalGenerators
import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveRetainedSections

/-! # Denominator transitions on source subopens of the projective immersion -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The original conormal transition holds on any source subopen where
both denominators are available, using the actual structural section map. -/
theorem paired_c3_projective_conormal_source_transition {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i l : Fin (k + 1))
    (j : Fin (n + 1)) (hj : j ∉ Set.range e)
    (T : (pairedC3Proj k).Opens)
    (hi : T ≤ pairedC3PolynomialCoordinateInclusion (A := ℂ) e ⁻¹ᵁ
      ProjSpace.standardOpen ℂ n (e i))
    (hl : T ≤ pairedC3PolynomialCoordinateInclusion (A := ℂ) e ⁻¹ᵁ
      ProjSpace.standardOpen ℂ n (e l)) :
    let p := pairedC3PolynomialCoordinateInclusion (A := ℂ) e
    pairedC3ModuleRestrict (s2c_conormal p) hi
        (pairedC3ProjectiveConormalGenerator e i j hj) =
      p.appLE (ProjSpace.standardOpen ℂ n (e i)) T hi
        (ProjSpace.coordinateRatioSection ℂ n (e i) (e l)) •
      pairedC3ModuleRestrict (s2c_conormal p) hl
        (pairedC3ProjectiveConormalGenerator e l j hj) := by
  dsimp only
  let p := pairedC3PolynomialCoordinateInclusion (A := ℂ) e
  let M := s2c_conormal p
  let V := ProjSpace.standardOpen ℂ n (e i) ⊓ ProjSpace.standardOpen ℂ n (e l)
  have ht : T ≤ p ⁻¹ᵁ V := le_inf hi hl
  let a := (pairedC3Proj n).presheaf.map (homOfLE (inf_le_left : V ≤ _)).op
    (ProjSpace.coordinateRatioSection ℂ n (e i) (e l))
  have h := congrArg (pairedC3ModuleRestrict M ht)
    (paired_c3_projective_conormal_generator_transition e i l j hj V inf_le_left inf_le_right)
  change pairedC3ModuleRestrict M ht (pairedC3ModuleRestrict M (p.preimage_mono inf_le_left)
      (pairedC3ProjectiveConormalGenerator e i j hj)) =
    pairedC3ModuleRestrict M ht (p.app V a • pairedC3ModuleRestrict M (p.preimage_mono inf_le_right)
      (pairedC3ProjectiveConormalGenerator e l j hj)) at h
  have hs := M.map_smul (homOfLE ht) (p.app V a)
    (pairedC3ModuleRestrict M (p.preimage_mono inf_le_right)
      (pairedC3ProjectiveConormalGenerator e l j hj))
  rw [hs, paired_c3_module_restrict_comp, paired_c3_module_restrict_comp] at h
  have hc : (pairedC3Proj k).presheaf.map (homOfLE ht).op (p.app V a) =
      p.appLE (ProjSpace.standardOpen ℂ n (e i)) T hi
        (ProjSpace.coordinateRatioSection ℂ n (e i) (e l)) := by
    exact congrArg (fun φ => φ (ProjSpace.coordinateRatioSection ℂ n (e i) (e l)))
      (p.map_appLE ht (homOfLE (inf_le_left : V ≤ _)).op)
  rw [hc] at h
  exact h

end HodgeLean.Foundations.Program.G32Native
