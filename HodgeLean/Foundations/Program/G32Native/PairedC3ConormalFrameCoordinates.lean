import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalStandardGenerators
import HodgeLean.Foundations.Program.G32Native.PairedC3FiniteFrameCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3MatchingCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeLineCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3ProductSections

/-! # Comparing original normal-ratio frames with negative-line coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable

/-- Once the original normal classes give a free frame on each original
subopen, their section comparisons with the native negative lines are natural
and agree on overlaps. The hypothesis refers to these specific generators. -/
def pairedC3ConormalComparisonOfGeneratorFrames {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1))
    (hframe : ∀ (i : Fin (k + 1)) (V : (pairedC3Proj k).Opens)
      (hi : V ≤ ProjSpace.standardOpen ℂ k i),
      Function.Bijective (pairedC3FiniteFrameSynthesis
        (fun j : {j : Fin (n + 1) // j ∉ Set.range e} =>
          pairedC3ConormalStandardGenerator e i j.val j.property) V hi)) :
    PairedC3LocalModuleComparison
      (s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e))
      (∏ᶜ (fun _ : {j : Fin (n + 1) // j ∉ Set.range e} => pairedC3NegativeLine k))
      (ProjSpace.standardOpen ℂ k) := by
  classical
  let g := fun i (j : {j : Fin (n + 1) // j ∉ Set.range e}) =>
    pairedC3ConormalStandardGenerator e i j.val j.property
  let cM := fun i V hi => pairedC3FiniteFrameCoordinate (g i) V hi (hframe i V hi)
  let cN := fun i V hi =>
    (pairedC3ProductSectionEquiv
      (fun _ : {j : Fin (n + 1) // j ∉ Set.range e} => pairedC3NegativeLine k) V).trans
      (LinearEquiv.piCongrRight (fun _ => pairedC3NegativeLineCoordinate k i V hi))
  refine pairedC3ComparisonOfMatchingCoordinates cM cN ?_ ?_
    (fun i j V hi _ => (pairedC3Proj k).presheaf.map (homOfLE hi).op
      (ProjSpace.coordinateRatioSection ℂ k i j)) ?_ ?_
  · intro i V W h hi s
    exact paired_c3_finite_frame_coordinate_restrict (g i) V W hi h
      (hframe i V hi) (hframe i W (h.trans hi)) s
  · intro i V W h hi s
    funext b
    change pairedC3NegativeLineCoordinate k i W (h.trans hi)
      (pairedC3ProductSectionEquiv _ W (pairedC3ModuleRestrict _ h s) b) = _
    rw [paired_c3_product_section_restrict]
    exact paired_c3_negative_line_coordinate_restrict k i V W hi h _
  · intro i j V hi hj s
    exact paired_c3_finite_frame_coordinate_transition (g i) (g j) V hi hj
      (hframe i V hi) (hframe j V hj) _
      (fun b => paired_c3_conormal_standard_generator_transition e i j b.val b.property V hi hj) s
  · intro i j V hi hj s
    funext b
    exact paired_c3_negative_line_coordinate_transition k i j V hi hj
      (pairedC3ProductSectionEquiv _ V s b)

#print axioms pairedC3ConormalComparisonOfGeneratorFrames
end HodgeLean.Foundations.Program.G32Native
