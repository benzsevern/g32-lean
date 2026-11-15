import HodgeLean.Foundations.Program.SchoenTransferC1a5CellExcisionHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5RelativeCoproductHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5BoundaryGeometryHelpers
import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-! Finite characteristic-cell comparison and the relative skeletal attachment step.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- A relative skeletal stage has finitely many cells when its target simplicial set is finite.
Source: Mathlib SSet.Finite.nonDegenerate and relativeCellComplexOfMono.Cell. -/
lemma c1a5_relative_cells_finite {X Y : SSet.{0}} (i : X ⟶ Y) [Y.Finite] (n : ℕ) :
    Finite (SSet.relativeCellComplexOfMono.Cell i n) := by
  exact Finite.of_injective
    (fun c : SSet.relativeCellComplexOfMono.Cell i n ↦
      (⟨c.simplex, c.nonDegenerate⟩ : Y.nonDegenerate n))
    (by intro c d h; apply SSet.relativeCellComplexOfMono.Cell.ext; exact congrArg Subtype.val h)

/-- Comparison passes across the actual relative skeletal attachment from its three local inputs.
Source: Hatcher §2.1, Theorems 2.20 and 2.27, finite relative cell sums and exact sequence transport. -/
lemma c1a5_relative_attachment_comparison {X Y : SSet.{0}} (i : X ⟶ Y) [Mono i] [Y.Finite]
    (n : ℕ) (hp : QuasiIso (c1a5Unit (SSet.skeletonOfMono i n : SSet)))
    (hs : QuasiIso (c1a5Unit (Δ[n] : SSet.{0})))
    (hb : QuasiIso (c1a5Unit (SSet.boundary.{0} n : SSet))) :
    QuasiIso (c1a5Unit (SSet.skeletonOfMono i (n + 1) : SSet)) := by
  have := c1a5_relative_cells_finite i n
  have hmono := c1a5_boundary_realization_mono n
  have hpair := c1a5_pair_comparison_of_realization_mono (SSet.boundary.{0} n).ι hb hs
  have hl : QuasiIso (c1a5RelativeUnit (SSet.relativeCellComplexOfMono.l i n)) :=
    c1a5_relative_unit_finite_coproduct (fun _ : SSet.relativeCellComplexOfMono.Cell i n ↦
      (SSet.boundary.{0} n).ι) (fun _ ↦ hpair)
  let l := SSet.relativeCellComplexOfMono.l i n
  let r := SSet.relativeCellComplexOfMono.r i n
  let t := SSet.relativeCellComplexOfMono.t i n
  let b := SSet.relativeCellComplexOfMono.b i n
  have w : l ≫ b = t ≫ r := (SSet.relativeCellComplexOfMono.w i n).symm
  have he : IsIso (c1a5RelativeMap c1a5Chains l r t b w) := c1a5_simplicial_cell_excision i n
  have hsing : QuasiIso (c1a5RelativeMap c1a5SingularChains l r t b w) :=
    c1a5_singular_cell_excision i n
  have hcomp : QuasiIso (c1a5RelativeMap c1a5Chains l r t b w ≫ c1a5RelativeUnit r) := by
    rw [c1a5_relative_square_naturality]
    have := hl
    have := hsing
    infer_instance
  have hr : QuasiIso (c1a5RelativeUnit r) := by
    have := he
    have := hcomp
    exact quasiIso_of_comp_left (c1a5RelativeMap c1a5Chains l r t b w) _
  have hm := c1a5_realization_map_mono r
  exact c1a5_ambient_comparison_of_realization_mono r hp hr

end HodgeLean.Foundations.Program
