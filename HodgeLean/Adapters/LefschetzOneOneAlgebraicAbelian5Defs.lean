import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Tactic

/-! # Translation incidence sets

These sets record which translations make a segment meet a specified subset.
They encode geometry, with no asserted dimension or avoidance property.
HC no distance; AV milestone no distance.
-/
noncomputable section
open Set
namespace HodgeLean.Adapters

/-- Translations for which the affine segment from `a` to `a + v` meets `Z`.
Source: Gunning--Rossi, Chapter I, analytic-set dimension; elementary incidence geometry. -/
def bh5_segmentIncidence (n : ℕ) (Z : Set (Fin n → ℂ)) (a v : Fin n → ℂ) :
    Set (Fin n → ℂ) := {z | ∃ t ∈ Icc (0 : ℝ) 1, z + a + t • v ∈ Z}

example (n : ℕ) (a v : Fin n → ℂ) : bh5_segmentIncidence n ∅ a v = ∅ := by
  ext z
  simp [bh5_segmentIncidence]

example : (0 : Fin 1 → ℂ) ∈ bh5_segmentIncidence 1 {0} 0 0 :=
  ⟨0, by norm_num, by simp⟩

example : (0 : Fin 2 → ℂ) ∈ bh5_segmentIncidence 2 {0} 0 0 :=
  ⟨0, by norm_num, by simp⟩

end HodgeLean.Adapters
