import HodgeLean.Foundations.BundleThom.ThomOrientationHelpers
import Mathlib.Topology.Instances.Matrix

/-! # Actual local interpolation of complex frame changes

Compactness of the parameter interval gives one base neighbourhood on which the entire interpolation is invertible.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open TopologicalSpace Topology
namespace HodgeLean.Foundations.BundleThom

/-- Straight interpolation from the matrix at a supplied base point to the varying actual matrix.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, local comparison of complex frames. -/
def i1_matrixInterpolation {B : Type*} (k : ℕ)
    (A : B → Matrix (Fin k) (Fin k) ℂ) (b : B) (p : unitInterval × B) :
    Matrix (Fin k) (Fin k) ℂ :=
  (1 - (p.1 : ℝ)) • A b + (p.1 : ℝ) • A p.2

/-- Actual matrix interpolation is jointly continuous in the parameter and the base.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, continuous frame changes. -/
theorem i1_matrixInterpolation_continuous {B : Type*} [TopologicalSpace B] (k : ℕ)
    (A : B → Matrix (Fin k) (Fin k) ℂ) (hA : Continuous A) (b : B) :
    Continuous (i1_matrixInterpolation k A b) := by
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul continuous_const).add
    ((continuous_subtype_val.comp continuous_fst).smul (hA.comp continuous_snd))

/-- Around an invertible matrix value, the whole actual interpolation stays invertible on one open base neighbourhood.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, local complex orientation comparison. -/
theorem i1_matrixInterpolation_locally_invertible {B : Type*} [TopologicalSpace B] (k : ℕ)
    (A : B → Matrix (Fin k) (Fin k) ℂ) (hA : Continuous A) (b : B) (hb : (A b).det ≠ 0) :
    ∃ U : Opens B, b ∈ U ∧ ∀ (t : unitInterval) (x : U),
      (i1_matrixInterpolation k A b (t, x.1)).det ≠ 0 := by
  let N : Set (unitInterval × B) := {p | (i1_matrixInterpolation k A b p).det ≠ 0}
  have hN : IsOpen N := isClosed_singleton.isOpen_compl.preimage
    (i1_matrixInterpolation_continuous k A hA b).matrix_det
  have hsub : (Set.univ : Set unitInterval) ×ˢ {b} ⊆ N := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have hx' : x = b := hx
    subst x
    change ((1 - (t : ℝ)) • A b + (t : ℝ) • A b).det ≠ 0
    rw [← add_smul, sub_add_cancel, one_smul]
    exact hb
  obtain ⟨T, U, hT, hU, hTU, hbU, hprod⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hN hsub
  refine ⟨⟨U, hU⟩, hbU (Set.mem_singleton b), ?_⟩
  intro t x
  exact hprod ⟨hTU (Set.mem_univ t), x.2⟩

end HodgeLean.Foundations.BundleThom
