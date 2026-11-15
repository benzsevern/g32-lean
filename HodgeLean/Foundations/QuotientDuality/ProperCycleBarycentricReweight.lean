import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairFaceNormalization

/-! # Actual barycentric coordinate changes on open face stars -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
open Semialgebraic.CompatibleTriangulation.Helpers
namespace HodgeLean.Foundations.QuotientDuality

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Positive barycentric points of the specified face, extended by zero to the ambient vertices.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates.
HC no distance; AV milestone no distance. -/
abbrev ProperCycleFacePoint (S : Finset ι) :=
  {p : stdSimplex ℝ ι | (∀ i ∈ S, 0 < p.val i) ∧ ∀ i ∉ S, p.val i = 0}

/-- Points of the actual open face star have positive weights on every selected vertex.
Source: Munkres, Elements of Algebraic Topology, section 2, open stars.
HC no distance; AV milestone no distance. -/
abbrev ProperCycleStarPoint (S : Finset ι) :=
  {w : stdSimplex ℝ ι | ∀ i ∈ S, 0 < w.val i}

/-- A positive point of a nonempty face star has positive total selected mass.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_star_mass_pos (S : Finset ι) (hS : S.Nonempty)
    (w : ProperCycleStarPoint S) : 0 < ∑ i ∈ S, w.val.val i := by
  obtain ⟨i, hi⟩ := hS
  exact Finset.sum_pos' (fun j _ => w.val.property.1 j) ⟨i, hi, w.property i hi⟩

/-- The selected coordinates of an actual face point have total mass one.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_selected_sum (S : Finset ι) (p : ProperCycleFacePoint S) :
    (∑ i ∈ S, p.val.val i) = 1 := by
  rw [← p.val.property.2]
  exact Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => p.property.2 i hi)

/-- Replace the selected barycentric weights by their original total mass times an actual positive face point.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinate changes.
HC no distance; AV milestone no distance. -/
def properCycle_face_reweight (S : Finset ι) (w : stdSimplex ℝ ι)
    (p : ProperCycleFacePoint S) : stdSimplex ℝ ι :=
  ⟨fun i => if i ∈ S then (∑ j ∈ S, w.val j) * p.val.val i else w.val i, by
    constructor
    · intro i
      dsimp only
      split_ifs
      · exact mul_nonneg (Finset.sum_nonneg (fun j _ => w.property.1 j)) (p.val.property.1 i)
      · exact w.property.1 i
    · have he (i : ι) :
          (if i ∈ S then (∑ j ∈ S, w.val j) * p.val.val i else w.val i) =
          w.val i + (if i ∈ S then (∑ j ∈ S, w.val j) * p.val.val i - w.val i else 0) := by
        split_ifs <;> ring
      simp_rw [he]
      rw [Finset.sum_add_distrib, Fintype.sum_ite_mem, Finset.sum_sub_distrib,
        ← Finset.mul_sum, properCycle_face_selected_sum, mul_one, w.property.2]
      ring⟩

/-- Reweighting preserves every unselected coordinate literally.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinate changes.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_reweight_outside (S : Finset ι) (w : stdSimplex ℝ ι)
    (p : ProperCycleFacePoint S) (i : ι) (hi : i ∉ S) :
    (properCycle_face_reweight S w p).val i = w.val i := by
  exact if_neg hi

/-- Reweighting keeps the original total selected mass.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinate changes.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_reweight_mass (S : Finset ι) (w : stdSimplex ℝ ι)
    (p : ProperCycleFacePoint S) :
    (∑ i ∈ S, (properCycle_face_reweight S w p).val i) = ∑ i ∈ S, w.val i := by
  calc
    _ = ∑ i ∈ S, (∑ j ∈ S, w.val j) * p.val.val i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact if_pos hi
    _ = _ := by rw [← Finset.mul_sum, properCycle_face_selected_sum, mul_one]

/-- Reweighting by positive face coordinates preserves positivity at each selected vertex.
Source: Munkres, Elements of Algebraic Topology, section 2, open stars.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_reweight_star (S : Finset ι) (hS : S.Nonempty)
    (w : ProperCycleStarPoint S) (p : ProperCycleFacePoint S) :
    ∀ i ∈ S, 0 < (properCycle_face_reweight S w.val p).val i := by
  intro i hi
  change 0 < if i ∈ S then (∑ j ∈ S, w.val.val j) * p.val.val i else w.val.val i
  rw [if_pos hi]
  exact mul_pos (properCycle_star_mass_pos S hS w) (p.property.1 i hi)

end HodgeLean.Foundations.QuotientDuality
