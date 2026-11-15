import HodgeLean.Foundations.QuotientDuality.ProperCycleBarycentricReweight

/-! # Inverse identities for actual barycentric face coordinates -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
open Semialgebraic.CompatibleTriangulation.Helpers
namespace HodgeLean.Foundations.QuotientDuality

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Normalize the positive selected coordinates of a star point to its actual face point.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates.
HC no distance; AV milestone no distance. -/
def properCycle_star_face (S : Finset ι) (hS : S.Nonempty)
    (w : ProperCycleStarPoint S) : ProperCycleFacePoint S :=
  ⟨s2e_pair_faceNormalize S w.val (properCycle_star_mass_pos S hS w),
    (by
      constructor
      · intro i hi
        change 0 < if i ∈ S then w.val.val i / (∑ j ∈ S, w.val.val j) else 0
        rw [if_pos hi]
        exact div_pos (w.property i hi) (properCycle_star_mass_pos S hS w)
      · intro i hi
        exact s2e_pair_faceNormalize_outside S w.val (properCycle_star_mass_pos S hS w) i hi)⟩

/-- A second selected-face coordinate change overwrites the first and retains the normal coordinates.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinate changes.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_reweight_comp (S : Finset ι) (w : stdSimplex ℝ ι)
    (p q : ProperCycleFacePoint S) :
    properCycle_face_reweight S (properCycle_face_reweight S w p) q =
      properCycle_face_reweight S w q := by
  apply Subtype.ext
  funext i
  change (if i ∈ S then (∑ j ∈ S, (properCycle_face_reweight S w p).val j) * q.val.val i
      else (properCycle_face_reweight S w p).val i) = _
  rw [properCycle_face_reweight_mass]
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    exact (if_pos hi).symm
  · rw [if_neg hi, properCycle_face_reweight_outside S w p i hi]
    exact (if_neg hi).symm

/-- Recombining a star point with its own normalized face coordinates recovers that point.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinate changes.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_reweight_star_face (S : Finset ι) (hS : S.Nonempty)
    (w : ProperCycleStarPoint S) :
    properCycle_face_reweight S w.val (properCycle_star_face S hS w) = w.val := by
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ S
  · change (if i ∈ S then (∑ j ∈ S, w.val.val j) *
        (if i ∈ S then w.val.val i / (∑ j ∈ S, w.val.val j) else 0) else w.val.val i) = _
    rw [if_pos hi, if_pos hi]
    field_simp [ne_of_gt (properCycle_star_mass_pos S hS w)]
  · exact properCycle_face_reweight_outside S w.val _ i hi

/-- The normalized face coordinate of a reweighted star is exactly the chosen face point.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinate changes.
HC no distance; AV milestone no distance. -/
lemma properCycle_star_face_reweight (S : Finset ι) (hS : S.Nonempty)
    (w : ProperCycleStarPoint S) (p : ProperCycleFacePoint S) :
    properCycle_star_face S hS
      ⟨properCycle_face_reweight S w.val p, properCycle_face_reweight_star S hS w p⟩ = p := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ S
  · change (if i ∈ S then (properCycle_face_reweight S w.val p).val i /
        (∑ j ∈ S, (properCycle_face_reweight S w.val p).val j) else 0) = _
    rw [if_pos hi, properCycle_face_reweight_mass]
    change (if i ∈ S then (∑ j ∈ S, w.val.val j) * p.val.val i else w.val.val i) /
      (∑ j ∈ S, w.val.val j) = p.val.val i
    rw [if_pos hi]
    field_simp [ne_of_gt (properCycle_star_mass_pos S hS w)]
  · change (if i ∈ S then _ else 0) = p.val.val i
    rw [if_neg hi, p.property.2 i hi]

/-- Positive face reweighting retains the zero coordinates and hence the actual supporting faces.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_reweight_zero_iff (S : Finset ι) (hS : S.Nonempty)
    (w : ProperCycleStarPoint S) (p : ProperCycleFacePoint S) (i : ι) :
    (properCycle_face_reweight S w.val p).val i = 0 ↔ w.val.val i = 0 := by
  by_cases hi : i ∈ S
  · exact iff_of_false (ne_of_gt (properCycle_face_reweight_star S hS w p i hi))
      (ne_of_gt (w.property i hi))
  · rw [properCycle_face_reweight_outside S w.val p i hi]

end HodgeLean.Foundations.QuotientDuality
