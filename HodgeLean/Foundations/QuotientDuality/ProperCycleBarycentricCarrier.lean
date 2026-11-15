import HodgeLean.Foundations.QuotientDuality.ProperCycleBarycentricProduct

/-! # Barycentric star products retaining the actual finite-face carrier -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Resetting selected positive weights preserves membership in the actual union of supporting faces.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates of simplicial complexes.
HC no distance; AV milestone no distance. -/
lemma properCycle_star_normal_face_carrier_iff (F : Set (Finset ι))
    (S : Finset ι) (hS : S.Nonempty) (p : ProperCycleFacePoint S) (w : ProperCycleStarPoint S) :
    (∃ s ∈ F, ∀ i ∉ s, w.val.val i = 0) ↔
      (∃ s ∈ F, ∀ i ∉ s, (properCycle_star_normal_map S hS p w).val.val.val i = 0) := by
  constructor
  · rintro ⟨s, hs, hw⟩
    refine ⟨s, hs, fun i hi => ?_⟩
    exact (properCycle_face_reweight_zero_iff S hS w p i).mpr (hw i hi)
  · rintro ⟨s, hs, hw⟩
    refine ⟨s, hs, fun i hi => ?_⟩
    exact (properCycle_face_reweight_zero_iff S hS w p i).mp (hw i hi)

/-- The star product restricts to the actual carrier specified by the finite supporting faces.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric star coordinates.
HC no distance; AV milestone no distance. -/
def properCycle_barycentric_carrier_product (F : Set (Finset ι))
    (S : Finset ι) (hS : S.Nonempty) (p : ProperCycleFacePoint S) :
    {w : ProperCycleStarPoint S | ∃ s ∈ F, ∀ i ∉ s, w.val.val i = 0} ≃ₜ
      (ProperCycleFacePoint S ×
        {v : ProperCycleNormalPoint S hS p | ∃ s ∈ F, ∀ i ∉ s, v.val.val.val i = 0}) := by
  let e := (properCycle_barycentric_star_product S hS p).subtype
    (p := fun w => ∃ s ∈ F, ∀ i ∉ s, w.val.val i = 0)
    (q := fun z => ∃ s ∈ F, ∀ i ∉ s, z.2.val.val.val i = 0)
    (fun w => properCycle_star_normal_face_carrier_iff F S hS p w)
  let t :
      {z : ProperCycleFacePoint S × ProperCycleNormalPoint S hS p |
        ∃ s ∈ F, ∀ i ∉ s, z.2.val.val.val i = 0} ≃ₜ
      (ProperCycleFacePoint S ×
        {v : ProperCycleNormalPoint S hS p | ∃ s ∈ F, ∀ i ∉ s, v.val.val.val i = 0}) :=
    { toFun := fun z => (z.val.1, ⟨z.val.2, z.property⟩)
      invFun := fun z => ⟨(z.1, z.2.val), z.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
      continuous_invFun :=
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _ }
  exact e.trans t

/-- Reweighting an actual face point replaces it by the chosen face point.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_reweight_of_face (S : Finset ι) (w p : ProperCycleFacePoint S) :
    properCycle_face_reweight S w.val p = p.val := by
  apply Subtype.ext
  funext i
  change (if i ∈ S then (∑ j ∈ S, w.val.val j) * p.val.val i else w.val.val i) = p.val.val i
  rw [properCycle_face_selected_sum]
  by_cases hi : i ∈ S
  · rw [if_pos hi, one_mul]
  · rw [if_neg hi, w.property.2 i hi, p.property.2 i hi]

/-- The normal coordinate equals the face apex exactly on the literal selected face.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric star coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_star_normal_apex_iff (S : Finset ι) (hS : S.Nonempty)
    (p : ProperCycleFacePoint S) (w : ProperCycleStarPoint S) :
    properCycle_star_normal_map S hS p w =
      properCycle_star_normal_map S hS p ⟨p.val, p.property.1⟩ ↔
      ∀ i ∉ S, w.val.val i = 0 := by
  have hapex : (properCycle_star_normal_map S hS p ⟨p.val, p.property.1⟩).val.val = p.val :=
    properCycle_face_reweight_of_face S p p
  constructor
  · intro h i hi
    have hc := congrArg (fun n : ProperCycleNormalPoint S hS p => n.val.val.val i) h
    change (properCycle_face_reweight S w.val p).val i =
      (properCycle_star_normal_map S hS p ⟨p.val, p.property.1⟩).val.val.val i at hc
    rw [properCycle_face_reweight_outside S w.val p i hi, hapex, p.property.2 i hi] at hc
    exact hc
  · intro hw
    have hm : (∑ j ∈ S, w.val.val j) = 1 := by
      rw [← w.val.property.2]
      exact Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hw i hi)
    apply Subtype.ext
    apply Subtype.ext
    rw [hapex]
    apply Subtype.ext
    funext i
    change (if i ∈ S then (∑ j ∈ S, w.val.val j) * p.val.val i else w.val.val i) = p.val.val i
    rw [hm]
    by_cases hi : i ∈ S
    · rw [if_pos hi, one_mul]
    · rw [if_neg hi, hw i hi, p.property.2 i hi]

end HodgeLean.Foundations.QuotientDuality
