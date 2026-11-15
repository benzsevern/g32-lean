import HodgeLean.Foundations.QuotientDuality.ProperCycleBarycentricCarrier
import HodgeLean.Foundations.QuotientDuality.ProperCycleFaceVectorChart

/-! # Actual vector-space product charts on marked finite-face carriers -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The distinguished normal point is the actual positive selected-face point with all other weights zero.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric stars.
HC no distance; AV milestone no distance. -/
def properCycle_carrier_normal_apex (F : Set (Finset ι))
    (S : Finset ι) (hS : S.Nonempty) (p : ProperCycleFacePoint S) (hSF : S ∈ F) :
    {v : ProperCycleNormalPoint S hS p | ∃ s ∈ F, ∀ i ∉ s, v.val.val.val i = 0} :=
  ⟨properCycle_star_normal_map S hS p ⟨p.val, p.property.1⟩, S, hSF, by
    intro i hi
    change (properCycle_face_reweight S p.val p).val i = 0
    rw [properCycle_face_reweight_of_face S p p]
    exact p.property.2 i hi⟩

/-- The literal barycentric star product carries the selected face to its actual normal apex.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric star coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_carrier_product_mark (F : Set (Finset ι))
    (S : Finset ι) (hS : S.Nonempty) (p : ProperCycleFacePoint S) (hSF : S ∈ F)
    (w : {w : ProperCycleStarPoint S | ∃ s ∈ F, ∀ i ∉ s, w.val.val i = 0}) :
    (properCycle_barycentric_carrier_product F S hS p w).2 =
      properCycle_carrier_normal_apex F S hS p hSF ↔
      ∀ i ∉ S, w.val.val.val i = 0 := by
  rw [Subtype.ext_iff]
  exact properCycle_star_normal_apex_iff S hS p w.val

/-- The actual open face star is open in the actual supporting-face carrier.
Source: Munkres, Elements of Algebraic Topology, section 2, open stars and barycentric coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_carrier_star_isOpen (F : Set (Finset ι)) (S : Finset ι) :
    IsOpen {w : {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0} |
      ∀ i ∈ S, 0 < w.val.val i} := by
  have he : {w : {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0} |
      ∀ i ∈ S, 0 < w.val.val i} =
      ⋂ i ∈ S, {w : {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0} |
        0 < w.val.val i} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  apply isOpen_biInter_finset
  intro i _
  exact isOpen_lt continuous_const
    ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val))

/-- Swapping the two actual subtype constraints identifies the open carrier star with star coordinates.
Source: Munkres, Elements of Algebraic Topology, section 2, subspace topology.
HC no distance; AV milestone no distance. -/
def properCycle_carrier_star_homeomorph (F : Set (Finset ι)) (S : Finset ι) :
    {w : {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0} |
      ∀ i ∈ S, 0 < w.val.val i} ≃ₜ
      {w : ProperCycleStarPoint S | ∃ s ∈ F, ∀ i ∉ s, w.val.val i = 0} where
  toFun w := ⟨⟨w.val.val, w.property⟩, w.val.property⟩
  invFun w := ⟨⟨w.val.val, w.property⟩, w.val.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _

/-- An open star of the actual face carrier has a constructed vector-space factor and actual normal fibre.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric star coordinates.
HC no distance; AV milestone no distance. -/
def properCycle_barycentric_vector_product (F : Set (Finset ι))
    (S : Finset ι) (hS : S.Nonempty) (p : ProperCycleFacePoint S) (j : S) :
    {w : {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0} |
      ∀ i ∈ S, 0 < w.val.val i} ≃ₜ
      (properCycle_log_tangent j ×
        {v : ProperCycleNormalPoint S hS p | ∃ s ∈ F, ∀ i ∉ s, v.val.val.val i = 0}) :=
  ((properCycle_carrier_star_homeomorph F S).trans
    (properCycle_barycentric_carrier_product F S hS p)).trans
      ((properCycle_face_vector_homeomorph S j).prodCongr (Homeomorph.refl _))

/-- The constructed vector chart retains the literal selected-face mark as the distinguished normal fibre.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric star coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_barycentric_vector_product_mark (F : Set (Finset ι))
    (S : Finset ι) (hS : S.Nonempty) (p : ProperCycleFacePoint S) (j : S) (hSF : S ∈ F)
    (w : {w : {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0} |
      ∀ i ∈ S, 0 < w.val.val i}) :
    (properCycle_barycentric_vector_product F S hS p j w).2 =
      properCycle_carrier_normal_apex F S hS p hSF ↔
      ∀ i ∉ S, w.val.val.val i = 0 :=
  properCycle_carrier_product_mark F S hS p hSF (properCycle_carrier_star_homeomorph F S w)

end HodgeLean.Foundations.QuotientDuality
