import HodgeLean.Foundations.QuotientDuality.ProperCycleSimplexLogChart

/-! # Actual vector-space coordinates on a selected barycentric face -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Restrict an actual positive face point to its selected vertex set.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates.
HC no distance; AV milestone no distance. -/
def properCycle_face_to_positive (S : Finset ι) (p : ProperCycleFacePoint S) :
    ProperCyclePositiveSimplex S :=
  ⟨⟨fun i => p.val.val i.val, by
      constructor
      · intro i
        exact p.val.property.1 _
      · rw [Finset.sum_coe_sort S (fun i => p.val.val i)]
        exact properCycle_face_selected_sum S p⟩,
    fun i => p.property.1 i.val i.property⟩

/-- Extend actual positive simplex coordinates by zero off the selected vertices.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates.
HC no distance; AV milestone no distance. -/
def properCycle_face_from_positive (S : Finset ι) (p : ProperCyclePositiveSimplex S) :
    ProperCycleFacePoint S := by
  let f : ι → ℝ := fun i => if hi : i ∈ S then p.val.val ⟨i, hi⟩ else 0
  have hsum : (∑ i, f i) = 1 := by
    calc
      _ = ∑ i ∈ S, f i := by
        apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
        intro i _ hi
        exact dif_neg hi
      _ = ∑ i : S, f i.val := (Finset.sum_coe_sort S f).symm
      _ = ∑ i : S, p.val.val i := by
        apply Finset.sum_congr rfl
        intro i _
        exact dif_pos i.property
      _ = 1 := p.val.property.2
  refine ⟨⟨f, ⟨?_, hsum⟩⟩, ?_, ?_⟩
  · intro i
    dsimp only [f]
    split_ifs
    · exact p.val.property.1 _
    · exact le_rfl
  · intro i hi
    change 0 < if hi : i ∈ S then p.val.val ⟨i, hi⟩ else 0
    rw [dif_pos hi]
    exact p.property _
  · intro i hi
    exact dif_neg hi

/-- Coordinate restriction is continuous on the actual face carrier.
Source: Munkres, Elements of Algebraic Topology, section 2, finite barycentric coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_to_positive_continuous (S : Finset ι) :
    Continuous (properCycle_face_to_positive S) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_apply i.val).comp (continuous_subtype_val.comp continuous_subtype_val)

/-- Coordinate extension by zero is continuous on the actual positive simplex.
Source: Munkres, Elements of Algebraic Topology, section 2, finite barycentric coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_from_positive_continuous (S : Finset ι) :
    Continuous (properCycle_face_from_positive S) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun p : ProperCyclePositiveSimplex S =>
    if hi : i ∈ S then p.val.val ⟨i, hi⟩ else 0)
  by_cases hi : i ∈ S
  · simp only [dif_pos hi]
    exact (continuous_apply (⟨i, hi⟩ : S)).comp (continuous_subtype_val.comp continuous_subtype_val)
  · simp only [dif_neg hi]
    exact continuous_const

/-- A selected positive face is homeomorphic to the positive simplex on precisely its actual vertices.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates.
HC no distance; AV milestone no distance. -/
def properCycle_face_positive_homeomorph (S : Finset ι) :
    ProperCycleFacePoint S ≃ₜ ProperCyclePositiveSimplex S where
  toFun := properCycle_face_to_positive S
  invFun := properCycle_face_from_positive S
  left_inv := by
    intro p
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (if hi : i ∈ S then p.val.val i else 0) = p.val.val i
    by_cases hi : i ∈ S
    · rw [dif_pos hi]
    · rw [dif_neg hi, p.property.2 i hi]
  right_inv := by
    intro p
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (if hi : i.val ∈ S then p.val.val ⟨i.val, hi⟩ else 0) = p.val.val i
    exact dif_pos i.property
  continuous_toFun := properCycle_face_to_positive_continuous S
  continuous_invFun := properCycle_face_from_positive_continuous S

/-- Positive coordinates on a selected face give explicit coordinates in a real normed vector space.
Source: Munkres, Elements of Algebraic Topology, section 2; Rudin, Principles of Mathematical Analysis,
third edition, chapter 8, logarithmic ratios and normalized exponentials.
HC no distance; AV milestone no distance. -/
def properCycle_face_vector_homeomorph (S : Finset ι) (j : S) :
    ProperCycleFacePoint S ≃ₜ properCycle_log_tangent j :=
  (properCycle_face_positive_homeomorph S).trans (properCycle_positive_simplex_log_homeomorph j)

end HodgeLean.Foundations.QuotientDuality
