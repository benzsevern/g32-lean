import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-! Dimension bounds for the actual skeletal filtration.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- A bounded-dimensional simplicial set equals its corresponding skeletal stage.
Source: Mathlib Subcomplex.eq_top_iff_of_hasDimensionLT and SSet.mem_skeleton. -/
lemma c1a5_skeleton_eq_top (K : SSet.{0}) (d : ℕ) [K.HasDimensionLT d] :
    K.skeleton d = ⊤ := by
  apply (SSet.Subcomplex.eq_top_iff_of_hasDimensionLT _ d).2
  intro i hi x hx
  exact K.mem_skeleton x hi

/-- The actual nth skeletal stage has dimension strictly below n.
Source: Mathlib SSet.mem_skeleton_obj_iff_of_nonDegenerate and Subcomplex.mem_nonDegenerate_iff. -/
lemma c1a5_skeleton_dimension (K : SSet.{0}) (n : ℕ) :
    (K.skeleton n : SSet).HasDimensionLT n where
  degenerate_eq_top d hd := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have hn : x ∈ (K.skeleton n : SSet).nonDegenerate d := hx
    have hk : x.val ∈ K.nonDegenerate d := (SSet.Subcomplex.mem_nonDegenerate_iff (K.skeleton n) x).1 hn
    have hlt := (K.mem_skeleton_obj_iff_of_nonDegenerate ⟨x.val, hk⟩ n).1 x.property
    omega

end HodgeLean.Foundations.Program
