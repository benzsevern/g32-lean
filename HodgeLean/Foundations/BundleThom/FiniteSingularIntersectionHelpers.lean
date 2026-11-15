import HodgeLean.Foundations.BundleThom.SingularSubsetIntersectionHelpers
import Mathlib.Data.Finset.Lattice.Fold

/-! # Actual singular ranges of finite intersections

HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Actual singular subset ranges preserve finite intersections, including the empty intersection.
Source: Hatcher, Algebraic Topology, §2.1, singular simplices in actual subspaces. -/
theorem i1_singularSubsetRange_finsetInf {ι : Type} (X : TopCat)
    (U : ι → Set X) (s : Finset ι) :
    s.inf (fun i => i1_singularSubsetRange X (U i)) =
      i1_singularSubsetRange X (s.inf U) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.inf_empty]
    ext n σ
    change True ↔ σ ∈ (i1_singularSubsetRange X Set.univ).obj n
    rw [i1_mem_singularSubsetRange_iff]
    simp
  | @insert a s ha ih =>
    rw [Finset.inf_insert, ih, ← i1_singularSubsetRange_inter, Finset.inf_insert]
    rfl

end HodgeLean.Foundations.BundleThom
