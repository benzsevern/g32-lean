import HodgeLean.Foundations.BundleThom.Defs
import Mathlib.Data.Finset.Lattice.Fold

/-! # Actual finite intersection–union distributivity for singular domains

The lattice identity is verified pointwise on actual simplices.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Intersection with an actual simplicial domain distributes over a supplied finite union of actual domains.
Source: Hatcher, Algebraic Topology, §2.2, intersection–union identities for singular domains. -/
theorem i1_subcomplex_inf_finsetSup {ι : Type} (X : SSet)
    (A : X.Subcomplex) (U : ι → X.Subcomplex) (s : Finset ι) :
    A ⊓ s.sup U = s.sup (fun i => A ⊓ U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sup_empty, inf_bot_eq]
  | @insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sup_insert, ← ih]
    ext n σ
    change (σ ∈ A.obj n ∧ (σ ∈ (U a).obj n ∨ σ ∈ (s.sup U).obj n)) ↔
      ((σ ∈ A.obj n ∧ σ ∈ (U a).obj n) ∨ (σ ∈ A.obj n ∧ σ ∈ (s.sup U).obj n))
    exact and_or_left

end HodgeLean.Foundations.BundleThom
