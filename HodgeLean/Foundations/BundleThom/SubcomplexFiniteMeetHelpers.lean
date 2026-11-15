import HodgeLean.Foundations.BundleThom.SubcomplexFiniteDistributivityHelpers
import Mathlib.Data.Finset.Lattice.Fold

/-! # Actual finite intersection coordinates

HC no distance; AV milestone no distance. -/

noncomputable section
open AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Intersecting each member of a nonempty finite family with one supplied domain inserts that domain into the finite intersection.
Source: Hatcher, Algebraic Topology, §2.2, finite intersection domains. -/
theorem i1_subcomplex_finsetInf_restrict {ι : Type} [DecidableEq ι] (X : SSet)
    (U : ι → X.Subcomplex) (a : ι) (s : Finset ι) (hs : s.Nonempty) :
    s.inf (fun i => U a ⊓ U i) = (insert a s).inf U := by
  classical
  change s.inf ((fun _ => U a) ⊓ U) = (insert a s).inf U
  rw [Finset.inf_inf, Finset.inf_const hs, Finset.inf_insert]

end HodgeLean.Foundations.BundleThom
