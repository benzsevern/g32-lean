import HodgeLean.Foundations.BundleThom.SubcomplexFiniteDistributivityHelpers
import HodgeLean.Foundations.BundleThom.RelativeFiniteUnionLowHomologyHelpers
import Mathlib.Data.Finset.Lattice.Fold

/-! # Low-degree relative homology on finite actual chain unions

The finite join remains in the ambient singular subcomplex lattice.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Every nonempty finite union of actual relative chain domains with vanishing degree-zero homology has vanishing degree-zero homology.
Source: Hatcher, Algebraic Topology, §2.2, finite relative chain unions. -/
theorem i1_relativeSubcomplexFinsetSupHomologyZero_isZero {ι : Type}
    (X : SSet) (Z : X.Subcomplex) (U : ι → X.Subcomplex) (s : Finset ι) :
    s.Nonempty →
    (∀ i ∈ s, IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (U i)).homology 0)) →
    IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (s.sup U)).homology 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    exact False.elim (Finset.not_nonempty_empty hs)
  | @insert a s ha ih =>
    intro hs hh
    by_cases hsn : s.Nonempty
    · rw [Finset.sup_insert]
      exact i1_relativeSubcomplexSupHomologyZero_isZero X Z _ _
        (hh a (Finset.mem_insert_self _ _))
        (ih hsn (fun i hi => hh i (Finset.mem_insert_of_mem hi)))
    · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
      subst s
      simpa only [Finset.sup_insert, Finset.sup_empty, sup_bot_eq] using
        hh a (Finset.mem_insert_self _ _)

/-- A nonempty finite relative chain union has zero degree-one homology when each domain has zero degree-one homology and every pairwise intersection has zero degree-zero homology.
Source: Hatcher, Algebraic Topology, §2.2, finite relative Mayer–Vietoris induction. -/
theorem i1_relativeSubcomplexFinsetSupHomologyOne_isZero {ι : Type}
    (X : SSet) (Z : X.Subcomplex) (U : ι → X.Subcomplex) (s : Finset ι) :
    s.Nonempty →
    (∀ i ∈ s, IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (U i)).homology 1)) →
    (∀ i ∈ s, ∀ j ∈ s,
      IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (U i ⊓ U j)).homology 0)) →
    IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (s.sup U)).homology 1) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    exact False.elim (Finset.not_nonempty_empty hs)
  | @insert a s ha ih =>
    intro hs hh hp
    by_cases hsn : s.Nonempty
    · have hz : IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (U a ⊓ s.sup U)).homology 0) := by
        rw [i1_subcomplex_inf_finsetSup X (U a) U s]
        exact i1_relativeSubcomplexFinsetSupHomologyZero_isZero X Z (fun i => U a ⊓ U i) s hsn
          (fun i hi => hp a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi))
      rw [Finset.sup_insert]
      exact i1_relativeSubcomplexSupHomologyOne_isZero X Z _ _
        (hh a (Finset.mem_insert_self _ _))
        (ih hsn (fun i hi => hh i (Finset.mem_insert_of_mem hi))
          (fun i hi j hj => hp i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))) hz
    · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
      subst s
      simpa only [Finset.sup_insert, Finset.sup_empty, sup_bot_eq] using
        hh a (Finset.mem_insert_self _ _)

end HodgeLean.Foundations.BundleThom
