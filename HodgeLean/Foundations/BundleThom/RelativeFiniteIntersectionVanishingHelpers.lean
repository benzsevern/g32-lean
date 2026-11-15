import HodgeLean.Foundations.BundleThom.SubcomplexFiniteMeetHelpers
import HodgeLean.Foundations.BundleThom.RelativeFinsetUnionLowHomologyHelpers

/-! # Finite relative union homology from actual intersection vanishing

The degree induction retains the actual subcomplex intersections.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- A finite relative chain union has zero homology in a supplied degree when every nonempty finite intersection has zero homology in that degree and all lower degrees.
Source: Hatcher, Algebraic Topology, §2.2, finite Mayer–Vietoris degree induction. -/
theorem i1_relativeSubcomplexFinsetSupHomology_isZero_of_intersections {ι : Type}
    (X : SSet) (Z : X.Subcomplex) (n : ℕ) (U : ι → X.Subcomplex) (s : Finset ι) :
    s.Nonempty →
    (∀ t : Finset ι, t.Nonempty → ∀ m, m ≤ n →
      IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (t.inf U)).homology m)) →
    IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (s.sup U)).homology n) := by
  classical
  induction n generalizing U s with
  | zero =>
    intro hs hh
    apply i1_relativeSubcomplexFinsetSupHomologyZero_isZero X Z U s hs
    intro i _
    simpa only [Finset.inf_singleton] using hh {i} (Finset.singleton_nonempty i) 0 le_rfl
  | succ n ihn =>
    induction s using Finset.induction_on with
    | empty =>
      intro hs
      exact False.elim (Finset.not_nonempty_empty hs)
    | @insert a s ha ihs =>
      intro hs hh
      have hA : IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (U a)).homology (n + 1)) := by
        simpa only [Finset.inf_singleton] using
          hh {a} (Finset.singleton_nonempty a) (n + 1) le_rfl
      by_cases hsn : s.Nonempty
      · have hI : IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj
            (U a ⊓ s.sup U)).homology n) := by
          rw [i1_subcomplex_inf_finsetSup X (U a) U s]
          apply ihn (fun i => U a ⊓ U i) s hsn
          intro t ht m hm
          rw [i1_subcomplex_finsetInf_restrict X U a t ht]
          exact hh (insert a t) (Finset.insert_nonempty a t) m (by omega)
        rw [Finset.sup_insert]
        exact i1_shortExactRightHomologySuccessor_isZero
          (i1_relativeSubcomplexChainSequence X Z (U a) (s.sup U))
          (i1_relativeSubcomplexChainSequence_shortExact X Z (U a) (s.sup U)) n
          (i1_biprodHomology_isZero _ _ (n + 1) hA (ihs hsn hh)) hI
      · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
        subst s
        simpa only [Finset.sup_insert, Finset.sup_empty, sup_bot_eq] using hA

end HodgeLean.Foundations.BundleThom
