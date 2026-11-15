import HodgeLean.Foundations.BundleResolution.ChernOpenUnionCapQuasiIsoHelpers
import Mathlib.Order.CompleteLattice.Finset

/-! # Actual cap gluing on finite open unions

At each insertion, the new overlap lies in the newly inserted member.
Local comparison on its open subsets supplies that overlap comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_domainEvenCapExtendedMap_quasiIso_finite_union (X Y : TopCat.{0})
    (f : X ⟶ Y) (Z : Set X) (k : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k))
    {I : Type*} (A : I → Set Y) (hA : ∀ i, IsOpen (A i))
    (hlocal : ∀ (i : I) (T : Set Y), IsOpen T → T ⊆ A i →
      QuasiIso (i1_domainEvenCapExtendedMap X Y f Z T k φ))
    (s : Finset I) (hs : s.Nonempty) :
    QuasiIso (i1_domainEvenCapExtendedMap X Y f Z (⋃ i ∈ s, A i) k φ) := by
  classical
  revert hs
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    exact False.elim (Finset.not_nonempty_empty hs)
  | @insert i s hi ih =>
    intro hs
    rw [Finset.set_biUnion_insert]
    by_cases hse : s = ∅
    · subst s
      have he : A i ∪ (⋃ j ∈ (∅ : Finset I), A j) = A i := by simp
      rw [he]
      exact hlocal i (A i) (hA i) Set.Subset.rfl
    · have hs' : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hse
      have hW : IsOpen (⋃ j ∈ s, A j) :=
        isOpen_iUnion fun j => isOpen_iUnion fun _ => hA j
      exact i1_domainEvenCapExtendedMap_quasiIso_union X Y f Z (A i) (⋃ j ∈ s, A j)
        (hA i) hW k φ
        (hlocal i (A i ∩ ⋃ j ∈ s, A j) ((hA i).inter hW) Set.inter_subset_left)
        (hlocal i (A i) (hA i) Set.Subset.rfl) (ih hs')

end HodgeLean.Foundations.BundleResolution
