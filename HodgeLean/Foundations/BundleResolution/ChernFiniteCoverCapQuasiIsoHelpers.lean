import HodgeLean.Foundations.BundleResolution.ChernFiniteUnionCapQuasiIsoHelpers

/-! # Actual global cap from finite open domain comparisons

The finite union comparison reaches the full base. The checked binary
cover comparison identifies that domain result with actual global cap.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_globalEvenCapExtendedMap_quasiIso_of_univ (X Y : TopCat.{0})
    (f : X ⟶ Y) (Z : Set X) (k : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k))
    (h : QuasiIso (i1_domainEvenCapExtendedMap X Y f Z Set.univ k φ)) :
    QuasiIso (i1_globalEvenCapExtendedMap X Y f Z k φ) := by
  apply i1_globalEvenCapExtendedMap_quasiIso_of_binary_cover X Y f Z Set.univ Set.univ
    isOpen_univ isOpen_univ (Set.union_self _) k φ
  · rw [Set.inter_self]
    exact h
  · exact h
  · exact h

theorem i1_globalEvenCapExtendedMap_quasiIso_of_finite_cover (X Y : TopCat.{0})
    (f : X ⟶ Y) (Z : Set X) (k : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k))
    {I : Type*} (A : I → Set Y) (hA : ∀ i, IsOpen (A i))
    (hlocal : ∀ (i : I) (T : Set Y), IsOpen T → T ⊆ A i →
      QuasiIso (i1_domainEvenCapExtendedMap X Y f Z T k φ))
    (s : Finset I) (hs : s.Nonempty) (hcover : (⋃ i ∈ s, A i) = Set.univ) :
    QuasiIso (i1_globalEvenCapExtendedMap X Y f Z k φ) := by
  apply i1_globalEvenCapExtendedMap_quasiIso_of_univ X Y f Z k φ
  have h := i1_domainEvenCapExtendedMap_quasiIso_finite_union X Y f Z k φ A hA hlocal s hs
  rw [hcover] at h
  exact h

end HodgeLean.Foundations.BundleResolution
