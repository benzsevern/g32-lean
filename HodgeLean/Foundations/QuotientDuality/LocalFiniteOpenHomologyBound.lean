import HodgeLean.Foundations.QuotientDuality.LocalTwoOpenHomologyVanishing
import HodgeLean.Foundations.QuotientDuality.LocalOpenCoverOrientation
import HodgeLean.Foundations.RationalHomologyManifold.EuclideanOpenBound

/-! Uniform open-subset homology bounds pass through finite open covers. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem finite_open_homology_bound (X : TopCat.{0}) (I : Type) (U : I → Opens X)
    (hbound : ∀ a, ∃ N : ℕ, ∀ (Z : TopCat.{0}) (j : Z ⟶ TopCat.of (U a)),
      IsOpenEmbedding j → ∀ i, N < i → Subsingleton (Homology ℚ Z i))
    (s : Finset I) :
    ∃ N : ℕ, ∀ (Z : TopCat.{0}) (j : Z ⟶ X), IsOpenEmbedding j →
      Set.range j ⊆ (↑(⨆ a ∈ s, U a) : Set X) →
      ∀ i, N < i → Subsingleton (Homology ℚ Z i) := by
  classical
  choose N hN using hbound
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    intro Z j hj hrange i hi
    letI : IsEmpty Z := ⟨fun z => by simpa using hrange ⟨z, rfl⟩⟩
    exact HodgeLean.Foundations.RationalHomologyManifold.euclidean_open_homology_bound 0 Z
      (TopCat.ofHom ⟨fun _ => 0, continuous_const⟩)
      (IsOpenEmbedding.of_isEmpty _) i hi
  | @insert a s ha ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨max (N a) M + 1, ?_⟩
    intro Z j hj hrange i hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    let V : Opens X := ⨆ b ∈ s, U b
    let A : Opens Z := ⟨j ⁻¹' (U a : Set X), (U a).isOpen.preimage hj.continuous⟩
    let B : Opens Z := ⟨j ⁻¹' (V : Set X), V.isOpen.preimage hj.continuous⟩
    have hcover : (A : Set Z) ∪ B = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      have H := hrange ⟨z, rfl⟩
      have he : (⨆ b ∈ insert a s, U b) = U a ⊔ V := by ext x; simp [V]
      rw [he] at H
      exact H
    let fA : TopCat.of A ⟶ TopCat.of (U a) :=
      TopCat.ofHom ⟨fun z => ⟨j z.val, z.property⟩,
        (hj.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hfA : IsOpenEmbedding fA := IsOpenEmbedding.of_comp _
      (U a).isOpen.isOpenEmbedding_subtypeVal (hj.comp A.isOpen.isOpenEmbedding_subtypeVal)
    have hHA := hN a (TopCat.of A) fA hfA (k + 1) (by omega)
    let fB : TopCat.of B ⟶ X := (openSubsetInclusion Z B) ≫ j
    have hfB : IsOpenEmbedding fB := hj.comp B.isOpen.isOpenEmbedding_subtypeVal
    have hBrange : Set.range fB ⊆ (V : Set X) := by
      rintro _ ⟨z, rfl⟩
      exact z.property
    have hHB := hM (TopCat.of B) fB hfB hBrange (k + 1) (by omega)
    let C : Opens Z := A ⊓ B
    let fC : TopCat.of C ⟶ TopCat.of (U a) :=
      TopCat.ofHom ⟨fun z => ⟨j z.val, z.property.1⟩,
        (hj.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hfC : IsOpenEmbedding fC := IsOpenEmbedding.of_comp _
      (U a).isOpen.isOpenEmbedding_subtypeVal (hj.comp C.isOpen.isOpenEmbedding_subtypeVal)
    have hHC := hN a (TopCat.of C) fC hfC k (by omega)
    exact two_open_homology_vanishing Z A B A.isOpen B.isOpen hcover k hHA hHB hHC

#print axioms finite_open_homology_bound
end HodgeLean.Foundations.QuotientDuality
