import HodgeLean.Foundations.QuotientDuality.PersistenceContractingPairs

/-! Actual subset-pair homotopies retaining the whole subspace during deformation. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Restrict the specified ambient homotopy to the actual marked subsets. -/
def persistenceSubsetPairHomotopy
    {X Y : TopCat.{0}} (A : Set X) (B : Set Y) (f g : X ⟶ Y)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hpres : ∀ (t : unitInterval) (a : X), a ∈ A → H (t, a) ∈ B) :
    TopPair.Homotopy (TopPair.ofSubsetHom f hf) (TopPair.ofSubsetHom g hg) where
  fst := H
  snd := {
    toFun := fun p => ⟨H (p.1, p.2.val), hpres p.1 p.2.val p.2.property⟩
    continuous_toFun := (H.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := fun a => Subtype.ext (H.apply_zero a.val)
    map_one_left := fun a => Subtype.ext (H.apply_one a.val) }
  w := by
    apply TopCat.ext
    rintro ⟨a, t⟩
    rfl

lemma persistence_pair_map_relative_homology_zero_of_range
    (K : Type) [CommRing K] {X Y : TopCat.{0}} (A : Set X) (B : Set Y)
    (f : X ⟶ Y) (hf : Set.MapsTo f A B) (hfall : ∀ x, f x ∈ B) (n : ℕ) :
    relativeHomologyMap K n (TopPair.ofSubsetHom f hf) = 0 := by
  let Q := TopPair.ofSubset (X := TopCat.of B) Set.univ
  let a : TopPair.ofSubset A ⟶ Q := TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun x => ⟨f x, hfall x⟩, f.hom.continuous.subtype_mk _⟩)
    (fun _ _ => Set.mem_univ _)
  let b : Q ⟶ TopPair.ofSubset B := TopPair.ofSubsetHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) (fun x _ => x.property)
  have hfactor : TopPair.ofSubsetHom f hf = a ≫ b := by
    apply persistence_pair_hom_ext
    rfl
  haveI : Subsingleton (RelativeHomology K Q n) :=
    ModuleCat.subsingleton_of_isZero
      (persistence_full_pair_relative_homology_isZero K (TopCat.of B) n)
  rw [hfactor, relativeHomologyMap_comp]
  ext u
  change relativeHomologyMap K n b (relativeHomologyMap K n a u) = 0
  rw [Subsingleton.elim (relativeHomologyMap K n a u) 0, map_zero]

lemma persistence_relative_homology_map_zero_of_pair_homotopy
    (K : Type) [CommRing K] {X Y : TopCat.{0}} (A : Set X) (B : Set Y)
    (f g : X ⟶ Y) (hf : Set.MapsTo f A B) (H : TopCat.Homotopy f g)
    (hpres : ∀ (t : unitInterval) (a : X), a ∈ A → H (t, a) ∈ B)
    (hfall : ∀ x, g x ∈ B) (n : ℕ) :
    relativeHomologyMap K n (TopPair.ofSubsetHom f hf) = 0 := by
  let hg : Set.MapsTo g A B := fun x _ => hfall x
  have h := (persistenceSubsetPairHomotopy A B f g hf hg H hpres).congr_relativeHomologyMap
    (R := K) n
  rw [persistence_pair_map_relative_homology_zero_of_range K A B g hg hfall n] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
