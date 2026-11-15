import HodgeLean.Foundations.QuotientDuality.PersistenceSubsetPairHomotopy
import HodgeLean.Foundations.QuotientDuality.PersistenceHomotopyTube

/-! Zero actual relative homology maps between controlled locus neighbourhoods. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal inclusion of the two neighbourhood pairs marked by the same locus. -/
def persistenceNeighbourhoodPairInclusion
    {X : Type} [TopologicalSpace X] (A M N : Set X) (hMN : M ⊆ N) :
    TopPair.ofSubset (X := TopCat.of M) {x | x.val ∈ A} ⟶
      TopPair.ofSubset (X := TopCat.of N) {x | x.val ∈ A} :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun x => ⟨x.val, hMN x.property⟩, continuous_subtype_val.subtype_mk _⟩)
    (fun _ hx => hx)

lemma persistence_neighbourhood_pair_inclusion_relative_homology_zero
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M N : Set X) (hMN : M ⊆ N) (r : C(X, X))
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) r)
    (hfixed : ∀ (t : unitInterval) a, a ∈ A → H (t, a) = a)
    (htraj : ∀ (t : unitInterval) x, x ∈ M → H (t, x) ∈ N)
    (hret : ∀ x ∈ M, r x ∈ A) (n : ℕ) :
    relativeHomologyMap K n (persistenceNeighbourhoodPairInclusion A M N hMN) = 0 := by
  let f : TopCat.of M ⟶ TopCat.of N :=
    TopCat.ofHom ⟨fun x => ⟨x.val, hMN x.property⟩, continuous_subtype_val.subtype_mk _⟩
  have hrN (x : M) : r x.val ∈ N := by
    have h := htraj 1 x.val x.property
    rw [H.apply_one] at h
    exact h
  let g : TopCat.of M ⟶ TopCat.of N :=
    TopCat.ofHom ⟨fun x => ⟨r x.val, hrN x⟩,
      (r.continuous.comp continuous_subtype_val).subtype_mk hrN⟩
  let H' : TopCat.Homotopy f g := {
    toFun := fun p => ⟨H (p.1, p.2.val), htraj p.1 p.2.val p.2.property⟩
    continuous_toFun := (H.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := fun x => Subtype.ext (H.apply_zero x.val)
    map_one_left := fun x => Subtype.ext (H.apply_one x.val) }
  apply persistence_relative_homology_map_zero_of_pair_homotopy K
    ({x : M | x.val ∈ A}) ({x : N | x.val ∈ A}) f g (fun _ hx => hx) H' _ _ n
  · intro t x hx
    change H (t, x.val) ∈ A
    rw [hfixed t x.val hx]
    exact hx
  · intro x
    exact hret x.val x.property

lemma persistence_ambient_deformation_relative_homology_shrink
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A N : Set X) (hN : IsOpen N) (hAN : A ⊆ N) (r : C(X, X))
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) r)
    (hfixed : ∀ (t : unitInterval) a, a ∈ A → H (t, a) = a)
    (hret : ∀ x ∈ N, r x ∈ A) (U : Set X) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ M : Set X, IsOpen M ∧ A ⊆ M ∧ ∃ hMU : M ⊆ U, ∀ n : ℕ,
      relativeHomologyMap K n (persistenceNeighbourhoodPairInclusion A M U hMU) = 0 := by
  obtain ⟨M₀, hM₀, hAM₀, hM₀U, htraj⟩ :=
    persistence_fixed_homotopy_neighbourhood_shrink A r H hfixed U hU hAU
  let M := M₀ ∩ N
  have hMU : M ⊆ U := fun _ hx => hM₀U hx.1
  refine ⟨M, hM₀.inter hN, (fun a ha => ⟨hAM₀ ha, hAN ha⟩), hMU, ?_⟩
  intro n
  exact persistence_neighbourhood_pair_inclusion_relative_homology_zero K A M U hMU r H hfixed
    (fun t x hx => htraj t x hx.1) (fun x hx => hret x hx.2) n

end HodgeLean.Foundations.QuotientDuality
