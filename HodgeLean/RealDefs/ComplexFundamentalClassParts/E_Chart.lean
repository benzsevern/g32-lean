import HodgeLean.RealDefs.ComplexFundamentalClassDefs
import HodgeConjecture.Mathlib.Topology.Category.TopPair

/-! # Maps of pairs for the chart step of Hatcher's Lemma 3.27

For an open `U ⊆ M` and `A ⊆ M`, the pair `(U, U \ A)` is `TopPair.ofSubset {u : U | u.1 ∉ A}`.
This file names the excision inclusion `(U, U \ A) ⟶ (M, M \ A)`, the restriction
`(U, U \ T) ⟶ (U, U \ S)` for `S ⊆ T`, and the isomorphism of pairs induced by a homeomorphism
`U ≃ₜ V` onto an open `V` of a second space, and proves that they commute with restriction to
smaller supports. It also records that restriction of supports along `HasClassAlong` is monotone.
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

/-- Pushing forward twice is pushing forward along the composite. -/
lemma j5cE_relativeHomologyMap_apply_apply {P Q R : TopPair} (n : ℕ) (f : P ⟶ Q) (g : Q ⟶ R)
    (z : RelativeHomology ℚ P n) :
    relativeHomologyMap ℚ n g (relativeHomologyMap ℚ n f z) =
      relativeHomologyMap ℚ n (f ≫ g) z := by
  rw [relativeHomologyMap_comp]
  rfl

/-- An isomorphism of pairs is injective on relative homology. -/
lemma j5cE_iso_injective {P Q : TopPair} (φ : P ≅ Q) (i : ℕ) :
    Function.Injective (relativeHomologyMap ℚ i φ.hom) := by
  intro a b hab
  have key : ∀ z, relativeHomologyMap ℚ i φ.inv (relativeHomologyMap ℚ i φ.hom z) = z := by
    intro z
    rw [j5cE_relativeHomologyMap_apply_apply, φ.hom_inv_id, relativeHomologyMap_id,
      LinearMap.id_apply]
  rw [← key a, ← key b, hab]

/-- The excision inclusion of pairs `(U, U \ A) ⟶ (M, M \ A)`, exactly the map of
`j5c_excision`.
Source: Hatcher, *Algebraic Topology*, Theorem 2.20 (excision). -/
abbrev j5cE_exMap {M : Type} [TopologicalSpace M] (U A : Set M) :
    TopPair.ofSubset (X := TopCat.of U) {u : U | u.1 ∉ A} ⟶
      TopPair.ofSubset (X := TopCat.of M) Aᶜ :=
  TopPair.ofSubsetHom (A := {u : U | u.1 ∉ A}) (B := Aᶜ)
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of U ⟶ TopCat.of M)
    (fun _ ha => ha)

example {M : Type} [TopologicalSpace M] (U A : Set M) :
    j5cE_exMap U A = TopPair.ofSubsetHom (A := {u : U | u.1 ∉ A}) (B := Aᶜ)
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of U ⟶ TopCat.of M)
      (fun _ ha => ha) :=
  rfl

/-- Enlarging the support inside `U`, as a map of pairs `(U, U \ T) ⟶ (U, U \ S)` for `S ⊆ T`.
Source: Hatcher, *Algebraic Topology*, §3.3, p. 236 (restriction `H_n(M | T) → H_n(M | S)`). -/
def j5cE_resMap {M : Type} [TopologicalSpace M] (U : Set M) {S T : Set M} (h : S ⊆ T) :
    TopPair.ofSubset (X := TopCat.of U) {u : U | u.1 ∉ T} ⟶
      TopPair.ofSubset (X := TopCat.of U) {u : U | u.1 ∉ S} :=
  TopPair.ofSubsetHom (X := TopCat.of U) (Y := TopCat.of U)
    (A := {u : U | u.1 ∉ T}) (B := {u : U | u.1 ∉ S}) (𝟙 (TopCat.of U))
    (fun (u : U) (hw : u.1 ∉ T) hS => hw (h hS))

example {M : Type} [TopologicalSpace M] (U : Set M) {S T : Set M} (h : S ⊆ T) :
    j5cE_resMap U h = TopPair.ofSubsetHom (X := TopCat.of U) (Y := TopCat.of U)
      (A := {u : U | u.1 ∉ T}) (B := {u : U | u.1 ∉ S}) (𝟙 (TopCat.of U))
    (fun (u : U) (hw : u.1 ∉ T) hS => hw (h hS)) :=
  rfl

/-- The homeomorphism `e.source ≃ₜ e.target` of an open partial homeomorphism.
Source: Hatcher, *Algebraic Topology*, §3.3, p. 231 (a chart is a homeomorphism of an open
neighbourhood onto an open subset of `ℝⁿ`). -/
def j5cE_sourceTargetHomeomorph {M E : Type} [TopologicalSpace M] [TopologicalSpace E]
    (e : OpenPartialHomeomorph M E) : e.source ≃ₜ e.target where
  toFun u := ⟨e u.1, e.map_source u.2⟩
  invFun v := ⟨e.symm v.1, e.map_target v.2⟩
  left_inv u := Subtype.ext (e.left_inv u.2)
  right_inv v := Subtype.ext (e.right_inv v.2)
  continuous_toFun :=
    (e.continuousOn.comp_continuous continuous_subtype_val fun u => u.2).subtype_mk _
  continuous_invFun :=
    (e.continuousOn_symm.comp_continuous continuous_subtype_val fun v => v.2).subtype_mk _

lemma j5cE_sourceTargetHomeomorph_apply {M E : Type} [TopologicalSpace M] [TopologicalSpace E]
    (e : OpenPartialHomeomorph M E) (u : e.source) :
    (j5cE_sourceTargetHomeomorph e u : E) = e u :=
  rfl

example {M E : Type} [TopologicalSpace M] [TopologicalSpace E]
    (e : OpenPartialHomeomorph M E) (v : e.target) :
    ((j5cE_sourceTargetHomeomorph e).symm v : M) = e.symm v :=
  rfl

/-- The homeomorphism between the empty subsets of two spaces.
Source: Hatcher, *Algebraic Topology*, §3.3, p. 236 (local homology along `∅` is `H(M, M)`). -/
def j5cE_emptyHomeomorph (M E : Type) [TopologicalSpace M] [TopologicalSpace E] :
    (∅ : Set M) ≃ₜ (∅ : Set E) where
  toFun u := absurd u.2 (Set.notMem_empty _)
  invFun v := absurd v.2 (Set.notMem_empty _)
  left_inv u := absurd u.2 (Set.notMem_empty _)
  right_inv v := absurd v.2 (Set.notMem_empty _)
  continuous_toFun := continuous_of_const fun u _ => absurd u.2 (Set.notMem_empty _)
  continuous_invFun := continuous_of_const fun v _ => absurd v.2 (Set.notMem_empty _)

example : Function.Injective (j5cE_emptyHomeomorph ℕ ℕ) :=
  (j5cE_emptyHomeomorph ℕ ℕ).injective

set_option backward.isDefEq.respectTransparency false in
/-- A homeomorphism `h : U ≃ₜ V` carrying `S ∩ U` onto `S' ∩ V` as an isomorphism of pairs
`(U, U \ S) ≅ (V, V \ S')`.
Source: Hatcher, *Algebraic Topology*, §2.1 (homeomorphisms of pairs induce isomorphisms on
relative homology). -/
def j5cE_pairIso {M E : Type} [TopologicalSpace M] [TopologicalSpace E] {U : Set M} {V : Set E}
    (h : U ≃ₜ V) (S : Set M) (S' : Set E) (hS : ∀ u : U, (h u : E) ∈ S' ↔ (u : M) ∈ S) :
    TopPair.ofSubset (X := TopCat.of U) {u : U | (u : M) ∉ S} ≅
      TopPair.ofSubset (X := TopCat.of V) {v : V | (v : E) ∉ S'} :=
  TopPair.isoOfSubset (X := TopCat.of U) (Y := TopCat.of V) h fun u => not_congr (hS u)

example {M E : Type} [TopologicalSpace M] [TopologicalSpace E] {U : Set M} {V : Set E}
    (h : U ≃ₜ V) (S : Set M) (S' : Set E) (hS : ∀ u : U, (h u : E) ∈ S' ↔ (u : M) ∈ S) :
    (j5cE_pairIso h S S' hS).hom ≫ (j5cE_pairIso h S S' hS).inv = 𝟙 _ :=
  Iso.hom_inv_id _

/-- A point of `U` and its image under `h` correspond. -/
lemma j5cE_point_iff {M E : Type} [TopologicalSpace M] [TopologicalSpace E] {U : Set M}
    {V : Set E} (h : U ≃ₜ V) (u : U) :
    ∀ v : U, (h v : E) ∈ ({(h u : E)} : Set E) ↔ (v : M) ∈ ({(u : M)} : Set M) := by
  intro v
  rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
  constructor
  · intro hv
    rw [h.injective (Subtype.ext hv)]
  · intro hv
    rw [Subtype.ext hv]

set_option backward.isDefEq.respectTransparency false in
/-- Excision commutes with restriction of supports. -/
lemma j5cE_exMap_comp_supportInclusion {M : Type} [TopologicalSpace M] (U : Set M)
    {S T : Set M} (h : S ⊆ T) :
    j5cE_exMap U T ≫ supportInclusionPairMap (TopCat.of M) h =
      j5cE_resMap U h ≫ j5cE_exMap U S := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext w
    apply Subtype.ext
    rfl
  · ext w
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Transport by `h`, then excision, then restriction of supports, is restriction of supports,
then transport, then excision. -/
lemma j5cE_pairIso_chain {M E : Type} [TopologicalSpace M] [TopologicalSpace E] {U : Set M}
    {V : Set E} (h : U ≃ₜ V) {S T : Set M} {S' T' : Set E}
    (hT : ∀ u : U, (h u : E) ∈ T' ↔ (u : M) ∈ T) (hS : ∀ u : U, (h u : E) ∈ S' ↔ (u : M) ∈ S)
    (hST : S ⊆ T) (hST' : S' ⊆ T') :
    (j5cE_pairIso h T T' hT).hom ≫ j5cE_exMap V T' ≫
        supportInclusionPairMap (TopCat.of E) hST' =
      j5cE_resMap U hST ≫ (j5cE_pairIso h S S' hS).hom ≫ j5cE_exMap V S' := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext w
    apply Subtype.ext
    rfl
  · ext w
    rfl

/-- A class along `B` restricts to a class along any `A ⊆ B`, with the same point values. -/
theorem j5cE_hasClassAlong_mono {M : Type} [TopologicalSpace M] {n : ℕ}
    {μ : ∀ x : M, RelativeHomology ℚ (pointComplementPair x) n} {A B : Set M} (hAB : A ⊆ B)
    (h : HasClassAlong M n μ B) : HasClassAlong M n μ A := by
  obtain ⟨α, hα⟩ := h
  refine ⟨relativeHomologyMap ℚ n (supportInclusionPairMap (TopCat.of M) hAB) α, fun x hx => ?_⟩
  rw [← hα x (hAB hx), j5cE_relativeHomologyMap_apply_apply, ← supportInclusionPairMap_trans]

end HodgeLean.RealDefs
