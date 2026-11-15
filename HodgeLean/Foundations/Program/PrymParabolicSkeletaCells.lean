import HodgeLean.Foundations.Program.PrymParabolicSkeletaLemmas
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cExcision

/-! # Cells attached along a closed set: relative homology

Generic tools for stage H3b step C (`PrymParabolicSkeleta`): finitely many closed cells
`Φ j : D → X` attached to a closed set `A` (`hg8_Cells`), with a model deformation of
`D ∖ {c}` onto the boundary `B` (`hg8_Model`). The deformation transported to the cells
deforms `X ∖ centres` onto `A` (`hg8_cellDeform`), so `H_*(X ∖ centres, A) = 0` and
`(X, A) → (X, X ∖ centres)` is bijective on relative homology (`hg8_cells_triple`). For a finite
partition of a space into clopen pieces, the retractions of singular chains onto the pieces are
chain maps, and every relative class is the sum of its pieces (`hg8_relative_decomp`). With
excision this gives the relative homology of cells attached along `A`: the images of
`H_*(D, B)` under the cells span `H_*(X, A)` (`hg8_cells_span`) and are independent
(`hg8_cells_independent`).
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular Opposite
open Convexity

namespace HodgeLean.Foundations.Program

/-- In a short exact sequence of complexes with acyclic third term, the first map is a
quasi-isomorphism (the long exact homology sequence). -/
theorem hg8_quasiIso_f_of_acyclic {C : Type*} [Category C] [Abelian C]
    (S : ShortComplex (ChainComplex C ℕ)) (hS : S.ShortExact) (h : S.X₃.Acyclic) :
    QuasiIso S.f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hepi : Epi (HomologicalComplex.homologyMap S.f i) :=
    (hS.homology_exact₂ i).epi_f (((h i).isZero_homology).eq_of_tgt _ _)
  have hmono : Mono (HomologicalComplex.homologyMap S.f i) :=
    (hS.homology_exact₁ (i + 1) i (by simp)).mono_g (((h (i + 1)).isZero_homology).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

/-- The relative chains of a pair are acyclic when every relative homology group vanishes. -/
theorem hg8_relative_acyclic (R : Type) [CommRing R] (P : TopPair.{0})
    (h : ∀ k (x : RelativeHomology R P k), x = 0) : ((relativeChainFunctor R).obj P).Acyclic := by
  intro k
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (ModuleCat.isZero_iff_subsingleton).2 ⟨fun x y ↦ (h k x).trans (h k y).symm⟩

/-- **Vanishing from a deformation.** If the inclusion `i : A → N` has a retraction `r` and the
identity of `N` is homotopic to `i ∘ r` relative to `A`, then `H_*(N, A) = 0`. -/
theorem hg8_relHomology_eq_zero_of_deformation (R : Type) [CommRing R] {A N : TopCat.{0}}
    (i : A ⟶ N) (hi : Topology.IsEmbedding i) (r : N ⟶ A) (hri : i ≫ r = 𝟙 A)
    (H : TopCat.Homotopy (𝟙 N) (r ≫ i)) (hH : ∀ t a, H (t, i a) = i a)
    (k : ℕ) (x : RelativeHomology R (TopPair.of i hi) k) : x = 0 := by
  let P := TopPair.of i hi
  let g : P ⟶ P := TopPair.ofHom (r ≫ i) (𝟙 A) (by
    change 𝟙 A ≫ i = i ≫ (r ≫ i)
    rw [Category.id_comp, ← Category.assoc, hri, Category.id_comp])
  let HP : TopPair.Homotopy (𝟙 P) g :=
    { fst := H
      snd := TopCat.Homotopy.refl (𝟙 A)
      w := by
        ext ⟨a, t⟩
        exact hH _ a }
  have h1 := TopPair.Homotopy.relativeHomologyMap_apply_eq (R := R) HP k x
  let F := (singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)
  have h0 : (relativeChainFunctor R).map g = 0 := by
    apply (cancel_epi (cokernel.π (F.map i))).1
    change cokernel.π _ ≫ cokernel.desc _ _ _ = cokernel.π _ ≫ 0
    erw [cokernel.π_desc, comp_zero]
    change F.map (r ≫ i) ≫ cokernel.π (F.map i) = 0
    rw [F.map_comp, Category.assoc, cokernel.condition, comp_zero]
  have hg : relativeHomologyMap R k g = 0 := by
    simp only [relativeHomologyMap, relativeHomologyFunctor, Functor.comp_map, h0,
      Functor.map_zero, ModuleCat.hom_zero]
    rfl
  have hid : relativeHomologyMap R k (𝟙 P) = LinearMap.id := by
    simp only [relativeHomologyMap, CategoryTheory.Functor.map_id, ModuleCat.hom_id]
  rw [hid, hg] at h1
  exact h1


/-- The pair `(N, A)` for `A ⊆ N ⊆ X`, with `A` as a space mapping into `N`. -/
abbrev hg8_nestedPair {X : TopCat.{0}} {A N : Set X} (hAN : A ⊆ N) : TopPair.{0} :=
  TopPair.of (TopCat.ofHom (⟨Set.inclusion hAN, continuous_inclusion hAN⟩ : C(A, N)))
    (Topology.IsEmbedding.inclusion hAN)

set_option backward.isDefEq.respectTransparency false in
/-- **Triples.** For `A ⊆ N ⊆ X` with `H_*(N, A) = 0`, the map `(X, A) → (X, N)` is bijective on
relative homology.
Source: Hatcher, *Algebraic Topology*, §2.1 (the long exact sequence of a triple). -/
theorem hg8_triple_bijective (R : Type) [CommRing R] {X : TopCat.{0}} {A N : Set X}
    (hAN : A ⊆ N) (h : ∀ k (x : RelativeHomology R (hg8_nestedPair hAN) k), x = 0) (k : ℕ) :
    Function.Bijective (relativeHomologyMap R k
      (TopPair.ofSubsetHom (𝟙 X) (fun _ ha ↦ hAN ha) :
        TopPair.ofSubset A ⟶ TopPair.ofSubset N)) := by
  let F := (singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)
  let f := ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom
  let g := ((chainPairFunctor R).obj (TopPair.ofSubset N)).hom
  let u := ((chainPairFunctor R).obj (hg8_nestedPair hAN)).hom
  have w : f ≫ 𝟙 _ = u ≫ g := by
    rw [Category.comp_id]
    change F.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ X) =
      F.map (TopCat.ofHom ⟨Set.inclusion hAN, continuous_inclusion hAN⟩ :
        TopCat.of A ⟶ TopCat.of N) ≫
      F.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of N ⟶ X)
    rw [← F.map_comp]
    rfl
  have : Mono f := relativeChainMap_mono R _
  have : Mono g := relativeChainMap_mono R _
  have hu : QuasiIso u := hg8_quasiIso_f_of_acyclic _
    (relativeChainShortComplex_shortExact R (hg8_nestedPair hAN))
    (hg8_relative_acyclic R _ h)
  have hq := b6m_cokernelMap_quasiIso R f g u (𝟙 _) w
  have heq : (relativeChainFunctor R).map (TopPair.ofSubsetHom (𝟙 X) (fun _ ha ↦ hAN ha) :
      TopPair.ofSubset A ⟶ TopPair.ofSubset N) = cokernel.map f g u (𝟙 _) w := by
    apply (cancel_epi (cokernel.π f)).1
    erw [cokernel.π_desc, cokernel.π_desc]
    change F.map (𝟙 X) ≫ _ = _
    rw [F.map_id]
    rfl
  have hiso : IsIso (HomologicalComplex.homologyMap
      ((relativeChainFunctor R).map (TopPair.ofSubsetHom (𝟙 X) (fun _ ha ↦ hAN ha) :
        TopPair.ofSubset A ⟶ TopPair.ofSubset N)) k) := by
    rw [heq]; infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hiso



/-- Finitely many closed cells `Φ j : D → X` attached to a closed set `A`: closed embeddings
sending the boundary `B` into `A`, with interiors disjoint from `A` and from each other, and
covering the complement of `A`.
Source: Hatcher, *Algebraic Topology*, §2.2 (cell complexes; characteristic maps). -/
structure hg8_Cells {X D J : Type} [TopologicalSpace X] [TopologicalSpace D] (A : Set X)
    (B : Set D) (Φ : J → C(D, X)) : Prop where
  closedA : IsClosed A
  emb : ∀ j, Topology.IsClosedEmbedding (Φ j)
  bdry : ∀ j b, b ∈ B → Φ j b ∈ A
  int : ∀ j y, y ∉ B → Φ j y ∉ A
  disj : ∀ j k y z, y ∉ B → z ∉ B → Φ j y = Φ k z → j = k
  cov : ∀ x, x ∉ A → ∃ j y, Φ j y = x

/-- A model cell `(D, B)` with a centre `c ∉ B` and a deformation of `D ∖ {c}` onto `B`
fixing `B`.
Source: Hatcher, *Algebraic Topology*, §2.1 (deformation retractions; Example 2.23). -/
structure hg8_Model {D : Type} [TopologicalSpace D] (B : Set D) (c : D) where
  /-- The deformation of `D ∖ {c}`. -/
  ρ : C(unitInterval × ({c}ᶜ : Set D), ({c}ᶜ : Set D))
  closed : IsClosed B
  centre : c ∉ B
  zero : ∀ y, ρ (0, y) = y
  one : ∀ y, (ρ (1, y) : D) ∈ B
  fix : ∀ t (y : ({c}ᶜ : Set D)), (y : D) ∈ B → ρ (t, y) = y

/-- The centres `Φ j c` of the cells. -/
def hg8_centres {X D J : Type} [TopologicalSpace X] [TopologicalSpace D] (Φ : J → C(D, X))
    (c : D) : Set X :=
  Set.range fun j ↦ Φ j c

/-- `A` contains no centre. -/
theorem hg8_A_sub_N {X D J : Type} [TopologicalSpace X] [TopologicalSpace D] {A : Set X}
    {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) {c : D} (hc : c ∉ B) :
    A ⊆ (hg8_centres Φ c)ᶜ := by
  rintro x hx ⟨j, rfl⟩
  exact hC.int j c hc hx

/-- A point outside `A` lies in the interior of a cell. -/
theorem hg8_cells_exists {X D J : Type} [TopologicalSpace X] [TopologicalSpace D] {A : Set X}
    {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) (x : X) (hx : x ∉ A) :
    ∃ p : J × D, Φ p.1 p.2 = x ∧ p.2 ∉ B := by
  obtain ⟨j, y, rfl⟩ := hC.cov x hx
  exact ⟨(j, y), rfl, fun hy ↦ hx (hC.bdry j y hy)⟩

/-- The deformation of `X ∖ centres` onto `A`. -/
def hg8_cellDeform {X D J : Type} [TopologicalSpace X] [TopologicalSpace D] {A : Set X}
    {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) {c : D} (M : hg8_Model B c)
    (p : unitInterval × ((hg8_centres Φ c)ᶜ : Set X)) : X := by
  classical
  exact if hx : (p.2 : X) ∈ A then p.2 else
    let q := (hg8_cells_exists hC p.2 hx).choose
    Φ q.1 (M.ρ (p.1, ⟨q.2, fun h ↦ p.2.2 ⟨q.1, by
      rw [← (hg8_cells_exists hC p.2 hx).choose_spec.1]
      exact congrArg (Φ q.1) h.symm⟩⟩))

/-- The deformation fixes `A`. -/
theorem hg8_cellDeform_A {X D J : Type} [TopologicalSpace X] [TopologicalSpace D] {A : Set X}
    {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) {c : D} (M : hg8_Model B c)
    (p : unitInterval × ((hg8_centres Φ c)ᶜ : Set X)) (hp : (p.2 : X) ∈ A) :
    hg8_cellDeform hC M p = p.2 := by
  simp [hg8_cellDeform, hp]

/-- On the cell `j`, the deformation is `Φ j ∘ ρ ∘ (Φ j)⁻¹`. -/
theorem hg8_cellDeform_cell {X D J : Type} [TopologicalSpace X] [TopologicalSpace D] {A : Set X}
    {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) {c : D} (M : hg8_Model B c)
    (t : unitInterval) (j : J) (y : ({c}ᶜ : Set D)) (hy : Φ j y ∈ (hg8_centres Φ c)ᶜ) :
    hg8_cellDeform hC M (t, ⟨Φ j y, hy⟩) = Φ j (M.ρ (t, y)) := by
  by_cases hyB : (y : D) ∈ B
  · rw [hg8_cellDeform_A hC M _ (hC.bdry j y hyB), M.fix t y hyB]
  · have hx : Φ j y ∉ A := hC.int j y hyB
    simp only [hg8_cellDeform, hx, dite_false]
    have hs := (hg8_cells_exists hC (Φ j y) hx).choose_spec
    have key : ∀ (q : J × D) (h1 : q.1 = j) (h2 : q.2 = (y : D)) (hne : q.2 ∈ ({c}ᶜ : Set D)),
        Φ q.1 (M.ρ (t, ⟨q.2, hne⟩)) = Φ j (M.ρ (t, y)) := by
      rintro ⟨q1, q2⟩ h1 h2 hne
      simp only at h1 h2
      subst h1 h2
      rfl
    exact key _ (hC.disj _ _ _ _ hs.2 hyB hs.1) ((hC.emb _).injective
      (hs.1.trans (by rw [hC.disj _ _ _ _ hs.2 hyB hs.1]))) _

/-- A point of a cell other than its centre has preimage other than `c`. -/
theorem hg8_symm_ne_centre {X D J : Type} [TopologicalSpace X] [TopologicalSpace D]
    {Φ : J → C(D, X)} (j : J) (hj : Topology.IsEmbedding (Φ j)) {c : D} (x : X)
    (hx : x ∈ Set.range (Φ j)) (hxN : x ∈ (hg8_centres Φ c)ᶜ) :
    hj.toHomeomorph.symm ⟨x, hx⟩ ∈ ({c}ᶜ : Set D) := by
  intro h
  apply hxN
  refine ⟨j, ?_⟩
  have := congrArg Subtype.val (hj.toHomeomorph.apply_symm_apply ⟨x, hx⟩)
  rw [Set.mem_singleton_iff.1 h] at this
  exact this

/-- The deformation is continuous: it is continuous on `A` and on each closed cell. -/
theorem hg8_cellDeform_continuous {X D J : Type} [TopologicalSpace X] [TopologicalSpace D]
    [Finite J] {A : Set X} {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) {c : D}
    (M : hg8_Model B c) : Continuous (hg8_cellDeform hC M) := by
  let S : Option J → Set (unitInterval × ((hg8_centres Φ c)ᶜ : Set X)) := fun o ↦
    match o with
    | none => {p | (p.2 : X) ∈ A}
    | some j => {p | (p.2 : X) ∈ Set.range (Φ j)}
  have hsnd : Continuous fun p : unitInterval × ((hg8_centres Φ c)ᶜ : Set X) ↦ (p.2 : X) :=
    continuous_subtype_val.comp continuous_snd
  refine LocallyFinite.continuous (locallyFinite_of_finite S) ?_ ?_ ?_
  · refine Set.eq_univ_of_forall fun p ↦ Set.mem_iUnion.2 ?_
    by_cases hp : (p.2 : X) ∈ A
    · exact ⟨none, hp⟩
    · obtain ⟨j, y, hy⟩ := hC.cov _ hp
      exact ⟨some j, y, hy⟩
  · rintro (_ | j)
    · exact hC.closedA.preimage hsnd
    · exact (hC.emb j).isClosed_range.preimage hsnd
  · rintro (_ | j)
    · exact hsnd.continuousOn.congr fun p hp ↦ hg8_cellDeform_A hC M p hp
    · rw [continuousOn_iff_continuous_domRestrict]
      let e := (hC.emb j).isEmbedding.toHomeomorph
      have hfun : (S (some j)).domRestrict (hg8_cellDeform hC M) = fun q ↦
          Φ j (M.ρ (q.1.1, ⟨e.symm ⟨q.1.2.1, q.2⟩,
            hg8_symm_ne_centre j (hC.emb j).isEmbedding _ q.2 q.1.2.2⟩)) := by
        funext q
        rw [Set.domRestrict_apply]
        have hq : q.1 = (q.1.1, ⟨Φ j (e.symm ⟨q.1.2.1, q.2⟩), by
            rw [show Φ j (e.symm ⟨q.1.2.1, q.2⟩) = q.1.2.1 from
              congrArg Subtype.val (e.apply_symm_apply ⟨q.1.2.1, q.2⟩)]
            exact q.1.2.2⟩) := by
          refine Prod.ext rfl (Subtype.ext ?_)
          exact (congrArg Subtype.val (e.apply_symm_apply ⟨q.1.2.1, q.2⟩)).symm
        exact (congrArg (hg8_cellDeform hC M) hq).trans (hg8_cellDeform_cell hC M _ j
          ⟨_, hg8_symm_ne_centre j (hC.emb j).isEmbedding _ q.2 q.1.2.2⟩ _)
      rw [hfun]
      refine (Φ j).continuous.comp (continuous_subtype_val.comp (M.ρ.continuous.comp ?_))
      refine Continuous.prodMk (continuous_fst.comp continuous_subtype_val) ?_
      refine Continuous.subtype_mk (e.symm.continuous.comp ?_) _
      exact Continuous.subtype_mk (hsnd.comp continuous_subtype_val) _

/-- A point of a cell other than its centre is not a centre. -/
theorem hg8_cell_not_centre {X D J : Type} [TopologicalSpace X] [TopologicalSpace D]
    {A : Set X} {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) {c : D} (hc : c ∉ B)
    (j : J) (z : D) (hz : z ≠ c) : Φ j z ∈ (hg8_centres Φ c)ᶜ := by
  rintro ⟨k, hk⟩
  by_cases hzB : z ∈ B
  · have hk' : Φ k c = Φ j z := hk
    exact hC.int k c hc (hk' ▸ hC.bdry j z hzB)
  · have hjk := hC.disj k j c z hc hzB hk
    subst hjk
    exact hz ((hC.emb k).injective hk).symm

/-- A point of `X ∖ centres` lies in `A` or in a cell away from its centre. -/
theorem hg8_cellDeform_cases {X D J : Type} [TopologicalSpace X] [TopologicalSpace D]
    {A : Set X} {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) {c : D}
    (x : ((hg8_centres Φ c)ᶜ : Set X)) :
    (x : X) ∈ A ∨ ∃ (j : J) (y : ({c}ᶜ : Set D)), Φ j y = x := by
  by_cases hx : (x : X) ∈ A
  · exact Or.inl hx
  · obtain ⟨j, y, hy⟩ := hC.cov _ hx
    refine Or.inr ⟨j, ⟨y, fun h ↦ x.2 ⟨j, ?_⟩⟩, hy⟩
    rw [← hy, Set.mem_singleton_iff.1 h]

/-- The deformation stays in `X ∖ centres`, starts at the identity and ends in `A`. -/
theorem hg8_cellDeform_props {X D J : Type} [TopologicalSpace X] [TopologicalSpace D]
    {A : Set X} {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) {c : D}
    (M : hg8_Model B c) :
    (∀ p, hg8_cellDeform hC M p ∈ (hg8_centres Φ c)ᶜ) ∧
      (∀ x, hg8_cellDeform hC M (0, x) = x) ∧ (∀ x, hg8_cellDeform hC M (1, x) ∈ A) := by
  refine ⟨fun p ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩ <;>
  [rcases hg8_cellDeform_cases hC p.2 with hx | ⟨j, y, hy⟩;
   rcases hg8_cellDeform_cases hC x with hx | ⟨j, y, hy⟩;
   rcases hg8_cellDeform_cases hC x with hx | ⟨j, y, hy⟩]
  · rw [hg8_cellDeform_A hC M _ hx]; exact p.2.2
  · obtain ⟨t, x⟩ := p
    obtain ⟨x, hxN⟩ := x
    simp only at hy
    subst hy
    rw [hg8_cellDeform_cell hC M t j y hxN]
    exact hg8_cell_not_centre hC M.centre j _ (M.ρ (t, y)).2
  · exact hg8_cellDeform_A hC M _ hx
  · obtain ⟨x, hxN⟩ := x
    simp only at hy
    subst hy
    rw [hg8_cellDeform_cell hC M 0 j y hxN, M.zero]
  · rw [hg8_cellDeform_A hC M (1, x) hx]; exact hx
  · obtain ⟨x, hxN⟩ := x
    simp only at hy
    subst hy
    rw [hg8_cellDeform_cell hC M 1 j y hxN]
    exact hC.bdry j _ (M.one y)

/-- **Removing the centres.** For cells attached to `A`, the inclusion `(X, A) → (X, X ∖ centres)`
is bijective on relative homology: `X ∖ centres` deforms onto `A`.
Source: Hatcher, *Algebraic Topology*, Proposition 2.22 and Lemma 2.34 (proof). -/
theorem hg8_cells_triple (R : Type) [CommRing R] {X D J : Type} [TopologicalSpace X]
    [TopologicalSpace D] [Finite J] {A : Set X} {B : Set D} {Φ : J → C(D, X)}
    (hC : hg8_Cells A B Φ) {c : D} (M : hg8_Model B c) (k : ℕ) :
    Function.Bijective (relativeHomologyMap R k
      (TopPair.ofSubsetHom (𝟙 (TopCat.of X)) (fun _ ha ↦ hg8_A_sub_N hC M.centre ha) :
        TopPair.ofSubset (X := TopCat.of X) A ⟶
          TopPair.ofSubset (X := TopCat.of X) (hg8_centres Φ c)ᶜ)) := by
  have hAN := hg8_A_sub_N hC M.centre
  obtain ⟨hmem, hzero, hone⟩ := hg8_cellDeform_props hC M
  refine hg8_triple_bijective R (X := TopCat.of X) hAN ?_ k
  let r : TopCat.of ((hg8_centres Φ c)ᶜ : Set X) ⟶ TopCat.of A :=
    TopCat.ofHom ⟨fun x ↦ ⟨hg8_cellDeform hC M (1, x), hone x⟩,
      ((hg8_cellDeform_continuous hC M).comp (Continuous.prodMk continuous_const
        continuous_id)).subtype_mk _⟩
  let i : TopCat.of A ⟶ TopCat.of ((hg8_centres Φ c)ᶜ : Set X) :=
    TopCat.ofHom ⟨Set.inclusion hAN, continuous_inclusion hAN⟩
  have hri : i ≫ r = 𝟙 _ := by
    ext a
    exact hg8_cellDeform_A hC M _ a.2
  let H : TopCat.Homotopy (𝟙 _) (r ≫ i) :=
    { toFun := fun p ↦ ⟨hg8_cellDeform hC M p, hmem p⟩
      continuous_toFun := (hg8_cellDeform_continuous hC M).subtype_mk _
      map_zero_left := fun x ↦ Subtype.ext (hzero x)
      map_one_left := fun x ↦ rfl }
  exact hg8_relHomology_eq_zero_of_deformation R i (Topology.IsEmbedding.inclusion hAN) r hri H
    (fun t a ↦ Subtype.ext (hg8_cellDeform_A hC M _ a.2))

/-! ## Splitting relative chains over a clopen partition -/

section Splitting

open scoped _root_.Simplicial

section Retraction

variable {C : Type*} [Category C] [HasCoproducts.{0} C] [Preadditive C]
  {X Y : SSet.{0}} (f : X ⟶ Y) (R : C)

/-- The retraction kills simplices outside the image. -/
theorem hg8_ι_retraction_zero (n : ℕ) (y : Y _⦋n⦌) (hy : ¬ ∃ x, f.app (op ⦋n⦌) x = y) :
    Y.ιChainComplex y ≫ SSet.chainComplexMapRetraction f R n = 0 := by
  refine (Cofan.IsColimit.fac (Y.isColimitChainComplexXCofan R n) _ y).trans ?_
  rw [dite_eq_right_of_eq_false (eq_false hy)]

/-- The retraction of the chains of `Y` onto those of `X`, as a chain map, when `f` is injective
and every simplex of `Y` with a face in the image of `f` lies in the image of `f`. -/
def hg8_retraction (hinj : ∀ n, Function.Injective (f.app (op ⦋n⦌)))
    (hface : ∀ (n : ℕ) (y : Y _⦋n + 1⦌) (i : Fin (n + 2)) (x : X _⦋n⦌),
      f.app _ x = Y.δ i y → ∃ x', f.app _ x' = y) :
    Y.chainComplex R ⟶ X.chainComplex R where
  f n := SSet.chainComplexMapRetraction f R n
  comm' := by
    rintro i j (rfl : j + 1 = i)
    refine SSet.chainComplex_hom_ext fun y ↦ ?_
    rw [SSet.ιChainComplex_d_assoc, Preadditive.sum_comp]
    by_cases hy : ∃ x, f.app (op ⦋j + 1⦌) x = y
    · obtain ⟨x, rfl⟩ := hy
      rw [SSet.ιChainComplex_comp_chainComplexMapRetraction_assoc f R _ x (hinj _),
        SSet.ιChainComplex_d]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Preadditive.zsmul_comp]
      congr 1
      have hn : Y.δ i (f.app _ x) = f.app _ (X.δ i x) :=
        (NatTrans.naturality_apply f (SimplexCategory.δ i).op x).symm
      rw [hn, SSet.ιChainComplex_comp_chainComplexMapRetraction f R _ _ (hinj _)]
    · rw [← Category.assoc, hg8_ι_retraction_zero f R _ y hy, zero_comp]
      refine (Finset.sum_eq_zero fun i _ ↦ ?_).symm
      rw [Preadditive.zsmul_comp, hg8_ι_retraction_zero f R _ _ ?_, zsmul_zero]
      rintro ⟨x, hx⟩
      exact hy (hface j y i x hx)

end Retraction

/-- Singular simplices map by composition. -/
theorem hg8_toSSet_map_apply {Y Z : TopCat.{0}} (ι : Z ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj Z).obj n) :
    Y.toSSetObjEquiv n ((TopCat.toSSet.map ι).app n x) =
      (ConcreteCategory.hom ι).comp (Z.toSSetObjEquiv n x) :=
  rfl

/-- An injective map is injective on singular simplices. -/
theorem hg8_toSSet_injective {Y Z : TopCat.{0}} (ι : Z ⟶ Y) (hι : Function.Injective ι)
    (n : SimplexCategoryᵒᵖ) : Function.Injective ((TopCat.toSSet.map ι).app n) := by
  intro x x' h
  apply (Z.toSSetObjEquiv n).injective
  ext z
  apply hι
  exact congrArg (fun y ↦ Y.toSSetObjEquiv n y z) h

/-- A singular simplex with values in the range of an embedding lifts through it. -/
theorem hg8_toSSet_lift {Y Z : TopCat.{0}} (ι : Z ⟶ Y) (hι : Topology.IsEmbedding ι)
    (n : SimplexCategoryᵒᵖ) (y : (TopCat.toSSet.obj Y).obj n)
    (hy : Set.range (Y.toSSetObjEquiv n y) ⊆ Set.range ι) :
    ∃ x, (TopCat.toSSet.map ι).app n x = y := by
  let e := hι.toHomeomorph
  let g : C(StdSimplex ℝ (Fin (n.unop.len + 1)), Z) :=
    ⟨fun z ↦ e.symm ⟨Y.toSSetObjEquiv n y z, hy ⟨z, rfl⟩⟩,
      e.symm.continuous.comp ((Y.toSSetObjEquiv n y).continuous.subtype_mk _)⟩
  refine ⟨(Z.toSSetObjEquiv n).symm g, (Y.toSSetObjEquiv n).injective ?_⟩
  ext z
  rw [hg8_toSSet_map_apply, Equiv.apply_symm_apply]
  exact congrArg Subtype.val (e.apply_symm_apply ⟨_, hy ⟨z, rfl⟩⟩)

/-- For an embedding with clopen range, a simplex with a face in the range lies in the range:
simplices are connected. -/
theorem hg8_toSSet_clopen_face {Y Z : TopCat.{0}} (ι : Z ⟶ Y) (hι : Topology.IsEmbedding ι)
    (hW : IsClopen (Set.range ι)) (n : ℕ) (y : (TopCat.toSSet.obj Y) _⦋n + 1⦌) (i : Fin (n + 2))
    (x : (TopCat.toSSet.obj Z) _⦋n⦌)
    (hx : (TopCat.toSSet.map ι).app _ x = (TopCat.toSSet.obj Y).δ i y) :
    ∃ x', (TopCat.toSSet.map ι).app _ x' = y := by
  apply hg8_toSSet_lift ι hι
  have hc : IsPreconnected (Set.range (Y.toSSetObjEquiv _ y)) :=
    isPreconnected_range (Y.toSSetObjEquiv _ y).continuous
  refine hc.subset_isClopen hW ?_
  obtain ⟨z⟩ : Nonempty (StdSimplex ℝ (Fin (n + 1))) := ⟨StdSimplex.single 0⟩
  refine ⟨Y.toSSetObjEquiv _ y (StdSimplex.map (SimplexCategory.δ i) z), ⟨_, rfl⟩, ?_⟩
  have := congrArg (fun w ↦ Y.toSSetObjEquiv _ w z) hx
  simp only [hg8_toSSet_map_apply] at this
  refine ⟨Z.toSSetObjEquiv _ x z, this.trans ?_⟩
  rfl

/-- The retraction of singular chains onto an embedded subspace with clopen range. -/
def hg8_clopenRet (R : Type) [CommRing R] {Y Z : TopCat.{0}} (ι : Z ⟶ Y)
    (hι : Topology.IsEmbedding ι) (hW : IsClopen (Set.range ι)) :
    SingularChainComplex R Y ⟶ SingularChainComplex R Z :=
  hg8_retraction (TopCat.toSSet.map ι) (ModuleCat.of R R)
    (fun _ ↦ hg8_toSSet_injective ι hι.injective _)
    (fun n y i x hx ↦ hg8_toSSet_clopen_face ι hι hW n y i x hx)

/-- The clopen retraction on a simplex of the subspace. -/
@[reassoc]
theorem hg8_ι_clopenRet (R : Type) [CommRing R] {Y Z : TopCat.{0}} (ι : Z ⟶ Y)
    (hι : Topology.IsEmbedding ι) (hW : IsClopen (Set.range ι)) (n : ℕ)
    (x : (TopCat.toSSet.obj Z) _⦋n⦌) :
    (TopCat.toSSet.obj Y).ιChainComplex ((TopCat.toSSet.map ι).app _ x) ≫
      (hg8_clopenRet R ι hι hW).f n = (TopCat.toSSet.obj Z).ιChainComplex x :=
  SSet.ιChainComplex_comp_chainComplexMapRetraction _ _ _ x (hg8_toSSet_injective ι hι.injective _)

/-- The clopen retraction on a simplex outside the subspace. -/
@[reassoc]
theorem hg8_ι_clopenRet_zero (R : Type) [CommRing R] {Y Z : TopCat.{0}} (ι : Z ⟶ Y)
    (hι : Topology.IsEmbedding ι) (hW : IsClopen (Set.range ι)) (n : ℕ)
    (y : (TopCat.toSSet.obj Y) _⦋n⦌) (hy : ¬ ∃ x, (TopCat.toSSet.map ι).app _ x = y) :
    (TopCat.toSSet.obj Y).ιChainComplex y ≫ (hg8_clopenRet R ι hι hW).f n = 0 :=
  hg8_ι_retraction_zero _ _ _ y hy

/-- Every simplex lies in one piece of a clopen partition. -/
theorem hg8_simplex_mem_piece {Y : TopCat.{0}} {J : Type} {Z : J → TopCat.{0}}
    (ι : ∀ j, Z j ⟶ Y) (hι : ∀ j, Topology.IsEmbedding (ι j))
    (hW : ∀ j, IsClopen (Set.range (ι j))) (hcov : ∀ y, ∃ j, y ∈ Set.range (ι j)) (n : ℕ)
    (y : (TopCat.toSSet.obj Y) _⦋n⦌) : ∃ j x, (TopCat.toSSet.map (ι j)).app _ x = y := by
  obtain ⟨j, hj⟩ := hcov (Y.toSSetObjEquiv _ y (StdSimplex.single 0))
  refine ⟨j, hg8_toSSet_lift (ι j) (hι j) _ y ?_⟩
  exact (isPreconnected_range (Y.toSSetObjEquiv _ y).continuous).subset_isClopen (hW j)
    ⟨_, ⟨_, rfl⟩, hj⟩

/-- A simplex lies in at most one piece of a disjoint family. -/
theorem hg8_simplex_piece_unique {Y : TopCat.{0}} {J : Type} {Z : J → TopCat.{0}}
    (ι : ∀ j, Z j ⟶ Y) (hdisj : ∀ j k, j ≠ k → Disjoint (Set.range (ι j)) (Set.range (ι k)))
    (n : ℕ) (j k : J) (x : (TopCat.toSSet.obj (Z j)) _⦋n⦌) (x' : (TopCat.toSSet.obj (Z k)) _⦋n⦌)
    (h : (TopCat.toSSet.map (ι j)).app _ x = (TopCat.toSSet.map (ι k)).app _ x') : j = k := by
  by_contra hjk
  have := congrArg (fun w ↦ Y.toSSetObjEquiv _ w (StdSimplex.single 0)) h
  simp only [hg8_toSSet_map_apply] at this
  exact Set.disjoint_left.1 (hdisj j k hjk) ⟨_, this⟩ ⟨_, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- For a finite partition of `Y` into clopen embedded pieces, the retractions followed by the
inclusions sum to the identity of the singular chains. -/
theorem hg8_clopenRet_sum (R : Type) [CommRing R] {Y : TopCat.{0}} {J : Type} [Fintype J]
    {Z : J → TopCat.{0}} (ι : ∀ j, Z j ⟶ Y) (hι : ∀ j, Topology.IsEmbedding (ι j))
    (hW : ∀ j, IsClopen (Set.range (ι j)))
    (hdisj : ∀ j k, j ≠ k → Disjoint (Set.range (ι j)) (Set.range (ι k)))
    (hcov : ∀ y, ∃ j, y ∈ Set.range (ι j)) :
    ∑ j, hg8_clopenRet R (ι j) (hι j) (hW j) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (ι j) = 𝟙 _ := by
  ext n : 1
  rw [show (∑ j, hg8_clopenRet R (ι j) (hι j) (hW j) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (ι j)).f n =
      ∑ j, (hg8_clopenRet R (ι j) (hι j) (hW j) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (ι j)).f n from
    (HomologicalComplex.eval _ _ n).map_sum _ _]
  refine SSet.chainComplex_hom_ext fun y ↦ ?_
  erw [Preadditive.comp_sum, HomologicalComplex.id_f, Category.comp_id]
  obtain ⟨j, x, rfl⟩ := hg8_simplex_mem_piece ι hι hW hcov n y
  rw [Finset.sum_eq_single j]
  · rw [HomologicalComplex.comp_f, ← Category.assoc, hg8_ι_clopenRet]
    exact SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map (ι j)) (ModuleCat.of R R) x
  · intro k _ hk
    rw [HomologicalComplex.comp_f, ← Category.assoc, hg8_ι_clopenRet_zero, zero_comp]
    rintro ⟨x', hx'⟩
    exact hk (hg8_simplex_piece_unique ι hdisj n k j x' x hx')
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The inclusion `W ∩ V → V` for subsets `W`, `V` of `Y`, with `W ∩ V` as a subset of `W`. -/
def hg8_interIncl {Y : TopCat.{0}} (W V : Set Y) :
    TopCat.of (Subtype.val ⁻¹' V : Set W) ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1.1, x.2⟩, by fun_prop⟩

/-- `hg8_interIncl` is an embedding. -/
theorem hg8_interIncl_isEmbedding {Y : TopCat.{0}} (W V : Set Y) :
    Topology.IsEmbedding (hg8_interIncl W V) := by
  refine Topology.IsEmbedding.of_comp (by fun_prop) continuous_subtype_val ?_
  show Topology.IsEmbedding (fun x : (Subtype.val ⁻¹' V : Set W) ↦ (x.1.1 : Y))
  exact Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal

/-- The range of `hg8_interIncl W V` is `V ∩ W`. -/
theorem hg8_interIncl_range {Y : TopCat.{0}} (W V : Set Y) :
    Set.range (hg8_interIncl W V) = Subtype.val ⁻¹' W := by
  ext v
  exact ⟨fun ⟨x, hx⟩ ↦ hx ▸ x.1.2, fun hv ↦ ⟨⟨⟨v.1, hv⟩, v.2⟩, rfl⟩⟩

/-- The range of `hg8_interIncl W V` is clopen in `V` when `W` is clopen. -/
theorem hg8_interIncl_clopen {Y : TopCat.{0}} (W V : Set Y) (hW : IsClopen W) :
    IsClopen (Set.range (hg8_interIncl W V)) := by
  rw [hg8_interIncl_range]
  exact hW.preimage continuous_subtype_val

/-- The inclusion of a clopen subset has clopen range. -/
theorem hg8_subset_clopen {Y : TopCat.{0}} (W : Set Y) (hW : IsClopen W) :
    IsClopen (Set.range (topologicalSubsetInclusion Y W)) := by
  rw [show Set.range (topologicalSubsetInclusion Y W) = W from Subtype.range_val]
  exact hW

/-- The retraction onto a clopen subset `W`, as a map of singular chains. -/
abbrev hg8_subsetRet (R : Type) [CommRing R] {Y : TopCat.{0}} (W : Set Y) (hW : IsClopen W) :
    SingularChainComplex R Y ⟶ SingularChainComplex R (TopCat.of W) :=
  hg8_clopenRet R (topologicalSubsetInclusion Y W) Topology.IsEmbedding.subtypeVal
    (hg8_subset_clopen W hW)

set_option backward.isDefEq.respectTransparency false in
/-- The retraction onto `W` sends chains of `V` to chains of `W ∩ V`. -/
theorem hg8_subsetRet_square (R : Type) [CommRing R] {Y : TopCat.{0}} (W V : Set Y)
    (hW : IsClopen W) :
    ((chainPairFunctor R).obj (TopPair.ofSubset V)).hom ≫ hg8_subsetRet R W hW =
      hg8_clopenRet R (hg8_interIncl W V) (hg8_interIncl_isEmbedding W V)
        (hg8_interIncl_clopen W V hW) ≫
        ((chainPairFunctor R).obj
          (TopPair.ofSubset (X := TopCat.of W) (Subtype.val ⁻¹' V))).hom := by
  ext n : 1
  refine SSet.chainComplex_hom_ext fun v ↦ ?_
  change (TopCat.toSSet.obj (TopCat.of V)).ιChainComplex v ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (topologicalSubsetInclusion Y V))
        (ModuleCat.of R R)).f n ≫ (hg8_subsetRet R W hW).f n =
    (TopCat.toSSet.obj (TopCat.of V)).ιChainComplex v ≫
      (hg8_clopenRet R (hg8_interIncl W V) (hg8_interIncl_isEmbedding W V)
        (hg8_interIncl_clopen W V hW)).f n ≫
      (SSet.chainComplexMap (TopCat.toSSet.map
        (topologicalSubsetInclusion (TopCat.of W) (Subtype.val ⁻¹' V))) (ModuleCat.of R R)).f n
  rw [SSet.ι_chainComplexMap_f_assoc]
  by_cases hv : ∃ x, (TopCat.toSSet.map (hg8_interIncl W V)).app _ x = v
  · obtain ⟨x, rfl⟩ := hv
    have ha : (TopCat.toSSet.map (topologicalSubsetInclusion Y V)).app _
        ((TopCat.toSSet.map (hg8_interIncl W V)).app (op ⦋n⦌) x) =
        (TopCat.toSSet.map (topologicalSubsetInclusion Y W)).app _
          ((TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of W) (Subtype.val ⁻¹' V))).app _
            x) := rfl
    rw [ha]
    erw [hg8_ι_clopenRet, hg8_ι_clopenRet_assoc R (hg8_interIncl W V)
      (hg8_interIncl_isEmbedding W V) (hg8_interIncl_clopen W V hW) n x, SSet.ι_chainComplexMap_f]
  · erw [hg8_ι_clopenRet_zero_assoc R (hg8_interIncl W V) (hg8_interIncl_isEmbedding W V)
      (hg8_interIncl_clopen W V hW) n v hv, zero_comp]
    refine hg8_ι_clopenRet_zero R _ _ _ n _ ?_
    rintro ⟨w, hw⟩
    apply hv
    refine hg8_toSSet_lift _ (hg8_interIncl_isEmbedding W V) _ v ?_
    rintro _ ⟨z, rfl⟩
    rw [hg8_interIncl_range]
    have := congrArg (fun u ↦ Y.toSSetObjEquiv _ u z) hw
    simp only [hg8_toSSet_map_apply] at this
    change ((TopCat.of V).toSSetObjEquiv _ v z).1 ∈ W
    rw [← show ((TopCat.of W).toSSetObjEquiv _ w z).1 = ((TopCat.of V).toSSetObjEquiv _ v z).1
      from this]
    exact ((TopCat.of W).toSSetObjEquiv _ w z).2

/-- The retraction onto a clopen `W` on relative chains of `(Y, V)`. -/
def hg8_relRet (R : Type) [CommRing R] {Y : TopCat.{0}} (W V : Set Y) (hW : IsClopen W) :
    (relativeChainFunctor R).obj (TopPair.ofSubset V) ⟶
      (relativeChainFunctor R).obj (TopPair.ofSubset (X := TopCat.of W) (Subtype.val ⁻¹' V)) :=
  cokernel.map _ _ _ _ (hg8_subsetRet_square R W V hW)

set_option backward.isDefEq.respectTransparency false in
/-- For a finite clopen partition, the relative retractions followed by the inclusions sum to the
identity of the relative chains. -/
theorem hg8_relRet_sum (R : Type) [CommRing R] {Y : TopCat.{0}} {J : Type} [Fintype J]
    (W : J → Set Y) (hW : ∀ j, IsClopen (W j)) (hdisj : ∀ j k, j ≠ k → Disjoint (W j) (W k))
    (hcov : ∀ y, ∃ j, y ∈ W j) (V : Set Y) :
    ∑ j, hg8_relRet R (W j) V (hW j) ≫
      (relativeChainFunctor R).map (b6m_subspacePairMap Y (W j) V) = 𝟙 _ := by
  have hsum := hg8_clopenRet_sum R (fun j ↦ topologicalSubsetInclusion Y (W j))
    (fun _ ↦ Topology.IsEmbedding.subtypeVal) (fun j ↦ hg8_subset_clopen (W j) (hW j))
    (fun j k hjk ↦ by
      simp only [topologicalSubsetInclusion, TopCat.hom_ofHom, ContinuousMap.coe_mk,
        Subtype.range_coe_subtype, Set.ofPred_mem_eq]
      exact hdisj j k hjk)
    (fun y ↦ by
      obtain ⟨j, hj⟩ := hcov y
      exact ⟨j, ⟨y, hj⟩, rfl⟩)
  apply (cancel_epi (cokernel.π ((chainPairFunctor R).obj (TopPair.ofSubset V)).hom)).1
  rw [Preadditive.comp_sum]
  erw [Category.comp_id]
  have key : ∀ j, cokernel.π ((chainPairFunctor R).obj (TopPair.ofSubset V)).hom ≫
      hg8_relRet R (W j) V (hW j) ≫ (relativeChainFunctor R).map (b6m_subspacePairMap Y (W j) V) =
      (hg8_clopenRet R (topologicalSubsetInclusion Y (W j)) Topology.IsEmbedding.subtypeVal
        (hg8_subset_clopen (W j) (hW j)) ≫
        ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
          (topologicalSubsetInclusion Y (W j))) ≫
        cokernel.π ((chainPairFunctor R).obj (TopPair.ofSubset V)).hom := by
    intro j
    rw [← Category.assoc]
    erw [cokernel.π_desc, Category.assoc, cokernel.π_desc]
    rfl
  rw [Finset.sum_congr rfl fun j _ ↦ key j, ← Preadditive.sum_comp]
  erw [hsum, Category.id_comp]

/-- **Splitting over a clopen partition.** Every relative class of `(Y, V)` is the sum of its
retractions to the pieces `(W j, W j ∩ V)` pushed back by the inclusions.
Source: Hatcher, *Algebraic Topology*, Proposition 2.6 (homology of a disjoint union). -/
theorem hg8_relative_decomp (R : Type) [CommRing R] {Y : TopCat.{0}} {J : Type} [Fintype J]
    (W : J → Set Y) (hW : ∀ j, IsClopen (W j)) (hdisj : ∀ j k, j ≠ k → Disjoint (W j) (W k))
    (hcov : ∀ y, ∃ j, y ∈ W j) (V : Set Y) (k : ℕ) (x : RelativeHomology R (TopPair.ofSubset V) k) :
    x = ∑ j, relativeHomologyMap R k (b6m_subspacePairMap Y (W j) V)
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (hg8_relRet R (W j) V (hW j)) k) x) := by
  have h := congrArg (fun φ ↦ ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ k) x)
    (hg8_relRet_sum R W hW hdisj hcov V)
  simp only [HomologicalComplex.homologyMap_id] at h
  rw [show HomologicalComplex.homologyMap (∑ j, hg8_relRet R (W j) V (hW j) ≫
      (relativeChainFunctor R).map (b6m_subspacePairMap Y (W j) V)) k =
      ∑ j, HomologicalComplex.homologyMap (hg8_relRet R (W j) V (hW j) ≫
      (relativeChainFunctor R).map (b6m_subspacePairMap Y (W j) V)) k from
    (HomologicalComplex.homologyFunctor _ _ k).map_sum _ _] at h
  refine h.symm.trans ?_
  erw [ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [HomologicalComplex.homologyMap_comp]
  rfl

end Splitting

/-! ## Relative homology of a space with cells attached -/

/-- Excision for an open cover `U ∪ V = Y`, as a bijection on relative homology.
Source: Hatcher, *Algebraic Topology*, Theorem 2.20; `b6m_openCover_relativeChainMap_quasiIso`. -/
theorem hg8_excision_bijective (R : Type) [CommRing R] (Y : TopCat.{0}) (U V : Set Y)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (k : ℕ) :
    Function.Bijective (relativeHomologyMap R k (b6m_subspacePairMap Y U V)) := by
  have := b6m_openCover_relativeChainMap_quasiIso R Y U V hU hV hUV
  have hiso : IsIso (HomologicalComplex.homologyMap
      ((relativeChainFunctor R).map (b6m_subspacePairMap Y U V)) k) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hiso

/-- Two maps of subset pairs with the same underlying map are equal. -/
theorem hg8_pairHom_ext {Y Z : TopCat.{0}} {A : Set Y} {B : Set Z}
    (f g : TopPair.ofSubset A ⟶ TopPair.ofSubset B)
    (h : ∀ y, TopPair.Hom.fst f y = TopPair.Hom.fst g y) : f = g := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext a
    apply Subtype.ext
    have hf := ConcreteCategory.congr_hom (TopPair.Hom.w f) a
    have hg := ConcreteCategory.congr_hom (TopPair.Hom.w g) a
    exact hf.trans ((h _).trans hg.symm)
  · ext y
    exact h y

/-- The map of pairs `(D, B) → (X, A)` of the cell `j`. -/
abbrev hg8_cellMap {X D J : Type} [TopologicalSpace X] [TopologicalSpace D] {A : Set X}
    {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) (j : J) :
    TopPair.ofSubset (X := TopCat.of D) B ⟶ TopPair.ofSubset (X := TopCat.of X) A :=
  TopPair.ofSubsetHom (TopCat.ofHom (Φ j)) fun b hb ↦ hC.bdry j b hb

/-- A point lies in the open cell `j` iff it is outside `A` and outside the other cells. -/
theorem hg8_mem_openCell_iff {X D J : Type} [TopologicalSpace X] [TopologicalSpace D]
    {A : Set X} {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) (j : J) (x : X) :
    x ∈ Φ j '' Bᶜ ↔ x ∉ A ∧ ∀ k, k ≠ j → x ∉ Set.range (Φ k) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨hC.int j y hy, fun k hk ⟨z, hz⟩ ↦ ?_⟩
    by_cases hzB : z ∈ B
    · exact hC.int j y hy (hz ▸ hC.bdry k z hzB)
    · exact hk (hC.disj k j z y hzB hy hz)
  · rintro ⟨hA, hk⟩
    obtain ⟨i, y, rfl⟩ := hC.cov x hA
    have hij : i = j := by
      by_contra h
      exact hk i h ⟨y, rfl⟩
    subst hij
    exact ⟨y, fun hy ↦ hA (hC.bdry i y hy), rfl⟩

/-- The open cells are open. -/
theorem hg8_openCell_isOpen {X D J : Type} [TopologicalSpace X] [TopologicalSpace D] [Finite J]
    {A : Set X} {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) (j : J) :
    IsOpen (Φ j '' Bᶜ) := by
  have h : Φ j '' Bᶜ = Aᶜ ∩ ⋂ k, ⋂ (_ : k ≠ j), (Set.range (Φ k))ᶜ := by
    ext x
    rw [hg8_mem_openCell_iff hC]
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iInter]
  rw [h]
  exact hC.closedA.isOpen_compl.inter (isOpen_iInter_of_finite fun k ↦
    isOpen_iInter_of_finite fun _ ↦ (hC.emb k).isClosed_range.isOpen_compl)

/-- The model cell structure on `D`: one cell, the identity. -/
theorem hg8_modelCells {D : Type} [TopologicalSpace D] {B : Set D} (hB : IsClosed B) :
    hg8_Cells B B (fun _ : Unit ↦ ContinuousMap.id D) where
  closedA := hB
  emb _ := Topology.IsClosedEmbedding.id
  bdry _ _ h := h
  int _ _ h := h
  disj _ _ _ _ _ _ _ := rfl
  cov x _ := ⟨(), x, rfl⟩

/-- Membership in the complement of the centre of the model. -/
theorem hg8_mem_modelN {D : Type} [TopologicalSpace D] (c y : D) :
    y ∈ (hg8_centres (fun _ : Unit ↦ ContinuousMap.id D) c)ᶜ ↔ y ≠ c := by
  simp [hg8_centres, eq_comm]

/-- Functoriality of relative homology, applied to a class. -/
theorem hg8_relHom_comp_apply (R : Type) [CommRing R] {P Q S : TopPair.{0}} (n : ℕ)
    (f : P ⟶ Q) (g : Q ⟶ S) (x : RelativeHomology R P n) :
    relativeHomologyMap R n (f ≫ g) x = relativeHomologyMap R n g (relativeHomologyMap R n f x) := by
  simp only [relativeHomologyMap, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The pieces of `X ∖ A` cut out by the open cells, as subsets of `X ∖ A`. -/
abbrev hg8_piece {X D J : Type} [TopologicalSpace X] [TopologicalSpace D] (A : Set X)
    (B : Set D) (Φ : J → C(D, X)) (j : J) : Set (Aᶜ : Set X) :=
  Subtype.val ⁻¹' (Φ j '' Bᶜ)

/-- The pieces are clopen in `X ∖ A`. -/
theorem hg8_piece_clopen {X D J : Type} [TopologicalSpace X] [TopologicalSpace D] [Finite J]
    {A : Set X} {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) (j : J) :
    IsClopen (hg8_piece A B Φ j) := by
  refine ⟨?_, (hg8_openCell_isOpen hC j).preimage continuous_subtype_val⟩
  have h : (hg8_piece A B Φ j)ᶜ = ⋃ k, ⋃ (_ : k ≠ j), hg8_piece A B Φ k := by
    ext u
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro hu
      obtain ⟨i, y, hy⟩ := hC.cov u.1 u.2
      have hyB : y ∉ B := fun h ↦ u.2 (hy ▸ hC.bdry i y h)
      refine ⟨i, fun hij ↦ hu (hij ▸ ⟨y, hyB, hy⟩), y, hyB, hy⟩
    · rintro ⟨k, hk, hu⟩ hj
      exact ((hg8_mem_openCell_iff hC k u.1).1 hu).2 j (Ne.symm hk) ⟨_, (Set.mem_image _ _ _).1 hj
        |>.choose_spec.2⟩
  rw [← isOpen_compl_iff, h]
  exact isOpen_iUnion fun k ↦ isOpen_iUnion fun _ ↦
    (hg8_openCell_isOpen hC k).preimage continuous_subtype_val

/-- **Cells span.** Every class of `H_k(X, A)` is a sum of images of classes of `H_k(D, B)`
under the cells.
Source: Hatcher, *Algebraic Topology*, Lemma 2.34 and Proposition 2.22. -/
theorem hg8_cells_span (R : Type) [CommRing R] {X D J : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace D] [Fintype J] {A : Set X} {B : Set D} {Φ : J → C(D, X)}
    (hC : hg8_Cells A B Φ) {c : D} (M : hg8_Model B c) (k : ℕ)
    (x : RelativeHomology R (TopPair.ofSubset (X := TopCat.of X) A) k) :
    ∃ y : J → RelativeHomology R (TopPair.ofSubset (X := TopCat.of D) B) k,
      x = ∑ j, relativeHomologyMap R k (hg8_cellMap hC j) (y j) := by
  classical
  let N : Set X := (hg8_centres Φ c)ᶜ
  have hAN : A ⊆ N := hg8_A_sub_N hC M.centre
  let ψ : TopPair.ofSubset (X := TopCat.of X) A ⟶ TopPair.ofSubset (X := TopCat.of X) N :=
    TopPair.ofSubsetHom (𝟙 (TopCat.of X)) fun _ ha ↦ hAN ha
  have hψ : Function.Bijective (relativeHomologyMap R k ψ) := hg8_cells_triple R hC M k
  let Dc : Set D := (hg8_centres (fun _ : Unit ↦ ContinuousMap.id D) c)ᶜ
  have hBDc : B ⊆ Dc := hg8_A_sub_N (hg8_modelCells M.closed) M.centre
  let θ : TopPair.ofSubset (X := TopCat.of D) B ⟶ TopPair.ofSubset (X := TopCat.of D) Dc :=
    TopPair.ofSubsetHom (𝟙 (TopCat.of D)) fun _ hb ↦ hBDc hb
  have hθ : Function.Bijective (relativeHomologyMap R k θ) :=
    hg8_cells_triple R (hg8_modelCells M.closed) M k
  have hΦN : ∀ j (y : D), y ∈ Dc → Φ j y ∈ N := fun j y hy ↦
    hg8_cell_not_centre hC M.centre j y ((hg8_mem_modelN c y).1 hy)
  let ΦN : ∀ j, TopPair.ofSubset (X := TopCat.of D) Dc ⟶ TopPair.ofSubset (X := TopCat.of X) N :=
    fun j ↦ TopPair.ofSubsetHom (TopCat.ofHom (Φ j)) fun y hy ↦ hΦN j y hy
  have hsq : ∀ j, θ ≫ ΦN j = hg8_cellMap hC j ≫ ψ := fun j ↦
    hg8_pairHom_ext _ _ fun _ ↦ rfl
  have hN : IsOpen N := (Set.finite_range _).isClosed.isOpen_compl
  have hexc := hg8_excision_bijective R (TopCat.of X) Aᶜ N hC.closedA.isOpen_compl hN
    (Set.eq_univ_of_forall fun x ↦ by
      by_cases hx : x ∈ A
      · exact Or.inr (hAN hx)
      · exact Or.inl hx) k
  obtain ⟨z, hz⟩ := hexc.2 (relativeHomologyMap R k ψ x)
  have hdec := hg8_relative_decomp R (Y := TopCat.of (Aᶜ : Set X)) (hg8_piece A B Φ)
    (hg8_piece_clopen hC) (fun i j hij ↦ Set.disjoint_left.2 fun u hu hu' ↦
      ((hg8_mem_openCell_iff hC i u.1).1 hu).2 j (Ne.symm hij) (by
        obtain ⟨y, -, hy⟩ := hu'
        exact ⟨y, hy⟩))
    (fun u ↦ by
      obtain ⟨i, y, hy⟩ := hC.cov u.1 u.2
      exact ⟨i, y, fun h ↦ u.2 (hy ▸ hC.bdry i y h), hy⟩) (Subtype.val ⁻¹' N) k z
  -- the map from a piece to `D`
  let e : ∀ j, D ≃ₜ Set.range (Φ j) := fun j ↦ (hC.emb j).isEmbedding.toHomeomorph
  have hmem : ∀ j (w : (hg8_piece A B Φ j : Set (Aᶜ : Set X))), (w.1.1 : X) ∈ Set.range (Φ j) :=
    fun j w ↦ by
      obtain ⟨y, -, hy⟩ := w.2
      exact ⟨y, hy⟩
  have hinv : ∀ j (w : (hg8_piece A B Φ j : Set (Aᶜ : Set X))),
      Φ j ((e j).symm ⟨w.1.1, hmem j w⟩) = w.1.1 := fun j w ↦
    congrArg Subtype.val ((e j).apply_symm_apply ⟨w.1.1, hmem j w⟩)
  let h : ∀ j, TopPair.ofSubset (X := TopCat.of (hg8_piece A B Φ j : Set (Aᶜ : Set X)))
      (Subtype.val ⁻¹' (Subtype.val ⁻¹' N)) ⟶ TopPair.ofSubset (X := TopCat.of D) Dc :=
    fun j ↦ TopPair.ofSubsetHom (TopCat.ofHom ⟨fun w ↦ (e j).symm ⟨w.1.1, hmem j w⟩,
      (e j).symm.continuous.comp (Continuous.subtype_mk (by fun_prop) _)⟩) (fun w hw ↦ by
        rw [hg8_mem_modelN]
        intro hc
        apply hw
        refine ⟨j, ?_⟩
        change Φ j c = w.1.1
        rw [← hinv j w]
        exact congrArg (Φ j) hc.symm)
  have hcomp : ∀ j, b6m_subspacePairMap (TopCat.of (Aᶜ : Set X)) (hg8_piece A B Φ j)
      (Subtype.val ⁻¹' N) ≫ b6m_subspacePairMap (TopCat.of X) Aᶜ N = h j ≫ ΦN j := fun j ↦
    hg8_pairHom_ext _ _ fun w ↦ (hinv j w).symm
  refine ⟨fun j ↦ Function.surjInv hθ.2 (relativeHomologyMap R k (h j)
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (hg8_relRet R (Y := TopCat.of (Aᶜ : Set X)) (hg8_piece A B Φ j)
      (Subtype.val ⁻¹' N) (hg8_piece_clopen hC j)) k) z)), hψ.1 ?_⟩
  rw [map_sum, ← hz]
  conv_lhs => rw [hdec, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  beta_reduce
  exact (hg8_relHom_comp_apply R k _ _ _).symm.trans
    ((congrArg (fun φ ↦ relativeHomologyMap R k φ _) (hcomp j)).trans
    ((hg8_relHom_comp_apply R k (h j) (ΦN j) _).trans
    ((congrArg (relativeHomologyMap R k (ΦN j)) (Function.surjInv_eq hθ.2 _)).symm.trans
    ((hg8_relHom_comp_apply R k θ (ΦN j) _).symm.trans
    ((congrArg (fun φ ↦ relativeHomologyMap R k φ _) (hsq j)).trans
    (hg8_relHom_comp_apply R k (hg8_cellMap hC j) ψ _))))))

/-- The pair `(D, D)` has zero relative homology. -/
theorem hg8_relHomology_univ (R : Type) [CommRing R] (D : TopCat.{0}) (k : ℕ)
    (x : RelativeHomology R (TopPair.ofSubset (Set.univ : Set D)) k) : x = 0 := by
  let i : TopCat.of (Set.univ : Set D) ⟶ D := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let r : D ⟶ TopCat.of (Set.univ : Set D) := TopCat.ofHom ⟨fun x ↦ ⟨x, trivial⟩, by fun_prop⟩
  let H : TopCat.Homotopy (𝟙 D) (r ≫ i) :=
    { toFun := fun p ↦ p.2
      continuous_toFun := continuous_snd
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl }
  exact hg8_relHomology_eq_zero_of_deformation R i Topology.IsEmbedding.subtypeVal r rfl H
    (fun _ _ ↦ rfl) k x

/-- If `g ∘ f` is injective and `f` is onto, `g` is injective. -/
theorem hg8_bijective_comp_left {M₁ M₂ M₃ : Type*} {f : M₁ → M₂} {g : M₂ → M₃}
    (hf : Function.Surjective f) (hgf : Function.Injective (g ∘ f)) : Function.Injective g := by
  intro a b h
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨b, rfl⟩ := hf b
  exact congrArg f (hgf h)

/-- The map of pairs `(D, D ∖ {c}) → (X, X ∖ {Φ i c})` of the cell `i`. -/
abbrev hg8_cellLocalMap {X D J : Type} [TopologicalSpace X] [TopologicalSpace D] {A : Set X}
    {B : Set D} {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) (c : D) (i : J) :
    TopPair.ofSubset (X := TopCat.of D) (hg8_centres (fun _ : Unit ↦ ContinuousMap.id D) c)ᶜ ⟶
      TopPair.ofSubset (X := TopCat.of X) ({Φ i c}ᶜ : Set X) :=
  TopPair.ofSubsetHom (TopCat.ofHom (Φ i)) fun y hy ↦ by
    rw [Set.mem_compl_singleton_iff]
    intro h
    apply (hg8_mem_modelN c y).1 hy
    exact (hC.emb i).injective h

/-- **One cell, by excision.** The cell `i` induces an injective map
`H_k(D, D ∖ {c}) → H_k(X, X ∖ {Φ i c})`: both groups excise to the open cell, on which `Φ i` is a
homeomorphism.
Source: Hatcher, *Algebraic Topology*, Theorem 2.20 (excision). -/
theorem hg8_cell_local_injective (R : Type) [CommRing R] {X D J : Type} [TopologicalSpace X]
    [T1Space X] [TopologicalSpace D] [T1Space D] [Finite J] {A : Set X} {B : Set D}
    {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) {c : D} (hB : IsClosed B) (hc : c ∉ B) (i : J)
    (k : ℕ) :
    Function.Injective (relativeHomologyMap R k (hg8_cellLocalMap hC c i)) := by
  let Dc : Set D := (hg8_centres (fun _ : Unit ↦ ContinuousMap.id D) c)ᶜ
  let Ni : Set X := {Φ i c}ᶜ
  let W : Set X := Φ i '' Bᶜ
  have hW : IsOpen W := hg8_openCell_isOpen hC i
  have hDc : IsOpen Dc := (Set.finite_range _).isClosed.isOpen_compl
  have hcW : Φ i c ∈ W := ⟨c, hc, rfl⟩
  have hexcX := hg8_excision_bijective R (TopCat.of X) W Ni hW isOpen_compl_singleton
    (Set.eq_univ_of_forall fun x ↦ by
      by_cases hx : x = Φ i c
      · exact Or.inl (hx ▸ hcW)
      · exact Or.inr hx) k
  have hexcD := hg8_excision_bijective R (TopCat.of D) Bᶜ Dc hB.isOpen_compl hDc
    (Set.eq_univ_of_forall fun y ↦ by
      by_cases hy : y = c
      · exact Or.inl (hy ▸ hc)
      · exact Or.inr ((hg8_mem_modelN c y).2 hy)) k
  -- the open cell as a homeomorphic copy of `Bᶜ`
  have hemb : Topology.IsEmbedding (fun b : (Bᶜ : Set D) ↦ Φ i b) :=
    (hC.emb i).isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hrange : Set.range (fun b : (Bᶜ : Set D) ↦ Φ i b) = W := by
    ext x
    exact ⟨fun ⟨b, hb⟩ ↦ ⟨b.1, b.2, hb⟩, fun ⟨b, hb, hx⟩ ↦ ⟨⟨b, hb⟩, hx⟩⟩
  let e : (Bᶜ : Set D) ≃ₜ W := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have he : ∀ b, (e b : X) = Φ i b := fun _ ↦ rfl
  let g := TopPair.isoOfSubset (X := TopCat.of (Bᶜ : Set D)) (Y := TopCat.of W)
    (A := Subtype.val ⁻¹' Dc) (B := Subtype.val ⁻¹' Ni) e (fun b ↦ by
      change (e b : X) ∈ Ni ↔ (b : D) ∈ Dc
      rw [he, hg8_mem_modelN, Set.mem_compl_singleton_iff]
      exact (hC.emb i).injective.ne_iff)
  have hg : Function.Bijective (relativeHomologyMap R k g.hom) := by
    refine (ConcreteCategory.isIso_iff_bijective _).mp ?_
    exact (relativeHomologyFunctor R k).map_isIso g.hom
  have hsq : g.hom ≫ b6m_subspacePairMap (TopCat.of X) W Ni =
      b6m_subspacePairMap (TopCat.of D) Bᶜ Dc ≫ hg8_cellLocalMap hC c i :=
    hg8_pairHom_ext _ _ fun _ ↦ rfl
  refine hg8_bijective_comp_left hexcD.2 ?_
  intro a b hab
  have h1 := hg8_relHom_comp_apply R k (b6m_subspacePairMap (TopCat.of D) Bᶜ Dc)
    (hg8_cellLocalMap hC c i) a
  have h2 := hg8_relHom_comp_apply R k (b6m_subspacePairMap (TopCat.of D) Bᶜ Dc)
    (hg8_cellLocalMap hC c i) b
  rw [← hsq, hg8_relHom_comp_apply] at h1 h2
  exact hg.1 (hexcX.1 (h1.trans (hab.trans h2.symm)))

/-- **Cells are independent.** If a sum of images of classes of `H_k(D, B)` under the cells
vanishes in `H_k(X, A)`, every class vanishes.
Source: Hatcher, *Algebraic Topology*, Lemma 2.34 and Theorem 2.20. -/
theorem hg8_cells_independent (R : Type) [CommRing R] {X D J : Type} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace D] [T1Space D] [Fintype J] {A : Set X} {B : Set D}
    {Φ : J → C(D, X)} (hC : hg8_Cells A B Φ) {c : D} (M : hg8_Model B c) (k : ℕ)
    (y : J → RelativeHomology R (TopPair.ofSubset (X := TopCat.of D) B) k)
    (hy : ∑ j, relativeHomologyMap R k (hg8_cellMap hC j) (y j) = 0) (i : J) : y i = 0 := by
  classical
  have hAi : ∀ a ∈ A, a ∈ ({Φ i c}ᶜ : Set X) := fun a ha h ↦
    hC.int i c M.centre (Set.mem_singleton_iff.1 h ▸ ha)
  let ψ : TopPair.ofSubset (X := TopCat.of X) A ⟶ TopPair.ofSubset (X := TopCat.of X)
      ({Φ i c}ᶜ : Set X) := TopPair.ofSubsetHom (𝟙 (TopCat.of X)) hAi
  have hne : ∀ j, j ≠ i → ∀ y : D, Φ j y ∈ ({Φ i c}ᶜ : Set X) := fun j hj y h ↦ by
    have h' : Φ j y = Φ i c := h
    by_cases hyB : y ∈ B
    · exact hC.int i c M.centre (h' ▸ hC.bdry j y hyB)
    · exact hj (hC.disj j i y c hyB M.centre h')
  have h0 := congrArg (relativeHomologyMap R k ψ) hy
  rw [map_sum, map_zero, Finset.sum_eq_single i] at h0
  · let Dc : Set D := (hg8_centres (fun _ : Unit ↦ ContinuousMap.id D) c)ᶜ
    have hBDc : B ⊆ Dc := hg8_A_sub_N (hg8_modelCells M.closed) M.centre
    let θ : TopPair.ofSubset (X := TopCat.of D) B ⟶ TopPair.ofSubset (X := TopCat.of D) Dc :=
      TopPair.ofSubsetHom (𝟙 (TopCat.of D)) fun _ hb ↦ hBDc hb
    have hθ : Function.Bijective (relativeHomologyMap R k θ) :=
      hg8_cells_triple R (hg8_modelCells M.closed) M k
    have hsq : hg8_cellMap hC i ≫ ψ = θ ≫ hg8_cellLocalMap hC c i :=
      hg8_pairHom_ext _ _ fun _ ↦ rfl
    rw [← hg8_relHom_comp_apply, hsq, hg8_relHom_comp_apply] at h0
    apply hθ.1
    rw [map_zero]
    apply hg8_cell_local_injective R hC M.closed M.centre i k
    rw [h0, map_zero]
  · intro j _ hj
    let θu : TopPair.ofSubset (X := TopCat.of D) B ⟶
        TopPair.ofSubset (X := TopCat.of D) (Set.univ : Set D) :=
      TopPair.ofSubsetHom (𝟙 (TopCat.of D)) fun _ _ ↦ trivial
    let Φu : TopPair.ofSubset (X := TopCat.of D) (Set.univ : Set D) ⟶
        TopPair.ofSubset (X := TopCat.of X) ({Φ i c}ᶜ : Set X) :=
      TopPair.ofSubsetHom (TopCat.ofHom (Φ j)) fun y _ ↦ hne j hj y
    have hsq : hg8_cellMap hC j ≫ ψ = θu ≫ Φu := hg8_pairHom_ext _ _ fun _ ↦ rfl
    rw [← hg8_relHom_comp_apply, hsq, hg8_relHom_comp_apply,
      hg8_relHomology_univ R (TopCat.of D) k (relativeHomologyMap R k θu (y j)), map_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

end HodgeLean.Foundations.Program
