import HodgeLean.Adapters.NormalConeB4Defs
import HodgeLean.RealDefs.ComplexFundamentalClass

/-! # Isolated points in supported homology

Excision represents each isolated intersection inside a neighborhood containing
no other support point. Restriction retains its local class at that point and
vanishes at the other points.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicTopology.Singular

/-- A map missing the target support induces zero on relative homology. -/
theorem a3b4a_gysin_homologyMap_zero_of_avoids_support
    {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set X) (T : Set Y)
    (h : ∀ x, f x ∈ T → x ∈ S) (hf : ∀ x, f x ∉ T) (n : ℕ) :
    relativeHomologyMap ℚ n (a3b4_supportPairMap f S T h) = 0 := by
  let F := a3b4_supportPairMap f (∅ : Set X) T (fun x hx => (hf x hx).elim)
  have heq : a3b4_supportPairMap f S T h =
      supportInclusionPairMap X (Set.empty_subset S) ≫ F := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext x <;> rfl
  rw [heq, relativeHomologyMap_comp]
  let := ModuleCat.subsingleton_of_isZero
    (HodgeLean.RealDefs.C_relativeHomology_compl_empty_isZero X n)
  ext z
  change relativeHomologyMap ℚ n F _ = 0
  have hz : relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.empty_subset S)) z = 0 := Subsingleton.elim _ _
  rw [hz, map_zero]

/-- A local homology class at one point extends to a finite support with zero
restrictions at all its other points. -/
theorem a3b4a_gysin_finite_support_single_class
    {X : Type} [TopologicalSpace X] [T1Space X] (S : Finset X)
    (x : X) (hx : x ∈ S) (n : ℕ)
    (μ : RelativeHomology ℚ (pointComplementPair x) n) :
    ∃ z : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of X) (S : Set X)ᶜ) n,
      relativeHomologyMap ℚ n
        (supportInclusionPairMap (TopCat.of X) (Set.singleton_subset_iff.mpr hx)) z = μ ∧
      ∀ (y : X) (hy : y ∈ S), y ≠ x →
        relativeHomologyMap ℚ n
          (supportInclusionPairMap (TopCat.of X) (Set.singleton_subset_iff.mpr hy)) z = 0 := by
  classical
  let U : Set X := (↑(S.erase x) : Set X)ᶜ
  have hU : IsOpen U := (S.erase x).finite_toSet.isClosed.isOpen_compl
  have hxU : x ∈ U := by simp [U]
  have hsingle : ∀ u : U, (u.1 ∈ S) → u.1 = x := by
    intro u hu
    by_contra hne
    exact u.2 (Finset.mem_erase.mpr ⟨hne, hu⟩)
  let f : TopCat.of U ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let F := a3b4_supportPairMap f {u : U | u.1 = x} (S : Set X) hsingle
  obtain ⟨v, hv⟩ := (neighborhoodPointComplement_relativeHomologyMap_bijective
    U x hU hxU n).2 μ
  refine ⟨relativeHomologyMap ℚ n F v, ?_, ?_⟩
  · have heq : F ≫ supportInclusionPairMap (TopCat.of X)
        (Set.singleton_subset_iff.mpr hx) = neighborhoodPointComplementPairMap U x := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq]
    exact hv
  · intro y hy hyx
    have hfy : ∀ u : U, f u ∉ ({y} : Set X) := by
      intro u hu
      have huy : u.1 = y := hu
      exact u.2 (Finset.mem_erase.mpr ⟨huy ▸ hyx, huy ▸ hy⟩)
    let G := a3b4_supportPairMap f {u : U | u.1 = x} ({y} : Set X)
      (fun u hu => (hfy u hu).elim)
    have heq : F ≫ supportInclusionPairMap (TopCat.of X)
        (Set.singleton_subset_iff.mpr hy) = G := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq]
    have hzero := a3b4a_gysin_homologyMap_zero_of_avoids_support f
      {u : U | u.1 = x} ({y} : Set X) (fun u hu => (hfy u hu).elim) hfy n
    change relativeHomologyMap ℚ n G v = 0
    rw [hzero]
    rfl

/-- All prescribed point classes on a finite support are realized simultaneously. -/
theorem a3b4a_gysin_finite_support_restrictions_surjective
    {X : Type} [TopologicalSpace X] [T1Space X] (S : Finset X) (n : ℕ) :
    Function.Surjective (fun z : RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of X) (S : Set X)ᶜ) n =>
        fun x : S => relativeHomologyMap ℚ n
          (supportInclusionPairMap (TopCat.of X) (Set.singleton_subset_iff.mpr x.2)) z) := by
  classical
  intro μ
  have hex := fun x : S => a3b4a_gysin_finite_support_single_class S x.1 x.2 n (μ x)
  choose z hz hzother using hex
  refine ⟨∑ x : S, z x, ?_⟩
  funext y
  dsimp only
  rw [map_sum]
  rw [Finset.sum_eq_single y]
  · exact hz y
  · intro x _ hxy
    exact hzother x y.1 y.2 (fun h => hxy (Subtype.ext h.symm))
  · simp

/-- Top-degree Euclidean homology on a finite support is determined bijectively
by its restrictions to the individual points. -/
theorem a3b4a_gysin_finite_support_restrictions_bijective
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (S : Finset E) :
    Function.Bijective (fun z : RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of E) (S : Set E)ᶜ) n =>
        fun x : S => relativeHomologyMap ℚ n
          (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr x.2)) z) := by
  refine ⟨?_, a3b4a_gysin_finite_support_restrictions_surjective S n⟩
  intro a b hab
  apply sub_eq_zero.mp
  apply (HodgeLean.RealDefs.j5c_compact_euclidean hn S.finite_toSet.isCompact).2
  intro x hx
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun hab ⟨x, hx⟩)

end HodgeLean.Adapters
