import HodgeLean.Adapters.NormalConeB4aGysinFiniteSupport
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ComplexClassDifferentiableInvariance

/-! # Counting regular zeros in local homology

A finite fibre of regular complex zeros contributes one positively oriented local
class per point. The proof uses local complex orientation invariance, excision,
and detection by point restrictions on the finite support.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicTopology.Singular

/-- A regular point contributes one positive local class, independently of
all other points in the finite fibre. -/
theorem a3b4a_gysin_regular_fibre_point_class
    (d : ℕ) (f : C((Fin d → ℂ), (Fin d → ℂ))) (S : Finset (Fin d → ℂ))
    (hS : ∀ x, f x = 0 ↔ x ∈ S)
    (A : S → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ x, (A x).det ≠ 0)
    (hderiv : ∀ x : S, HasFDerivAt (fun z => f (z + x.1))
      ((A x).mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0)
    (x : S) :
    let E := Fin d → ℂ
    let F := a3b4_supportPairMap (TopCat.ofHom f) (S : Set E) {0}
      (fun x hx => (hS x).mp hx)
    ∃ z : RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of E) (S : Set E)ᶜ) (2 * d),
      relativeHomologyMap ℚ (2 * d)
        (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr x.2)) z =
          HodgeLean.RealDefs.translatedStandardComplexLocalClass d x.1 ∧
      (∀ y : S, y ≠ x → relativeHomologyMap ℚ (2 * d)
        (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr y.2)) z = 0) ∧
      relativeHomologyMap ℚ (2 * d) F z = standardComplexLocalClass ℚ d := by
  classical
  let E := Fin d → ℂ
  let F := a3b4_supportPairMap (TopCat.ofHom f) (S : Set E) {0}
    (fun x hx => (hS x).mp hx)
  let g : E → E := fun z => f (z + x.1)
  have hg : ContinuousOn g Set.univ :=
    (f.continuous.comp (continuous_id.add continuous_const)).continuousOn
  have hg0 : g 0 = 0 := by simpa [g] using (hS x.1).mpr x.2
  obtain ⟨V, hVU, hne, hVo, h0V, hmap⟩ :=
    exists_open_complexDifferentiable_localClass_invariance d (A x) (hA x)
      Set.univ isOpen_univ (Set.mem_univ 0) g hg hg0 (hderiv x)
  obtain ⟨v, hv⟩ := (neighborhoodPointComplement_relativeHomologyMap_bijective
    V 0 hVo h0V (2 * d)).2 (standardComplexLocalClass ℚ d)
  let t : TopCat.of V ⟶ TopCat.of E :=
    TopCat.ofHom ⟨fun u => u.1 + x.1, continuous_subtype_val.add continuous_const⟩
  have hsingle : ∀ u : V, t u ∈ S → u.1 = 0 := by
    intro u hu
    by_contra hu0
    exact hne u.1 u.2 hu0 ((hS (t u)).mpr hu)
  let H := a3b4_supportPairMap t {u : V | u.1 = 0} (S : Set E) hsingle
  refine ⟨relativeHomologyMap ℚ (2 * d) H v, ?_, ?_, ?_⟩
  · have heq : H ≫ supportInclusionPairMap (TopCat.of E)
        (Set.singleton_subset_iff.mpr x.2) =
        neighborhoodPointComplementPairMap V 0 ≫ translationPointComplementPairMap E x.1 := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq,
      relativeHomologyMap_comp, LinearMap.comp_apply, hv]
    rfl
  · intro y hyx
    have hmiss : ∀ u : V, t u ∉ ({y.1} : Set E) := by
      intro u hu
      have huy : t u = y.1 := hu
      have hu0 := hsingle u (huy ▸ y.2)
      apply hyx
      apply Subtype.ext
      calc y.1 = t u := huy.symm
           _ = x.1 := by change u.1 + x.1 = x.1; rw [hu0, zero_add]
    let G := a3b4_supportPairMap t {u : V | u.1 = 0} ({y.1} : Set E)
      (fun u hu => (hmiss u hu).elim)
    have heq : H ≫ supportInclusionPairMap (TopCat.of E)
        (Set.singleton_subset_iff.mpr y.2) = G := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq]
    have hzero := a3b4a_gysin_homologyMap_zero_of_avoids_support t
      {u : V | u.1 = 0} ({y.1} : Set E) (fun u hu => (hmiss u hu).elim) hmiss (2 * d)
    change relativeHomologyMap ℚ (2 * d) G v = 0
    rw [hzero]
    rfl
  · have heq : H ≫ F =
        complexNeighborhoodPuncturedPairMapOf d V g (hg.mono hVU) hne := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq]
    exact hmap v hv

/-- A finite fibre of regular zeros has homological degree equal to its cardinality. -/
theorem a3b4a_gysin_regular_fibre_degree
    (d : ℕ) (f : C((Fin d → ℂ), (Fin d → ℂ))) (S : Finset (Fin d → ℂ))
    (hS : ∀ x, f x = 0 ↔ x ∈ S)
    (A : S → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ x, (A x).det ≠ 0)
    (hderiv : ∀ x : S, HasFDerivAt (fun z => f (z + x.1))
      ((A x).mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0)
    (α : RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin d → ℂ)) (S : Set (Fin d → ℂ))ᶜ) (2 * d))
    (hα : ∀ x : S, relativeHomologyMap ℚ (2 * d)
      (supportInclusionPairMap (TopCat.of (Fin d → ℂ))
        (Set.singleton_subset_iff.mpr x.2)) α =
          HodgeLean.RealDefs.translatedStandardComplexLocalClass d x.1) :
    relativeHomologyMap ℚ (2 * d)
      (a3b4_supportPairMap (TopCat.ofHom f) (S : Set (Fin d → ℂ)) {0}
        (fun x hx => (hS x).mp hx)) α =
      (S.card : ℚ) • standardComplexLocalClass ℚ d := by
  classical
  let E := Fin d → ℂ
  let F := a3b4_supportPairMap (TopCat.ofHom f) (S : Set E) {0}
    (fun x hx => (hS x).mp hx)
  have hex := fun x : S =>
    a3b4a_gysin_regular_fibre_point_class d f S hS A hA hderiv x
  choose z hz hzother hzmap using hex
  change ∀ x : S, relativeHomologyMap ℚ (2 * d) F (z x) =
    standardComplexLocalClass ℚ d at hzmap
  have hsum : α = ∑ x : S, z x := by
    apply (a3b4a_gysin_finite_support_restrictions_bijective
      (show Module.finrank ℝ E = 2 * d by
        dsimp [E]
        rw [Module.finrank_pi_fintype]
        simp [Complex.finrank_real_complex, mul_comm]) S).1
    funext y
    dsimp only
    rw [map_sum, Finset.sum_eq_single y]
    · exact (hα y).trans (hz y).symm
    · intro x _ hxy
      exact hzother x y hxy.symm
    · simp
  change relativeHomologyMap ℚ (2 * d) F α = _
  rw [hsum, map_sum]
  simp only [hzmap, Finset.sum_const, Finset.card_univ, Fintype.card_coe]
  exact (Nat.cast_smul_eq_nsmul ℚ S.card (standardComplexLocalClass ℚ d)).symm

end HodgeLean.Adapters
