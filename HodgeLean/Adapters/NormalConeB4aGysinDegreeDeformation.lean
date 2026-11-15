import HodgeLean.Adapters.NormalConeB4aGysinRegularDegree

/-! # Conservation of degree along a support-preserving deformation

A homotopy whose inverse image of the target support stays inside a fixed source
support induces a homotopy of relative pairs. This permits comparison with a
regular fibre without requiring the initial fibre to be regular.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicTopology.Singular

/-- A continuous deformation preserving the complements defines a homotopy of pairs. -/
def a3b4a_gysin_supportPairHomotopy
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (S : Set X) (T : Set Y)
    (hf : ∀ x, f x ∈ T → x ∈ S) (hg : ∀ x, g x ∈ T → x ∈ S)
    (hH : ∀ (t : unitInterval) (x : X), H (t, x) ∈ T → x ∈ S) :
    TopPair.Homotopy (a3b4_supportPairMap (TopCat.ofHom f) S T hf)
      (a3b4_supportPairMap (TopCat.ofHom g) S T hg) where
  fst := H
  snd :=
    { toFun := fun tx => ⟨H (tx.1, tx.2.1), fun ht => tx.2.2 (hH tx.1 tx.2.1 ht)⟩
      continuous_toFun := (H.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      map_zero_left := fun x => Subtype.ext (H.map_zero_left x.1)
      map_one_left := fun x => Subtype.ext (H.map_one_left x.1) }
  w := rfl

/-- The induced map on supported homology is constant during such a deformation. -/
theorem a3b4a_gysin_homologyMap_deformation
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (S : Set X) (T : Set Y)
    (hf : ∀ x, f x ∈ T → x ∈ S) (hg : ∀ x, g x ∈ T → x ∈ S)
    (hH : ∀ (t : unitInterval) (x : X), H (t, x) ∈ T → x ∈ S) (n : ℕ) :
    relativeHomologyMap ℚ n (a3b4_supportPairMap (TopCat.ofHom f) S T hf) =
      relativeHomologyMap ℚ n (a3b4_supportPairMap (TopCat.ofHom g) S T hg) :=
  (a3b4a_gysin_supportPairHomotopy H S T hf hg hH).congr_relativeHomologyMap n

/-- Deformation to a regular finite fibre computes the original map's degree,
provided all zeros stay inside the support carrying the normalized class. -/
theorem a3b4a_gysin_degree_of_regular_deformation
    (d : ℕ) {f g : C((Fin d → ℂ), (Fin d → ℂ))}
    (H : ContinuousMap.Homotopy f g) (K : Set (Fin d → ℂ))
    (hf : ∀ x, f x = 0 → x ∈ K)
    (hH : ∀ (t : unitInterval) (x : Fin d → ℂ), H (t, x) = 0 → x ∈ K)
    (S : Finset (Fin d → ℂ)) (hS : ∀ x, g x = 0 ↔ x ∈ S)
    (A : S → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ x, (A x).det ≠ 0)
    (hderiv : ∀ x : S, HasFDerivAt (fun z => g (z + x.1))
      ((A x).mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0)
    (α : RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin d → ℂ)) Kᶜ) (2 * d))
    (hα : ∀ (x : Fin d → ℂ) (hx : x ∈ K), relativeHomologyMap ℚ (2 * d)
      (supportInclusionPairMap (TopCat.of (Fin d → ℂ))
        (Set.singleton_subset_iff.mpr hx)) α =
          HodgeLean.RealDefs.translatedStandardComplexLocalClass d x) :
    relativeHomologyMap ℚ (2 * d)
      (a3b4_supportPairMap (TopCat.ofHom f) K {0} hf) α =
      (S.card : ℚ) • standardComplexLocalClass ℚ d := by
  let E := Fin d → ℂ
  have hg : ∀ x, g x = 0 → x ∈ K := by
    intro x hx
    apply hH 1 x
    exact (H.map_one_left x).trans hx
  have hSK : (S : Set E) ⊆ K := fun x hx => hg x ((hS x).mpr hx)
  let R := supportInclusionPairMap (TopCat.of E) hSK
  let β := relativeHomologyMap ℚ (2 * d) R α
  have hβ : ∀ x : S, relativeHomologyMap ℚ (2 * d)
      (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr x.2)) β =
        HodgeLean.RealDefs.translatedStandardComplexLocalClass d x.1 := by
    intro x
    have heq : R ≫ supportInclusionPairMap (TopCat.of E)
        (Set.singleton_subset_iff.mpr x.2) = supportInclusionPairMap (TopCat.of E)
          (Set.singleton_subset_iff.mpr (hSK x.2)) := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl
    change relativeHomologyMap ℚ (2 * d) _ (relativeHomologyMap ℚ (2 * d) R α) = _
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq]
    exact hα x.1 (hSK x.2)
  have heq : a3b4_supportPairMap (TopCat.ofHom g) K {0} hg =
      R ≫ a3b4_supportPairMap (TopCat.ofHom g) (S : Set E) {0}
        (fun x hx => (hS x).mp hx) := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl
  rw [a3b4a_gysin_homologyMap_deformation H K {0} hf hg hH, heq,
    relativeHomologyMap_comp, LinearMap.comp_apply]
  exact a3b4a_gysin_regular_fibre_degree d g S hS A hA hderiv β hβ

/-- Translation of the target along the straight segment from zero to a vector. -/
def a3b4a_gysin_translationHomotopy
    {X : Type} [TopologicalSpace X] {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : C(X, E)) (a : E) :
    ContinuousMap.Homotopy f (f - ContinuousMap.const X a) where
  toFun := fun tx => f tx.2 - (tx.1 : ℝ) • a
  continuous_toFun := (f.continuous.comp continuous_snd).sub
    ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
  map_zero_left := fun x => by simp
  map_one_left := fun x => by simp

/-- A lower norm bound off the support keeps all zeros of a small translation
inside that support throughout the straight-line deformation. -/
theorem a3b4a_gysin_translation_zeros_stay_in_support
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : C(E, E)) (K : Set E) (ε : ℝ)
    (hbound : ∀ x, x ∉ K → ε ≤ ‖f x‖) (a : E) (ha : ‖a‖ < ε) :
    ∀ (t : unitInterval) (x : E),
      a3b4a_gysin_translationHomotopy f a (t, x) = 0 → x ∈ K := by
  intro t x hz
  by_contra hx
  have heq : f x = (t : ℝ) • a := sub_eq_zero.mp hz
  have ht : ‖(t : ℝ) • a‖ ≤ ‖a‖ := by
    rw [norm_smul, Real.norm_of_nonneg t.2.1]
    exact mul_le_of_le_one_left (norm_nonneg a) t.2.2
  exact (not_le_of_gt ha) ((hbound x hx).trans (heq ▸ ht))

/-- The fixed generator at an isolated, possibly degenerate zero can be evaluated
by a small regular translation when a compact support traps the deformation. -/
theorem a3b4a_gysin_isolated_zero_degree
    (d : ℕ) (f : C((Fin d → ℂ), (Fin d → ℂ)))
    (hf : ∀ x, f x = 0 ↔ x = 0)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K) (ε : ℝ)
    (hbound : ∀ x, x ∉ K → ε ≤ ‖f x‖)
    (a : Fin d → ℂ) (ha : ‖a‖ < ε)
    (S : Finset (Fin d → ℂ)) (hS : ∀ x, f x = a ↔ x ∈ S)
    (A : S → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ x, (A x).det ≠ 0)
    (hderiv : ∀ x : S, HasFDerivAt (fun z => f (z + x.1) - a)
      ((A x).mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0) :
    relativeHomologyMap ℚ (2 * d)
      (a3b4_supportPairMap (TopCat.ofHom f) {0} {0} (fun x hx => (hf x).mp hx))
      (standardComplexLocalClass ℚ d) =
        (S.card : ℚ) • standardComplexLocalClass ℚ d := by
  let E := Fin d → ℂ
  let g := f - ContinuousMap.const E a
  let H := a3b4a_gysin_translationHomotopy f a
  have hH := a3b4a_gysin_translation_zeros_stay_in_support f K ε hbound a ha
  have hfK : ∀ x, f x = 0 → x ∈ K := by
    intro x hx
    apply hH 0 x
    change f x - (0 : ℝ) • a = 0
    simpa only [zero_smul, sub_zero] using hx
  have h0K : (0 : E) ∈ K := hfK 0 ((hf 0).mpr rfl)
  have hn : Module.finrank ℝ E = 2 * d := by
    dsimp [E]
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  obtain ⟨α, hα⟩ := HodgeLean.RealDefs.j5c_hasClassAlong_of_isCompact
    (M := E) (E := E) hn (HodgeLean.RealDefs.translatedStandardComplexLocalClass d)
    (HodgeLean.RealDefs.j5c_translatedStandardComplexLocalClass_locallyCoherent d) hK
  have htranslation : translationPointComplementPairMap E 0 =
      𝟙 (pointComplementPair (0 : E)) := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext x
      apply Subtype.ext
      change x.1 + 0 = x.1
      exact add_zero x.1
    · ext x
      exact @add_zero E _ x
  have hres : relativeHomologyMap ℚ (2 * d)
      (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr h0K)) α =
        standardComplexLocalClass ℚ d := by
    rw [hα 0 h0K]
    unfold HodgeLean.RealDefs.translatedStandardComplexLocalClass
    rw [htranslation, relativeHomologyMap_id]
    rfl
  have hgS : ∀ x, g x = 0 ↔ x ∈ S := by
    intro x
    change f x - a = 0 ↔ x ∈ S
    rw [sub_eq_zero]
    exact hS x
  have heval := a3b4a_gysin_degree_of_regular_deformation d H K hfK hH
    S hgS A hA hderiv α hα
  have heq : a3b4_supportPairMap (TopCat.ofHom f) K {0} hfK =
      supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr h0K) ≫
        a3b4_supportPairMap (TopCat.ofHom f) {0} {0} (fun x hx => (hf x).mp hx) := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext x <;> rfl
  rw [heq, relativeHomologyMap_comp, LinearMap.comp_apply, hres] at heval
  exact heval

end HodgeLean.Adapters
