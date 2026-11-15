import HodgeLean.Adapters.NormalConeB4aGysinTransverseFinite

/-! # Weighted normal-cycle expansion of a transverse finite intersection

The coefficients are the point restrictions of the source class. No choice of
an abstract spanning expansion is used in the resulting ambient class.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular

/-- A finite transverse intersection maps to the weighted sum of its ambient normal cycles. -/
theorem a3b4a_gysin_transverse_normalCycle_sum
    {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    {γ : AlgebraicCycle Z ℚ} {c : ℕ}
    (U : Set (Fin c → ℂ)) (hU : IsOpen U)
    (f : (Fin c → ℂ) → ComplexPoint (Over.mk q)) (hf : ContinuousOn f U)
    (S : Finset (Fin c → ℂ)) (hSU : (S : Set (Fin c → ℂ)) ⊆ U)
    (hS : ∀ v ∈ U, f v ∈ a3b4_cycleSupport q γ ↔ v ∈ S)
    (C : S → A3b4aGysinNormalChart q γ c) (hC : ∀ x : S, f x.1 = (C x).point)
    (A : S → Matrix (Fin c) (Fin c) ℂ) (hA : ∀ x, (A x).det ≠ 0)
    (hderiv : ∀ x : S, HasFDerivAt (fun v => ((C x).chart (f (v + x.1))).2)
      ((A x).mulVecLin.toContinuousLinearMap : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) 0)
    (w : S → ℚ)
    (α : RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of U) {u : U | u.1 ∉ S}) (2 * c))
    (hα : ∀ x : S, relativeHomologyMap ℚ (2 * c)
      (supportInclusionPairMap (TopCat.of (Fin c → ℂ)) (Set.singleton_subset_iff.mpr x.2))
      (relativeHomologyMap ℚ (2 * c)
        (a3b4_neighborhoodPairMap U (S : Set (Fin c → ℂ))) α) =
        w x • HodgeLean.RealDefs.translatedStandardComplexLocalClass c x.1) :
    relativeHomologyMap ℚ (2 * c)
      (a3b4_supportPairMap (TopCat.ofHom ⟨fun u : U => f u.1, hf.domRestrict⟩)
        {u : U | u.1 ∈ S} (a3b4_cycleSupport q γ)
        (fun u hu => (hS u.1 u.2).mp hu)) α =
      ∑ x : S, w x • a3b4a_gysin_normalCycle (C x) := by
  classical
  let E := Fin c → ℂ
  let J := a3b4_neighborhoodPairMap U (S : Set E)
  let F := a3b4_supportPairMap (TopCat.ofHom ⟨fun u : U => f u.1, hf.domRestrict⟩)
    {u : U | u.1 ∈ S} (a3b4_cycleSupport q γ) (fun u hu => (hS u.1 u.2).mp hu)
  have hex := fun x : S => a3b4a_gysin_transverse_point_normalCycle
    U hU f hf S hSU hS C hC A hA hderiv x
  choose z hz hzother hzmap using hex
  change ∀ x : S, relativeHomologyMap ℚ (2 * c) F (z x) =
    a3b4a_gysin_normalCycle (C x) at hzmap
  have hsum : α = ∑ x : S, w x • z x := by
    have hpair : TopPair.ofSubsetHom
        (A := {u : U | u.1 ∉ (S : Set E)}) (B := (S : Set E)ᶜ)
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of U ⟶ TopCat.of E)
        (fun _ ha => ha) = J := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    have hinj := (HodgeLean.RealDefs.j5c_excision hU S.finite_toSet.isClosed hSU (2 * c)).1
    rw [hpair] at hinj
    apply hinj
    apply (a3b4a_gysin_finite_support_restrictions_bijective
      (show Module.finrank ℝ E = 2 * c by
        dsimp [E]
        rw [Module.finrank_pi_fintype]
        simp [Complex.finrank_real_complex, mul_comm]) S).1
    funext y
    dsimp only
    rw [map_sum, map_sum, Finset.sum_eq_single y]
    · rw [map_smul, map_smul, hz y, hα y]
    · intro x _ hxy
      rw [map_smul, map_smul, hzother x y hxy.symm, smul_zero]
    · simp
  change relativeHomologyMap ℚ (2 * c) F α = _
  rw [hsum, map_sum]
  simp only [map_smul, hzmap]


/-- Evaluation on a transverse finite intersection retains each ambient cycle multiplicity. -/
theorem a3b4a_gysin_transverse_pullback_evaluation
    {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    {γ : AlgebraicCycle Z ℚ} {c : ℕ}
    (U : Set (Fin c → ℂ)) (hU : IsOpen U)
    (f : (Fin c → ℂ) → ComplexPoint (Over.mk q)) (hf : ContinuousOn f U)
    (S : Finset (Fin c → ℂ)) (hSU : (S : Set (Fin c → ℂ)) ⊆ U)
    (hS : ∀ v ∈ U, f v ∈ a3b4_cycleSupport q γ ↔ v ∈ S)
    (C : S → A3b4aGysinNormalChart q γ c) (hC : ∀ x : S, f x.1 = (C x).point)
    (A : S → Matrix (Fin c) (Fin c) ℂ) (hA : ∀ x, (A x).det ≠ 0)
    (hderiv : ∀ x : S, HasFDerivAt (fun v => ((C x).chart (f (v + x.1))).2)
      ((A x).mulVecLin.toContinuousLinearMap : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) 0)
    (w : S → ℚ)
    (α : RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of U) {u : U | u.1 ∉ S}) (2 * c))
    (hα : ∀ x : S, relativeHomologyMap ℚ (2 * c)
      (supportInclusionPairMap (TopCat.of (Fin c → ℂ)) (Set.singleton_subset_iff.mpr x.2))
      (relativeHomologyMap ℚ (2 * c)
        (a3b4_neighborhoodPairMap U (S : Set (Fin c → ℂ))) α) =
        w x • HodgeLean.RealDefs.translatedStandardComplexLocalClass c x.1)
    (β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c))
    (hβ : a3b4_IsCycleClass q γ c β) :
    relativeCohomologyEquivDualHomology ℚ _ (2 * c)
      (relativeCohomologyMap ℚ (2 * c)
        (a3b4_supportPairMap (TopCat.ofHom ⟨fun u : U => f u.1, hf.domRestrict⟩)
          {u : U | u.1 ∈ S} (a3b4_cycleSupport q γ)
          (fun u hu => (hS u.1 u.2).mp hu)) β) α =
      ∑ x : S, w x * a3b4_multiplicity q γ (f x.1) := by
  classical
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    a3b4a_gysin_transverse_normalCycle_sum U hU f hf S hSU hS C hC A hA hderiv w α hα,
    map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_smul, a3b4a_gysin_normalCycle_pairing (C x) β hβ, hC x, smul_eq_mul]

end HodgeLean.Adapters
