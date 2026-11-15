import HodgeLean.Adapters.NormalConeB4aGysinTransverseDisk
import HodgeLean.Adapters.NormalConeB4aGysinFiniteSupport

/-! # Finite transverse intersections as ambient normal cycles

Excision localizes each intersection point. Its image is the normal cycle of
the ambient support chart, with the complex orientation.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular

/-- Each transverse point has a supported representative mapping to its ambient normal cycle. -/
theorem a3b4a_gysin_transverse_point_normalCycle
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
    (x : S) :
    ∃ z : RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of U) {u : U | u.1 ∉ S}) (2 * c),
      relativeHomologyMap ℚ (2 * c)
        (supportInclusionPairMap (TopCat.of (Fin c → ℂ)) (Set.singleton_subset_iff.mpr x.2))
        (relativeHomologyMap ℚ (2 * c)
          (a3b4_neighborhoodPairMap U (S : Set (Fin c → ℂ))) z) =
          HodgeLean.RealDefs.translatedStandardComplexLocalClass c x.1 ∧
      (∀ y : S, y ≠ x → relativeHomologyMap ℚ (2 * c)
        (supportInclusionPairMap (TopCat.of (Fin c → ℂ)) (Set.singleton_subset_iff.mpr y.2))
        (relativeHomologyMap ℚ (2 * c)
          (a3b4_neighborhoodPairMap U (S : Set (Fin c → ℂ))) z) = 0) ∧
      relativeHomologyMap ℚ (2 * c)
        (a3b4_supportPairMap (TopCat.ofHom ⟨fun u : U => f u.1, hf.domRestrict⟩)
          {u : U | u.1 ∈ S} (a3b4_cycleSupport q γ)
          (fun u hu => (hS u.1 u.2).mp hu)) z = a3b4a_gysin_normalCycle (C x) := by
  classical
  let E := Fin c → ℂ
  let T : Set E := {v | v + x.1 ∈ U}
  have hT : IsOpen T := hU.preimage (continuous_id.add continuous_const)
  have h0T : (0 : E) ∈ T := by simpa [T] using hSU x.2
  let g : E → ComplexPoint (Over.mk q) := fun v => f (v + x.1)
  have hg : ContinuousOn g T := hf.comp
    (continuous_id.add continuous_const).continuousOn (fun _ hv => hv)
  have hg0 : g 0 = (C x).point := by simpa [g] using hC x
  obtain ⟨V, hVT, hVo, h0V, hVS, hmap⟩ := a3b4a_gysin_transverse_disk_normalClass
    (C x).chart _ (C x).support_eq (C x).point (C x).mem_source (C x).mem_support
    T hT h0T g hg hg0 (A x) (hA x) (hderiv x)
  obtain ⟨v, hv⟩ := (neighborhoodPointComplement_relativeHomologyMap_bijective
    V 0 hVo h0V (2 * c)).2 (standardComplexLocalClass ℚ c)
  let t : TopCat.of V ⟶ TopCat.of U := TopCat.ofHom
    ⟨fun u => ⟨u.1 + x.1, hVT u.2⟩,
      (continuous_subtype_val.add continuous_const).subtype_mk _⟩
  have hsingle : ∀ u : V, (t u).1 ∈ S → u.1 = 0 :=
    fun u hu => hVS u ((hS (t u).1 (t u).2).mpr hu)
  let H := a3b4_supportPairMap t {u : V | u.1 = 0} {u : U | u.1 ∈ S} hsingle
  let J := a3b4_neighborhoodPairMap U (S : Set E)
  let F := a3b4_supportPairMap (TopCat.ofHom ⟨fun u : U => f u.1, hf.domRestrict⟩)
    {u : U | u.1 ∈ S} (a3b4_cycleSupport q γ) (fun u hu => (hS u.1 u.2).mp hu)
  refine ⟨relativeHomologyMap ℚ (2 * c) H v, ?_, ?_, ?_⟩
  · have heq : H ≫ J ≫ supportInclusionPairMap (TopCat.of E)
        (Set.singleton_subset_iff.mpr x.2) =
        neighborhoodPointComplementPairMap V 0 ≫ translationPointComplementPairMap E x.1 := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp,
      ← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq,
      relativeHomologyMap_comp, LinearMap.comp_apply, hv]
    rfl
  · intro y hyx
    have hmiss : ∀ u : V, (t u).1 ∉ ({y.1} : Set E) := by
      intro u hu
      have huy : (t u).1 = y.1 := hu
      have hu0 := hsingle u (huy ▸ y.2)
      apply hyx
      apply Subtype.ext
      calc y.1 = (t u).1 := huy.symm
           _ = x.1 := by change u.1 + x.1 = x.1; rw [hu0, zero_add]
    let tE : TopCat.of V ⟶ TopCat.of E :=
      t ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let G := a3b4_supportPairMap tE {u : V | u.1 = 0} ({y.1} : Set E)
      (fun u hu => (hmiss u hu).elim)
    have heq : H ≫ J ≫ supportInclusionPairMap (TopCat.of E)
        (Set.singleton_subset_iff.mpr y.2) = G := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp,
      ← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq]
    have hzero := a3b4a_gysin_homologyMap_zero_of_avoids_support tE
      {u : V | u.1 = 0} ({y.1} : Set E) (fun u hu => (hmiss u hu).elim) hmiss (2 * c)
    change relativeHomologyMap ℚ (2 * c) G v = 0
    rw [hzero]
    rfl
  · have heq : H ≫ F = a3b4_supportPairMap
        (TopCat.ofHom ⟨fun u : V => g u.1, (hg.mono hVT).domRestrict⟩)
        {u : V | u.1 = 0} (a3b4_cycleSupport q γ) hVS := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq]
    exact hmap v hv

end HodgeLean.Adapters
