import HodgeLean.Adapters.NormalConeB4aGysinNormalCycles
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ComplexClassDifferentiableInvariance

/-! # Transverse disks and ambient normal cycles

An invertible complex derivative of the normal coordinate gives the positive
normal generator. The disk map itself may have varying tangential coordinates.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicTopology.Singular

/-- A disk transverse to a flattened support represents its positive normal class. -/
theorem a3b4a_gysin_transverse_disk_normalClass
    {M : Type} [TopologicalSpace M] {r c : ℕ}
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin c → ℂ)))
    (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (x : M) (hx : x ∈ e.source) (hxS : x ∈ S)
    (U : Set (Fin c → ℂ)) (hU : IsOpen U) (h0U : 0 ∈ U)
    (f : (Fin c → ℂ) → M) (hf : ContinuousOn f U) (hf0 : f 0 = x)
    (A : Matrix (Fin c) (Fin c) ℂ) (hA : A.det ≠ 0)
    (hderiv : HasFDerivAt (fun v => (e (f v)).2)
      (A.mulVecLin.toContinuousLinearMap : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) 0) :
    ∃ (V : Set (Fin c → ℂ)) (hVU : V ⊆ U), IsOpen V ∧ 0 ∈ V ∧
      ∃ hVS : ∀ v : V, f v.1 ∈ S → v.1 = 0,
      ∀ z : RelativeHomology ℚ (neighborhoodPointComplementPair V 0) (2 * c),
        relativeHomologyMap ℚ (2 * c) (neighborhoodPointComplementPairMap V 0) z =
          standardComplexLocalClass ℚ c →
        relativeHomologyMap ℚ (2 * c)
          (a3b4_supportPairMap (TopCat.ofHom ⟨fun v : V => f v.1,
            (hf.mono hVU).domRestrict⟩) {v : V | v.1 = 0} S hVS) z =
          relativeHomologyMap ℚ (2 * c)
            (a3b4_neighborhoodPairMap
              (flattenedSupportNeighborhood (Fin r → ℂ) c e x hx) S)
            (flattenedSupportNormalClass (Fin r → ℂ) c e x hx S hS
              ((hS x hx).mp hxS)) := by
  let W := flattenedSupportNeighborhood (Fin r → ℂ) c e x hx
  have hWe : (W : Set M) ⊆ e.source :=
    flattenedSupportNeighborhood_subset_source (Fin r → ℂ) c e x hx
  let T := U ∩ f ⁻¹' (W : Set M)
  have hT : IsOpen T := hf.isOpen_inter_preimage hU W.isOpen
  have h0T : (0 : Fin c → ℂ) ∈ T := by
    refine ⟨h0U, ?_⟩
    change f 0 ∈ W
    rw [hf0]
    exact mem_flattenedSupportNeighborhood (Fin r → ℂ) c e x hx
  let g := fun v => (e (f v)).2
  have hg : ContinuousOn g T :=
    (e.continuousOn.comp (hf.mono Set.inter_subset_left)
      (fun v hv => hWe hv.2)).snd
  have hg0 : g 0 = 0 := by
    dsimp only [g]
    rw [hf0]
    exact (hS x hx).mp hxS
  obtain ⟨V, hVT, hne, hVo, h0V, hmap⟩ :=
    exists_open_complexDifferentiable_localClass_invariance c A hA T hT h0T
      g hg hg0 hderiv
  have hVU : V ⊆ U := hVT.trans Set.inter_subset_left
  have hVS : ∀ v : V, f v.1 ∈ S → v.1 = 0 := by
    intro v hv
    by_contra hv0
    exact hne v.1 v.2 hv0 ((hS (f v.1) (hWe (hVT v.2).2)).mp hv)
  refine ⟨V, hVU, hVo, h0V, hVS, ?_⟩
  intro z hz
  let F := a3b4_supportPairMap
    (TopCat.ofHom ⟨fun v : V => (⟨f v.1, (hVT v.2).2⟩ : W),
      ((hf.mono hVU).domRestrict).subtype_mk _⟩)
    {v : V | v.1 = 0} {w : W | w.1 ∈ S} hVS
  have hF : relativeHomologyMap ℚ (2 * c) F z =
      flattenedSupportNormalClass (Fin r → ℂ) c e x hx S hS ((hS x hx).mp hxS) := by
    apply chartNormalProjection_relativeHomologyMap_injective (Fin r → ℂ) c e S hS x hx
      ((hS x hx).mp hxS)
    rw [chartNormalProjection_normalClass, ← LinearMap.comp_apply, ← relativeHomologyMap_comp]
    have heq : F ≫ chartNormalProjectionPair (Fin r → ℂ) c e S hS W hWe =
        complexNeighborhoodPuncturedPairMapOf c V g (hg.mono hVT) hne := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext v <;> rfl
    change relativeHomologyMap ℚ (2 * c)
      (F ≫ chartNormalProjectionPair (Fin r → ℂ) c e S hS W hWe) z = _
    rw [heq]
    exact hmap z hz
  have heq : F ≫ a3b4_neighborhoodPairMap W S =
      a3b4_supportPairMap (TopCat.ofHom ⟨fun v : V => f v.1,
        (hf.mono hVU).domRestrict⟩) {v : V | v.1 = 0} S hVS := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext v <;> rfl
  rw [← heq, relativeHomologyMap_comp, LinearMap.comp_apply, hF]

end HodgeLean.Adapters
