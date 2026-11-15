import HodgeLean.Adapters.NormalConeB4aDefs
import HodgeLean.Adapters.NormalConeB2Cycle

/-! # Supports of fundamental cycles in a fibre

The positive generic lengths retain every irreducible component. Base change
then identifies the support on the fibre with the inverse image of the total support.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

/-- The support points of the fundamental cycle are exactly the images of generic points. -/
theorem a3b4a_gysin_idealCycle_support {Z : Scheme.{0}} [IsNoetherian Z]
    (J : Z.IdealSheafData) :
    (a3b2_idealCycle J (a3b2_components_finite_of_isNoetherian J)
      (a3b2_length_ne_top_of_isLocallyNoetherian J)).support =
      J.subschemeι '' genericPoints J.subscheme := by
  classical
  ext z
  change _ ≠ 0 ↔ _
  constructor
  · intro hz
    by_contra hn
    exact hz (a3b2_idealCycle_apply_eq_zero J _ _ z (by
      simpa only [Set.mem_image, not_exists, not_and] using hn))
  · rintro ⟨y, hy, rfl⟩
    rw [a3b2_idealCycle_apply J _ _ ⟨y, hy⟩]
    exact ne_of_gt (Nat.cast_pos.mpr (a3b2_genericLength_pos J _ ⟨y, hy⟩))

/-- The union of component supports of a fundamental cycle is the subscheme support. -/
theorem a3b4a_gysin_idealCycle_supportClosure {Z : Scheme.{0}} [IsNoetherian Z]
    (J : Z.IdealSheafData) :
    (⋃ ξ ∈ (a3b2_idealCycle J (a3b2_components_finite_of_isNoetherian J)
      (a3b2_length_ne_top_of_isLocallyNoetherian J)).support, closure {ξ}) = J.support := by
  rw [a3b4a_gysin_idealCycle_support, ← Scheme.IdealSheafData.range_subschemeι]
  ext z
  constructor
  · intro hz
    obtain ⟨ξ, ⟨y, hy, rfl⟩, hz⟩ := Set.mem_iUnion₂.mp hz
    exact (IsClosedImmersion.isClosedEmbedding J.subschemeι).isClosed_range.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr ⟨y, rfl⟩) hz
  · rintro ⟨y, rfl⟩
    let ξ := genericPoints.ofComponent
      ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
    have hy : y ∈ closure {ξ.1} := by
      rw [(genericPoints.isGenericPoint ξ).def, genericPoints.component_ofComponent]
      exact mem_irreducibleComponent
    refine Set.mem_iUnion₂.mpr ⟨J.subschemeι ξ.1, ⟨ξ.1, ξ.2, rfl⟩, ?_⟩
    have hs := (specializes_iff_mem_closure).mpr hy
    exact specializes_iff_mem_closure.mp (hs.map J.subschemeι.continuous)

/-- For an immersion, the analytic support of the image cycle is the inverse image of its range. -/
theorem a3b4a_gysin_imageCycle_support {Z K : Scheme.{0}} [IsNoetherian Z]
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) (i : K ⟶ Z) [IsClosedImmersion i] :
    a3b4_cycleSupport q (a3b3_imageCycle i inferInstance) =
      Point.underlying ⁻¹' Set.range i := by
  unfold a3b4_cycleSupport a3b3_imageCycle
  rw [a3b4a_gysin_idealCycle_supportClosure, Scheme.Hom.support_ker,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.closure_eq]

/-- The map of fibres inherits the immersion property. -/
theorem a3b4a_gysin_fibreMap_isClosedImmersion {Z K : Scheme.{0}}
    (i : K ⟶ Z) [IsClosedImmersion i] (h : Z ⟶ a3b2_line ℂ)
    (hK : K ⟶ a3b2_line ℂ) (hiK : i ≫ h = hK) (s : ℂ) :
    IsClosedImmersion (a3b4a_fibreMap i h hK hiK s) := by
  have : IsClosedImmersion
      (a3b4a_fibreMap i h hK hiK s ≫ pullback.fst h (a3b2_point ℂ s)) := by
    unfold a3b4a_fibreMap
    simp only [pullback.map, pullback.lift_fst]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (a3b4a_fibreMap i h hK hiK s) (pullback.fst h (a3b2_point ℂ s))

/-- The range of the fibre map is the inverse image of the original immersion's range. -/
theorem a3b4a_gysin_fibreMap_range {Z K : Scheme.{0}}
    (i : K ⟶ Z) (h : Z ⟶ a3b2_line ℂ)
    (hK : K ⟶ a3b2_line ℂ) (hiK : i ≫ h = hK) (s : ℂ) :
    Set.range (a3b4a_fibreMap i h hK hiK s) =
      pullback.fst h (a3b2_point ℂ s) ⁻¹' Set.range i := by
  unfold a3b4a_fibreMap
  rw [Scheme.Pullback.range_map]
  change _ ∩ (_ ⁻¹' Set.range id) = _
  rw [Set.range_id, Set.preimage_univ, Set.inter_univ]

/-- The analytic fibre-cycle support is exactly the inverse image of the total-cycle support. -/
theorem a3b4a_gysin_fibre_support {Z K : Scheme.{0}} [IsNoetherian Z]
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) (i : K ⟶ Z) [IsClosedImmersion i]
    (h : Z ⟶ a3b2_line ℂ) (hK : K ⟶ a3b2_line ℂ) (hiK : i ≫ h = hK) (s : ℂ)
    (x : a3b4_an (pullback.fst h (a3b2_point ℂ s) ≫ q)) :
    a3b4_anMap (q' := q) (pullback.fst h (a3b2_point ℂ s)) rfl x ∈
        a3b4_cycleSupport q (a3b3_imageCycle i inferInstance) ↔
      x ∈ a3b4_cycleSupport (pullback.fst h (a3b2_point ℂ s) ≫ q)
        (a3b3_imageCycle (a3b4a_fibreMap i h hK hiK s)
          (a3b4a_fibre_isNoetherian h s)) := by
  let := a3b4a_fibre_isNoetherian h s
  let := a3b4a_gysin_fibreMap_isClosedImmersion i h hK hiK s
  rw [a3b4a_gysin_imageCycle_support, a3b4a_gysin_imageCycle_support,
    a3b4a_gysin_fibreMap_range]
  rfl

end HodgeLean.Adapters
