import HodgeLean.Foundations.Program.G32Native.ProjectiveKernelBundleComparison

/-! # Normalization under specified linear fibre coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Bundle
open HodgeLean.Foundations.BundleThom HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program.G32Native

/-- A supported fibre map with specified complex linear coordinates retains Thom normalization.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex orientation. -/
theorem bundleThom_linear_fibre
    {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (b : B) (L : (Fin k → ℂ) ≃ₗ[ℂ] E b)
    (f : puncturedPair ℂ k ⟶
      TopPair.ofSubset (X := i1_totalSpace k E) (i1_zeroSupport k E)ᶜ)
    (hf : ∀ v, TopPair.Hom.fst f v = (⟨b, L v⟩ : TotalSpace (Fin k → ℂ) E)) :
    relativeCohomologyMap ℚ (2 * k) f (i1_bundleThom k E) =
      normalizedPointCoclass k := by
  let e := trivializationAt (Fin k → ℂ) E b
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  let A := L.trans (e.continuousLinearEquivAt ℂ b hb).toLinearEquiv
  let M := LinearMap.toMatrix' A.toLinearMap
  have hM (v : Fin k → ℂ) : M.mulVec v = A v := LinearMap.toMatrix'_mulVec _ v
  have hd : M.det ≠ 0 := by
    apply isUnit_iff_ne_zero.mp
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro v w h
    exact A.injective ((hM v).symm.trans (h.trans (hM w)))
  have heq : f = complexMatrixPuncturedPairMap k M hd ≫
      i1_chartFibreInclusion k E e b hb ≫ i1_chartInclusion k E e := by
    apply MorphismProperty.Arrow.Hom.ext
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro v
      apply Subtype.ext
      change (f.left v).val = _
      rw [show (f.left v).val = TopPair.Hom.fst f v.1 from
        ConcreteCategory.congr_hom f.w v]
      rw [hf]
      change (⟨b, L v.1⟩ : TotalSpace (Fin k → ℂ) E) =
        ⟨b, (e.continuousLinearEquivAt ℂ b hb).symm (M.mulVec v.1)⟩
      rw [hM]
      exact congrArg (fun w => (⟨b, w⟩ : TotalSpace (Fin k → ℂ) E))
        ((e.continuousLinearEquivAt ℂ b hb).symm_apply_apply (L v.1)).symm
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro v
      rw [hf]
      change (⟨b, L v⟩ : TotalSpace (Fin k → ℂ) E) =
        ⟨b, (e.continuousLinearEquivAt ℂ b hb).symm (M.mulVec v)⟩
      rw [hM]
      exact congrArg (fun w => (⟨b, w⟩ : TotalSpace (Fin k → ℂ) E))
        ((e.continuousLinearEquivAt ℂ b hb).symm_apply_apply (L v)).symm
  rw [heq, relativeCohomologyMap_comp, LinearMap.comp_apply,
    relativeCohomologyMap_comp, LinearMap.comp_apply]
  rw [show relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E e)
    (i1_bundleThom k E) = i1_chartOrientation k E e from
      Classical.choose_spec (i1_bundleThom_exists_unique k E).exists e inferInstance]
  rw [i1_chartOrientation_fibre, i1_complexMatrix_relativeCohomologyMap]

#print axioms bundleThom_linear_fibre
end HodgeLean.Foundations.Program.G32Native
