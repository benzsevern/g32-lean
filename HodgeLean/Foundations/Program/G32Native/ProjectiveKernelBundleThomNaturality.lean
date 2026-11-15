import HodgeLean.Foundations.Program.G32Native.KernelThomChartDetection
import HodgeLean.Foundations.Program.G32Native.KernelThomFibreNormalization

/-! # Complex Thom naturality for the actual projective kernel model -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Bundle
open HodgeLean.Foundations.BundleThom HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program.G32Native
open EulerModel

/-- Normalized Thom naturality for an actual complex-linear bundle homeomorphism.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex Thom
orientation and uniqueness; Fulton, Intersection Theory, §6.3, zero sections.
The input retains full fibre maps and both total-space topologies. -/
theorem projective_kernel_bundle_thom_naturality_aux
    {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (D : ProjectiveKernelBundleComparison k E) :
    relativeCohomologyMap ℚ (2 * k) D.pairMap (normalKernelGlobalThomClass k) =
      i1_bundleThom k E := by
  have hinverse : relativeCohomologyMap ℚ (2 * k) D.pairIso.inv (i1_bundleThom k E) =
      normalKernelGlobalThomClass k := by
    apply kernelChartPairParam_ext
    intro j
    rw [kernelChartPairParam_normalization]
    apply i1_contractibleProductCoclass_ext k (0 : Fin k → ℂ) (2 * k)
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      ← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
    have hprojection : i1_productNormalSection k (0 : Fin k → ℂ) ≫
        i1_productNormalProjection (Fin k → ℂ) k = 𝟙 (puncturedPair ℂ k) :=
      i1_productNormalSection_projection k 0
    conv_rhs => rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      hprojection, relativeCohomologyMap_id, LinearMap.id_apply]
    let b := D.base.symm (kernelChartBase k j 0)
    have hb : kernelChartBase k j 0 = D.base b := (D.base.apply_symm_apply _).symm
    let T := LinearEquiv.ofEq (projectiveNormalKernel k (kernelChartBase k j 0))
      (projectiveNormalKernel k (D.base b)) (congrArg (projectiveNormalKernel k) hb)
    let L := ((kernelChartFibreEquiv k j 0).trans T).trans (D.fibre b).symm
    apply bundleThom_linear_fibre k E b L
    intro v
    change D.total.symm (normalCoordinateKernelParam k j (0, v)) = ⟨b, L v⟩
    have hparam : normalCoordinateKernelParam k j (0, v) =
        ⟨(D.base b, (T (kernelChartFibreEquiv k j 0 v)).val),
          (T (kernelChartFibreEquiv k j 0 v)).property⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · exact hb
      · rfl
    rw [hparam, D.inverse_fibre]
    rfl
  have h := congrArg (relativeCohomologyMap ℚ (2 * k) D.pairIso.hom) hinverse
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    Iso.hom_inv_id, relativeCohomologyMap_id, LinearMap.id_apply,
    D.pairIso_hom] at h
  exact h.symm

#print axioms projective_kernel_bundle_thom_naturality_aux
end HodgeLean.Foundations.Program.G32Native
