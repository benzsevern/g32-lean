import HodgeLean.Foundations.Program.G32Native.KernelThomPairTransport

/-! # Linear fibres in the original ordered kernel charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Bundle
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native
open EulerModel

/-- The actual base point of the ordered model chart. -/
def kernelChartBase (k : ℕ) (j : Fin (k + 1)) (z : Fin k → ℂ) :=
  (normalPermutationBaseHomeomorph k (Equiv.swap 0 j)).symm (normalProjectiveChart k z)

/-- The original model parameterization is linear and bijective on each fixed fibre. -/
def kernelChartFibreEquiv (k : ℕ) (j : Fin (k + 1)) (z : Fin k → ℂ) :
    (Fin k → ℂ) ≃ₗ[ℂ] projectiveNormalKernel k (kernelChartBase k j z) := by
  let A := normalCoordinatePermutation k (Equiv.swap 0 j)
  let f := A.symm.toLinearMap.comp
    ((LinearMap.ker (normalEvaluation k z)).subtype.comp (normalKernelChart k z))
  have hf (a : Fin k → ℂ) : f a ∈ projectiveNormalKernel k (kernelChartBase k j z) :=
    (normalCoordinateKernelParam k j (z, a)).property
  let g := f.codRestrict _ hf
  apply LinearEquiv.ofBijective g
  constructor
  · intro a b h
    apply (normalKernelChart_bijective k z).1
    apply Subtype.ext
    exact A.symm.injective (congrArg Subtype.val h)
  · intro v
    have hv : A v.1 ∈ LinearMap.ker (normalEvaluation k z) := by
      rw [← projectiveNormalKernel_chart]
      have h := (normalCoordinatePermutation_kernel k (Equiv.swap 0 j)
        (kernelChartBase k j z) v.1).mpr v.2
      simpa only [kernelChartBase, Homeomorph.apply_symm_apply] using h
    refine ⟨(A v.1).2, ?_⟩
    apply Subtype.ext
    change A.symm (normalKernelChart k z (A v.1).2).1 = v.1
    rw [normalKernelChart_vector_tail k z (A v.1) hv, A.symm_apply_apply]

/-- The linear frame retains the literal vector of the original parameterization. -/
theorem kernelChartFibreEquiv_val (k : ℕ) (j : Fin (k + 1)) (z a : Fin k → ℂ) :
    (kernelChartFibreEquiv k j z a).val = (normalCoordinateKernelParam k j (z, a)).val.2 := rfl

/-- Product coordinates map continuously into the original zero-complement pair. -/
def kernelChartPairParam (k : ℕ) (j : Fin (k + 1)) :
    i1_productNormalPair (Fin k → ℂ) k ⟶
      TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0}ᶜ :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨normalCoordinateKernelParam k j,
      (isOpenEmbedding_normalCoordinateKernelParam k j).continuous⟩)
    (fun za h hzero => h ((normalCoordinateKernelChart_vector_zero_iff k j za).mp hzero))

#print axioms kernelChartFibreEquiv
#print axioms kernelChartPairParam
end HodgeLean.Foundations.Program.G32Native
