import HodgeLean.Foundations.BundleResolution.ChernTensorExactHelpers

/-! # Actual chain cokernels after rational tensoring

The actual tensor quotient is identified by the cokernel universal property
using the checked short exact tensor sequence.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits MonoidalCategory
namespace HodgeLean.Foundations.BundleResolution

def i1_tensorRightCokernelIso {K K' : ChainComplex (ModuleCat ℚ) ℕ}
    (f : K ⟶ K') [Mono f] (L : ChainComplex (ModuleCat ℚ) ℕ) :
    cokernel (f ▷ L) ≅ (cokernel f) ⊗ L := by
  have hS : (ShortComplex.cokernelSequence f).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f
      mono_f := by change Mono f; infer_instance
      epi_g := by change Epi (cokernel.π f); infer_instance }
  have hT := i1_tensorRightShortComplex_shortExact (ShortComplex.cokernelSequence f) hS L
  exact (cokernelIsCokernel (f ▷ L)).coconePointUniqueUpToIso hT.gIsCokernel

theorem i1_tensorRightCokernelIso_π {K K' : ChainComplex (ModuleCat ℚ) ℕ}
    (f : K ⟶ K') [Mono f] (L : ChainComplex (ModuleCat ℚ) ℕ) :
    cokernel.π (f ▷ L) ≫ (i1_tensorRightCokernelIso f L).hom = cokernel.π f ▷ L := by
  unfold i1_tensorRightCokernelIso
  exact (cokernelIsCokernel (f ▷ L)).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

theorem i1_tensorRight_mono {K K' : ChainComplex (ModuleCat ℚ) ℕ}
    (f : K ⟶ K') [Mono f] (L : ChainComplex (ModuleCat ℚ) ℕ) : Mono (f ▷ L) := by
  have hS : (ShortComplex.cokernelSequence f).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f
      mono_f := by change Mono f; infer_instance
      epi_g := by change Epi (cokernel.π f); infer_instance }
  exact (i1_tensorRightShortComplex_shortExact (ShortComplex.cokernelSequence f) hS L).mono_f

end HodgeLean.Foundations.BundleResolution
