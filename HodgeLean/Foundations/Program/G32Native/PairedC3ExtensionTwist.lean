import HodgeLean.Foundations.Program.G32Native.PairedC3ExtensionCoherence
import HodgeLean.Foundations.Program.G32Native.PairedC3PositiveKernelVanishing
import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeTensorFrame
import HodgeLean.Foundations.Program.G32Native.PairedC3TensorSectionDescent
import HodgeLean.Foundations.Program.G32Native.PairedC3FreeQuotientSection
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.InvertibleExactness
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.InvertibleCoherence

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open ProjSpaceCech AlgebraicGeometry.ProjSpace Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- Tensoring with an invertible sheaf preserves quasicoherence. -/
theorem paired_c3_invertible_tensor_quasicoherent {X : Scheme.{0}}
    (M L : X.Modules) [M.IsQuasicoherent] (hL : IsInvertible L) :
    (M ⊗ L).IsQuasicoherent := by
  have h := hL.isQuasicoherent_tensorPow M 1
  let e : M ⊗ L.tensorPow 1 ≅ M ⊗ L :=
    whiskerLeftIso M (tensorPowOneIso L)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((sheafOfModulesEquivalence X).functor.mapIso e) h

/-- The inverse line frame and positive Cech vanishing split the original extension.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1 and the cohomology sequence. -/
theorem paired_c3_extension_frame_of_inverse_line
    (k a b : ℕ) (T : ShortComplex (pairedC3Proj k).Modules) (hT : T.ShortExact)
    (e₁ : T.X₁ ≅ (SheafOfModules.free (Fin a) ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf))
    (e₃ : T.X₃ ≅ pairedC3SplitBundle k 0 b)
    (eL : pairedC3NegativeLine k ⊗ twistingSheaf ℂ k ≅ 𝟙_ (pairedC3Proj k).Modules) :
    Nonempty (T.X₂ ≅ pairedC3SplitBundle k (a + 1) b) := by
  let L : (pairedC3Proj k).Modules := twistingSheaf ℂ k
  let F := tensorRight (C := (pairedC3Proj k).Modules) L
  let S := T.map F
  have hL : IsInvertible L := isInvertible_twistingSheaf ℂ k
  have hS : S.ShortExact := hL.shortExact_tensorRight T hT
  letI := paired_c3_route_n_extension_middle_quasicoherent k a b T hT e₁ e₃
  letI : S.X₂.IsQuasicoherent := paired_c3_invertible_tensor_quasicoherent T.X₂ L hL
  let eS₃ : S.X₃ ≅ SheafOfModules.free (Fin b) :=
    F.mapIso e₃ ≪≫ pairedC3NegativeTensorFrame k L eL b
  have hfree : (SheafOfModules.free (Fin b) : (pairedC3Proj k).Modules).IsQuasicoherent :=
    inferInstance
  letI : S.X₃.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (pairedC3Proj k).ringCatSheaf).prop_of_iso
      ((sheafOfModulesEquivalence _).functor.mapIso eS₃.symm) hfree
  let f := (𝟙 (pairedC3Proj k)) ≫ π ℂ k
  let K := stdCoverPullback (𝟙 (pairedC3Proj k))
  letI : Subsingleton ((toOModulePresheaf f S.X₁).HSucc K 0) :=
    paired_c3_extension_positive_kernel_vanishing k a 0 T.X₁ e₁
  have hsurj : Function.Surjective (S.g.app ⊤) :=
    paired_global_sections_surjective_of_cech_h1 f K S hS
  obtain ⟨s, hs⟩ := paired_c3_free_quotient_section S.g hsurj (Fin b) eS₃
  let eInv : L ⊗ pairedC3NegativeLine k ≅ 𝟙_ (pairedC3Proj k).Modules :=
    (β_ L (pairedC3NegativeLine k)) ≪≫ eL
  obtain ⟨t, ht⟩ := paired_c3_section_of_tensor_section eInv T.g s hs
  exact ⟨pairedC3ExtensionFrameOfSection k a b T hT e₁ e₃ t ht⟩

end HodgeLean.Foundations.Program.G32Native
