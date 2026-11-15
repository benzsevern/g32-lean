import HodgeLean.Foundations.Program.G32Native.PairedC3SplitBundleSum
import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeSumLift
import HodgeLean.Foundations.Program.G32Native.PairedC3SplitFiniteFrames
import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeTwistFrame
import HodgeLean.Foundations.Program.G32Native.PairedC3TensorEquivalence
import HodgeLean.Foundations.Program.G32Native.PairedC3InvertibleTransport
import HodgeLean.Foundations.Program.G32Native.PairedC3TwistedExtensionSection
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.InvertibleCoherence

/-! # Extensions of negative lines by trivial bundles -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- B0.4: the original quotient arrow has a section. The relevant
extension group is H¹(P^k,O(1)) in each matrix entry.
Source: Hartshorne, Algebraic Geometry, III.5.1.
Checked: finite endpoint frames, native positive twisting, and the original tensor equivalence. -/
theorem paired_c3_positive_twist_extension_section_aux
    (k a b : ℕ) (E : ShortComplex (pairedC3Proj k).Modules)
    (hE : E.ShortExact)
    (e₁ : E.X₁ ≅ pairedC3SplitBundle k a 0)
    (e₃ : E.X₃ ≅ pairedC3SplitBundle k 0 b) :
    ∃ s : E.X₃ ⟶ E.X₂, s ≫ E.g = 𝟙 _ := by
  let L := ProjSpace.twistingSheaf ℂ k
  have hL : Scheme.Modules.IsInvertible L := ProjSpace.isInvertible_twistingSheaf ℂ k
  letI : E.X₂.IsLocallyFree := paired_c3_split_extension_middle_locallyFree k a b E hE e₁ e₃
  letI : E.X₂.IsQuasicoherent := inferInstance
  letI : E.X₃.IsLocallyFree := by
    apply paired_module_locallyFree_of_pullbackFrames
    intro x
    obtain ⟨U, hx, ⟨frame⟩⟩ := paired_c3_split_bundle_finite_frames k 0 b x
    exact ⟨U, hx, Fin (0 + b), ⟨frame.symm ≪≫
      (Scheme.Modules.pullback U.ι).mapIso e₃.symm⟩⟩
  letI : E.X₃.IsQuasicoherent := inferInstance
  letI : (E.X₂ ⊗ L.tensorPow 1).IsQuasicoherent := hL.isQuasicoherent_tensorPow E.X₂ 1
  letI : (E.X₃ ⊗ L.tensorPow 1).IsQuasicoherent := hL.isQuasicoherent_tensorPow E.X₃ 1
  let eT₃ : E.X₃ ⊗ L.tensorPow 1 ≅ SheafOfModules.free (Fin b) :=
    (tensorLeft E.X₃).mapIso (Scheme.Modules.tensorPowOneIso L) ≪≫
      (tensorRight L).mapIso e₃ ≪≫ pairedC3NegativeSumTwistFrame k b
  obtain ⟨s, hs⟩ := paired_c3_twisted_extension_section k a b 1 E hE e₁ eT₃
  exact paired_c3_section_of_invertible_twist
    (paired_c3_invertible_of_iso (Scheme.Modules.tensorPowOneIso L) hL) E.g s hs

/-- A section of the original quotient gives the stated bundle isomorphism. -/
def pairedC3PositiveTwistExtensionFrame
    (k a b : ℕ) (E : ShortComplex (pairedC3Proj k).Modules)
    (hE : E.ShortExact)
    (e₁ : E.X₁ ≅ pairedC3SplitBundle k a 0)
    (e₃ : E.X₃ ≅ pairedC3SplitBundle k 0 b)
    (s : E.X₃ ⟶ E.X₂) (hs : s ≫ E.g = 𝟙 _) :
    E.X₂ ≅ pairedC3SplitBundle k a b :=
  (ShortComplex.Splitting.ofExactOfSection E hE.exact s hs hE.mono_f).isoBinaryBiproduct ≪≫
    biprod.mapIso e₁ e₃ ≪≫ pairedC3SplitBundleSum k a b

#print axioms paired_c3_positive_twist_extension_section_aux
#print axioms pairedC3PositiveTwistExtensionFrame
end HodgeLean.Foundations.Program.G32Native
