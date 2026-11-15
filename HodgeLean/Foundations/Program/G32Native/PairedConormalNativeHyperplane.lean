import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeProjective
import HodgeLean.Foundations.Program.G32Native.PairedConormalIdealIsoPullback
import HodgeLean.Foundations.Curves.Picard.LineBundles.IdealModuleTransportIso
import HodgeLean.Foundations.Program.SchoenCycleProjectiveAffineIdeals
import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs

/-! # The actual hyperplane ideal under the native projective identification -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual reduced coordinate hyperplane ideal on the native polynomial Proj. -/
def paired_nativeHyperplaneIdeal (k : ℕ) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨(Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)
      (MvPolynomial.X 0)).carrierᶜ,
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)
        (MvPolynomial.X 0)).isOpen.isClosed_compl⟩

/-- The original retained hyperplane ideal pulls back to the actual native
coordinate hyperplane under the specified projective scheme identification. -/
theorem paired_nativeHyperplaneIdeal_eq_comap (k : ℕ) :
    (s2e_hyperplaneIdeal k).comap (pairedNativeProjectiveIso ℂ k).hom =
      paired_nativeHyperplaneIdeal k := by
  unfold s2e_hyperplaneIdeal paired_nativeHyperplaneIdeal
  rw [s2e_open_comap_vanishingIdeal]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply Closeds.ext
  have hp := pairedNativeProjectiveIso_coordinateOpen ℂ k (0 : Fin (k + 1))
  change (pairedNativeProjectiveIso ℂ k).hom ⁻¹ᵁ
    AlgebraicGeometry.ComplexProjectiveSpace.projectiveSpaceBasicOpen k (MvPolynomial.X 0) =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)
        (MvPolynomial.X 0) at hp
  change (pairedNativeProjectiveIso ℂ k).hom ⁻¹'
    ((AlgebraicGeometry.ComplexProjectiveSpace.projectiveSpaceBasicOpen k
      (MvPolynomial.X 0)).carrierᶜ) = _
  rw [Set.preimage_compl]
  exact congrArg (fun U => U.carrierᶜ) hp

/-- The actual retained hyperplane ideal module pulls back to the actual
native hyperplane ideal module through the natural kernel comparison. -/
def paired_nativeHyperplaneModuleIso (k : ℕ) :
    (Scheme.Modules.pullback (pairedNativeProjectiveIso ℂ k).hom).obj
        (Conormal.idealModule (s2e_hyperplaneIdeal k).subschemeι) ≅
      Conormal.idealModule (paired_nativeHyperplaneIdeal k).subschemeι :=
  HodgeLean.Foundations.Curves.Picard.LineBundles.idealModuleTransportIso
    (paired_nativeHyperplaneIdeal_eq_comap k)
    (paired_idealPullbackIso_of_iso (pairedNativeProjectiveIso ℂ k) (s2e_hyperplaneIdeal k))

end HodgeLean.Foundations.Program.G32Native
