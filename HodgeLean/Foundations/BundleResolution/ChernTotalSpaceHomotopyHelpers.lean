import HodgeLean.Foundations.BundleResolution.ProjectiveTopology
import HodgeLean.Foundations.BundleThom.Defs
import Mathlib.Topology.Homotopy.Equiv

/-! # Actual bundle total-space deformation to the zero section

Scalar multiplication gives a homotopy in the supplied total topology.
No fibre norm or additional chart data is introduced.
HC no distance; AV milestone no distance. -/

noncomputable section
open Bundle TopologicalSpace Topology
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] {k : ℕ} (E : I1ComplexBundle B k)

def i1_complexBundleTotalProjection : C(TotalSpace (Fin k → ℂ) E.fibre, B) :=
  ⟨TotalSpace.proj, FiberBundle.continuous_proj (Fin k → ℂ) E.fibre⟩

def i1_complexBundleTotalDeformation :
    ContinuousMap.Homotopy
      ((i1_zeroSection k E.fibre).comp (i1_complexBundleTotalProjection E))
      (ContinuousMap.id (TotalSpace (Fin k → ℂ) E.fibre)) where
  toFun p := ⟨p.2.proj, ((p.1 : ℝ) : ℂ) • p.2.2⟩
  continuous_toFun := (i1_totalSpace_smul_continuous E).comp
    ((Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  map_zero_left v := by
    change (⟨v.proj, (0 : ℂ) • v.2⟩ : TotalSpace (Fin k → ℂ) E.fibre) = ⟨v.proj, 0⟩
    rw [zero_smul]
  map_one_left v := by
    change (⟨v.proj, (1 : ℂ) • v.2⟩ : TotalSpace (Fin k → ℂ) E.fibre) = v
    rw [one_smul]

def i1_complexBundleTotalHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (TotalSpace (Fin k → ℂ) E.fibre) B where
  toFun := i1_complexBundleTotalProjection E
  invFun := i1_zeroSection k E.fibre
  left_inv := ⟨i1_complexBundleTotalDeformation E⟩
  right_inv := ContinuousMap.Homotopic.refl _

end HodgeLean.Foundations.BundleResolution
