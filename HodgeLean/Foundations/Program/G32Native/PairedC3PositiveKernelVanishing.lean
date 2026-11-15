import HodgeLean.Foundations.Program.G32Native.PairedC3SplitBundleVanishing
import HodgeLean.Foundations.Program.G32Native.PairedConormalFreeStabilizedFrame

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open ProjSpaceCech AlgebraicGeometry.ProjSpace Scheme.Modules
open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual positive twisting line has zero positive Cech cohomology.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1. -/
theorem paired_c3_positive_native_vanishing (k q : ℕ) :
    Subsingleton ((toOModulePresheaf ((𝟙 (pairedC3Proj k)) ≫ π ℂ k)
      (twistingSheaf ℂ k)).HSucc (stdCoverPullback (𝟙 (pairedC3Proj k))) q) := by
  letI := twistingSectionPresheaf_subsingleton_HSucc ℂ k 1 q
  exact subsingleton_HSucc_of_iso _ _ (tensorPowOneIso (twistingSheaf ℂ k)) q

/-- Tensoring a finite free sheaf with O(1) retains positive Cech vanishing.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1. -/
theorem paired_c3_positive_free_vanishing (k a q : ℕ) :
    Subsingleton ((toOModulePresheaf ((𝟙 (pairedC3Proj k)) ≫ π ℂ k)
      ((SheafOfModules.free (Fin a)) ⊗ (twistingSheaf ℂ k))).HSucc
        (stdCoverPullback (𝟙 (pairedC3Proj k))) q) := by
  letI := paired_c3_positive_native_vanishing k q
  exact finiteFreeTensor_subsingleton_HSucc _ (twistingSheaf ℂ k) (Fin a) _ q

/-- The original N.4 kernel after tensoring with O(1) has zero positive Cech cohomology.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1. -/
theorem paired_c3_extension_positive_kernel_vanishing (k a q : ℕ)
    (A : (pairedC3Proj k).Modules)
    (e : A ≅ (SheafOfModules.free (Fin a) ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf)) :
    Subsingleton ((toOModulePresheaf ((𝟙 (pairedC3Proj k)) ≫ π ℂ k)
      (A ⊗ (twistingSheaf ℂ k))).HSucc
        (stdCoverPullback (𝟙 (pairedC3Proj k))) q) := by
  letI := paired_c3_positive_free_vanishing k (a + 1) q
  let eA : A ≅ SheafOfModules.free (Fin (a + 1)) :=
    e ≪≫ (paired_free_biprod_unitFinIso (pairedC3Proj k) a).symm
  let eT : (tensor (X := pairedC3Proj k) (SheafOfModules.free (Fin (a + 1))) (twistingSheaf ℂ k)) ≅
      (tensor (X := pairedC3Proj k) A (twistingSheaf ℂ k)) :=
    ((tensorRight (C := (pairedC3Proj k).Modules) (twistingSheaf ℂ k)).mapIso eA).symm
  exact subsingleton_HSucc_of_iso _ _ eT q

end HodgeLean.Foundations.Program.G32Native
