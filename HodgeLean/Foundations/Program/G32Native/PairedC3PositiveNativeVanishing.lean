import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.ModuleSheafCohomologyIso
import HodgeLean.Foundations.Program.G32Native.PairedConormalGlobalSectionLift
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects
import HodgeLean.Foundations.Program.G32Native.PairedConormalUnitLift
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafPositiveVanishing
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.FiniteFreeTensorVanishing
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Sheaves.AffineExactSequenceSections

/-! # Positive native twists and lifting through their extensions -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open ProjSpaceCech AlgebraicGeometry.ProjSpace Scheme.Modules
open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
variable (k : ℕ)
local notation "A" => MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ
local notation "f" => ((𝟙 (Proj A)) ≫ π ℂ k)
local notation "K" => stdCoverPullback (𝟙 (Proj A))

/-- Finite sums of native nonnegative twists have zero positive Cech groups.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1. -/
theorem paired_c3_positive_free_native_vanishing (a d q : ℕ) :
    Subsingleton ((toOModulePresheaf f
      ((SheafOfModules.free (Fin a) : (pairedC3Proj k).Modules) ⊗
        (twistingSheaf ℂ k).tensorPow d)).HSucc K q) := by
  letI := twistingSectionPresheaf_subsingleton_HSucc ℂ k d q
  exact finiteFreeTensor_subsingleton_HSucc f
    ((twistingSheaf ℂ k).tensorPow d) (Fin a) K q

#print axioms paired_c3_positive_free_native_vanishing
/-- Positive native kernels lift global sections through the original projection.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1 and the cohomology sequence. -/
theorem paired_c3_positive_kernel_global_lift (a d : ℕ)
    (E : ShortComplex (pairedC3Proj k).Modules) (hE : E.ShortExact)
    [E.X₂.IsQuasicoherent] [E.X₃.IsQuasicoherent]
    (e : E.X₁ ≅ (SheafOfModules.free (Fin a) : (pairedC3Proj k).Modules) ⊗
      (twistingSheaf ℂ k).tensorPow d) :
    Function.Surjective (E.g.app ⊤) := by
  letI := paired_c3_positive_free_native_vanishing k a d 0
  letI := subsingleton_HSucc_of_iso f K e.symm 0
  exact paired_global_sections_surjective_of_cech_h1 f K E hE

#print axioms paired_c3_positive_kernel_global_lift
/-- A finite free quotient has a section for a positive native kernel.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1 and the cohomology sequence. -/
theorem paired_c3_positive_kernel_free_quotient_section (a b d : ℕ)
    (E : ShortComplex (pairedC3Proj k).Modules) (hE : E.ShortExact)
    [E.X₂.IsQuasicoherent] [E.X₃.IsQuasicoherent]
    (e₁ : E.X₁ ≅ (SheafOfModules.free (Fin a) : (pairedC3Proj k).Modules) ⊗
      (twistingSheaf ℂ k).tensorPow d)
    (e₃ : E.X₃ ≅ SheafOfModules.free (Fin b)) :
    ∃ s : E.X₃ ⟶ E.X₂, s ≫ E.g = 𝟙 _ := by
  have hlift (j : Fin b) := conormal_unit_lift_of_top_surjective E.g
    (paired_c3_positive_kernel_global_lift k a d E hE e₁)
    (SheafOfModules.ιFree j ≫ e₃.inv)
  choose l hl using hlift
  let u : SheafOfModules.free (Fin b) ⟶ E.X₂ := Sigma.desc l
  have hu : u ≫ E.g = e₃.inv := by
    apply Sigma.hom_ext
    intro j
    simpa only [u, Category.assoc, Sigma.ι_desc_assoc, SheafOfModules.ιFree] using hl j
  refine ⟨e₃.hom ≫ u, ?_⟩
  rw [Category.assoc, hu, e₃.hom_inv_id]

#print axioms paired_c3_positive_kernel_free_quotient_section
end HodgeLean.Foundations.Program.G32Native
