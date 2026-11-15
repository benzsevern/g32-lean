import HodgeLean.Foundations.Program.G32Native.PairedConormalGlobalSectionLift
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafPositiveVanishing
import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeNativeVanishing
import HodgeLean.Foundations.Program.G32Native.PairedC3BinaryCechVanishing
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.FiniteFreeTensorVanishing
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Sheaves.AffineExactSequenceSections
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Sheaves.ModuleSheafAffSES

/-! # Cech vanishing of the actual mixed bundle in Route N -/
noncomputable section
set_option maxHeartbeats 200000
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

/-- Finite free native modules have zero positive Cech cohomology.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1. -/
theorem paired_c3_free_native_vanishing (a q : ℕ) :
    Subsingleton ((toOModulePresheaf f
      (SheafOfModules.free (Fin a) : (pairedC3Proj k).Modules)).HSucc K q) := by
  haveI : Subsingleton ((toOModulePresheaf f
      (𝟙_ (pairedC3Proj k).Modules)).HSucc K q) :=
    twistingSectionPresheaf_subsingleton_HSucc ℂ k 0 q
  letI := finiteFreeTensor_subsingleton_HSucc f
    (𝟙_ (pairedC3Proj k).Modules) (Fin a) K q
  exact subsingleton_HSucc_of_iso f K
    (MonoidalCategory.rightUnitor (C := (pairedC3Proj k).Modules)
      (SheafOfModules.free (Fin a))) q

#print axioms paired_c3_free_native_vanishing

/-- All positive Cech groups vanish for the actual recursive mixed bundle.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1. -/
theorem paired_c3_split_bundle_vanishing (hk : 0 < k) (a b q : ℕ) :
    Subsingleton ((toOModulePresheaf f (pairedC3SplitBundle k a b)).HSucc K q) := by
  induction b with
  | zero => exact paired_c3_free_native_vanishing k a q
  | succ b ih =>
    letI := ih
    letI := paired_c3_negative_native_vanishing ℂ k hk q
    exact paired_c3_binary_vanishing f (pairedC3SplitBundle k a b)
      (pairedC3NegativeLine k) K q

#print axioms paired_c3_split_bundle_vanishing
/-- Every compatible quotient section lifts through the original map of
an exact native sequence with the actual mixed kernel.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1 and the cohomology sequence. -/
theorem paired_c3_split_kernel_section_lift (hk : 0 < k) (a b : ℕ)
    (E : ShortComplex (pairedC3Proj k).Modules) (hE : E.ShortExact)
    [E.X₂.IsQuasicoherent] [E.X₃.IsQuasicoherent]
    (e : E.X₁ ≅ pairedC3SplitBundle k a b) :
    Function.Surjective ((toOModulePresheafHom f E.g).toAffHom.H0Map K) := by
  letI := paired_c3_split_bundle_vanishing k hk a b 0
  letI := subsingleton_HSucc_of_iso f K e.symm 0
  exact (toOModulePresheafAffSES f E hE).H0Map_proj_surjective_of_subsingleton_H1 K

#print axioms paired_c3_split_kernel_section_lift
/-- The mixed-kernel vanishing lifts actual global sections through the
original native projection, on the whole projective parameter scheme.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1 and the cohomology sequence. -/
theorem paired_c3_split_kernel_global_lift (hk : 0 < k) (a b : ℕ)
    (E : ShortComplex (pairedC3Proj k).Modules) (hE : E.ShortExact)
    [E.X₂.IsQuasicoherent] [E.X₃.IsQuasicoherent]
    (e : E.X₁ ≅ pairedC3SplitBundle k a b) :
    Function.Surjective (E.g.app ⊤) := by
  letI := paired_c3_split_bundle_vanishing k hk a b 0
  letI := subsingleton_HSucc_of_iso f K e.symm 0
  exact paired_global_sections_surjective_of_cech_h1 f K E hE

#print axioms paired_c3_split_kernel_global_lift
end HodgeLean.Foundations.Program.G32Native
