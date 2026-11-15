import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeCechComparison
import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeCechVanishing
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModuleHEquivFD

/-! # Positive Cech vanishing for the actual native negative line -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open ProjSpaceCech AlgebraicGeometry.ProjSpace Scheme.Modules
open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
variable (R : Type) [CommRing R] (n : ℕ)
local notation "A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- Every positive native negative-line cocycle is an actual coboundary.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1. -/
theorem paired_c3_negative_native_exact (hn : 0 < n) (q : ℕ)
    (z : (pairedC3NegativeSectionPresheaf R n).cochain
      (stdCoverPullback (𝟙 (Proj A))) (q + 1))
    (hz : (pairedC3NegativeSectionPresheaf R n).d
      (stdCoverPullback (𝟙 (Proj A))) (q + 1) z = 0) :
    ∃ y, (pairedC3NegativeSectionPresheaf R n).d
      (stdCoverPullback (𝟙 (Proj A))) q y = z := by
  let e := pairedC3NegativeCochainEquiv R n
  let c := (e (q + 1)).symm z
  have hc : GradedModule.d (GradedModule.FD R n (-1)) (q + 1) c = 0 := by
    apply (e (q + 2)).injective
    rw [map_zero, paired_c3_negative_cochain_d]
    change (pairedC3NegativeSectionPresheaf R n).d _ (q + 1)
      (e (q + 1) ((e (q + 1)).symm z)) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact hz
  letI : Subsingleton (Twist.H R n (-1) (q + 1)) :=
    paired_c3_cech_positive_vanishing R n (-1) (by omega) q
  let E := (GradedModule.nonempty_HEquiv_FD R n (-1) (q + 1)).some
  have hsub : Subsingleton (GradedModule.H (GradedModule.FD R n (-1)) (q + 1)) :=
    ⟨fun x y => E.symm.injective (Subsingleton.elim _ _)⟩
  change Subsingleton (_ ⧸ _) at hsub
  have ht := (Submodule.Quotient.subsingleton_iff.mp hsub)
  have hmem : c ∈ LinearMap.range (GradedModule.d (GradedModule.FD R n (-1)) q) := by
    have h := congrArg (fun S => (⟨c, hc⟩ : LinearMap.ker
      (GradedModule.d (GradedModule.FD R n (-1)) (q + 1))) ∈ S) ht
    exact h.mpr (Submodule.mem_top)
  obtain ⟨b, hb⟩ := hmem
  refine ⟨e q b, ?_⟩
  rw [← paired_c3_negative_cochain_d, hb]
  exact (e (q + 1)).apply_symm_apply z

#print axioms paired_c3_negative_native_exact

/-- The original native negative line has zero positive Cech cohomology.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1. -/
theorem paired_c3_negative_native_vanishing (hn : 0 < n) (q : ℕ) :
    Subsingleton ((pairedC3NegativeSectionPresheaf R n).HSucc
      (stdCoverPullback (𝟙 (Proj A))) q) := by
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro z
  exact paired_c3_negative_native_exact R n hn q z.val z.property

#print axioms paired_c3_negative_native_vanishing
end HodgeLean.Foundations.Program.G32Native
