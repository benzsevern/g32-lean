import HodgeLean.Foundations.Program.G32Native.PairedC3RetainedLastBlowupNumerical
import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupLciFrames
import HodgeLean.Foundations.Program.SchoenCycleS3Initial
import HodgeLean.Foundations.Program.G32Native.PairedResidualSliceFrames
import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedResidualNumerical
import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupPresentation
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program
namespace ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24
attribute [local instance] G32JointComponent.h_T20_slice_immersion
attribute [local instance] G32JointComponent.hQ

/-- Local lci frames of the actual total transform replace the invertibility
input in the last-blowup numerical caller, with all selected data retained.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.8.
The residue index is retained; the coordinate swap supplies its normalization. -/
theorem jointSelected_numerical_of_retained_lci_frames
    (hNormalField : by_elab return (← Lean.getConstInfo
      ``HodgeLean.Foundations.BundleThom.joint_projective_selfRestriction_eq_bundleEuler).type.bindingDomain!)
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S)
    (P : G32JointOrientedPositiveData R)
    (Jres : (P.T.B (Fin.last R.r)).left.IdealSheafData)
    (hnot : ¬ (P.C.ℓ.left.ker.support : Set (P.T.B (Fin.last R.r)).left) ⊆ Jres.support)
    {Q₀ X : Scheme.{0}} (i₀ : Q₀ ⟶ X) [IsClosedImmersion i₀]
    (σ : (P.T.B (Fin.last R.r)).left ⟶ X)
    (p : (G32Native.residualUnion P.C.ℓ Jres).left ⟶ Q₀)
    (sq : CategoryTheory.IsPullback p
      (G32Native.residualUnionι P.C.ℓ Jres).left i₀ σ)
    (hT : ∀ x : (G32Native.residualUnion P.C.ℓ Jres).left,
      ∃ (U : (G32Native.residualUnion P.C.ℓ Jres).left.Opens),
        x ∈ U ∧ IsAffine U.toScheme ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj
          (s2c_conormal (G32Native.residualUnionι P.C.ℓ Jres).left) ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin R.P.k) : U.toScheme.Modules)))
    (e₀ : s2c_conormal i₀ ≅
      (SheafOfModules.free (R := Q₀.ringCatSheaf) (Fin R.P.k) : Q₀.Modules))
    (C : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 C.hom]
    (c₀ : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C) [IsClosedImmersion c₀.left]
    (g : G32Native.residualComponent (V := P.T.B (Fin.last R.r)) Jres ⟶ C)
    [Smooth g.left]
    (sq₂ : CategoryTheory.IsPullback
      (G32Native.residualIntersection P.C.ℓ Jres).hom
      (G32Native.residualIntersectionSecond P.C.ℓ Jres).left c₀.left g.left)
    (j : Fin (R.P.k + 1))
    (hJ : Jres.comap P.C.ℓ.left = s2e_s2b_residueIdeal R.P.k j)
    :
    ∃ degree : Cohomology ℚ (TopCat.of (ComplexPoint P.C.Q)) (2 * R.P.k) →ₗ[ℚ] ℚ,
      degree (s2e_normalEuler P.C.ι R.P.k P.c) ≠ 0 := by
  haveI := G32Native.paired_last_lci_comparison_of_frames i₀
    (G32Native.residualUnionι P.C.ℓ Jres).left σ p sq R.P.k e₀ hT
  exact jointSelected_numerical_of_retained_last_blowup hNormalField R P Jres hnot
    i₀ σ p sq e₀ C c₀ g sq₂ j hJ

#print axioms jointSelected_numerical_of_retained_lci_frames
end ResidueSelected
end HodgeLean.Foundations.Program
