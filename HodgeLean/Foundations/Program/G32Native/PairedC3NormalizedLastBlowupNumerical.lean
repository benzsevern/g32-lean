import HodgeLean.Foundations.Program.SchoenCycleS3Initial
import HodgeLean.Foundations.Program.G32Native.PairedResidualSliceFrames
import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedNormalizedResidualNumerical
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

/-- The last-transform conormal and the residual ruling supply the numerical
functional on the same selected component. All geometric inputs are explicit.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.6 and Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.7.13 and II.8.
The hyperplane identification retains the projective coordinate change.
The penultimate frame, natural comparison and marked ruling are inputs. -/
theorem jointSelected_numerical_of_normalized_last_blowup
    (hNormalField : by_elab return (← Lean.getConstInfo
      ``HodgeLean.Foundations.BundleThom.joint_projective_selfRestriction_eq_bundleEuler).type.bindingDomain!)
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S)
    (P : G32JointOrientedPositiveData R)
    (Jres : (P.T.B (Fin.last R.r)).left.IdealSheafData)
    (hnot : ¬ (P.C.ℓ.left.ker.support : Set (P.T.B (Fin.last R.r)).left) ⊆ Jres.support)
    {Q₀ X : Scheme.{0}} (i₀ : Q₀ ⟶ X)
    (σ : (P.T.B (Fin.last R.r)).left ⟶ X)
    (p : (G32Native.residualUnion P.C.ℓ Jres).left ⟶ Q₀)
    (sq : CategoryTheory.IsPullback p
      (G32Native.residualUnionι P.C.ℓ Jres).left i₀ σ)
    [IsIso (Conormal.comparisonMap i₀
      (G32Native.residualUnionι P.C.ℓ Jres).left σ p sq.w)]
    (e₀ : s2c_conormal i₀ ≅
      (SheafOfModules.free (R := Q₀.ringCatSheaf) (Fin R.P.k) : Q₀.Modules))
    (C : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 C.hom]
    (c₀ : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C) [IsClosedImmersion c₀.left]
    (g : G32Native.residualComponent (V := P.T.B (Fin.last R.r)) Jres ⟶ C)
    [Smooth g.left]
    (sq₂ : CategoryTheory.IsPullback
      (G32Native.residualIntersection P.C.ℓ Jres).hom
      (G32Native.residualIntersectionSecond P.C.ℓ Jres).left c₀.left g.left)
    (I : (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)).IdealSheafData)
    (n : Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ)) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ)))
    (hI : I.comap n.hom.left = s2e_hyperplaneIdeal R.P.k)
    (e : (G32Native.residualIntersection P.C.ℓ Jres).left ≅ I.subscheme)
    (he : e.hom ≫ I.subschemeι =
      (G32Native.residualIntersectionFirst P.C.ℓ Jres).left)
    :
    ∃ degree : Cohomology ℚ (TopCat.of (ComplexPoint P.C.Q)) (2 * R.P.k) →ₗ[ℚ] ℚ,
      degree (s2e_normalEuler P.C.ι R.P.k P.c) ≠ 0 := by
  letI := P.C.residue.curve
  let γ : g3_power R.Z (2 * R.P.k) ⟶ R.B₀ :=
    eqToHom (congrArg (g3_power R.Z) R.hselected.symm) ≫ R.γ
  letI : IsFinite γ.left := by
    dsimp only [γ, Over.comp_left]
    infer_instance
  have hsurj : Function.Surjective (Point.map γ) := by
    obtain ⟨_, h, _⟩ := s2e_symmetric_quotient_reindex R.Z R.B₀
      (R.h + 1) (2 * R.P.k) R.hselected.symm R.γ R.hγinv R.hγsurj R.hγ
    exact h
  have hframes := G32Native.paired_retained_slice_conormal_frames
    R.Z R.B₀ R.P.k R.r γ hsurj P.T.B P.T.e₀ P.T.b P.T.D
      P.T.hcartier P.T.hblowup (Fin.last R.r) P.C.ℓ
  exact jointSelected_numerical_of_normalized_residual hNormalField R P I n hI
    (G32Native.pairedLastBlowupPresentation P.C.ℓ R.P.k _ _ Jres hnot
      i₀ σ p sq e₀ C c₀ g sq₂ e he hframes)

#print axioms jointSelected_numerical_of_normalized_last_blowup
end ResidueSelected
end HodgeLean.Foundations.Program
