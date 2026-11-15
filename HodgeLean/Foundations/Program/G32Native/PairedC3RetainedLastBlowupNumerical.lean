import HodgeLean.Foundations.Program.G32Native.PairedC3NormalizedLastBlowupNumerical
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateNormalization
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
The stored residue index selects the hyperplane, and the coordinate
exchange supplies its normalization. The geometric inputs remain explicit. -/
theorem jointSelected_numerical_of_retained_last_blowup
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
    (j : Fin (R.P.k + 1))
    (hJ : Jres.comap P.C.ℓ.left = s2e_s2b_residueIdeal R.P.k j)
    :
    ∃ degree : Cohomology ℚ (TopCat.of (ComplexPoint P.C.Q)) (2 * R.P.k) →ₗ[ℚ] ℚ,
      degree (s2e_normalEuler P.C.ι R.P.k P.c) ≠ 0 := by
  obtain ⟨e, he⟩ := (G32Native.residual_intersection_subscheme_iff
    P.C.ℓ Jres (s2e_s2b_residueIdeal R.P.k j)).mpr hJ
  exact jointSelected_numerical_of_normalized_last_blowup hNormalField R P
    Jres hnot i₀ σ p sq e₀ C c₀ g sq₂
    (s2e_s2b_residueIdeal R.P.k j)
    (s2e_linearProjectiveOverIso (G32Native.pairedC3CoordinateSwap R.P.k j)).symm
    (G32Native.pairedC3_coordinate_swap_inverse_hyperplane R.P.k j) e he

#print axioms jointSelected_numerical_of_retained_last_blowup
end ResidueSelected
end HodgeLean.Foundations.Program
