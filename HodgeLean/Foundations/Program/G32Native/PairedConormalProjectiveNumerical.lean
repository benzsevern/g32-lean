import HodgeLean.Foundations.Program.G32Native.PairedConormalEuler
import HodgeLean.Foundations.Program.G32Native.JointProjectiveSelfRestriction
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Numerical self-intersection using the projective normal-field input -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular Bundle TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The elementary conormal sequence and the projective normal-field input
supply numerical self-intersection on the supplied normalized component.
The normal-field argument has exactly the first argument type of
`joint_projective_selfRestriction_eq_bundleEuler`.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.6;
Fulton, Intersection Theory, Corollary 6.3 and Example 6.1.4. -/
theorem paired_conormal_projective_numerical
    (hNormalField : by_elab return (← Lean.getConstInfo
      ``HodgeLean.Foundations.BundleThom.joint_projective_selfRestriction_eq_bundleEuler).type.bindingDomain!)
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [IsProjective W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c)
    (V : Scheme) (v : V ⟶ W.left) [IsOpenImmersion v]
    (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)]
    [CompactSpace (ComplexPoint Q)] [T2Space (ComplexPoint Q)]
    (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (hH : IsIntegral (s2c_subscheme Q
      ((s2e_hyperplaneIdeal k).comap eQ.hom.left)).left)
    (cH : letI := hH
      s2e_supportedClass Q (s2e_componentCycle
        (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1)
    (hcH : letI := hH
      a3b4_IsCycleClass Q.hom (s2e_componentCycle
        (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH)
    (M : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules)
    (E : s2c_conormal j ≅ (Scheme.Modules.pullback eQ.hom.left).obj M)
    (f : (SheafOfModules.free
      (R := (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).ringCatSheaf) (Fin k) :
        (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules) ⟶ M)
    (g : M ⟶ (Scheme.Modules.pushforward
      (s2c_subschemeι (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
        (s2e_hyperplaneIdeal k)).left).obj
      (SheafOfModules.unit (s2c_subscheme
        (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
        (s2e_hyperplaneIdeal k)).left.ringCatSheaf))
    (hfg : f ≫ g = 0) (hseq : (ShortComplex.mk f g hfg).ShortExact) :
    ∃ degree : Cohomology ℚ (TopCat.of (ComplexPoint Q)) (2 * k) →ₗ[ℚ] ℚ,
      degree (s2e_normalEuler ι k c) ≠ 0 := by
  letI := hH
  have hself := joint_projective_selfRestriction_eq_bundleEuler
    hNormalField ι k c hc V v j hj
  have hchern := paired_conormal_analytic_euler_aux Q k hk eQ V j
    (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj)) hH cH hcH M E f g hfg hseq
  have htop := normalized_hyperplane_top_ne_zero Q k hk eQ hH cH hcH
  obtain ⟨degree, hdegree⟩ := Module.Projective.exists_dual_ne_zero ℚ htop
  exact ⟨degree, paired_euler_numerical_of_comparison ι k c _ _
    hself hchern degree hdegree⟩

#print axioms paired_conormal_projective_numerical

end HodgeLean.Foundations.Program.G32Native
