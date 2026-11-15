import HodgeLean.Foundations.Program.G32Native.SupportedSelfRestriction
import HodgeLean.Foundations.Program.G32Native.TopHyperplanePower
import HodgeLean.Foundations.Program.G32Native.PairedConormalModelComparison

/-! # Euler class of an elementary projective conormal modification -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The elementary conormal sequence gives the signed top normal Euler class.
The analytic Euler is defined by the actual dual conormal and its Thom class.
No supported ambient class is a parameter of this comparison.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.6, pp. 16–17;
Fulton, Intersection Theory, §3.2, Whitney formula and dual bundles;
Bott–Tu, Differential Forms in Algebraic Topology, §20, top Chern and Euler. -/
theorem paired_conormal_analytic_euler_aux
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (V : Scheme) (j : Q.left ⟶ V) [IsClosedImmersion j]
    (sV : V ⟶ Spec ↧ℂ) (hj : j ≫ sV = Q.hom)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) sV]
    [CompactSpace (ComplexPoint Q)] [T2Space (ComplexPoint Q)]
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
    letI := hH
    i1_normalBundleEuler j k sV hj = (-1 : ℚ) ^ k •
      s2e_hyperplanePower (TopCat.of (ComplexPoint Q))
        (s2e_classToAbsolute Q (s2e_componentCycle
          (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH) k := by
  classical
  letI := hH
  have hbound : (Finset.univ.erase (0 : Fin (k + 1))).card ≤ k := by simp
  obtain ⟨hpt, _, _, _⟩ := EulerModel.coordinate_intersection_class Q k eQ
    (Finset.univ.erase 0) hbound
  letI := hpt
  exact (paired_conormal_model_comparison_aux Q k hk eQ V j sV hj M E f g hfg hseq).trans
    (EulerModel.normalKernelGlobalThomClass_hyperplane_sign Q k hk eQ cH hcH)

/-- The signed coefficient survives application of the same numerical functional. -/
theorem paired_euler_numerical_of_comparison
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (k : ℕ)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (euler Htop : Cohomology ℚ (TopCat.of (ComplexPoint Q)) (2 * k))
    (hself : s2e_normalEuler ι k c = euler)
    (hchern : euler = (-1 : ℚ) ^ k • Htop)
    (degree : Cohomology ℚ (TopCat.of (ComplexPoint Q)) (2 * k) →ₗ[ℚ] ℚ)
    (hH : degree Htop ≠ 0) : degree (s2e_normalEuler ι k c) ≠ 0 := by
  rw [hself, hchern, map_smul, smul_eq_mul]
  exact mul_ne_zero (pow_ne_zero k (by norm_num)) hH

#print axioms paired_conormal_analytic_euler_aux
#print axioms paired_euler_numerical_of_comparison

end HodgeLean.Foundations.Program.G32Native
