import HodgeLean.Foundations.Program.G32Native.EulerModel.HyperplaneClass
import HodgeLean.Foundations.Program.G32Native.EulerModel.HyperplaneComplement
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalizedClass

/-! # Degree two for the specified normalized projective hyperplane -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified hyperplane component has exact coheight one. -/
theorem hyperplane_generic_coheight
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)).left] :
    Order.coheight
      ((s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)).left
        (genericPoint (s2c_subscheme Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)).left)) = 1 := by
  let I := (s2e_hyperplaneIdeal k).comap eQ.hom.left
  let QH := s2c_subscheme Q I
  let jH := s2c_subschemeι Q I
  obtain ⟨E⟩ := coordinate_hyperplane_model eQ hk
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ))
  letI : Smooth PP.hom := IntersectionProductScaf_projective_smooth (k - 1)
  letI : Smooth QH.hom := by
    rw [← Over.w E.hom]
    change Smooth (E.hom.left ≫ PP.hom)
    infer_instance
  letI : IsClosedImmersion jH.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hQ := s2e_projective_model_dimension Q k eQ
  have hH := s2e_projective_model_dimension QH (k - 1) E
  exact s2e_immersion_generic_coheight_of_dimensions jH (k - 1) 1 hH (by rw [hQ]; omega)

#print axioms hyperplane_generic_coheight
/-- The supplied normalized hyperplane representative has nonzero absolute class. -/
theorem normalized_hyperplane_class_ne_zero
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)).left]
    (cH : s2e_supportedClass Q
      (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1)
    (hcH : a3b4_IsCycleClass Q.hom
      (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH) :
    s2e_classToAbsolute Q
      (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH ≠ 0 := by
  have hne := normalized_single_prime_class_ne_zero Q _ _ 1
    (s2e_componentCycle_support _) (hyperplane_generic_coheight Q k hk eQ) cH hcH
  intro hzero
  apply hne
  apply (model_hyperplane_classToAbsolute_bijective eQ 1 (by omega)).1
  simpa only [map_zero] using hzero

#print axioms normalized_hyperplane_class_ne_zero
/-- The supplied normalized hyperplane class spans the actual degree-two cohomology. -/
theorem normalized_hyperplane_class_spans
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)).left]
    (cH : s2e_supportedClass Q
      (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1)
    (hcH : a3b4_IsCycleClass Q.hom
      (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH)
    (v : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint Q)) 2) :
    ∃ r : ℚ, v = r • s2e_classToAbsolute Q
      (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH := by
  obtain ⟨w, hw⟩ := (model_hyperplane_classToAbsolute_bijective eQ 1 (by omega)).2 v
  obtain ⟨r, hr⟩ := normalized_single_prime_class_spans Q _ _ 1
    (s2e_componentCycle_support _) (hyperplane_generic_coheight Q k hk eQ) cH hcH w
  refine ⟨r, ?_⟩
  rw [← hw, hr, map_smul]

#print axioms normalized_hyperplane_class_spans
/-- The normalized hyperplane top power on the projective line is nonzero. -/
theorem normalized_hyperplane_top_ne_zero_dimension_one
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (1 + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q ((s2e_hyperplaneIdeal 1).comap eQ.hom.left)).left]
    (cH : s2e_supportedClass Q
      (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal 1).comap eQ.hom.left)) ℚ) 1)
    (hcH : a3b4_IsCycleClass Q.hom
      (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal 1).comap eQ.hom.left)) ℚ) 1 cH) :
    s2e_hyperplanePower (TopCat.of (ComplexPoint Q))
      (s2e_classToAbsolute Q
        (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal 1).comap eQ.hom.left)) ℚ) 1 cH) 1 ≠ 0 := by
  change HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint Q))
    (Nat.add_zero 2) _ (HodgeLean.Foundations.Singular.unit _) ≠ 0
  rw [HodgeLean.Foundations.Singular.cup_one]
  exact normalized_hyperplane_class_ne_zero Q 1 (by omega) eQ cH hcH

#print axioms normalized_hyperplane_top_ne_zero_dimension_one
end HodgeLean.Foundations.Program.G32Native.EulerModel
