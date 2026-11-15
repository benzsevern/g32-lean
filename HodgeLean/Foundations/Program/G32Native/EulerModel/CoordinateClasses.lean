import HodgeLean.Foundations.Program.G32Native.EulerModel.HyperplaneClass

/-! # Normalized classes of retained coordinate linear subspaces -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Each actual coordinate intersection on the specified model is smooth, integral,
has its expected coheight, and carries a normalized supported class. -/
theorem coordinate_intersection_class
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (T : Finset (Fin (k + 1))) (hT : T.card ≤ k) :
    let I := (s2e_s2b_intersectionIdeal k T).comap eQ.hom.left
    let QT := s2c_subscheme Q I
    let jT := s2c_subschemeι Q I
    ∃ (hI : IsIntegral QT.left),
      letI := hI
      Smooth QT.hom ∧
      Order.coheight (jT.left (genericPoint QT.left)) = T.card ∧
      ∃ c : s2e_supportedClass Q (s2e_componentCycle jT ℚ) T.card,
        a3b4_IsCycleClass Q.hom (s2e_componentCycle jT ℚ) T.card c := by
  let I := (s2e_s2b_intersectionIdeal k T).comap eQ.hom.left
  let QT := s2c_subscheme Q I
  let jT := s2c_subschemeι Q I
  obtain ⟨E₁⟩ := subscheme_comap_model eQ (s2e_s2b_intersectionIdeal k T)
  obtain ⟨E₂⟩ := s2e_coordinate_intersection_over k T hT
  let E := E₁ ≪≫ E₂
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k - T.card + 1)) (Spec ↧ℂ))
  letI : IsIntegral PP.left := IntersectionProductScaf_projective_integral (k - T.card)
  letI hI : IsIntegral QT.left := IsIntegral.of_isIso E.inv.left
  letI : Smooth PP.hom := IntersectionProductScaf_projective_smooth (k - T.card)
  letI hsm : Smooth QT.hom := by
    rw [← Over.w E.hom]
    change Smooth (E.hom.left ≫ PP.hom)
    infer_instance
  letI : IsClosedImmersion jT.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hdimQ := s2e_projective_model_dimension Q k eQ
  have hdimT := s2e_projective_model_dimension QT (k - T.card) E
  have hc : Order.coheight (jT.left (genericPoint QT.left)) = T.card :=
    s2e_immersion_generic_coheight_of_dimensions jT (k - T.card) T.card hdimT
      (by rw [hdimQ]; omega)
  refine ⟨hI, hsm, hc, ?_⟩
  apply a3b4a_cycleClass_exists_of_codimension
  intro x hx
  rw [s2e_componentCycle_support] at hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact hc.ge

#print axioms coordinate_intersection_class
/-- The prime ideal of an integral subscheme generic point is its actual defining ideal. -/
theorem subscheme_generic_primeIdeal
    (Q : Over (Spec ↧ℂ)) (I : Q.left.IdealSheafData)
    [IsIntegral I.subscheme] :
    ccm3_primeIdeal Q.left (I.subschemeι (genericPoint I.subscheme)) = I := by
  have hs : (⟨closure {I.subschemeι (genericPoint I.subscheme)}, isClosed_closure⟩ :
      Closeds Q.left) = I.support := by
    apply Closeds.ext
    letI : IsClosedImmersion (s2c_subschemeι Q I).left :=
      inferInstanceAs (IsClosedImmersion I.subschemeι)
    change closure {I.subschemeι (genericPoint I.subscheme)} = _
    have he : closure {I.subschemeι (genericPoint I.subscheme)} = Set.range I.subschemeι := by
      rw [← Set.image_singleton, I.subschemeι.isClosedEmbedding.closure_image_eq,
        genericPoint_closure, Set.image_univ]
    rw [he, Scheme.IdealSheafData.range_subschemeι]
  change Scheme.IdealSheafData.vanishingIdeal _ = I
  rw [hs, Scheme.IdealSheafData.vanishingIdeal_support]
  simpa only [Scheme.IdealSheafData.ker_subschemeι] using
    s2e_kernel_radical_of_reduced I.subschemeι

#print axioms subscheme_generic_primeIdeal
/-- The sum of actual coordinate intersection ideals cuts out the union of their coordinates. -/
theorem coordinate_intersection_ideal_union
    (k : ℕ) (T U : Finset (Fin (k + 1))) :
    s2e_s2b_intersectionIdeal k (T ∪ U) =
      s2e_s2b_intersectionIdeal k T ⊔ s2e_s2b_intersectionIdeal k U := by
  simp only [s2e_s2b_intersectionIdeal, Finset.mem_union, iSup_or, iSup_sup_eq]

#print axioms coordinate_intersection_ideal_union
/-- A smooth actual integral subscheme gives the same smooth reduced component. -/
theorem subscheme_generic_component_smooth
    (Q : Over (Spec ↧ℂ)) (I : Q.left.IdealSheafData)
    [IsIntegral I.subscheme] [Smooth (I.subschemeι ≫ Q.hom)] :
    Smooth (cycleComponentι Q.left (I.subschemeι (genericPoint I.subscheme)) ≫ Q.hom) := by
  change Smooth ((ccm3_primeIdeal Q.left (I.subschemeι (genericPoint I.subscheme))).subschemeι ≫ Q.hom)
  rw [subscheme_generic_primeIdeal]
  infer_instance

#print axioms subscheme_generic_component_smooth
/-- A smooth component has empty first ambient singular boundary. -/
theorem smooth_component_boundary_zero
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (p : Q.left) [Smooth (cycleComponentι Q.left p ≫ Q.hom)] :
    cycleComponentSingularAmbientClosedFiltration Q p 0 = ⊥ := by
  ext x
  simp [cycleComponentSingularAmbientClosedFiltration, cycleComponentSingularClosedFiltration,
    reducedSmoothClosedFiltration_zero, singularLocusClosed, Scheme.Hom.smoothLocus_eq_top]

#print axioms smooth_component_boundary_zero
/-- Equal defining ideals have the same actual generic point in the ambient scheme. -/
theorem subscheme_generic_point_congr
    (Q : Over (Spec ↧ℂ)) (I J : Q.left.IdealSheafData)
    [IsIntegral I.subscheme] [IsIntegral J.subscheme] (h : I = J) :
    I.subschemeι (genericPoint I.subscheme) = J.subschemeι (genericPoint J.subscheme) := by
  subst J
  rfl

#print axioms subscheme_generic_point_congr
end HodgeLean.Foundations.Program.G32Native.EulerModel
