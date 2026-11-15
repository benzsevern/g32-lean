import HodgeLean.Foundations.Program.MilneDivisorsHodge

noncomputable section
set_option maxHeartbeats 200000
set_option Elab.async false
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Module
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

theorem m2_grading_mem_lefschetz (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) :
    let M := cohomologyHodgeStructure (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) 1
    gradingOperator M.H M.isInternal ∈ g32p_lefschetz J pol := by
  letI := (torusCohomology_cupProductOf J).finite
  let M := cohomologyHodgeStructure (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
    (hodgeDecomposition_of_abelian J) 1
  let C := gradingOperator M.H M.isInternal
  have hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → M.H pq = ⊥ := by
    intro pq h10 h01
    exact cohomologyHodgePiece_one_eq_bot J pq h10 h01
  have hc2 (x : ℂ ⊗[ℚ] HQ J 1) : C (C x) = -x :=
    LinearMap.congr_fun (spec_eqw_gradingOperator_mul_self (H := M.H) (hH := M.isInternal) hsupp) x
  have hu : IsUnit C := by
    refine ⟨⟨C, -C, ?_, ?_⟩, rfl⟩
    · apply LinearMap.ext
      intro x
      change C (-C x) = x
      rw [map_neg, hc2, neg_neg]
    · apply LinearMap.ext
      intro x
      change -C (C x) = x
      rw [hc2, neg_neg]
  have hc : C ∈ m0_endCentralizer J := by
    rw [m0_endCentralizer, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨φ, rfl⟩
    exact p1r_comp_gradingOperator M.H M.isInternal _
      (p1r_map_cohomologyHodgePiece_le J (spec_g4_abelianEnd0Action_mem_hodgeEndH1 J φ))
  have hclass := (pol1_hodge_iff_polarizationVec_type J (finiteBetti_abelian J)
    (spec_bettiDeRhamIso_abelian J) pol).mp
    (p1_mem_hdg J ((p1_isPolarization_iff J pol).2 ⟨hη, hpos⟩))
  rw [pol1_exterior_type_iff_grading_zero,
    HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul] at hclass
  have hskew := (pol1_exteriorDer_eq_zero_iff_dualForm_skew
    (pol1_complexify_nondegenerate hη) C).mp hclass
  have hf : ∀ x y, m0_form J pol hη (C x) (C y) = m0_form J pol hη x y := by
    intro x y
    simp only [m0_form, polarizationForm, pol1_dualForm_complexify]
    rw [hskew, hc2, map_neg, neg_neg]
  exact (m0_mem_lefschetz_iff J pol hη C).2 ⟨hu, hc, hf⟩

theorem m2_fixed_iff_operator_commutes (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (d : HQ J 2) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1))
    (hu : u ∈ g32p_lefschetz J pol) :
    exteriorPower.map 2 u (HodgeBlocks.complexifyWedge 2
      (polarizationVec (torusCohomology_cupProductOf J) d)) =
      HodgeBlocks.complexifyWedge 2 (polarizationVec (torusCohomology_cupProductOf J) d) ↔
    u ∘ₗ (m2_operator J pol hη d).baseChange ℂ =
      (m2_operator J pol hη d).baseChange ℂ ∘ₗ u := by
  letI := (torusCohomology_cupProductOf J).finite
  rw [m2_bivector_fixed_iff_commutes (pol1_complexify_nondegenerate hη) _ u hu.1 hu.2.2,
    ← m2_ratio_complexify hη]
  rfl

end HodgeLean.Foundations.Program
