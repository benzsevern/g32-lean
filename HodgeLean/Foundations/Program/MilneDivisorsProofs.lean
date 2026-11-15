import HodgeLean.Foundations.Program.MilnePowerDivisors
import HodgeLean.Foundations.Program.MilneInvariantsDescent
import HodgeLean.Foundations.Program.MilneDivisorsDefs
import HodgeLean.Foundations.Program.MilneDivisorsGroup
import HodgeLean.Foundations.DivisorClassHodge

/-! # Auxiliary statements for Milne M2 -/

noncomputable section
set_option maxHeartbeats 200000
set_option Elab.async false
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

theorem m2_operator_injective_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) :
    Function.Injective (m2_operator J pol hη) := by
  letI := (torusCohomology_cupProductOf J).finite
  exact m2_contract_ratio_injective ((torusCohomology_cupProductOf J).cupWedgeEquiv 2).symm hη

theorem m2_operator_selfadjoint_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (d : HQ J 2) :
    p1_adjoint (polarizationVec (torusCohomology_cupProductOf J) pol) hη
      (m2_operator J pol hη d) = m2_operator J pol hη d := by
  exact m2_contract_ratio_selfadjoint hη (polarizationVec (torusCohomology_cupProductOf J) d)

theorem m2_divisor_rosati_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (d : HQ J 2) :
    let hP : p1_IsPolarization J pol := (p1_isPolarization_iff J pol).2 ⟨hη, hpos⟩
    d ∈ algebraicCycleClassSpan J 1 ↔
      ∃ φ : AbelianEnd0 J, (abelianEnd0Action J φ).unop = m2_operator J pol hη d ∧
        p1_rosati J pol (p1_isNondegenerate J hP) (p1_adjoint_mem_range J hP) φ = φ := by
  dsimp only
  have hd : d ∈ algebraicCycleClassSpan J 1 ↔ d ∈ Hdg^1(J; ℚ) :=
    ⟨fun h => dc1_divisorClass_le_hodge J h,
      fun h => chowG_lefschetzOneOne_abelian J h⟩
  refine hd.trans ((m2_hodge_iff_operator J pol hη hpos d).trans ?_)
  constructor
  · intro hT
    obtain ⟨φ, hφ⟩ := (p1r_mem_range_iff J _).2 hT
    change (abelianEnd0Action J φ).unop = m2_operator J pol hη d at hφ
    refine ⟨φ, hφ, ?_⟩
    apply p1r_unop_abelianEnd0Action_injective J
    dsimp only
    rw [p1r_abelianEnd0Action_rosati, hφ]
    exact m2_operator_selfadjoint_aux J pol hη d
  · rintro ⟨φ, hφ, -⟩
    exact (p1r_mem_range_iff J _).1 ⟨φ, hφ⟩

theorem m2_fixed_endomorphism_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (d : HQ J 2) :
    (∀ u ∈ g32p_lefschetz J pol,
      exteriorPower.map 2 u (HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) d)) =
      HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) d)) ↔
      ∃ φ : AbelianEnd0 J, (abelianEnd0Action J φ).unop = m2_operator J pol hη d := by
  constructor
  · intro h
    apply (p1r_mem_range_iff J _).2
    apply (m2_hodgeEnd_iff_grading J _).2
    have hC := m2_grading_mem_lefschetz J pol hη hpos
    exact ((m2_fixed_iff_operator_commutes J pol hη d _ hC).1 (h _ hC)).symm
  · rintro ⟨φ, hφ⟩ u hu
    apply (m2_fixed_iff_operator_commutes J pol hη d u hu).2
    have hc := ((m0_mem_lefschetz_iff J pol hη u).1 hu).2.1
    have hh := (Subalgebra.mem_centralizer_iff ℂ).mp hc _ ⟨φ, rfl⟩
    change ((abelianEnd0Action J φ).unop).baseChange ℂ ∘ₗ u =
      u ∘ₗ ((abelianEnd0Action J φ).unop).baseChange ℂ at hh
    rw [hφ] at hh
    exact hh.symm

theorem m2_divisor_fixed_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (d : HQ J 2) :
    d ∈ algebraicCycleClassSpan J 1 ↔
    ∀ u ∈ g32p_lefschetz J pol,
      exteriorPower.map 2 u (HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) d)) =
      HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) d) := by
  refine (m2_divisor_rosati_aux J pol hη hpos d).trans ?_
  refine Iff.trans ?_ (m2_fixed_endomorphism_aux J pol hη hpos d).symm
  constructor
  · rintro ⟨φ, hφ, -⟩
    exact ⟨φ, hφ⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, hφ, ?_⟩
    apply p1r_unop_abelianEnd0Action_injective J
    dsimp only
    rw [p1r_abelianEnd0Action_rosati, hφ]
    exact m2_operator_selfadjoint_aux J pol hη d

theorem m2_invariants_baseChange_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (r n : ℕ) :
    g32p_invariants J pol r n =
      (((g32p_invariants J pol r n).restrictScalars ℚ).comap
        (TensorProduct.mk ℚ ℂ (HQ (g3_power J r) n) 1)).baseChange ℂ := by
  exact m2_invariants_descend J pol hη r n

theorem m2_power_divisors_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (r : ℕ) :
    g32p_invariants J pol r 2 =
      (algebraicCycleClassSpan (g3_power J r) 1).baseChange ℂ := by
  exact (m2_invariants_descend J pol hη r 2).trans
    (congrArg (fun p : Submodule ℚ (HQ (g3_power J r) 2) => p.baseChange ℂ)
      (m2_power_rational_divisors J pol hη hpos r))

end HodgeLean.Foundations.Program
