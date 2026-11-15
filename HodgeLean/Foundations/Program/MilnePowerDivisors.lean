import HodgeLean.Foundations.Program.MilnePowerPolarization
import HodgeLean.Foundations.Program.MilneInvariantsDescent
import HodgeLean.Foundations.DivisorClassHodge

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program

theorem m2_power_fixed_iff_hodge (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (r : ℕ) (d : HQ (g3_power J r) 2) :
    (∀ u ∈ g32p_lefschetz J pol, exteriorPower.map 2 (m2_powerAction J r u)
      (HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf (g3_power J r)) d)) =
      HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf (g3_power J r)) d)) ↔
      d ∈ Hdg^1(g3_power J r; ℚ) := by
  let Y := g3_power J r
  letI := (torusCohomology_cupProductOf Y).finite
  let E := m2_powerFormQ J pol hη r
  let T := m2_formOperator E (polarizationVec (torusCohomology_cupProductOf Y) d)
  have hE := m2_powerForm_nondegenerate J pol hη r
  have hskew := m2_powerForm_grading_skew J pol hη hpos r
  have hfixed (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) (hu : u ∈ g32p_lefschetz J pol) :
      exteriorPower.map 2 (m2_powerAction J r u)
        (HodgeBlocks.complexifyWedge 2 (polarizationVec (torusCohomology_cupProductOf Y) d)) =
        HodgeBlocks.complexifyWedge 2 (polarizationVec (torusCohomology_cupProductOf Y) d) ↔
      m2_powerAction J r u ∘ₗ T.baseChange ℂ = T.baseChange ℂ ∘ₗ m2_powerAction J r u := by
    have hiso := m2_powerForm_preserved J pol hη r u hu
    have hs := (Module.End.isUnit_iff _).1
      (m2_isUnit_of_form_preserving (E.baseChange ℂ) hE _ hiso)
    rw [m2_form_fixed_iff_commutes (E.baseChange ℂ) hE _ _ hs.2 hiso,
      ← m2_formOperator_complexify E]
  constructor
  · intro h
    have hC : m2_hodgeGrading J ∈ g32p_lefschetz J pol :=
      m2_grading_mem_lefschetz J pol hη hpos
    have hc := (hfixed _ hC).1 (h _ hC)
    rw [m2_powerAction_grading] at hc
    apply (m2_hodge_iff_formOperator Y E hE hskew d).2
    exact (m2_hodgeEnd_iff_grading Y T).2 hc.symm
  · intro hd u hu
    have hT := (m2_hodge_iff_formOperator Y E hE hskew d).1 hd
    obtain ⟨φ, hφ⟩ := (p1r_mem_range_iff Y T).2 hT
    apply (hfixed u hu).2
    have hc := m2_powerAction_centralizer J pol hη r u hu
    have hh := (Subalgebra.mem_centralizer_iff ℂ).mp hc _ ⟨φ, rfl⟩
    change ((abelianEnd0Action Y φ).unop).baseChange ℂ ∘ₗ m2_powerAction J r u =
      m2_powerAction J r u ∘ₗ ((abelianEnd0Action Y φ).unop).baseChange ℂ at hh
    dsimp only at hφ
    rw [hφ] at hh
    exact hh.symm


theorem m2_power_rational_divisors (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r : ℕ) :
    (((g32p_invariants J pol r 2).restrictScalars ℚ).comap
      (TensorProduct.mk ℚ ℂ (HQ (g3_power J r) 2) 1)) =
      algebraicCycleClassSpan (g3_power J r) 1 := by
  ext d
  change (1 : ℂ) ⊗ₜ[ℚ] d ∈ g32p_invariants J pol r 2 ↔
    d ∈ algebraicCycleClassSpan (g3_power J r) 1
  refine (m2_rational_invariants_iff_power_fixed J pol r d).trans ?_
  refine (m2_power_fixed_iff_hodge J pol hη hpos r d).trans ?_
  exact ⟨fun hd => chowG_lefschetzOneOne_abelian (g3_power J r) hd,
    fun hd => dc1_divisorClass_le_hodge (g3_power J r) hd⟩


end HodgeLean.Foundations.Program
