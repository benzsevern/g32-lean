import HodgeLean.Foundations.Program.MilneDivisorsDefs
import HodgeLean.Foundations.Program.MilneDivisorsLinear

noncomputable section
set_option maxHeartbeats 200000
set_option Elab.async false
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Module
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

theorem m2_ratio_complexify {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω) (d : ⋀[ℚ]^2 V) :
    (contract d ∘ₗ (contractEquiv hω).symm.toLinearMap).baseChange ℂ =
      contract (HodgeBlocks.complexifyWedge 2 d) ∘ₗ
        (contractEquiv (pol1_complexify_nondegenerate hω)).symm.toLinearMap := by
  apply ((Module.finBasis ℚ V).baseChange ℂ).ext
  intro i
  simp only [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
  obtain ⟨φ, hφ⟩ := hω.2 (Module.finBasis ℚ V i)
  rw [← hφ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    contractEquiv_symm_contract, ← pol1_contract_complexify ω φ,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, contractEquiv_symm_contract,
    pol1_contract_complexify]

theorem m2_hodgeEnd_iff_grading (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (T : Module.End ℚ (HQ J 1)) :
    let M := cohomologyHodgeStructure (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) 1
    T ∈ hodgeEndH1 J ↔ T.baseChange ℂ ∘ₗ gradingOperator M.H M.isInternal =
      gradingOperator M.H M.isInternal ∘ₗ T.baseChange ℂ := by
  dsimp only
  let M := cohomologyHodgeStructure (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
    (hodgeDecomposition_of_abelian J) 1
  let C := gradingOperator M.H M.isInternal
  have he10 : M.H (1, 0) = complexHolomorphicH1 J := by
    change cohomologyHodgePiece J 1 (1, 0) = _
    rw [spec_g4_cohomologyHodgePiece_one_eq]
    simp [latticeHodgePieces]
  have he01 : M.H (0, 1) = complexAntiholomorphicH1 J := by
    change cohomologyHodgePiece J 1 (0, 1) = _
    rw [spec_g4_cohomologyHodgePiece_one_eq]
    simp [latticeHodgePieces]
  have h10 : ∀ x ∈ complexHolomorphicH1 J, C x = Complex.I • x := by
    intro x hx
    have h := gradingOperator_apply_of_mem M.H M.isInternal (he10 ▸ hx)
    simpa only [Int.cast_one, Int.cast_zero, sub_zero, mul_one] using h
  have h01 : ∀ x ∈ complexAntiholomorphicH1 J, C x = -Complex.I • x := by
    intro x hx
    have h := gradingOperator_apply_of_mem M.H M.isInternal (he01 ▸ hx)
    simpa only [Int.cast_zero, Int.cast_one, zero_sub, mul_neg, mul_one] using h
  constructor
  · intro hT
    exact p1r_comp_gradingOperator M.H M.isInternal _
      (p1r_map_cohomologyHodgePiece_le J hT)
  · intro hc
    have hi : (Complex.I : ℂ) ≠ -Complex.I := by
      intro h
      have hh := congrArg Complex.im h
      norm_num at hh
    have ep := m2_eigenspace_of_split (complexHolomorphicH1 J) (complexAntiholomorphicH1 J)
      C Complex.I (-Complex.I) hi (spec_complexH1_split J).1 h10 h01
    have eq := m2_eigenspace_of_split (complexAntiholomorphicH1 J) (complexHolomorphicH1 J)
      C (-Complex.I) Complex.I hi.symm
      (by rw [sup_comm]; exact (spec_complexH1_split J).1) h01 h10
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      rw [← ep]
      apply Module.End.mem_eigenspace_iff.mpr
      calc
        C (T.baseChange ℂ x) = T.baseChange ℂ (C x) := (LinearMap.congr_fun hc x).symm
        _ = Complex.I • T.baseChange ℂ x := by rw [h10 _ hx, map_smul]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← eq]
      apply Module.End.mem_eigenspace_iff.mpr
      calc
        C (T.baseChange ℂ x) = T.baseChange ℂ (C x) := (LinearMap.congr_fun hc x).symm
        _ = -Complex.I • T.baseChange ℂ x := by rw [h01 _ hx, map_smul]

theorem m2_hodge_iff_operator (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (d : HQ J 2) :
    d ∈ Hdg^1(J; ℚ) ↔ m2_operator J pol hη d ∈ hodgeEndH1 J := by
  letI := (torusCohomology_cupProductOf J).finite
  let M := cohomologyHodgeStructure (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
    (hodgeDecomposition_of_abelian J) 1
  let C := gradingOperator M.H M.isInternal
  have hclass (a : HQ J 2) : a ∈ Hdg^1(J; ℚ) ↔
      InvariantsExterior.exteriorDer 2 C (HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) a)) = 0 := by
    refine (pol1_hodge_iff_polarizationVec_type J (finiteBetti_abelian J)
      (spec_bettiDeRhamIso_abelian J) a).trans ?_
    rw [pol1_exterior_type_iff_grading_zero,
      HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul]
    rfl
  have hp := (hclass pol).mp (p1_mem_hdg J ((p1_isPolarization_iff J pol).2 ⟨hη, hpos⟩))
  refine (hclass d).trans ?_
  rw [m2_derivation_fixed_iff_commutes (pol1_complexify_nondegenerate hη) _ C hp,
    ← m2_ratio_complexify hη]
  change C ∘ₗ (m2_operator J pol hη d).baseChange ℂ =
      (m2_operator J pol hη d).baseChange ℂ ∘ₗ C ↔ _
  rw [eq_comm]
  exact (m2_hodgeEnd_iff_grading J (m2_operator J pol hη d)).symm

end HodgeLean.Foundations.Program
