import HodgeLean.Papers.G34AssemblyDefs

/-! # G34 Theorems A and B, assembly: proofs of the frozen statements -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

theorem g34a_remainingFields_aux (F : wtr_UniversalFamily 4 1) (P : g34h_PrymFamily)
    (h46 : g34s_Prop46 P) (Φ : g34b_BoundaryPeriodMap F P.fiber)
    (hpar : ∀ s, g34b_ParabolicPolarization (g34h_fiber_polarized P s))
    (spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q : wtr_Variety 4, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q)) :
    g34h_RemainingFields F P := by
  exact ⟨fun s _ => g34b_fiber_disc P.fiber (g34h_fiber_polarized P) hpar s,
    g34s_fiber_alg P h46, g34b_dominant F P.fiber Φ, spread, transport⟩

theorem g34a_theoremA_aux (F : wtr_UniversalFamily 4 1) (P : g34h_PrymFamily)
    (h46 : g34s_Prop46 P) (Φ : g34b_BoundaryPeriodMap F P.fiber)
    (hpar : ∀ s, g34b_ParabolicPolarization (g34h_fiber_polarized P s))
    (spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q : wtr_Variety 4, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A := by
  exact g34b_theoremA_of_boundary F P.fiber (g34h_fiber_polarized P) hpar Φ
    (g34s_fiber_alg P h46) spread transport A

theorem g34a_theoremA_of_premises_aux (B : g34a_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A := by
  exact g34a_theoremA_aux B.F B.P B.h46 B.Φ B.hpar B.spread B.transport A

theorem g34a_theoremB_of_premises_aux (B : g34a_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (hComp : ∀
      (W : letI := (finiteBetti_abelian A).finite 1
        HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
      (hW : letI := (finiteBetti_abelian A).finite 1; W.IsWeilType)
      (pol : HQ A 2)
      (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
      (_hRos : letI := (finiteBetti_abelian A).finite 1;
        IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J)
      (_hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
      (_hDim : TopologicalSpace.dim A.left = 6),
      (∀ (X : Over (Spec ↧ℂ)),
        [GrpObj X] → [IsCommMonObj X] → [IsIntegral X.left] →
        [Smooth X.hom] → [IsProjective X.hom] → G34TheoremAStatement X) →
      letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW) :
    G34TheoremBStatement A := by
  exact g34c_theoremB_of A (fun X _ _ _ _ _ => g34a_theoremA_of_premises_aux B X) hComp

theorem g34a_exists_member_fiber_aux (B : g34a_premises) :
    ∃ s, wtr_IsMember 4 1 (B.P.fiber s) := by
  exact ⟨B.P.base, ⟨g34h_fiber_polarized B.P B.P.base,
    g34b_fiber_disc B.P.fiber (g34h_fiber_polarized B.P) B.hpar B.P.base⟩⟩

end HodgeLean.Papers
