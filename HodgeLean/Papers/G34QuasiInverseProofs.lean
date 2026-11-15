import HodgeLean.Papers.G34QuasiInverseDefs
import HodgeLean.Papers.G34Narrow
import HodgeLean.Papers.QuasiInverse

/-! # G34 quasi-inverse premises: proofs of the frozen statements -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers

set_option maxRecDepth 2000 in
theorem g34q_reverse_of_premise_aux (h : g34q_premise 4) :
    ∀ P Q, wtr_IsMember 4 1 P → wtr_IsMember 4 1 Q →
      wtr_KIsog P Q → wtr_KIsog Q P := by
  intro P Q _ _ hf
  obtain ⟨f, f_mon, f_isogeny, f_K, c, c_pos, f_pol⟩ := hf
  obtain ⟨w⟩ := h P Q f f_mon f_isogeny
  exact qinv_wtr_KIsog_reverse_of_witness (n := 4) P Q f f_mon f_isogeny
    f_K c c_pos f_pol w

theorem g34q_theoremA_of_premises_aux (B : g34q_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A := by
  let C : g34n_premises :=
    { F := B.F
      P := B.P
      h46 := B.h46
      Φ := B.Φ
      hpar := B.hpar
      spread := B.spread
      reverse := g34q_reverse_of_premise_aux B.qinv }
  exact g34n_theoremA_of_premises C A

theorem g34q_theoremB_of_premises_aux (B : g34q_premises) (A : Over (Spec ↧ℂ))
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
  let C : g34n_premises :=
    { F := B.F
      P := B.P
      h46 := B.h46
      Φ := B.Φ
      hpar := B.hpar
      spread := B.spread
      reverse := g34q_reverse_of_premise_aux B.qinv }
  exact g34n_theoremB_of_premises C A hComp

end HodgeLean.Papers
