import HodgeLean.Papers.PapersArithmetic
import HodgeLean.Papers.SkeletonG34Defs

set_option maxHeartbeats 400000

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open HodgeLean.Adapters ComplexConjugate

namespace HodgeLean.Papers

theorem g34c_split_class_aux
    (t : ℚ) (ht : t < 0) :
    ∃ m : ℕ, 0 < m ∧ SameNormClass 3 m ((-1 : ℚ) / t) ∧
      SameNormClass 3 (t * (-m : ℚ)) 1 := by
  obtain ⟨m, hmpos, hm⟩ := papers_positive_class_nat_rep 3 ((-1 : ℚ) / t)
    (div_pos_of_neg_of_neg (by norm_num) ht)
  refine ⟨m, hmpos, hm, ?_⟩
  have hclass := papers_compensation_class 3 t (m : ℚ) 1 4 (by omega) (ne_of_lt ht) hm
  norm_num at hclass ⊢
  exact hclass

theorem g34c_two_independent_aux
    (ω c : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (hc : c ≠ 0) :
    !![c, conj c;
      c * conj ((1 : ℂ) + ω) ^ 2, conj (c * conj ((1 : ℂ) + ω) ^ 2)].det ≠ 0 := by
  have hdet := (papers_compensation_det_ne_zero_iff ω hω 1 1 c hc).2 (by
    intro q
    simpa only [Rat.cast_one, one_mul, (papers_compensation_example ω hω).1] using
      (papers_compensation_example ω hω).2 q)
  simpa using hdet

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]

theorem g34c_theoremB_of_aux
    (hA : ∀ (B : Over (Spec ↧ℂ)),
      [GrpObj B] → [IsCommMonObj B] → [IsIntegral B.left] →
      [Smooth B.hom] → [IsProjective B.hom] → G34TheoremAStatement B)
    (hComp : ∀
      (W : letI := (finiteBetti_abelian A).finite 1
        HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
      (hW : letI := (finiteBetti_abelian A).finite 1; W.IsWeilType)
      (pol : HQ A 2)
      (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
      (hRos : letI := (finiteBetti_abelian A).finite 1;
        IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J)
      (hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
      (hDim : TopologicalSpace.dim A.left = 6),
      (∀ (B : Over (Spec ↧ℂ)),
        [GrpObj B] → [IsCommMonObj B] → [IsIntegral B.left] →
        [Smooth B.hom] → [IsProjective B.hom] → G34TheoremAStatement B) →
      letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW) :
    G34TheoremBStatement A := by
  intro W hW pol hη hRos hPos hDim
  exact hComp W hW pol hη hRos hPos hDim hA

end HodgeLean.Papers
