import HodgeLean.Papers.G34CompensationProofs

/-! # Compensation from split eightfolds to sixfolds

This module freezes the arithmetic specialization used in G34 Proposition 10.2, the explicit
two-line independence calculation, and the implication from G34 Theorem A plus one named
geometric compensation premise to G34 Theorem B. The premise represents the product,
Künneth, algebraic external-product, and contraction argument. No construction of those maps is
claimed here. HC no distance; AV milestone no distance.
-/

set_option maxHeartbeats 400000

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open HodgeLean.Adapters ComplexConjugate

namespace HodgeLean.Papers

/-- The sixfold discriminant class `[t]` has a positive integral compensator `[m] = [-1/t]`,
and the product class `[t][-m]` is the split eightfold class `[1]`.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Proposition 10.2, specialized to `n = 4`, `k = 1`. -/
theorem g34c_split_class
    (t : ℚ) (ht : t < 0) :
    ∃ m : ℕ, 0 < m ∧ SameNormClass 3 m ((-1 : ℚ) / t) ∧
      SameNormClass 3 (t * (-m : ℚ)) 1 :=
  g34c_split_class_aux t ht

example (t : ℚ) (ht : t < 0) :
    ∃ m : ℕ, 0 < m ∧ SameNormClass 3 m ((-1 : ℚ) / t) ∧
      SameNormClass 3 (t * (-m : ℚ)) 1 :=
  g34c_split_class t ht

/-- The two explicit algebraic lines contributed by the compensating CM surface are independent.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), proof of Proposition 10.2, "Two independent classes". -/
theorem g34c_two_independent
    (ω c : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (hc : c ≠ 0) :
    !![c, conj c;
      c * conj ((1 : ℂ) + ω) ^ 2, conj (c * conj ((1 : ℂ) + ω) ^ 2)].det ≠ 0 :=
  g34c_two_independent_aux ω c hω hc

example (ω c : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (hc : c ≠ 0) :
    !![c, conj c;
      c * conj ((1 : ℂ) + ω) ^ 2, conj (c * conj ((1 : ℂ) + ω) ^ 2)].det ≠ 0 :=
  g34c_two_independent ω c hω hc

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]

/-- G34 Theorem B follows from Theorem A for every split eightfold and the named geometric
compensation step for the given sixfold. The direct premise is the narrow honest boundary of the
current API: it must construct the CM surface product, identify the relevant Künneth summands,
and contract algebraic classes back to `A`.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem B and Proposition 10.2; Schoen, *Addendum to:
Hodge classes on self-products of a variety with an automorphism*, Compositio Math. 114 (1998),
Proposition 10; Voisin, Bourbaki exposé 1248 (2026), Lemma 2.9. -/
theorem g34c_theoremB_of
    (hA : ∀ (B : Over (Spec ↧ℂ)),
      [GrpObj B] → [IsCommMonObj B] → [IsIntegral B.left] →
      [Smooth B.hom] → [IsProjective B.hom] → G34TheoremAStatement B)
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
      (∀ (B : Over (Spec ↧ℂ)),
        [GrpObj B] → [IsCommMonObj B] → [IsIntegral B.left] →
        [Smooth B.hom] → [IsProjective B.hom] → G34TheoremAStatement B) →
      letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW) :
    G34TheoremBStatement A :=
  g34c_theoremB_of_aux A hA hComp

example
    (hA : ∀ (B : Over (Spec ↧ℂ)),
      [GrpObj B] → [IsCommMonObj B] → [IsIntegral B.left] →
      [Smooth B.hom] → [IsProjective B.hom] → G34TheoremAStatement B)
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
      (∀ (B : Over (Spec ↧ℂ)),
        [GrpObj B] → [IsCommMonObj B] → [IsIntegral B.left] →
        [Smooth B.hom] → [IsProjective B.hom] → G34TheoremAStatement B) →
      letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW) :
    G34TheoremBStatement A :=
  g34c_theoremB_of A hA hComp

end HodgeLean.Papers
