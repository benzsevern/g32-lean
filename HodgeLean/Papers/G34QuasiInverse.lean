import HodgeLean.Papers.G34QuasiInverseProofs

/-! # G34 reverse isogenies from classical quasi-inverses (FROZEN)

This module records an implication from the classical quasi-inverse input for isogenies of
the underlying abelian varieties. The premise supplies only a reverse morphism, its
group-homomorphism and isogeny properties, and a positive multiplication relation. It has no
Weil-action, polarization, or cycle clause.

The module does not construct a universal family, a Prym family, a boundary period map,
spreading, parabolic polarizations, or compensation.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers

/-- The classical quasi-inverse premise supplies exactly the reverse field used by
`g34n_premises`.
Source: Mumford, *Abelian Varieties*, §4; `qinv_wtr_KIsog_reverse_of_witness`. -/
theorem g34q_reverse_of_premise (h : g34q_premise 4) :
    ∀ P Q, wtr_IsMember 4 1 P → wtr_IsMember 4 1 Q →
      wtr_KIsog P Q → wtr_KIsog Q P :=
  g34q_reverse_of_premise_aux h

example (h : g34q_premise 4) (P Q : wtr_Variety 4)
    (hP : wtr_IsMember 4 1 P) (hQ : wtr_IsMember 4 1 Q)
    (hf : wtr_KIsog P Q) : wtr_KIsog Q P :=
  g34q_reverse_of_premise h P Q hP hQ hf

/-- G34 Theorem A from the named inputs with reverse isogenies supplied by the classical
quasi-inverse premise.
Source: G34 v1.5, Theorem A and its proof; Mumford, *Abelian Varieties*, §4. -/
theorem g34q_theoremA_of_premises (B : g34q_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A :=
  g34q_theoremA_of_premises_aux B A

example (B : g34q_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A := g34q_theoremA_of_premises B A

/-- G34 Theorem B from the quasi-inverse premise bundle and the compensation input.
Source: G34 v1.5, Theorem B and Proposition 10.2; Schoen, Compositio Math. 114 (1998),
Proposition 10; Voisin, Bourbaki exposé 1248 (2026), Lemma 2.9. -/
theorem g34q_theoremB_of_premises (B : g34q_premises) (A : Over (Spec ↧ℂ))
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
    G34TheoremBStatement A :=
  g34q_theoremB_of_premises_aux B A hComp

example (B : g34q_premises) (A : Over (Spec ↧ℂ))
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
    G34TheoremBStatement A :=
  g34q_theoremB_of_premises B A hComp

end HodgeLean.Papers
