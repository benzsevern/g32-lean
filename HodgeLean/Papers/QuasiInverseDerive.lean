import HodgeLean.Papers.QuasiInverseDeriveProofs

/-!
# Quasi-inverses derived from analytic representations (FROZEN SPEC)

This module records implications from an isogeny on complex points to an integral analytic
quasi-inverse, its holomorphic descent, and its algebraic realization. It then removes the
classical quasi-inverse premise from the G32 and G34 literature bundles.

It does not construct the universal or Prym families, period maps, spreading data, parabolic
polarizations, or the compensation input for G34 Theorem B.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers

/-- The analytic representation of an isogeny on complex points is bijective.
Source: Mumford, *Abelian Varieties*, §4; Birkenhake–Lange, *Complex Abelian Varieties*,
2nd ed., §1.2; `spec_abelianHom_analyticRepresentation`. -/
theorem qderiv_analyticRepresentation_bijective {n : ℕ} (P Q : wtr_Variety n)
    (f : P.X ⟶ Q.X) [IsMonHom f] (hf : ccm2_IsogenyOnPoints f) :
    ∃ A : (Fin (dim P.X.left) → ℂ) →ₗ[ℂ] (Fin (dim Q.X.left) → ℂ),
      Function.Bijective A ∧ ∀ v,
        Additive.toMul (complexExponential Q.X (dim Q.X.left) (A v)) =
          Point.map f (Additive.toMul (complexExponential P.X (dim P.X.left) v)) :=
  qderiv_analyticRepresentation_bijective_aux P Q f hf

example {n : ℕ} (P Q : wtr_Variety n) (f : P.X ⟶ Q.X) [IsMonHom f]
    (hf : ccm2_IsogenyOnPoints f) :
    ∃ A : (Fin (dim P.X.left) → ℂ) →ₗ[ℂ] (Fin (dim Q.X.left) → ℂ),
      Function.Bijective A ∧ ∀ v,
        Additive.toMul (complexExponential Q.X (dim Q.X.left) (A v)) =
          Point.map f (Additive.toMul (complexExponential P.X (dim P.X.left) v)) :=
  qderiv_analyticRepresentation_bijective P Q f hf

/-- A bijective analytic representation preserving the forward lattices has an integral
quasi-inverse after multiplication by a positive integer.
Source: Mumford, *Abelian Varieties*, §4; Birkenhake–Lange, *Complex Abelian Varieties*,
2nd ed., Proposition 1.2.1; `complexExponentialLatticeBasis`. -/
theorem qderiv_exists_integral_quasiInverse_lattice {n : ℕ} (P Q : wtr_Variety n)
    (A : (Fin (dim P.X.left) → ℂ) →ₗ[ℂ] (Fin (dim Q.X.left) → ℂ))
    (hbij : Function.Bijective A)
    (hA : ∀ l ∈ abelianPeriodLattice P.X, A l ∈ abelianPeriodLattice Q.X) :
    ∃ (N : ℕ) (B : (Fin (dim Q.X.left) → ℂ) →ₗ[ℂ]
        (Fin (dim P.X.left) → ℂ)),
      0 < N ∧
      (∀ l ∈ abelianPeriodLattice Q.X, B l ∈ abelianPeriodLattice P.X) ∧
      B.comp A = (N : ℂ) • LinearMap.id ∧ A.comp B = (N : ℂ) • LinearMap.id :=
  qderiv_exists_integral_quasiInverse_lattice_aux P Q A hbij hA

example {n : ℕ} (P Q : wtr_Variety n)
    (A : (Fin (dim P.X.left) → ℂ) →ₗ[ℂ] (Fin (dim Q.X.left) → ℂ))
    (hbij : Function.Bijective A)
    (hA : ∀ l ∈ abelianPeriodLattice P.X, A l ∈ abelianPeriodLattice Q.X) :
    ∃ (N : ℕ) (B : (Fin (dim Q.X.left) → ℂ) →ₗ[ℂ]
        (Fin (dim P.X.left) → ℂ)),
      0 < N ∧
      (∀ l ∈ abelianPeriodLattice Q.X, B l ∈ abelianPeriodLattice P.X) ∧
      B.comp A = (N : ℂ) • LinearMap.id ∧ A.comp B = (N : ℂ) • LinearMap.id :=
  qderiv_exists_integral_quasiInverse_lattice P Q A hbij hA

/-- A complex-linear map between the two universal covers descends uniquely when it sends the
source period lattice into the target period lattice.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Proposition 1.2.1;
`spec_existsUnique_holomorphic_descent`. -/
theorem qderiv_existsUnique_holomorphic_descent_between {n : ℕ}
    (P Q : wtr_Variety n)
    (B : (Fin (dim Q.X.left) → ℂ) →ₗ[ℂ] (Fin (dim P.X.left) → ℂ))
    (hB : ∀ l ∈ abelianPeriodLattice Q.X, B l ∈ abelianPeriodLattice P.X) :
    ∃! F : ComplexPoint Q.X → ComplexPoint P.X,
      ContMDiff (modelWithCornersSelf ℂ (Fin (dim Q.X.left) → ℂ))
        (modelWithCornersSelf ℂ (Fin (dim P.X.left) → ℂ)) ω F ∧
        ∀ v, F (Additive.toMul (complexExponential Q.X (dim Q.X.left) v)) =
          Additive.toMul (complexExponential P.X (dim P.X.left) (B v)) :=
  qderiv_existsUnique_holomorphic_descent_between_aux P Q B hB

example {n : ℕ} (P Q : wtr_Variety n)
    (B : (Fin (dim Q.X.left) → ℂ) →ₗ[ℂ] (Fin (dim P.X.left) → ℂ))
    (hB : ∀ l ∈ abelianPeriodLattice Q.X, B l ∈ abelianPeriodLattice P.X) :
    ∃! F : ComplexPoint Q.X → ComplexPoint P.X,
      ContMDiff (modelWithCornersSelf ℂ (Fin (dim Q.X.left) → ℂ))
        (modelWithCornersSelf ℂ (Fin (dim P.X.left) → ℂ)) ω F ∧
        ∀ v, F (Additive.toMul (complexExponential Q.X (dim Q.X.left) v)) =
          Additive.toMul (complexExponential P.X (dim P.X.left) (B v)) :=
  qderiv_existsUnique_holomorphic_descent_between P Q B hB

/-- Every monoid-hom isogeny on points between the varieties in the Weil-transfer framework has
a positive multiplication quasi-inverse.
Source: Mumford, *Abelian Varieties*, §4; `gagam_algebraize`. -/
theorem qderiv_witness {n : ℕ} (P Q : wtr_Variety n) (f : P.X ⟶ Q.X)
    (hf : IsMonHom f) (hi : ccm2_IsogenyOnPoints f) : Nonempty (qinv_Witness P Q f) :=
  qderiv_witness_aux P Q f hf hi

example {n : ℕ} (P Q : wtr_Variety n) (f : P.X ⟶ Q.X)
    (hf : IsMonHom f) (hi : ccm2_IsogenyOnPoints f) : Nonempty (qinv_Witness P Q f) :=
  qderiv_witness P Q f hf hi

/-- The G32 classical quasi-inverse premise follows from analytic uniformization and GAGA.
Source: Mumford, *Abelian Varieties*, §4; Serre, GAGA (1956), §3, Proposition 13. -/
theorem qderiv_qinv_premise : qinv_premise :=
  qderiv_qinv_premise_aux

example : qinv_premise := qderiv_qinv_premise

/-- The dimension-indexed G34 classical quasi-inverse premise follows from analytic
uniformization and GAGA.
Source: Mumford, *Abelian Varieties*, §4; Serre, GAGA (1956), §3, Proposition 13. -/
theorem qderiv_g34q_premise (n : ℕ) : g34q_premise n :=
  qderiv_g34q_premise_aux n

example (n : ℕ) : g34q_premise n := qderiv_g34q_premise n

/-- The six named G32 literature inputs imply Theorem A, with the quasi-inverse supplied by
analytic uniformization and GAGA.
Source: G32 v0.16, Theorem A and Sections 2–7; Mumford, *Abelian Varieties*, §4. -/
theorem qderiv_g32_theoremA_of_premises (B : qderiv_g32_premises)
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  qderiv_g32_theoremA_of_premises_aux B A W pol

example (B : qderiv_g32_premises) (A : Over (Spec ↧ℂ)) [GrpObj A]
    [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  qderiv_g32_theoremA_of_premises B A W pol

/-- The six named G34 literature inputs imply Theorem A, with the quasi-inverse supplied by
analytic uniformization and GAGA.
Source: G34 v1.5, Theorem A and Sections 2–10; Mumford, *Abelian Varieties*, §4. -/
theorem qderiv_g34_theoremA_of_premises (B : qderiv_g34_premises)
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom] : G34TheoremAStatement A :=
  qderiv_g34_theoremA_of_premises_aux B A

example (B : qderiv_g34_premises) (A : Over (Spec ↧ℂ)) [GrpObj A]
    [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A := qderiv_g34_theoremA_of_premises B A

/-- The six named G34 literature inputs and the compensation input imply Theorem B, with the
quasi-inverse supplied by analytic uniformization and GAGA.
Source: G34 v1.5, Theorem B and Proposition 10.2; Mumford, *Abelian Varieties*, §4. -/
theorem qderiv_g34_theoremB_of_premises (B : qderiv_g34_premises)
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom]
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
  qderiv_g34_theoremB_of_premises_aux B A hComp

example (B : qderiv_g34_premises) (A : Over (Spec ↧ℂ)) [GrpObj A]
    [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
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
    G34TheoremBStatement A := qderiv_g34_theoremB_of_premises B A hComp

end HodgeLean.Papers
