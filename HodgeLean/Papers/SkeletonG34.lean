import HodgeLean.Papers.SkeletonG34Proofs
import HodgeLean.Papers.SkeletonG34Finite

/-! # G34 v1.5 main-theorem skeleton (FROZEN SPEC)

The conditional Theorem 11.2 takes Weil-class algebraicity as a premise. In the paper,
that premise is Theorem B's conclusion. A and B are unasserted definitions; C explicitly
assumes the statement of B and composes it with the conditional connector.
-/

set_option maxHeartbeats 200000

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic
open HodgeLean.Adapters

namespace HodgeLean.Papers

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]
variable {L : Type*} [Field L] [Algebra ℚ L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
  [Smooth Y.hom] [IsProjective Y.hom]
variable {r : ℕ}

/-- **G34 v1.5, conditional Theorem 11.2.**
For an abelian variety with a `ℚ(√-3)` action, the Lie-algebra form of the full unitary Hodge
group, algebraic rational Weil classes, and the three displayed classical cycle inputs imply the
Hodge conjecture for the supplied power data.  The dimension-six specialization and the
algebraicity assertion of Theorem B are not consequences of this statement.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem 11.2 (`thm:powers`) and Theorem C;
Fulton, *Intersection Theory*, 2nd ed., Chapter 8 and Corollary 19.2;
Griffiths--Harris, *Principles of Algebraic Geometry*, Chapter 1 §2. -/
theorem skelg34_theorem112_conditional (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hWA : letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
        (f1_weilAction A θ u 3 hu)
        (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
          (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
            (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk))
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q)
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  skelg34_theorem112_conditional_aux A θ u hu hL pol hη hRos hGk hWA P hPull hC9 h11

/-- Theorem C as the composition of Theorem B and conditional Theorem 11.2.
The paper's Theorem B is an explicit statement-only premise.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem C and its proof in §11;
Fulton, *Intersection Theory*, 2nd ed., Chapter 8 and Corollary 19.2;
Griffiths--Harris, *Principles of Algebraic Geometry*, Chapter 1 §2. -/
theorem skelg34_theoremC (hB : G34TheoremBStatement A) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
    (hDim : TopologicalSpace.dim A.left = 6)
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q)
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p := by
  let := (finiteBetti_abelian A).finite 1
  have hW := isWeilType_of_hodgeLieIsGk (by norm_num : (0 : ℚ) < 3)
    (f1_weilAction A θ u 3 hu)
    (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk
  have hWA := hB (f1_weilAction A θ u 3 hu) hW pol hη hRos hPos hDim
  exact skelg34_theorem112_conditional A θ u hu hL pol hη hRos hGk hWA P hPull hC9 h11

/-- info: 'HodgeLean.Papers.G34TheoremAStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms G34TheoremAStatement

/-- info: 'HodgeLean.Papers.G34TheoremBStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms G34TheoremBStatement

/-- info: 'HodgeLean.Papers.skelg34_theorem112_conditional_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms skelg34_theorem112_conditional_aux

/-- info: 'HodgeLean.Papers.skelg34_theorem112_conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms skelg34_theorem112_conditional

/-- info: 'HodgeLean.Papers.skelg34_theoremC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms skelg34_theoremC

/-- info: 'HodgeLean.Papers.G34ClassDatumStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms G34ClassDatumStatement

/-- info: 'HodgeLean.Papers.G34SupplierIdentityStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms G34SupplierIdentityStatement

/-- info: 'HodgeLean.Papers.G34SupplierExampleStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms G34SupplierExampleStatement

/-- info: 'HodgeLean.Papers.skelg34_typeIII_determinant_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms skelg34_typeIII_determinant_aux

/-- info: 'HodgeLean.Papers.skelg34_typeIII_determinant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms skelg34_typeIII_determinant

end HodgeLean.Papers
