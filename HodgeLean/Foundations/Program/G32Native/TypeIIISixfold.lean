import HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldSteps

noncomputable section
set_option maxHeartbeats 200000
open scoped Quaternion TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm

namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}

local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite

/-- The induced Eisenstein action, retaining the endomorphism chosen in the input.
Source: G32 v0.16, Lemma 8.1. -/
def typeIIIWeilAction (Q : TypeIIISixfoldData A pol) :
    letI := (torusCohomology_cupProductOf A).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3 :=
  Q.inducedWeilAction

/-- Lemma 8.1 on a retained diagonal quaternionic homology presentation.
The positive compatible polarization is `Q.positive`, on the same `pol`.
Source: G32 v0.16, Lemma 8.1. -/
theorem typeIII_lemma81 (Q : TypeIIISixfoldData A pol) :
    (typeIIIWeilAction Q).J = (Q.pullback
      (Q.endomorphisms (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, Q.b]))).unop ∧
    dim A.left = 6 ∧ (typeIIIWeilAction Q).IsWeilType ∧
    ∃ hR : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol)
        (typeIIIWeilAction Q).J,
      weilDatumClass (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
        (typeIIIWeilAction Q) Q.nondegenerate hR =
        (Q.discriminantUnit : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  obtain ⟨W, hJ, hW, hR⟩ := typeIII_weil_action_aux Q
  have hEq : W = typeIIIWeilAction Q := by
    cases W with
    | mk J hsq hpres =>
      change J = _ at hJ
      subst J
      rfl
  subst W
  exact ⟨hJ, Q.dim_eq_six, hW, hR, typeIII_discriminant_comparison_aux Q _ hJ hR⟩

/-- The norm-class hypothesis in Corollary 8.2 supplies the exact Theorem A
membership predicate, on the same action and polarization.
Source: G32 v0.16, Corollary 8.2, first clause, and Lemma 8.1. -/
theorem typeIII_member_of_discriminant (Q : TypeIIISixfoldData A pol)
    (hdisc : (Q.discriminantUnit : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) =
      classNegTwo) :
    IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (typeIIIWeilAction Q) pol := by
  obtain ⟨_, hdim, hW, hR, hdet⟩ := typeIII_lemma81 Q
  exact ⟨hdim, hW, Q.nondegenerate, hR, Q.positive, hdet.trans hdisc⟩

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_lemma81
#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_member_of_discriminant

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIWeilAction
