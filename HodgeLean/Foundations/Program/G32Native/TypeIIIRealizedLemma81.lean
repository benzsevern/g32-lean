import HodgeLean.Foundations.Program.G32Native.TypeIIIRealization
import HodgeLean.Foundations.Program.G32Native.TypeIIISixfold

noncomputable section
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.HermitianForm HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite

/-- Lemma 8.1 from the ordinary polarized type III setting, including the
retained homology realization and the full six-dimensional discriminant.
Source: G32 v0.16, Lemma 8.1 and its preceding paragraph. -/
theorem typeIII_lemma81_from_endomorphisms (G : TypeIIIPolarizedSixfold A pol) :
    let Q := G.realization
    Q.b = G.b ∧ HEq Q.endomorphisms G.endomorphisms ∧
    (typeIIIWeilAction Q).J = (Q.pullback
      (Q.endomorphisms (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, Q.b]))).unop ∧
    dim A.left = 6 ∧ (typeIIIWeilAction Q).IsWeilType ∧
    PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) Q.nondegenerate ∧
    ∃ hR : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol)
        (typeIIIWeilAction Q).J,
      weilDatumClass (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
        (typeIIIWeilAction Q) Q.nondegenerate hR =
        (Q.discriminantUnit : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  intro Q
  obtain ⟨hJ, hdim, hW, hR, hdisc⟩ := typeIII_lemma81 Q
  exact ⟨G.realization_b, G.realization_endomorphisms, hJ, hdim, hW,
    Q.positive, hR, hdisc⟩

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_lemma81_from_endomorphisms
