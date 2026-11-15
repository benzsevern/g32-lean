import HodgeLean.Foundations.Program.G32Native.TypeIIIRosati
import HodgeLean.Foundations.Program.G32Native.TypeIIIWeilType
import HodgeLean.Foundations.Program.G32Native.TypeIIIActualDiscriminant

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

/-- The geometric action comparison in Lemma 8.1: the chosen Eisenstein
quaternion acts through actual endomorphism pullback; the anticommuting
quaternion exchanges the holomorphic eigenspaces. The trace form gives Rosati.
Source: G32 v0.16, Lemma 8.1, first paragraph of proof;
Birkenhake–Lange, Complex Abelian Varieties, second edition, sections 5.2, 9.4–9.6;
van Geemen, An introduction to the Hodge conjecture for abelian varieties,
LNM 1594 (1994), sections 5–6. -/
theorem typeIII_weil_action_aux (Q : TypeIIISixfoldData A pol) :
    ∃ W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3,
      W.J = (Q.pullback (Q.endomorphisms (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, Q.b]))).unop ∧
      W.IsWeilType ∧
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J := by
  exact ⟨Q.inducedWeilAction, rfl, Q.inducedWeilAction_isWeilType, Q.generator_rosati⟩

/-- The full six-dimensional discriminant comparison, on the action retained
by the first step. Project `T` to `K`, use `det_hEntries` on each of the three
blocks, then `H = 2u conjugate(T_K)`. The comparison includes transport from
homology to the repository's dual polarization form on cohomology.
Source: G32 v0.16, Lemma 8.1, second paragraph of proof;
van Geemen, An introduction to the Hodge conjecture for abelian varieties,
LNM 1594 (1994), sections 5–6; Birkenhake–Lange, Complex Abelian Varieties,
second edition, section 9.6. -/
theorem typeIII_discriminant_comparison_aux (Q : TypeIIISixfoldData A pol)
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (hJ : W.J = (Q.pullback
      (Q.endomorphisms (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, Q.b]))).unop)
    (hR : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J) :
    weilDatumClass (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W
      Q.nondegenerate hR =
      (Q.discriminantUnit : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  have hEq : W = Q.inducedWeilAction := by
    cases W with
    | mk J hsq hpres =>
      change J = _ at hJ
      subst J
      rfl
  subst W
  exact Q.discriminant_class

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_weil_action_aux
#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_discriminant_comparison_aux
