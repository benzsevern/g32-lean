import HodgeLean.Foundations.Program.G32Native.TypeIIIPaperDefs
import HodgeLean.Adapters.AbelianCMDataDefs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

open HodgeLean.Foundations.Program.TypeIIIPaper
namespace HodgeLean.Foundations.Program.GeneralTypeIII

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

local instance : Module.Finite ℚ (HQ A 1) :=
  (torusCohomology_cupProductOf A).finite

variable
  (W : letI := (torusCohomology_cupProductOf A).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2)

/-- Six-dimensional polarized Weil data, with no discriminant restriction.
Source: G34 v1.5, Theorem B and §12; Birkenhake–Lange, §§5.2, 9.4–9.6. -/
structure SixfoldData : Prop where
  dim_eq : TopologicalSpace.dim A.left = 6
  isWeilType : W.IsWeilType
  nondegenerate : Symplectic.IsNondegenerate
    (polarizationVec (torusCohomology_cupProductOf A) pol)
  rosati : Symplectic.IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J

/-- G32 membership supplies the shared sixfold data. -/
def SixfoldData.ofMember
    (h : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol) :
    SixfoldData A W pol := ⟨h.dim_eq, h.isWeilType, h.nondegenerate, h.rosati⟩

/-- The balanced eigenspace has complex dimension three. -/
theorem SixfoldData.finrank_eq_three (h : SixfoldData A W pol) :
    Module.finrank ℂ ↥(W.Vs ⊓
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.H (1, 0)) = 3 := by
  have ht := two_mul_finrank_vs_inf_h10_eq (finiteBetti_abelian A)
    (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
    (torusCohomology_cupProductOf A) (by norm_num : (0 : ℚ) < 3) W h.isWeilType
  rw [h.dim_eq] at ht
  omega

variable (hM : SixfoldData A W pol)

/-- The selected Weil space in degree six, using the sixfold dimension calculation.
Source: van Geemen–Verra, §4.3; G32 Lemma 8.1. -/
def weilSix : Submodule ℚ (HQ A (2 * 3)) := by
  have U := weilClassOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hM.isWeilType
  rw [hM.finrank_eq_three] at U
  exact U

/-- Quaternionic presentation and the general-member condition in Lie vocabulary.
The negative parameter makes the quaternion algebra totally definite over ℚ.
The algebra equivalence retains the exact endomorphism algebra; `eisenstein` retains
its selected quadratic subfield. `general` says the Hodge Lie algebra is the full
polarization-skew centralizer of that algebra, rather than an arbitrary subalgebra.
No Hodge generation or algebraicity conclusion is a field.
Source: Abdulali, Annals of Mathematics 155 (2002), §2.3, Proposition 2.3.1,
§3 and Theorem 4.1 (general member of a PEL-family of type III).
The group-to-Lie dictionary is the repository convention, not a new comparison theorem. -/
structure GeneralPELMember where
  b : ℚ
  b_neg : b < 0
  end0 : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A
  eisenstein : W.J = (abelianEnd0Action A (end0 ⟨0, 1, 0, 0⟩)).unop
  rosati : ∀ d x y,
    polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate
      ((abelianEnd0Action A (end0 d)).unop x) y =
    polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate x
      ((abelianEnd0Action A (end0 (star d))).unop y)
  general :
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian A)
      (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
      (torusCohomology_cupProductOf A)
    let E := polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate
    (hodgeLieAlgebra S.weight1.H S.weight1.isInternal : Set (Module.End ℚ (HQ A 1))) =
      {X | (∀ x y, E (X x) y + E x (X y) = 0) ∧
        ∀ d : AbelianEnd0 A, X.comp (abelianEnd0Action A d).unop =
          (abelianEnd0Action A d).unop.comp X}

end HodgeLean.Foundations.Program.GeneralTypeIII
