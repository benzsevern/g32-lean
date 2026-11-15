import HodgeLean.Papers.SkeletonG32Defs
import HodgeLean.Adapters.AbelianCMDataDefs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program.TypeIIIPaper

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- Exterior action of a rational endomorphism, transported to actual cohomology.
Source: van Geemen–Verra, Quaternionic Pryms and Hodge Classes, §4.6. -/
def rationalPullback (d : AbelianEnd0 A) (n : ℕ) : Module.End ℚ (HQ A n) :=
  let e := (torusCohomology_cupProductOf A).cupWedgeEquiv n
  e.toLinearMap.comp ((exteriorPower.map n (abelianEnd0Action A d).unop).comp
    e.symm.toLinearMap)

example (d : AbelianEnd0 A) (n : ℕ) (v : HQ A n) :
    rationalPullback A d n v = (torusCohomology_cupProductOf A).cupWedgeEquiv n
      (exteriorPower.map n (abelianEnd0Action A d).unop
        ((torusCohomology_cupProductOf A).cupWedgeEquiv n |>.symm v)) := rfl

/-- Rational span of all invertible rational-endomorphism translates of a middle space.
This defines a submodule, without asserting generation or algebraicity.
Source: van Geemen–Verra, §4.6, definition of the quaternionic classes. -/
def quaternionicSpan (U : Submodule ℚ (HQ A (2 * 3))) : Submodule ℚ (HQ A (2 * 3)) :=
  ⨆ d : (AbelianEnd0 A)ˣ, U.map (rationalPullback A (d : AbelianEnd0 A) (2 * 3))

example (U : Submodule ℚ (HQ A (2 * 3))) (d : (AbelianEnd0 A)ˣ) :
    U.map (rationalPullback A (d : AbelianEnd0 A) (2 * 3)) ≤ quaternionicSpan A U :=
  le_iSup (fun d : (AbelianEnd0 A)ˣ =>
    U.map (rationalPullback A (d : AbelianEnd0 A) (2 * 3))) d

local instance : Module.Finite ℚ (HQ A 1) :=
  (torusCohomology_cupProductOf A).finite

variable
  (W : letI := (torusCohomology_cupProductOf A).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2)
  (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)

/-- The selected Weil space in degree six, using membership's dimension calculation.
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

end HodgeLean.Foundations.Program.TypeIIIPaper
