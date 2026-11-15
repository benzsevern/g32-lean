import HodgeLean.Foundations.Program.G32Native.PELMemberFromIsometries


noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Abdulali
namespace HodgeLean.Foundations.Program.TypeIIIPaper

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite
variable
  (W : HodgeBlocks.WeilAction
    (abelianVarietyCohomologyOf (finiteBetti_abelian A)
      (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
      (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2)
  (h : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)

/-- The generic Hodge group of the connected quaternionic PEL isometry
 group supplies the original G32 general-member record. The input is an
 algebraic group equality, and the rational Lie equality is derived internally.
 Source: Abdulali, Annals of Mathematics 155 (2002), Proposition 2.3.1,
 pp. 919, 922, and §§3.1–3.3; Borel, Linear Algebraic Groups, §3.5. -/
def generalPELMember_of_generic_hodge_group
    (b : ℚ) (hb : b < 0) (end0 : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A)
    (heisenstein : W.J = (abelianEnd0Action A (end0 ⟨0, 1, 0, 0⟩)).unop)
    (hadj : ∀ d x y,
      polarizationForm (torusCohomology_cupProductOf A) h.nondegenerate
        ((abelianEnd0Action A (end0 d)).unop x) y =
      polarizationForm (torusCohomology_cupProductOf A) h.nondegenerate x
        ((abelianEnd0Action A (end0 (star d))).unop y))
    {n : ℕ} (basis : Module.Basis (Fin n) ℚ (HQ A 1))
    (hGroup : g2_hodgeGroup
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.H
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.isInternal basis =
      GeneralTypeIII.pelGenericGroup
        (LinearMap.toMatrix₂ (Algebra.TensorProduct.basis ℂ basis)
          (Algebra.TensorProduct.basis ℂ basis)
          ((polarizationForm (torusCohomology_cupProductOf A) h.nondegenerate).baseChange ℂ))
        (Set.range fun i : Fin 4 =>
          LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ basis)
            (Algebra.TensorProduct.basis ℂ basis)
            ((abelianEnd0Action A
              (end0 (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b i))).unop.baseChange ℂ))) :
    GeneralPELMember A W pol h := by
  let P := GeneralTypeIII.generalPELMember_of_isometries A W pol
    (GeneralTypeIII.SixfoldData.ofMember A W pol h)
    b hb end0 heisenstein hadj basis hGroup
  exact {
    b := P.b
    b_neg := P.b_neg
    end0 := P.end0
    eisenstein := P.eisenstein
    rosati := P.rosati
    general := P.general }

/-- A member with the generic PEL Hodge group satisfies the exact rational
Lie condition used by the G32 powers implication.
Source: Abdulali, Annals of Mathematics 155 (2002), Proposition 2.3.1,
p. 919, and §4, p. 922; Borel, Linear Algebraic Groups, §3.5. -/
theorem general_pel_lie_of_generic_hodge_group
    (b : ℚ) (hb : b < 0) (end0 : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A)
    (heisenstein : W.J = (abelianEnd0Action A (end0 ⟨0, 1, 0, 0⟩)).unop)
    (hadj : ∀ d x y,
      polarizationForm (torusCohomology_cupProductOf A) h.nondegenerate
        ((abelianEnd0Action A (end0 d)).unop x) y =
      polarizationForm (torusCohomology_cupProductOf A) h.nondegenerate x
        ((abelianEnd0Action A (end0 (star d))).unop y))
    {n : ℕ} (basis : Module.Basis (Fin n) ℚ (HQ A 1))
    (hGroup : g2_hodgeGroup
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.H
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.isInternal basis =
      GeneralTypeIII.pelGenericGroup
        (LinearMap.toMatrix₂ (Algebra.TensorProduct.basis ℂ basis)
          (Algebra.TensorProduct.basis ℂ basis)
          ((polarizationForm (torusCohomology_cupProductOf A) h.nondegenerate).baseChange ℂ))
        (Set.range fun i : Fin 4 =>
          LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ basis)
            (Algebra.TensorProduct.basis ℂ basis)
            ((abelianEnd0Action A
              (end0 (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b i))).unop.baseChange ℂ))) :
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian A)
      (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
      (torusCohomology_cupProductOf A)
    let E := polarizationForm (torusCohomology_cupProductOf A) h.nondegenerate
    (hodgeLieAlgebra S.weight1.H S.weight1.isInternal : Set (Module.End ℚ (HQ A 1))) =
      {X | (∀ x y, E (X x) y + E x (X y) = 0) ∧
        ∀ d : AbelianEnd0 A, X.comp (abelianEnd0Action A d).unop =
          (abelianEnd0Action A d).unop.comp X} := by
  exact (generalPELMember_of_generic_hodge_group A W pol h
    b hb end0 heisenstein hadj basis hGroup).general

#print axioms general_pel_lie_of_generic_hodge_group

#print axioms generalPELMember_of_generic_hodge_group
end HodgeLean.Foundations.Program.TypeIIIPaper
