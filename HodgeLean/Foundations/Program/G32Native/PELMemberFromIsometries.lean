import HodgeLean.Foundations.Program.G32Native.PELMemberFromGroup
import HodgeLean.Foundations.Program.G32Native.PELGenericTangentBaseChange

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Abdulali
namespace HodgeLean.Foundations.Program.GeneralTypeIII

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite
variable
  (W : HodgeBlocks.WeilAction
    (abelianVarietyCohomologyOf (finiteBetti_abelian A)
      (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
      (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2) (h : SixfoldData A W pol)

/-- Supply the tangent calculation internally for the constructed connected
D-linear polarization-isometry group. The retained endomorphism presentation,
Eisenstein equation, Rosati equation, and actual group equality remain explicit.
Source: Borel, Linear Algebraic Groups, second edition, §§3.5, 3.11;
Abdulali, Annals 155 (2002), Proposition 2.3.1 and §§3.1–3.3. -/
def generalPELMember_of_isometries
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
      pelGenericGroup
        (LinearMap.toMatrix₂ (Algebra.TensorProduct.basis ℂ basis)
          (Algebra.TensorProduct.basis ℂ basis)
          ((polarizationForm (torusCohomology_cupProductOf A) h.nondegenerate).baseChange ℂ))
        (Set.range fun i : Fin 4 =>
          LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ basis)
            (Algebra.TensorProduct.basis ℂ basis)
            ((abelianEnd0Action A
              (end0 (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b i))).unop.baseChange ℂ))) :
    GeneralPELMember A W pol h :=
  generalPELMember_of_group A W pol h b hb end0 heisenstein hadj basis _ hGroup
    (pelGenericGroup_tangent basis _ _)

#print axioms generalPELMember_of_isometries
end HodgeLean.Foundations.Program.GeneralTypeIII
