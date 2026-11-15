import HodgeLean.Foundations.Program.G32Native.PELReferenceMarking
import HodgeLean.Foundations.Program.G32Native.PELMemberFromIsometries

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

variable (A B : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj B] [IsCommMonObj B] [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite
local instance : Module.Finite ℚ (HQ B 1) := (torusCohomology_cupProductOf B).finite
variable
  (W : HodgeBlocks.WeilAction
    (abelianVarietyCohomologyOf (finiteBetti_abelian A)
      (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
      (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2) (h : SixfoldData A W pol)

/-- Assemble the shared type-III record by transport from an exact reference
fibre. Target End⁰, its adjoint equation, and the tangent formula are constructed
internally. Identification of the reference generic group is still an input.
Source: Abdulali, Annals 155 (2002), Proposition 2.3.1 and §§3.1–3.3;
Birkenhake–Lange, Complex Abelian Varieties, §§1.2, 5.5, 9.6. -/
def generalPELMember_of_reference
    (b : ℚ) (hb : b < 0) (e : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 B)
    {n : ℕ} (basis : Module.Basis (Fin n) ℚ (HQ B 1))
    (m : HQ B 1 ≃ₗ[ℚ] HQ A 1)
    (EB : LinearMap.BilinForm ℚ (HQ B 1))
    (hform : ∀ x y,
      polarizationForm (torusCohomology_cupProductOf A) h.nondegenerate (m x) (m y) = EB x y)
    (hgen : ∀ x, m ((abelianEnd0Action B (e ⟨0, 1, 0, 0⟩)).unop x) = W.J (m x))
    (hadj : ∀ d x y, EB ((abelianEnd0Action B (e d)).unop x) y =
      EB x ((abelianEnd0Action B (e (star d))).unop y))
    (hGroup : g2_hodgeGroup (latticeHodgePieces A)
        (spec_latticeHodgePieces_isInternal A) (basis.map m) =
      g2_hodgeGroup (latticeHodgePieces B) (spec_latticeHodgePieces_isInternal B) basis)
    (hGeneric : g2_hodgeGroup (latticeHodgePieces B)
        (spec_latticeHodgePieces_isInternal B) basis =
      pelGenericGroup
        (LinearMap.toMatrix₂ (Algebra.TensorProduct.basis ℂ basis)
          (Algebra.TensorProduct.basis ℂ basis) (EB.baseChange ℂ))
        (Set.range fun i : Fin 4 =>
          LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ basis)
            (Algebra.TensorProduct.basis ℂ basis)
            ((abelianEnd0Action B
              (e (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b i))).unop.baseChange ℂ))) :
    GeneralPELMember A W pol h := by
  let t := referenceEnd0Equiv A B (basis.map m) basis hGroup
  let end0 := e.trans t
  refine generalPELMember_of_isometries A W pol h b hb end0 ?_ ?_ (basis.map m) ?_
  · exact referenceEnd0Equiv_generator A B basis m hGroup _ W.J _ rfl hgen
  · exact referenceEnd0Equiv_rosati A B basis m hGroup e.toAlgHom _ EB hform hadj
  · have hH : (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.H = latticeHodgePieces A :=
      spec_g4_cohomologyHodgePiece_one_eq A
    have hg : g2_hodgeGroup
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1.H
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1.isInternal (basis.map m) =
        g2_hodgeGroup (latticeHodgePieces A)
          (spec_latticeHodgePieces_isInternal A) (basis.map m) := by
      congr 1
    rw [hg, hGroup, hGeneric]
    congr 1
    · ext i j
      simpa [LinearMap.toMatrix₂_apply] using (hform (basis i) (basis j)).symm
    · congr 1
      funext i
      rw [LinearMap.toMatrix_baseChange, LinearMap.toMatrix_baseChange]
      exact congrArg (fun M => M.map (algebraMap ℚ ℂ))
        (referenceEnd0Equiv_matrix A B (basis.map m) basis hGroup
          (e (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b i))).symm

#print axioms generalPELMember_of_reference
end HodgeLean.Foundations.Program.GeneralTypeIII
