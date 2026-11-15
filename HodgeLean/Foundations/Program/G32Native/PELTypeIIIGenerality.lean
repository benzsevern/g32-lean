import HodgeLean.Foundations.Program.G32Native.PELSplitReferenceFromTypeIII
import HodgeLean.Foundations.Program.G32Native.PELDomainGeneric

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
open GeneralTypeIII

variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}

/-- Generality expressed using the connected D-linear polarization isometry group.
Source: G32 v0.18, §8, Corollary 8.2(ii); Abdulali, Annals 155 (2002), Proposition 2.3.1. -/
theorem g32_from_data_generality_iff_pel (Q : G32Native.TypeIIIFormData A pol) :
    (g2_hodgeGroup (latticeHodgePieces A) (spec_latticeHodgePieces_isInternal A)
        (PELSplitReference.ofTypeIII Q).basis =
      pelDomainHodgeGroup (PELSplitReference.ofTypeIII Q)
        (pel_hodgeGenericPoint (PELSplitReference.ofTypeIII Q)).val) ↔
    (g2_hodgeGroup (latticeHodgePieces A) (spec_latticeHodgePieces_isInternal A)
        (PELSplitReference.ofTypeIII Q).basis =
      g1_identityComponent (pelIsometryGroup
        ((PELSplitReference.ofTypeIII Q).form.map (algebraMap ℚ ℂ))
        (Set.range fun i : Fin 4 =>
          ((PELSplitReference.ofTypeIII Q).operator
            (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 Q.b i)).map
              (algebraMap ℚ ℂ)))) := by
  have he := pel_generic_point_hodgeGroup_eq (PELSplitReference.ofTypeIII Q)
    (pel_hodgeGenericPoint _) (pel_hodgeGenericPoint_contains _)
  exact ⟨fun h => h.trans he, fun h => h.trans he.symm⟩


#print axioms g32_from_data_generality_iff_pel
end HodgeLean.Foundations.Program
