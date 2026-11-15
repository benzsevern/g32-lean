import HodgeLean.Foundations.Program.G32Native.PELActualEndOrder
import HodgeLean.Foundations.Program.G32Native.TypeIIIFormDiagonalization
import HodgeLean.Foundations.Program.G32Native.TypeIIISixfold
import HodgeLean.Foundations.Program.G32Native.TypeIIIActualRosati
import HodgeLean.Foundations.PositivePolarization

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct Quaternion CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}

/-- The carrier with the quadratic action selected by the quaternion presentation. -/
abbrev typeIIIReferenceVariety (Q : TypeIIIFormData A pol) : wtr_Variety 3 :=
  { X := A, W := typeIIIWeilAction Q.diagonal, pol := pol }

/-- The trace polarization polarizes the induced Weil action. -/
theorem typeIIIReference_polarized (Q : TypeIIIFormData A pol) :
    wtr_PolarizedWeil 3 (typeIIIReferenceVariety Q) := by
  obtain ⟨_, hd, hw, hr, _⟩ := typeIII_lemma81 Q.diagonal
  exact ⟨hd, hw, Q.nondegenerate, hr, Q.positive⟩

/-- The canonical quaternion involution is adjoint for the retained trace polarization. -/
theorem typeIIIReference_adjoint (Q : TypeIIIFormData A pol)
    (d : ℍ[ℚ, -3, 0, Q.b]) (x y : HQ A 1) :
    polarizationForm (torusCohomology_cupProductOf A) Q.nondegenerate
      ((abelianEnd0Action A (Q.endomorphisms d)).unop x) y =
    polarizationForm (torusCohomology_cupProductOf A) Q.nondegenerate x
      ((abelianEnd0Action A (Q.endomorphisms (star d))).unop y) := by
  have hP : p1_IsPolarization A pol :=
    (p1_isPolarization_iff A pol).2 ⟨Q.nondegenerate, Q.positive⟩
  have he := p1r_abelianEnd0Action_rosati (p1_isNondegenerate_of_isPositive_aux hP)
    (p1_adjoint_mem_range_aux A hP) (Q.endomorphisms d)
  rw [typeIII_actual_rosati Q.b Q.b_neg Q.endomorphisms hP d] at he
  have ht := p1r_dualForm_adjoint (p1_isNondegenerate_of_isPositive_aux hP)
    (abelianEnd0Action A (Q.endomorphisms d)).unop x y
  rw [← he] at ht
  exact ht

/-- A rational basis of the actual twelve-dimensional cohomology. -/
def typeIIIReferenceBasis (Q : TypeIIIFormData A pol) : Module.Basis (Fin 12) ℚ (HQ A 1) := by
  letI := (torusCohomology_cupProductOf A).finite
  have hd : Module.finrank ℚ (HQ A 1) = 12 := by
    rw [(torusCohomology_cupProductOf A).finrank_eq, Q.diagonal.dim_eq_six]
  exact (Module.finBasis ℚ (HQ A 1)).reindex (finCongr hd)

/-- The printed quaternionic form data supplies a reference with its actual integral order.
Source: G32 v0.18, §8, Lemma 8.1; Birkenhake–Lange, §§1.2, 5.2, 9.6. -/
def PELSplitReference.ofTypeIII (Q : TypeIIIFormData A pol) : PELSplitReference where
  B := typeIIIReferenceVariety Q
  polarized := typeIIIReference_polarized Q
  b := Q.b
  b_neg := Q.b_neg
  end0 := Q.endomorphisms
  basis := typeIIIReferenceBasis Q
  eisenstein := rfl
  adjoint := typeIIIReference_adjoint Q
  order := actualEndOrder A Q.endomorphisms
  finite := actualEndOrder_finite A Q.endomorphisms
  full := actualEndOrder_full A Q.endomorphisms
  integral := (actualEndOrderEquiv A Q.endomorphisms).symm.toRingHom
  integral_eq := actualEndOrder_integral_eq A Q.endomorphisms

#print axioms typeIIIReference_polarized
#print axioms typeIIIReference_adjoint
#print axioms typeIIIReferenceBasis
#print axioms PELSplitReference.ofTypeIII
end HodgeLean.Foundations.Program.GeneralTypeIII
