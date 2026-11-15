import HodgeLean.Foundations.Program.G32Native.PELDomainGeneric
import HodgeLean.Foundations.Program.G32Native.G32PELGenericMember
import HodgeLean.Foundations.Program.G32Native.TypeIIISixfold
import HodgeLean.Foundations.Program.G32Native.TypeIIIFormDiscriminant
import HodgeLean.Foundations.Program.G32Native.PELDomainPresentation
import HodgeLean.Foundations.Program.G32Native.TypeIIIActualRosati

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
open GeneralTypeIII

/-- The matrix-domain generic group supplies the per-member powers record.
Source: Abdulali, Annals 155 (2002), Proposition 2.3.1 and §4. -/
def generalPELMember_of_domain_generic (R : PELSplitReference)
    (h : IsMemberOfM (finiteBetti_abelian R.B.X)
      (spec_bettiDeRhamIso_abelian R.B.X) (hodgeDecomposition_of_abelian R.B.X)
      (torusCohomology_cupProductOf R.B.X) R.B.W R.B.pol)
    (hgeneral : g2_hodgeGroup (latticeHodgePieces R.B.X)
      (spec_latticeHodgePieces_isInternal R.B.X) R.basis =
        pelDomainHodgeGroup R (pel_hodgeGenericPoint R).val) :
    TypeIIIPaper.GeneralPELMember R.B.X R.B.W R.B.pol h := by
  apply TypeIIIPaper.generalPELMember_of_generic_hodge_group
    R.B.X R.B.W R.B.pol h R.b R.b_neg R.end0 R.eisenstein R.adjoint R.basis
  have hg : g2_hodgeGroup
      (abelianVarietyCohomologyOf (finiteBetti_abelian R.B.X)
        (spec_bettiDeRhamIso_abelian R.B.X) (hodgeDecomposition_of_abelian R.B.X)
        (torusCohomology_cupProductOf R.B.X)).weight1.H
      (abelianVarietyCohomologyOf (finiteBetti_abelian R.B.X)
        (spec_bettiDeRhamIso_abelian R.B.X) (hodgeDecomposition_of_abelian R.B.X)
        (torusCohomology_cupProductOf R.B.X)).weight1.isInternal R.basis =
      g2_hodgeGroup (latticeHodgePieces R.B.X)
        (spec_latticeHodgePieces_isInternal R.B.X) R.basis := by
    congr 1
    exact spec_g4_cohomologyHodgePiece_one_eq _
  rw [hg, hgeneral, pel_generic_point_hodgeGroup_eq R _ (pel_hodgeGenericPoint_contains R)]
  simp only [LinearMap.toMatrix_baseChange]
  congr 1
  ext i j
  simp [PELSplitReference.form, LinearMap.toMatrix₂_apply]

/-- A form with the domain's generic Hodge group supplies the powers record.
Source: Abdulali, Annals 155 (2002), Proposition 2.3.1 and §4. -/
def generalPELMember_of_form_domain_generic (R : PELSplitReference)
    (Q : G32Native.TypeIIIFormData R.B.X R.B.pol)
    (hdisc : Q.discriminantClass = classNegTwo)
    (hgeneral : g2_hodgeGroup (latticeHodgePieces R.B.X)
      (spec_latticeHodgePieces_isInternal R.B.X) R.basis =
        pelDomainHodgeGroup R (pel_hodgeGenericPoint R).val) :
    TypeIIIPaper.GeneralPELMember R.B.X (G32Native.typeIIIWeilAction Q.diagonal) R.B.pol
      (G32Native.typeIII_member_of_discriminant Q.diagonal
        (Q.discriminantClass_eq.symm.trans hdisc)) := by
  let h := G32Native.typeIII_member_of_discriminant Q.diagonal
    (Q.discriminantClass_eq.symm.trans hdisc)
  have hP : p1_IsPolarization R.B.X R.B.pol :=
    (p1_isPolarization_iff R.B.X R.B.pol).2 ⟨Q.nondegenerate, Q.positive⟩
  have hadj (d : ℍ[ℚ, -3, 0, Q.b]) (x y : HQ R.B.X 1) :
      polarizationForm (torusCohomology_cupProductOf R.B.X) h.nondegenerate
        ((abelianEnd0Action R.B.X (Q.endomorphisms d)).unop x) y =
      polarizationForm (torusCohomology_cupProductOf R.B.X) h.nondegenerate x
        ((abelianEnd0Action R.B.X (Q.endomorphisms (star d))).unop y) := by
    have he := p1r_abelianEnd0Action_rosati (p1_isNondegenerate_of_isPositive_aux hP)
      (p1_adjoint_mem_range_aux R.B.X hP) (Q.endomorphisms d)
    rw [G32Native.typeIII_actual_rosati Q.b Q.b_neg Q.endomorphisms hP d] at he
    have ht := p1r_dualForm_adjoint (p1_isNondegenerate_of_isPositive_aux hP)
      (abelianEnd0Action R.B.X (Q.endomorphisms d)).unop x y
    rw [← he] at ht
    exact ht
  apply TypeIIIPaper.generalPELMember_of_generic_hodge_group
    R.B.X _ R.B.pol h Q.b Q.b_neg Q.endomorphisms rfl hadj R.basis
  have hg : g2_hodgeGroup
      (abelianVarietyCohomologyOf (finiteBetti_abelian R.B.X)
        (spec_bettiDeRhamIso_abelian R.B.X) (hodgeDecomposition_of_abelian R.B.X)
        (torusCohomology_cupProductOf R.B.X)).weight1.H
      (abelianVarietyCohomologyOf (finiteBetti_abelian R.B.X)
        (spec_bettiDeRhamIso_abelian R.B.X) (hodgeDecomposition_of_abelian R.B.X)
        (torusCohomology_cupProductOf R.B.X)).weight1.isInternal R.basis =
      g2_hodgeGroup (latticeHodgePieces R.B.X)
        (spec_latticeHodgePieces_isInternal R.B.X) R.basis := by
    congr 1
    exact spec_g4_cohomologyHodgePiece_one_eq _
  have hf : LinearMap.toMatrix₂ (Algebra.TensorProduct.basis ℂ R.basis)
      (Algebra.TensorProduct.basis ℂ R.basis)
      ((polarizationForm (torusCohomology_cupProductOf R.B.X) h.nondegenerate).baseChange ℂ) =
      R.form.map (algebraMap ℚ ℂ) := by
    ext i j
    simp [PELSplitReference.form, LinearMap.toMatrix₂_apply]
  rw [hg, hgeneral, pel_generic_point_hodgeGroup_eq R _ (pel_hodgeGenericPoint_contains R), hf]
  simpa only [LinearMap.toMatrix_baseChange, pelEnd0Matrix, LinearMap.coe_mk, AddHom.coe_mk] using
    pelGenericGroup_presentation R Q.b Q.endomorphisms

#print axioms generalPELMember_of_domain_generic
#print axioms generalPELMember_of_form_domain_generic
end HodgeLean.Foundations.Program
