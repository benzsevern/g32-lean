import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexQuotient

/-! # Original relative subcomplex Mayer--Vietoris quotient models -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original left quotient of the subcomplex Mayer--Vietoris diagram is the literal relative complex of the intersection.
Source: Hatcher, Algebraic Topology, section 2.2, relative Mayer--Vietoris chains.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_mv_left_iso
    (X : TopCat.{0}) (P Q : (TopCat.toSSet.obj X).Subcomplex) :
    (cokernel (properCycle_subcomplex_mv_to_ambient X P Q)).X₁ ≅
      properCycle_subcomplex_quotient (P ⊓ Q) :=
  PreservesCokernel.iso ShortComplex.π₁ (properCycle_subcomplex_mv_to_ambient X P Q)

/-- The original middle quotient is the biproduct of the two literal relative chain quotients.
Source: Hatcher, Algebraic Topology, section 2.2, relative Mayer--Vietoris chains.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_mv_middle_iso
    (X : TopCat.{0}) (P Q : (TopCat.toSSet.obj X).Subcomplex) :
    (cokernel (properCycle_subcomplex_mv_to_ambient X P Q)).X₂ ≅
      properCycle_subcomplex_quotient P ⊞ properCycle_subcomplex_quotient Q :=
  PreservesCokernel.iso ShortComplex.π₂ (properCycle_subcomplex_mv_to_ambient X P Q) ≪≫
    ProperCycleRelativeMV.cokernelBiprodMapIso
      (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap Q.ι (ModuleCat.of ℚ ℚ))

/-- The original final quotient is the literal relative complex modulo the union subcomplex.
Source: Hatcher, Algebraic Topology, section 2.2, relative Mayer--Vietoris chains.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_mv_right_iso
    (X : TopCat.{0}) (P Q : (TopCat.toSSet.obj X).Subcomplex) :
    (cokernel (properCycle_subcomplex_mv_to_ambient X P Q)).X₃ ≅
      properCycle_subcomplex_quotient (P ⊔ Q) :=
  PreservesCokernel.iso ShortComplex.π₃ (properCycle_subcomplex_mv_to_ambient X P Q)

/-- The intersection model retains the actual left quotient projection.
Source: Hatcher, Algebraic Topology, section 2.2, relative chain projections.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_mv_left_projection
    (X : TopCat.{0}) (P Q : (TopCat.toSSet.obj X).Subcomplex) :
    (cokernel.π (properCycle_subcomplex_mv_to_ambient X P Q)).τ₁ ≫
        (properCycle_subcomplex_mv_left_iso X P Q).hom =
      cokernel.π (SSet.chainComplexMap (P ⊓ Q).ι (ModuleCat.of ℚ ℚ)) :=
  PreservesCokernel.π_iso_hom ShortComplex.π₁ (properCycle_subcomplex_mv_to_ambient X P Q)

/-- The middle model retains both original quotient projections.
Source: Hatcher, Algebraic Topology, section 2.2, relative chain projections.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_mv_middle_projection
    (X : TopCat.{0}) (P Q : (TopCat.toSSet.obj X).Subcomplex) :
    (cokernel.π (properCycle_subcomplex_mv_to_ambient X P Q)).τ₂ ≫
        (properCycle_subcomplex_mv_middle_iso X P Q).hom =
      biprod.map (cokernel.π (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ)))
        (cokernel.π (SSet.chainComplexMap Q.ι (ModuleCat.of ℚ ℚ))) := by
  change ShortComplex.π₂.map (cokernel.π (properCycle_subcomplex_mv_to_ambient X P Q)) ≫
    (PreservesCokernel.iso ShortComplex.π₂ (properCycle_subcomplex_mv_to_ambient X P Q)).hom ≫
      (ProperCycleRelativeMV.cokernelBiprodMapIso
        (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ))
        (SSet.chainComplexMap Q.ι (ModuleCat.of ℚ ℚ))).hom = _
  erw [PreservesCokernel.π_iso_hom_assoc, ProperCycleRelativeMV.cokernelBiprodMapIso_projection]

/-- The union model retains the actual final quotient projection.
Source: Hatcher, Algebraic Topology, section 2.2, relative chain projections.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_mv_right_projection
    (X : TopCat.{0}) (P Q : (TopCat.toSSet.obj X).Subcomplex) :
    (cokernel.π (properCycle_subcomplex_mv_to_ambient X P Q)).τ₃ ≫
        (properCycle_subcomplex_mv_right_iso X P Q).hom =
      cokernel.π (SSet.chainComplexMap (P ⊔ Q).ι (ModuleCat.of ℚ ℚ)) :=
  PreservesCokernel.π_iso_hom ShortComplex.π₃ (properCycle_subcomplex_mv_to_ambient X P Q)

end HodgeLean.Foundations.QuotientDuality
