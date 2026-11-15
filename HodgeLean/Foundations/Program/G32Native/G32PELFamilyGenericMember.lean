import HodgeLean.Foundations.Program.G32Native.PELPeriodComponentGeneration
import HodgeLean.Foundations.Program.G32Native.PELContainingGroupEndomorphisms
import HodgeLean.Foundations.Program.G32Native.G32PELGenericMember

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII
namespace PELSplitFamily
variable {R : PELSplitReference} (F : PELSplitFamily R)

/-- The exact reference Hodge group lies in the connected PEL group.
Source: Abdulali, Annals of Mathematics 155 (2002), §§2.1, 3.2. -/
theorem reference_hodgeGroup_subset_isometries :
    g2_hodgeGroup (latticeHodgePieces R.B.X) (spec_latticeHodgePieces_isInternal R.B.X)
      R.basis ⊆ pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
          (algebraMap ℚ ℂ)) := by
  exact polarized_hodgeGroup_subset_connected_pel R.B.X R.B.pol
    R.polarized.nondegenerate R.polarized.positive
    (fun i : Fin 4 => R.end0 (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)) R.basis

/-- A generic member retains exactly the reference quaternion endomorphism algebra.
Source: Mumford, Abelian Varieties, §§19, 22; Abdulali, Annals 155 (2002), §4. -/
theorem action_bijective_of_general (z : PELSplitComponent R)
    (hgeneral : F.hodgeGroup z = F.genericGroup) : Function.Bijective (F.action z) := by
  constructor
  · intro d e he
    apply R.end0.injective
    apply spec_g4_abelianEnd0Action_injective R.B.X
    apply MulOpposite.unop_injective
    apply (LinearMap.toMatrix R.basis R.basis).injective
    change R.operator d = R.operator e
    rw [← F.action_matrix z d, ← F.action_matrix z e, he]
  · apply containing_group_action_surjective (F.fibre z).X R.B.X
      (F.basis z) R.basis (F.action z) R.end0 (F.action_matrix z)
    change _ ⊆ F.hodgeGroup z
    rw [pel_general_member_hodge_group R F z hgeneral]
    exact reference_hodgeGroup_subset_isometries (R := R)

/-- A general member of the retained effective polarized PEL family supplies
the original G32 record. Exactness of End⁰ and the rational Lie condition
are derived, rather than included in the generic-member premise.
Source: Abdulali, Annals of Mathematics 155 (2002), Proposition 2.3.1,
p. 919, and §4, p. 922. -/
def g32_generalPELMember_of_family (z : PELSplitComponent R)
    (hgeneral : F.hodgeGroup z = F.genericGroup)
    (h : IsMemberOfM (finiteBetti_abelian (F.fibre z).X)
      (spec_bettiDeRhamIso_abelian (F.fibre z).X)
      (hodgeDecomposition_of_abelian (F.fibre z).X)
      (torusCohomology_cupProductOf (F.fibre z).X) (F.fibre z).W (F.fibre z).pol) :
    TypeIIIPaper.GeneralPELMember (F.fibre z).X (F.fibre z).W (F.fibre z).pol h := by
  let end0 := AlgEquiv.ofBijective (F.action z) (F.action_bijective_of_general z hgeneral)
  apply TypeIIIPaper.generalPELMember_of_generic_hodge_group
    (F.fibre z).X (F.fibre z).W (F.fibre z).pol h R.b R.b_neg end0
    (F.action_generator z) (F.action_adjoint z) (F.basis z)
  have hH : (abelianVarietyCohomologyOf (finiteBetti_abelian (F.fibre z).X)
      (spec_bettiDeRhamIso_abelian (F.fibre z).X)
      (hodgeDecomposition_of_abelian (F.fibre z).X)
      (torusCohomology_cupProductOf (F.fibre z).X)).weight1.H =
      latticeHodgePieces (F.fibre z).X := spec_g4_cohomologyHodgePiece_one_eq _
  have hg : g2_hodgeGroup
      (abelianVarietyCohomologyOf (finiteBetti_abelian (F.fibre z).X)
        (spec_bettiDeRhamIso_abelian (F.fibre z).X)
        (hodgeDecomposition_of_abelian (F.fibre z).X)
        (torusCohomology_cupProductOf (F.fibre z).X)).weight1.H
      (abelianVarietyCohomologyOf (finiteBetti_abelian (F.fibre z).X)
        (spec_bettiDeRhamIso_abelian (F.fibre z).X)
        (hodgeDecomposition_of_abelian (F.fibre z).X)
        (torusCohomology_cupProductOf (F.fibre z).X)).weight1.isInternal (F.basis z) =
      F.hodgeGroup z := by
    congr 1
  rw [hg, F.form_matrix z]
  change F.hodgeGroup z = pelGenericGroup _
    (Set.range fun i : Fin 4 => LinearMap.toMatrix _ _
      ((abelianEnd0Action (F.fibre z).X
        (F.action z (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i))).unop.baseChange ℂ))
  simp only [LinearMap.toMatrix_baseChange, F.action_matrix]
  exact pel_general_member_hodge_group R F z hgeneral

/-- The literal rational Lie equality required by G32's powers argument,
from a general member of the retained effective PEL family.
Source: Abdulali, Annals of Mathematics 155 (2002), Proposition 2.3.1,
p. 919, and §4, p. 922. -/
theorem g32_general_pel_lie_of_family (z : PELSplitComponent R)
    (hgeneral : F.hodgeGroup z = F.genericGroup)
    (h : IsMemberOfM (finiteBetti_abelian (F.fibre z).X)
      (spec_bettiDeRhamIso_abelian (F.fibre z).X)
      (hodgeDecomposition_of_abelian (F.fibre z).X)
      (torusCohomology_cupProductOf (F.fibre z).X) (F.fibre z).W (F.fibre z).pol) :
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian (F.fibre z).X)
      (spec_bettiDeRhamIso_abelian (F.fibre z).X)
      (hodgeDecomposition_of_abelian (F.fibre z).X)
      (torusCohomology_cupProductOf (F.fibre z).X)
    let E := polarizationForm (torusCohomology_cupProductOf (F.fibre z).X) h.nondegenerate
    (hodgeLieAlgebra S.weight1.H S.weight1.isInternal :
      Set (Module.End ℚ (HQ (F.fibre z).X 1))) =
      {X | (∀ x y, E (X x) y + E x (X y) = 0) ∧
        ∀ d : AbelianEnd0 (F.fibre z).X,
          X.comp (abelianEnd0Action (F.fibre z).X d).unop =
            (abelianEnd0Action (F.fibre z).X d).unop.comp X} :=
  (F.g32_generalPELMember_of_family z hgeneral h).general

#print axioms g32_general_pel_lie_of_family
#print axioms reference_hodgeGroup_subset_isometries
#print axioms action_bijective_of_general
#print axioms g32_generalPELMember_of_family
end PELSplitFamily
end HodgeLean.Foundations.Program.GeneralTypeIII
