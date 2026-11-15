import HodgeLean.Foundations.Program.G32Native.PELSplitTransport
import HodgeLean.Foundations.Program.UniversalFamilyB60bDiscriminant

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program.GeneralTypeIII
namespace PELSplitFamily

/-- Reference membership transports to every marked fibre, including special fibres.
Source: van Geemen, LNM 1594, §5; invariance of the Hermitian determinant under isometry. -/
theorem member_of_reference {R : PELSplitReference} (F : PELSplitFamily R)
    (h : IsMemberOfM (finiteBetti_abelian R.B.X)
      (spec_bettiDeRhamIso_abelian R.B.X) (hodgeDecomposition_of_abelian R.B.X)
      (torusCohomology_cupProductOf R.B.X) R.B.W R.B.pol)
    (z : PELSplitComponent R) :
    IsMemberOfM (finiteBetti_abelian (F.fibre z).X)
      (spec_bettiDeRhamIso_abelian (F.fibre z).X)
      (hodgeDecomposition_of_abelian (F.fibre z).X)
      (torusCohomology_cupProductOf (F.fibre z).X) (F.fibre z).W (F.fibre z).pol := by
  let P := F.polarized z
  refine ⟨P.dim_eq, P.isWeilType, P.nondegenerate, P.rosati, P.positive, ?_⟩
  have he := weilDetClass_equiv
    ⟨R.B.W.J, R.B.W.J_sq⟩ ⟨(F.fibre z).W.J, (F.fibre z).W.J_sq⟩
    (polarizationForm (torusCohomology_cupProductOf R.B.X) h.nondegenerate)
    (polarizationForm (torusCohomology_cupProductOf (F.fibre z).X) P.nondegenerate)
    (F.mark z) (F.generator_eq z) (F.form_eq z)
    ((isRosatiSkew_iff_dualForm h.nondegenerate R.B.W.J).mp h.rosati)
    ((isRosatiSkew_iff_dualForm P.nondegenerate (F.fibre z).W.J).mp P.rosati)
    (isAlt_polarizationForm _ _) (isAlt_polarizationForm _ _)
    (nondegenerate_polarizationForm _ _) (nondegenerate_polarizationForm _ _)
  exact he.trans h.datum

#print axioms member_of_reference
end PELSplitFamily
end HodgeLean.Foundations.Program.GeneralTypeIII
