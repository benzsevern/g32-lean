import HodgeLean.Foundations.Program.G32Native.ConormalIdealInclusionNaturality

/-! # Original equation sections before the ambient affine coordinate change -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Algebraic

/-- The original open equation retains its scalar through the typed inclusion. -/
theorem originalIdealOpenSection_typed_scalar
    {Q W : Scheme.{0}} (j : Q ⟶ W) (A : W.Opens)
    (u : RingHom.ker (j.app A).hom) :
    originalIdealOpenSection j A u ≫ conormalIdealInclusion (j ∣_ A) =
      f5sheaf_scal (X := A.toScheme) (A.topIso.inv u.val) :=
  originalIdealOpenSection_inclusion_scalar j A u

/-- Changing the source to its affine coordinates retains the original equation. -/
theorem originalIdealChartSource_scalar
    {Q W : Scheme.{0}} (j : Q ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom) :
    conormalSourceIdealSection (j ∣_ A) (hA.preimage j).isoSpec.symm
        (originalIdealOpenSection j A u) ≫
      conormalIdealInclusion ((hA.preimage j).isoSpec.inv ≫ (j ∣_ A)) =
        f5sheaf_scal (X := A.toScheme) (A.topIso.inv u.val) :=
  conormalSourceIdealSection_scalar (j ∣_ A) (hA.preimage j).isoSpec.symm
    (originalIdealOpenSection j A u) (A.topIso.inv u.val)
    (originalIdealOpenSection_typed_scalar j A u)

end HodgeLean.Foundations.TubularEuler
