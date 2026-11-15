import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalFrame
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineComparison
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Affine sheaf frames from the actual regular equations -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
open RingTheory.Sequence

/-- The closed immersion defined by regular equations has a rank-n
conormal sheaf frame on its quotient spectrum.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8. -/
def pairedC3AffineConormalFrame
    {A : Type} [CommRing A] {n : ℕ} (f : Fin n → A)
    (hreg : IsWeaklyRegular A (List.ofFn f)) :
    let I := Ideal.span (Set.range f)
    let B := CommRingCat.of (A ⧸ I)
    s2c_conormal (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
      (SheafOfModules.free (R := (Spec B).ringCatSheaf) (Fin n) : (Spec B).Modules) := by
  dsimp only
  let I := Ideal.span (Set.range f)
  let B := CommRingCat.of (A ⧸ I)
  let q : CommRingCat.of A ⟶ B := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let eI : (RingHom.ker q.hom) ≃ₗ[A] I :=
    LinearEquiv.ofEq _ _ (Ideal.mk_ker)
  let eT := (eI.baseChange A (A ⧸ I) _ _).trans
    ((TensorProduct.quotTensorEquivQuotSMul I I).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective)
  let eF := (pairedC3RegularConormalFrame f hreg).symm.trans
    (Finsupp.linearEquivFunOnFinite (A ⧸ I) (A ⧸ I) (Fin n)).symm
  exact unionConormalAffineComparisonTargetIso (CommRingCat.of A) B q ≪≫
    (tilde.functor B).mapIso (eT.trans eF).toModuleIso ≪≫
    tildeFinsupp (R := B) (Fin n)

#print axioms pairedC3AffineConormalFrame
end HodgeLean.Foundations.Program.G32Native
