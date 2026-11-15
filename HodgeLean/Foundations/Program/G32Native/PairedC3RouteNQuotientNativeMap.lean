import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNAffineIdealMap
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNQuotientIdeal
import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineQuotient

/-! # The natural nonflat ideal comparison for a principal quotient -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- A relation regular on the original slice gives an invertible natural
ideal comparison on the actual affine quotient square, without requiring
flatness of the ambient quotient map.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8. -/
theorem paired_conormal_principal_quotient_ideal_map_isIso
    {A : Type} [CommRing A] (I : Ideal A) (r : A)
    (hr : IsSMulRegular (A ⧸ I) r) :
    let S := A ⧸ Ideal.span {r}
    IsIso (Conormal.idealPullbackMap
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap A S)))))
      (Spec.map (CommRingCat.ofHom (algebraMap A S)))
      (Conormal.quotientBaseChangeMap (S := S) I)
      (Conormal.quotientBaseChangeMap_square (S := S) I)) := by
  dsimp only
  let S := A ⧸ Ideal.span {r}
  let p := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap A S)))
  let k := CommRingCat.ofHom
    (Ideal.quotientMap (I.map (algebraMap A S)) (algebraMap A S) Ideal.le_comap_map)
  have h := paired_conormal_affine_ideal_map_isIso
    (CommRingCat.of (A ⧸ I)) (CommRingCat.of (S ⧸ I.map (algebraMap A S))) p q k
    (Conormal.quotientBaseChangeMap_square (S := S) I)
  simp only [p, q, CommRingCat.hom_ofHom] at h
  erw [Ideal.mk_ker, Ideal.mk_ker] at h
  exact h (pairedC3QuotientIdealBaseChange I r hr) (by
    intro x
    exact congrArg Subtype.val (paired_c3_quotient_ideal_baseChange_one_tmul I r hr x))

end HodgeLean.Foundations.Program.G32Native
