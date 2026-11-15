import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNSurjectiveIdeal
import HodgeLean.Foundations.Program.G32Native.PairedC3PolynomialSliceRelation
import HodgeLean.Foundations.AlgebraicGeometry.ConormalFlatIdeal

/-! # Original ideal tensors on a supplied Rees chart -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial AlgebraicGeometry.Conormal
open scoped TensorProduct
open TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The original ideal tensor is its actual image on the supplied Rees
chart. The coefficient map need not be flat.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
def pairedC3ReesIdealTensorEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (u v a : A) (t : B)
    (hs : Function.Surjective (eval₂RingHom (algebraMap A B) t))
    (hk : RingHom.ker (eval₂RingHom (algebraMap A B) t) = Ideal.span {C u - X * C v})
    (ha : u - a * v ∈ I) (hv : IsSMulRegular (A ⧸ I) v) :
    (B ⊗[A] I) ≃ₗ[B] I.map (algebraMap A B) := by
  let P := A[X]
  letI : Algebra P B := (eval₂RingHom (algebraMap A B) t).toAlgebra
  letI : IsScalarTower A P B := IsScalarTower.of_algebraMap_eq (by
    intro c
    exact (eval₂_C _ _).symm)
  let K : Ideal P := I.map (algebraMap A P)
  let e₀ := idealExtensionEquiv (S := P) I
  let e₁ := pairedC3SurjectiveIdealBaseChange hs K (C u - X * C v) hk
    (paired_c3_polynomial_slice_relation_regular I u v a ha hv)
  have he : K.map (algebraMap P B) = I.map (algebraMap A B) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A P B]
  exact ((AlgebraTensorModule.cancelBaseChange A P B B I).symm.trans
    ((e₀.baseChange P B _ _).trans e₁)).trans (LinearEquiv.ofEq _ _ he)

/-- The supplied-chart tensor isomorphism keeps the original coefficient
image of each original ideal element. -/
theorem paired_c3_rees_ideal_tensor_one_tmul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (u v a : A) (t : B)
    (hs : Function.Surjective (eval₂RingHom (algebraMap A B) t))
    (hk : RingHom.ker (eval₂RingHom (algebraMap A B) t) = Ideal.span {C u - X * C v})
    (ha : u - a * v ∈ I) (hv : IsSMulRegular (A ⧸ I) v) (x : I) :
    (pairedC3ReesIdealTensorEquiv I u v a t hs hk ha hv (1 ⊗ₜ[A] x)).val =
      algebraMap A B x.val := by
  simp only [pairedC3ReesIdealTensorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.baseChange_tmul, paired_c3_surjective_ideal_baseChange_one_tmul]
  change (eval₂RingHom (algebraMap A B) t)
    ((idealExtensionEquiv (S := A[X]) I (1 ⊗ₜ[A] x)).val) = algebraMap A B x.val
  change (eval₂RingHom (algebraMap A B) t) ((1 : A[X]) * C x.val) = _
  rw [one_mul]
  exact eval₂_C _ _

end HodgeLean.Foundations.Program.G32Native
