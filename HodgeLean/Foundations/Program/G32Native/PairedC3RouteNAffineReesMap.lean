import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNAffineSchemeIdealMap
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNReesIdealTensor

/-! # The native comparison on an actual supplied affine Rees square -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- The actual affine Rees presentation gives an invertible natural
source-to-total ideal comparison. The source and target remain the
original affine schemes in the supplied cartesian square.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_conormal_affine_rees_ideal_map_isIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i'] [IsAffine W] [IsAffine W']
    (f : W' ⟶ W) (g : Q' ⟶ Q) (sq : IsPullback g i' i f)
    (u v a : Γ(W, ⊤)) (t : Γ(W', ⊤))
    (hs : Function.Surjective (eval₂RingHom f.appTop.hom t))
    (hk : RingHom.ker (eval₂RingHom f.appTop.hom t) = Ideal.span {C u - X * C v})
    (ha : u - a * v ∈ RingHom.ker i.appTop.hom)
    (hv : IsSMulRegular (Γ(W, ⊤) ⧸ RingHom.ker i.appTop.hom) v) :
    IsIso (idealPullbackMap i i' f g sq.w) := by
  letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := f.appTop.hom.toAlgebra
  have : IsAffine Q := isAffine_of_isAffineHom i
  have : IsAffine Q' := isAffine_of_isAffineHom i'
  have sqΓ : IsPullback (Spec.map g.appTop) (Spec.map i'.appTop)
      (Spec.map i.appTop) (Spec.map f.appTop) :=
    sq.of_iso Q'.isoSpec Q.isoSpec W'.isoSpec W.isoSpec
      (Scheme.isoSpec_hom_naturality g).symm
      (Scheme.isoSpec_hom_naturality i').symm
      (Scheme.isoSpec_hom_naturality i).symm
      (Scheme.isoSpec_hom_naturality f).symm
  have hp : Function.Surjective i.appTop.hom := i.app_surjective ⊤ (isAffineOpen_top W)
  have hsq : IsPullback g.appTop.op i'.appTop.op i.appTop.op f.appTop.op :=
    IsPullback.of_map_of_faithful Scheme.Spec sqΓ
  have hker : (RingHom.ker i.appTop.hom).map f.appTop.hom = RingHom.ker i'.appTop.hom :=
    pushout_kernel_eq i.appTop f.appTop g.appTop i'.appTop hsq.unop.flip hp
  let eI := (pairedC3ReesIdealTensorEquiv (RingHom.ker i.appTop.hom) u v a t hs hk ha hv).trans
    (LinearEquiv.ofEq _ _ hker)
  apply paired_conormal_affine_scheme_ideal_map_isIso i i' f g sq eI
  intro x
  dsimp only [eI]
  rw [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact paired_c3_rees_ideal_tensor_one_tmul _ u v a t hs hk ha hv x

end HodgeLean.Foundations.Program.G32Native
