import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNOriginalOpenIdealMap
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNReesIdealTensor
import HodgeLean.Foundations.Program.SchoenCycleC1AffineComapSections

/-! # The original-section Rees presentation of the native comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal HodgeLean.Foundations.Program

/-- The original chart section maps and binomial relation give the
invertible restriction of the actual source-to-total ideal comparison.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_conormal_original_rees_ideal_map_isIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) (g : Q' ⟶ Q) (sq : IsPullback g i' i f)
    (U : W.affineOpens) (V : W'.affineOpens) (hle : V.1 ≤ f ⁻¹ᵁ U.1)
    (u v a : Γ(W, U)) (t : Γ(W', V))
    (hs : Function.Surjective (eval₂RingHom (f.appLE U.1 V.1 hle).hom t))
    (hk : RingHom.ker (eval₂RingHom (f.appLE U.1 V.1 hle).hom t) =
      Ideal.span {C u - X * C v})
    (ha : u - a * v ∈ i.ker.ideal U)
    (hv : IsSMulRegular (Γ(W, U) ⧸ i.ker.ideal U) v) :
    IsIso ((Scheme.Modules.pullback V.1.ι).map (idealPullbackMap i i' f g sq.w)) := by
  letI : Algebra Γ(W, U) Γ(W', V) := (f.appLE U.1 V.1 hle).hom.toAlgebra
  have hker : i'.ker = i.ker.comap f := by
    rw [← sq.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hmap : (RingHom.ker (i.app U.1).hom).map (f.appLE U.1 V.1 hle).hom =
      RingHom.ker (i'.app V.1).hom := by
    have H := s2e_c1_affine_comap_appLE f i.ker U V hle
    rw [← hker, Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at H
    exact H.symm
  rw [Scheme.Hom.ker_apply] at ha hv
  let eI := (pairedC3ReesIdealTensorEquiv (RingHom.ker (i.app U.1).hom)
      u v a t hs hk ha hv).trans (LinearEquiv.ofEq _ _ hmap)
  apply paired_conormal_original_open_ideal_map_isIso i i' f g sq U V hle eI
  intro x
  dsimp only [eI]
  rw [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact paired_c3_rees_ideal_tensor_one_tmul _ u v a t hs hk ha hv x

#print axioms paired_conormal_original_rees_ideal_map_isIso
end HodgeLean.Foundations.Program.G32Native
