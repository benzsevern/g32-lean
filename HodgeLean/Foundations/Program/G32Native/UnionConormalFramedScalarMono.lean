import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineFrames
import HodgeLean.Foundations.Program.G32Native.UnionConormalIdealGeneric
import HodgeLean.Foundations.Program.G32Native.UnionConormalTildeMono
import Mathlib.RingTheory.Localization.FractionRing

/-! # Scalar right inverses for framed affine sheaf arrows -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A generically invertible scalar right inverse makes an equally framed
associated-sheaf arrow monic over an integral affine ring. -/
lemma union_framed_tilde_mono_of_scalar_right_inverse
    (A : CommRingCat) [IsDomain A] (M N : ModuleCat A)
    (f : M ⟶ N) (g : N ⟶ M) (a : A) (ha : a ≠ 0)
    (hfg : f.hom.comp g.hom = a • (LinearMap.id : N →ₗ[A] N))
    (p : ℕ)
    (eM : tilde M ≅ (SheafOfModules.free (R := (Spec A).ringCatSheaf) (Fin p) :
      (Spec A).Modules))
    (eN : tilde N ≅ (SheafOfModules.free (R := (Spec A).ringCatSheaf) (Fin p) :
      (Spec A).Modules)) : Mono (tilde.map f) := by
  haveI := unionAffineFrame_free A M p eM
  haveI := unionAffineFrame_finite A M p eM
  haveI := unionAffineFrame_free A N p eN
  haveI := unionAffineFrame_finite A N p eN
  have hAK := IsFractionRing.injective A (FractionRing A)
  have hi : Function.Injective f.hom :=
    union_free_injective_of_generic_surjective hAK
      ((unionAffineFrame_finrank A M p eM).trans
        (unionAffineFrame_finrank A N p eN).symm) f.hom
      (union_generic_surjective_of_scalar_right_inverse f.hom g.hom a hfg
        (by simpa only [map_zero] using hAK.ne ha))
  haveI : Mono f := (ModuleCat.mono_iff_injective f).mpr hi
  exact union_tilde_map_mono (R := A) f

#print axioms union_framed_tilde_mono_of_scalar_right_inverse
end HodgeLean.Foundations.Program.G32Native
