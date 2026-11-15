import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.DualNumber

/-! # Differences of actual dual-number algebra points -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Subtract two first-order variations with the same actual residue map,
while retaining that residue map as the base component.
Source: Hartshorne, Algebraic Geometry, II.8, tangent vectors as derivations. -/
def s2e_u1_dualDifference
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (f g : A →ₐ[ℂ] DualNumber ℂ)
    (hred : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp f =
      (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp g) : A →ₐ[ℂ] DualNumber ℂ where
  toFun a := TrivSqZeroExt.inl (f a).fst + TrivSqZeroExt.inr ((f a).snd - (g a).snd)
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by
    ext <;> simp [map_add, sub_add_sub_comm]
  map_mul' a b := by
    have ha : (g a).fst = (f a).fst := (DFunLike.congr_fun hred a).symm
    have hb : (g b).fst = (f b).fst := (DFunLike.congr_fun hred b).symm
    ext <;> simp [map_mul, DualNumber.snd_mul, ha, hb] <;> ring
  commutes' r := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

/-- Point separation together with a zero stationary tangent kernel implies
separation of all actual dual-number algebra points.
Source: Hartshorne, Algebraic Geometry, II.8, linearity of tangent maps. -/
theorem s2e_u1_injective_of_stationary_dual_kernel
    {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (j : B →ₐ[ℂ] A)
    (hpoint : Function.Injective (fun e : A →ₐ[ℂ] ℂ => e.comp j))
    (hkernel : ∀ (e : A →ₐ[ℂ] ℂ) (φ : A →ₐ[ℂ] DualNumber ℂ),
      (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp φ = e →
      φ.comp j = (TrivSqZeroExt.inlAlgHom ℂ ℂ ℂ).comp (e.comp j) →
      φ = (TrivSqZeroExt.inlAlgHom ℂ ℂ ℂ).comp e) :
    Function.Injective (fun f : A →ₐ[ℂ] DualNumber ℂ => f.comp j) := by
  intro f g hfg
  have hred : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp f =
      (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp g := by
    apply hpoint
    apply AlgHom.ext
    intro b
    exact congrArg TrivSqZeroExt.fst (DFunLike.congr_fun hfg b)
  let d := s2e_u1_dualDifference f g hred
  let e := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp f
  have hdred : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp d = e := by
    ext a
    simp [d, e, s2e_u1_dualDifference]
  have hdj : d.comp j = (TrivSqZeroExt.inlAlgHom ℂ ℂ ℂ).comp (e.comp j) := by
    ext b
    · simp [d, e, s2e_u1_dualDifference]
    · have hb := DFunLike.congr_fun hfg b
      change f (j b) = g (j b) at hb
      simp [d, e, s2e_u1_dualDifference, hb]
  have hdconst := hkernel e d hdred hdj
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · exact DFunLike.congr_fun hred a
  · have ha := congrArg TrivSqZeroExt.snd (DFunLike.congr_fun hdconst a)
    have ha' : (f a).snd - (g a).snd = 0 := by
      simpa [d, e, s2e_u1_dualDifference] using ha
    exact sub_eq_zero.mp ha'

end HodgeLean.Foundations.Program
