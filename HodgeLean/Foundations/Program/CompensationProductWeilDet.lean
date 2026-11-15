import HodgeLean.Foundations.Program.CompensationProductDeterminant
import HodgeLean.Foundations.WeilHermitian

/-! # Orthogonal products of quadratic actions and their Hermitian determinants -/

noncomputable section
set_option maxHeartbeats 400000
open Module HodgeLean.Foundations HodgeLean.Foundations.WeilHermitian

namespace HodgeLean.Foundations.Program

variable {U V Z : Type*} [AddCommGroup U] [Module ℚ U]
  [AddCommGroup V] [Module ℚ V] [AddCommGroup Z] [Module ℚ Z] {a : ℚ}

/-- The quadratic scalar action in the type carrying a specified operator.
Source: `WeilHermitian.equiv_smul`. -/
theorem cp_withJ_smul (J : {J : Module.End ℚ U // J ∘ₗ J = a • LinearMap.id})
    (z : QuadraticAlgebra ℚ a 0) (v : WithJ U J) :
    z • v = z.re • v + z.im • (WithJ.equiv J).symm (J.1 (WithJ.equiv J v)) := by
  apply (WithJ.equiv J).injective
  simpa only [map_add, map_smul, LinearEquiv.apply_symm_apply] using equiv_smul J z v

/-- An intertwiner of product quadratic actions is linear over the quadratic algebra.
Source: restriction of scalars through `WeilHermitian.omegaHom`. -/
def cp_withJ_prodEquiv
    (JU : {J : Module.End ℚ U // J ∘ₗ J = a • LinearMap.id})
    (JV : {J : Module.End ℚ V // J ∘ₗ J = a • LinearMap.id})
    (JZ : {J : Module.End ℚ Z // J ∘ₗ J = a • LinearMap.id})
    (e : (U × V) ≃ₗ[ℚ] Z) (hJ : ∀ x, JZ.1 (e x) = e (JU.1 x.1, JV.1 x.2)) :
    (WithJ U JU × WithJ V JV) ≃ₗ[QuadraticAlgebra ℚ a 0] WithJ Z JZ where
  toAddEquiv := (((WithJ.equiv JU).prodCongr (WithJ.equiv JV)).trans
    (e.trans (WithJ.equiv JZ).symm)).toAddEquiv
  map_smul' := by
    intro z x
    apply (WithJ.equiv JZ).injective
    change e (WithJ.equiv JU (z • x.1), WithJ.equiv JV (z • x.2)) =
      WithJ.equiv JZ (z • (WithJ.equiv JZ).symm
        (e (WithJ.equiv JU x.1, WithJ.equiv JV x.2)))
    rw [equiv_smul, equiv_smul, equiv_smul, LinearEquiv.apply_symm_apply]
    change e (z.re • (WithJ.equiv JU x.1, WithJ.equiv JV x.2) +
      z.im • (JU.1 (WithJ.equiv JU x.1), JV.1 (WithJ.equiv JV x.2))) = _
    rw [map_add, map_smul, map_smul, hJ]

/-- An orthogonal rational product with compatible quadratic actions has multiplying Weil
Hermitian determinant classes.
Source: `cp_detClass_orthogonalSum`, `WeilHermitian.weilHermitian`. -/
theorem cp_weilDetClass_product [Module.Finite ℚ U] [Module.Finite ℚ V] [Module.Finite ℚ Z]
    [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)]
    (EU : LinearMap.BilinForm ℚ U) (EV : LinearMap.BilinForm ℚ V) (EZ : LinearMap.BilinForm ℚ Z)
    (JU : {J : Module.End ℚ U // J ∘ₗ J = a • LinearMap.id})
    (JV : {J : Module.End ℚ V // J ∘ₗ J = a • LinearMap.id})
    (JZ : {J : Module.End ℚ Z // J ∘ₗ J = a • LinearMap.id})
    (hRU : ∀ x y, EU (JU.1 x) y = -EU x (JU.1 y))
    (hRV : ∀ x y, EV (JV.1 x) y = -EV x (JV.1 y))
    (hRZ : ∀ x y, EZ (JZ.1 x) y = -EZ x (JZ.1 y))
    (hAU : EU.IsAlt) (hAV : EV.IsAlt) (hAZ : EZ.IsAlt)
    (hNU : EU.Nondegenerate) (hNV : EV.Nondegenerate) (hNZ : EZ.Nondegenerate)
    (e : (U × V) ≃ₗ[ℚ] Z) (hJ : ∀ x, JZ.1 (e x) = e (JU.1 x.1, JV.1 x.2))
    (hE : ∀ x y, EZ (e x) (e y) = EU x.1 y.1 + EV x.2 y.2) :
    weilDetClass EZ JZ hRZ hAZ hNZ =
      weilDetClass EU JU hRU hAU hNU * weilDetClass EV JV hRV hAV hNV := by
  unfold weilDetClass
  apply cp_detClass_orthogonalSum _ _ _ _ _ _ _ _ _ (cp_withJ_prodEquiv JU JV JZ e hJ)
  intro x y
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_add, re_weilHermitian]
    change EZ (e (WithJ.equiv JU x.1, WithJ.equiv JV x.2))
      (JZ.1 (e (WithJ.equiv JU y.1, WithJ.equiv JV y.2))) =
      EU (WithJ.equiv JU x.1) (JU.1 (WithJ.equiv JU y.1)) +
        EV (WithJ.equiv JV x.2) (JV.1 (WithJ.equiv JV y.2))
    rw [hJ, hE]
  · simp only [QuadraticAlgebra.im_add, im_weilHermitian]
    exact hE (WithJ.equiv JU x.1, WithJ.equiv JV x.2) (WithJ.equiv JU y.1, WithJ.equiv JV y.2)

end HodgeLean.Foundations.Program
