import HodgeLean.Foundations.Program.CompensationProductWeilDet
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # The compensation determinant for a quadratic line -/

noncomputable section
set_option maxHeartbeats 400000
open Module HodgeLean.Foundations HodgeLean.Foundations.WeilHermitian
open HodgeLean.Foundations.HermitianForm

namespace HodgeLean.Foundations.Program

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {a : ℚ}

/-- The conjugate quadratic action has the negative operator.
Source: conjugation of the generator of `QuadraticAlgebra ℚ a 0`. -/
def cp_negQuadraticOperator (J : {J : Module.End ℚ V // J ∘ₗ J = a • LinearMap.id}) :
    {J : Module.End ℚ V // J ∘ₗ J = a • LinearMap.id} :=
  ⟨-J.1, by
    ext x
    simpa only [LinearMap.comp_apply, LinearMap.neg_apply, map_neg, neg_neg,
      LinearMap.smul_apply, LinearMap.id_apply] using LinearMap.congr_fun J.2 x⟩

/-- A rank-two rational quadratic space is a line over its quadratic field.
Source: `WeilHermitian.finrank_withJ`. -/
theorem cp_quadraticLine_finrank [Module.Finite ℚ V]
    [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)]
    (hrank : Module.finrank ℚ V = 2)
    (J : {J : Module.End ℚ V // J ∘ₗ J = a • LinearMap.id}) :
    Module.finrank (QuadraticAlgebra ℚ a 0) (WithJ V J) = 1 := by
  have h := finrank_withJ J
  rw [hrank] at h
  omega

/-- A quadratic line and its conjugate with reciprocal scale have determinant class `[-m]`.
Source: the one-dimensional Gram matrices are `h` and `-h/m`; rational squares are norms. -/
theorem cp_rankTwo_compensation_class [Module.Finite ℚ V]
    [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)]
    (hrank : Module.finrank ℚ V = 2) (E : LinearMap.BilinForm ℚ V)
    (J : {J : Module.End ℚ V // J ∘ₗ J = a • LinearMap.id})
    (hR : ∀ x y, E (J.1 x) y = -E x (J.1 y)) (hAlt : E.IsAlt) (hND : E.Nondegenerate)
    (m : ℚ) (hm : m ≠ 0)
    (hRN : ∀ x y, (m⁻¹ • E) ((cp_negQuadraticOperator J).1 x) y =
      -(m⁻¹ • E) x ((cp_negQuadraticOperator J).1 y))
    (hAN : (m⁻¹ • E).IsAlt) (hNN : (m⁻¹ • E).Nondegenerate) :
    weilDetClass E J hR hAlt hND *
      weilDetClass (m⁻¹ • E) (cp_negQuadraticOperator J) hRN hAN hNN =
      ((Units.mk0 (-m) (neg_ne_zero.mpr hm) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ a 0)) := by
  classical
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℚ) (M := V) (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let vp := (WithJ.equiv J).symm v
  let vn := (WithJ.equiv (cp_negQuadraticOperator J)).symm v
  have hvp : vp ≠ 0 := by
    intro h
    exact hv (by simpa only [vp, LinearEquiv.apply_symm_apply, map_zero] using congrArg (WithJ.equiv J) h)
  have hvn : vn ≠ 0 := by
    intro h
    exact hv (by simpa only [vn, LinearEquiv.apply_symm_apply, map_zero] using congrArg (WithJ.equiv (cp_negQuadraticOperator J)) h)
  let bp := FiniteDimensional.basisSingleton Unit (cp_quadraticLine_finrank hrank J) vp hvp
  let bn := FiniteDimensional.basisSingleton Unit
    (cp_quadraticLine_finrank hrank (cp_negQuadraticOperator J)) vn hvn
  let HP := weilHermitian E J hR
  let HN := weilHermitian (m⁻¹ • E) (cp_negQuadraticOperator J) hRN
  have hgp : gramDetℚ HP bp = E v (J.1 v) := by
    simp only [gramDetℚ, gramDet, Matrix.det_unique, LinearMap.toMatrix₂_apply,
      bp, FiniteDimensional.basisSingleton_apply, HP, re_weilHermitian, vp,
      LinearEquiv.apply_symm_apply]
  have hgn : gramDetℚ HN bn = -(E v (J.1 v)) / m := by
    simp only [gramDetℚ, gramDet, Matrix.det_unique, LinearMap.toMatrix₂_apply,
      bn, FiniteDimensional.basisSingleton_apply, HN, re_weilHermitian, vn,
      LinearEquiv.apply_symm_apply]
    change m⁻¹ * E v (-J.1 v) = -(E v (J.1 v)) / m
    rw [map_neg]
    ring
  have hh : E v (J.1 v) ≠ 0 := by
    rw [← hgp]
    exact gramDetℚ_ne_zero (isSymm_weilHermitian hAlt) (nondegenerate_weilHermitian hND) bp
  unfold weilDetClass
  rw [detClass_eq _ _ bp, detClass_eq _ _ bn, ← QuotientGroup.mk_mul]
  apply mk_eq_mk_of_eq_mul (n := (Units.mk0 (E v (J.1 v) / m) (div_ne_zero hh hm)) ^ 2)
    (sq_mem_normSubgroup _)
  change gramDetℚ HP bp * gramDetℚ HN bn = (E v (J.1 v) / m) ^ 2 * (-m)
  rw [hgp, hgn]
  field_simp

/-- The compensation calculation applies to any form identified with the reciprocal multiple.
Source: `cp_rankTwo_compensation_class`. -/
theorem cp_rankTwo_compensation_class_of_eq [Module.Finite ℚ V]
    [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)]
    (hrank : Module.finrank ℚ V = 2) (E : LinearMap.BilinForm ℚ V)
    (J : {J : Module.End ℚ V // J ∘ₗ J = a • LinearMap.id})
    (hR : ∀ x y, E (J.1 x) y = -E x (J.1 y)) (hAlt : E.IsAlt) (hND : E.Nondegenerate)
    (m : ℚ) (hm : m ≠ 0) (EN : LinearMap.BilinForm ℚ V) (hEN : EN = m⁻¹ • E)
    (hRN : ∀ x y, EN ((cp_negQuadraticOperator J).1 x) y = -EN x ((cp_negQuadraticOperator J).1 y))
    (hAN : EN.IsAlt) (hNN : EN.Nondegenerate) :
    weilDetClass E J hR hAlt hND * weilDetClass EN (cp_negQuadraticOperator J) hRN hAN hNN =
      ((Units.mk0 (-m) (neg_ne_zero.mpr hm) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ a 0)) := by
  subst EN
  exact cp_rankTwo_compensation_class hrank E J hR hAlt hND m hm hRN hAN hNN


end HodgeLean.Foundations.Program
