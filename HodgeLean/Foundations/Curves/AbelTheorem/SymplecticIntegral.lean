import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

noncomputable section
open Module Set
open scoped BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000

variable {M : Type*} [AddCommGroup M]

theorem integral_pair_of_basis_coordinate {ι : Type*} (b : Basis ι ℤ M) (i : ι)
    (Q : LinearMap.BilinForm ℤ M) (hQ : Function.Surjective Q) :
    ∃ y : M, Q y (b i) = 1 := by
  classical
  obtain ⟨y, hy⟩ := hQ (b.coord i)
  refine ⟨y, ?_⟩
  rw [hy]
  simp

theorem integral_alternating_skew (Q : LinearMap.BilinForm ℤ M)
    (hQ : ∀ x, Q x x = 0) (x y : M) : Q x y = -Q y x := by
  have h := hQ (x + y)
  simp only [map_add, LinearMap.add_apply, hQ] at h
  omega

theorem integral_pair_remainder_mem (Q : LinearMap.BilinForm ℤ M)
    (hQ : ∀ x, Q x x = 0) (x y : M) (hxy : Q x y = 1) (z : M) :
    z + Q y z • x - Q x z • y ∈ LinearMap.ker (Q x) ⊓ LinearMap.ker (Q y) := by
  have hyx : Q y x = -1 := by rw [integral_alternating_skew Q hQ, hxy]
  change Q x (z + Q y z • x - Q x z • y) = 0 ∧
    Q y (z + Q y z • x - Q x z • y) = 0
  constructor <;> simp only [map_sub, map_add, map_smul,
    smul_eq_mul, hQ, hxy, hyx] <;> ring

def integralPairProjection (Q : LinearMap.BilinForm ℤ M)
    (hQ : ∀ x, Q x x = 0) (x y : M) (hxy : Q x y = 1) :
    M →ₗ[ℤ] ↥(LinearMap.ker (Q x) ⊓ LinearMap.ker (Q y) : Submodule ℤ M) :=
  (LinearMap.id + (Q y).smulRight x - (Q x).smulRight y).codRestrict _
    (integral_pair_remainder_mem Q hQ x y hxy)

theorem integral_pair_projection_restrict (Q : LinearMap.BilinForm ℤ M)
    (hQ : ∀ x, Q x x = 0) (x y : M) (hxy : Q x y = 1)
    (z : ↥(LinearMap.ker (Q x) ⊓ LinearMap.ker (Q y) : Submodule ℤ M)) :
    integralPairProjection Q hQ x y hxy z.val = z := by
  apply Subtype.ext
  change z.val + Q y z.val • x - Q x z.val • y = z.val
  rw [show Q x z.val = 0 from z.property.1, show Q y z.val = 0 from z.property.2]
  simp

theorem integral_pair_complement_surjective (Q : LinearMap.BilinForm ℤ M)
    (hQ : ∀ x, Q x x = 0) (hS : Function.Surjective Q)
    (x y : M) (hxy : Q x y = 1) :
    Function.Surjective (Q.restrict
      (LinearMap.ker (Q x) ⊓ LinearMap.ker (Q y))) := by
  let K : Submodule ℤ M := LinearMap.ker (Q x) ⊓ LinearMap.ker (Q y)
  let P := integralPairProjection Q hQ x y hxy
  intro φ
  obtain ⟨z, hz⟩ := hS (φ.comp P)
  refine ⟨P z, ?_⟩
  ext t
  have he : Q z t.val = φ t := by
    have ht := LinearMap.congr_fun hz t.val
    change Q z t.val = φ (P t.val) at ht
    rw [integral_pair_projection_restrict] at ht
    exact ht
  change Q (z + Q y z • x - Q x z • y) t.val = φ t
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, show Q x t.val = 0 from t.property.1,
    show Q y t.val = 0 from t.property.2, mul_zero, add_zero, sub_zero]
  exact he

theorem integral_pair_complement_rank_lt [Module.Finite ℤ M] [Module.Free ℤ M]
    (Q : LinearMap.BilinForm ℤ M) (hQ : ∀ x, Q x x = 0)
    (x y : M) (hxy : Q x y = 1) :
    finrank ℤ (LinearMap.ker (Q x) ⊓ LinearMap.ker (Q y) : Submodule ℤ M) <
      finrank ℤ M := by
  let K : Submodule ℤ M := LinearMap.ker (Q x) ⊓ LinearMap.ker (Q y)
  have hyx : Q y x = -1 := by rw [integral_alternating_skew Q hQ, hxy]
  let f : K × ℤ →ₗ[ℤ] M :=
    K.subtype.comp (LinearMap.fst ℤ K ℤ) + (LinearMap.snd ℤ K ℤ).smulRight x
  have hf : Function.Injective f := by
    rintro ⟨u, n⟩ ⟨v, m⟩ he
    change u.val + n • x = v.val + m • x at he
    have hh := congrArg (Q y) he
    simp only [map_add, map_smul, smul_eq_mul,
      show Q y u.val = 0 from u.property.2,
      show Q y v.val = 0 from v.property.2, hyx, mul_neg, mul_one, zero_add] at hh
    have hnm : n = m := by omega
    subst m
    exact Prod.ext (Subtype.ext (add_right_cancel he)) rfl
  have hb := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_prod, Module.finrank_self] at hb
  change finrank ℤ K < finrank ℤ M
  omega

end HodgeLean.Foundations.Curves.AbelTheorem
