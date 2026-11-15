import HodgeLean.Foundations.HermitianForm
import Mathlib.Analysis.Real.Sqrt

/-! # The Hermitian form of a Weil-type polarized space

Foundations target T4 (`docs/roadmap/foundations.md` §4 T4), run 1.

## Setting

`V` is a rational vector space, `d : ℚ`, `J : V →ₗ[ℚ] V` with `J ∘ₗ J = -d • id`, and
`E : LinearMap.BilinForm ℚ V` an alternating form for which `J` is skew:
`E (J x) y = - E x (J y)` (equivalently `E (J x) (J y) = d · E x y`, `isSkew_iff`). In the
`K`-module sections `J` is bundled with its relation as `J : {J // J ∘ₗ J = a • id}`, `a = -d`,
and `K = QuadraticAlgebra ℚ a 0 = ℚ(ω)`, `ω² = a`; `K` is a field when `a` is not a square
(`Fact (∀ r, r ^ 2 ≠ a + 0 * r)`, inferred from `Fact (¬ IsSquare a)`), in particular for `d > 0`.

## Main definitions

* `WeilHermitian.WithJ V J`: `V` as a `K`-vector space, `ω` acting as `J`.
* `WeilHermitian.weilHermitian E J hskew`: the Hermitian form `h x y = E x (J y) + ω · E x y`.
* `WeilHermitian.weilDetClass E J …`: its determinant class (T3's `detClass`) in `ℚˣ ⧸ Nm(Kˣ)`.

## Main results

* `isSkew_iff`: `J` skew for `E` iff `E (J x) (J y) = d · E x y`, for `d ≠ 0`.
* `finrank_withJ`: `2 · dim_K V = dim_ℚ V`.
* `isSymm_weilHermitian`, `nondegenerate_weilHermitian`, `re_weilHermitian`, `im_weilHermitian`.
* `weilDetClass_smul`: `weilDetClass (c • E) = [c] ^ dim_K V · weilDetClass E`, so the class does
  not depend on the normalization of `E` in even `K`-dimension (`weilDetClass_smul_of_even`), and
  does in odd `K`-dimension (`weilDetClass_two_exE_ne`, over `ℚ(√-3)`).
* `hermSignature_weilHermitian`: for a complex structure `I` on `ℝ ⊗ V` commuting with `J` with
  `E(x, I x) > 0`, the signature is `(½ dim ker (J - √d I), ½ dim ker (J + √d I))`, the real form
  of `(dim (V_s ∩ H^{1,0}), dim (V_{s̄} ∩ H^{1,0}))`.

Relation to the goal: HC no distance; AV milestone no distance; F-1569's datum becomes a predicate
on `(V, E, J)`.
-/

open Module

namespace HodgeLean.Foundations

namespace WeilHermitian

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

section Skew

/-- `J ∘ₗ J = -d • id`, pointwise. -/
theorem apply_apply_of_comp {d : ℚ} {J : V →ₗ[ℚ] V} (hJ : J ∘ₗ J = -d • LinearMap.id) (x : V) :
    J (J x) = -d • x := by
  simpa using LinearMap.congr_fun hJ x

/-- The two forms of the compatibility between `J` and `E`. If `J ∘ₗ J = -d` then `J` is skew for
`E` (`E (J x) y = - E x (J y)`) iff `E (J x) (J y) = d · E x y` (the Rosati form). The forward
direction holds for every `d`; the backward one needs `d ≠ 0`, and nothing about `E`.

Source: the compatibility of a polarization with an action of an imaginary quadratic field,
van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, LNM 1594 (1994), §5
(Weil classes); the equivalence of the two forms is proved here. -/
theorem isSkew_iff {d : ℚ} (hd : d ≠ 0) {J : V →ₗ[ℚ] V} (hJ : J ∘ₗ J = -d • LinearMap.id)
    (E : LinearMap.BilinForm ℚ V) :
    (∀ x y, E (J x) y = -E x (J y)) ↔ ∀ x y, E (J x) (J y) = d * E x y := by
  constructor
  · intro h x y
    rw [h, apply_apply_of_comp hJ, map_smul, smul_eq_mul]
    ring
  · intro h x y
    have := h x (J y)
    rw [apply_apply_of_comp hJ, map_smul, smul_eq_mul] at this
    apply mul_left_cancel₀ hd
    linear_combination -this

end Skew

section Module

/-- The type synonym of `V` on which `J` acts as the generator `ω` of `K = ℚ(ω)`, `ω² = a`.
Here `J` is an endomorphism bundled with the proof `J ∘ₗ J = a • id` (the subtype that
`QuadraticAlgebra.lift` takes), so that `a`, hence `K = QuadraticAlgebra ℚ a 0`, can be read off
from the type of `J`.

Choice (T4 item 2): a type synonym, not a `def` of a `Module` structure. A `Module K V` instance on
`V` itself would sit next to the given `Module ℚ V`, and a non-instance `def` would force `letI`
into every statement. On `WithJ V J` the `ℚ`-structure is copied from `V`, the `K`-structure is an
instance, and `IsScalarTower ℚ K (WithJ V J)` holds. `WithJ.equiv J : WithJ V J ≃ₗ[ℚ] V` moves
between the two.

Source: restriction of scalars along `ℚ[J] ≅ ℚ(√a)`, as in van Geemen, LNM 1594, §5 (an action
of an imaginary quadratic field on `H¹(A, ℚ)` makes it a `K`-vector space). -/
@[nolint unusedArguments]
def WithJ (V : Type*) [AddCommGroup V] [Module ℚ V] {a : ℚ}
    (_J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id}) : Type _ := V

variable {a : ℚ} (J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id})

instance : AddCommGroup (WithJ V J) := inferInstanceAs (AddCommGroup V)

instance : Module ℚ (WithJ V J) := inferInstanceAs (Module ℚ V)

/-- The identity of `V`, as a `ℚ`-linear equivalence `WithJ V J ≃ₗ[ℚ] V`.

Source: the type synonym `WithJ`, defined here. -/
def WithJ.equiv : WithJ V J ≃ₗ[ℚ] V := LinearEquiv.refl ℚ V

example (x : V) : WithJ.equiv J ((WithJ.equiv J).symm x) = x := rfl

instance WithJ.instFiniteDimensional [FiniteDimensional ℚ V] : FiniteDimensional ℚ (WithJ V J) :=
  inferInstanceAs (FiniteDimensional ℚ V)

/-- `J (J x) = a • x`. -/
theorem apply_apply (x : V) : J.1 (J.1 x) = a • x := by
  simpa using LinearMap.congr_fun J.2 x

/-- The `ℚ`-algebra map `ℚ(ω) → End V`, `x + y ω ↦ x + y J`.

Source: `QuadraticAlgebra.lift`. -/
noncomputable def omegaHom : QuadraticAlgebra ℚ a 0 →ₐ[ℚ] Module.End ℚ V :=
  QuadraticAlgebra.lift ⟨J, by rw [Module.End.mul_eq_comp, J.2, zero_smul, add_zero]; rfl⟩

theorem omegaHom_apply (z : QuadraticAlgebra ℚ a 0) (x : V) :
    omegaHom J z x = z.re • x + z.im • J.1 x := by
  simp [omegaHom]

/-- `omegaHom` sends `ω` to `J`. -/
example : omegaHom J QuadraticAlgebra.omega = J := by
  ext x
  simp [omegaHom_apply]

/-- The `K`-module structure on `WithJ V J`: `(x + y ω) • v = x • v + y • J v`.

Source: restriction of scalars along `omegaHom`, as for `WithJ`. -/
noncomputable instance WithJ.instModule : Module (QuadraticAlgebra ℚ a 0) (WithJ V J) :=
  Module.compHom V (omegaHom J).toRingHom

/-- The action of `z = x + y ω` on `WithJ V J` is `x + y J`. -/
theorem equiv_smul (z : QuadraticAlgebra ℚ a 0) (v : WithJ V J) :
    WithJ.equiv J (z • v) = z.re • WithJ.equiv J v + z.im • J.1 (WithJ.equiv J v) :=
  omegaHom_apply J z v

/-- `ω` acts as `J`. -/
theorem equiv_omega_smul (v : WithJ V J) :
    WithJ.equiv J ((QuadraticAlgebra.omega : QuadraticAlgebra ℚ a 0) • v) =
      J.1 (WithJ.equiv J v) := by
  simp [equiv_smul]

instance WithJ.instIsScalarTower : IsScalarTower ℚ (QuadraticAlgebra ℚ a 0) (WithJ V J) :=
  ⟨fun q z v ↦ (WithJ.equiv J).injective <| by
    simp only [equiv_smul, map_smul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul,
      smul_add, smul_eq_mul, mul_smul]⟩

instance WithJ.instModuleFinite [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)] [FiniteDimensional ℚ V] :
    Module.Finite (QuadraticAlgebra ℚ a 0) (WithJ V J) :=
  Module.Finite.of_restrictScalars_finite ℚ _ _

/-- `dim_ℚ V = 2 dim_K V`. -/
theorem finrank_withJ [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)] [FiniteDimensional ℚ V] :
    2 * finrank (QuadraticAlgebra ℚ a 0) (WithJ V J) = finrank ℚ V := by
  rw [← QuadraticAlgebra.finrank_eq_two a 0, Module.finrank_mul_finrank,
    (WithJ.equiv J).finrank_eq]

end Module

section Form

open QuadraticAlgebra

variable (E : LinearMap.BilinForm ℚ V) {a : ℚ} (J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id})

/-- The Weil-type Hermitian form of `(E, J)`: `h x y = E x (J y) + ω · E x y`, with values in
`K = ℚ(ω)`, `ω² = a` (`a = -d`). With `J` skew for `E`, it is conjugate-linear in the first
argument and linear in the second (`weilHermitian_omega_smul_left`,
`weilHermitian_omega_smul_right`), Hermitian if `E` is alternating (`isSymm_weilHermitian`) and
nondegenerate if `E` is (`nondegenerate_weilHermitian`). Its coordinates are
`re (h x y) = E x (J y)` and `im (h x y) = E x y` (`re_weilHermitian`, `im_weilHermitian`):
`E` is exactly the `ω`-coefficient, with sign `+`.

Source: the Hermitian form attached to a polarization and an imaginary quadratic action,
van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, LNM 1594 (1994),
§5; the normalization `E(x, Jy) + ω E(x, y)` is fixed here and tested on the examples below. -/
noncomputable def weilHermitian (hskew : ∀ x y, E (J.1 x) y = -E x (J.1 y)) :
    WithJ V J →ₗ⋆[QuadraticAlgebra ℚ a 0] WithJ V J →ₗ[QuadraticAlgebra ℚ a 0]
      QuadraticAlgebra ℚ a 0 :=
  LinearMap.mk₂'ₛₗ (starRingEnd _) (RingHom.id _)
    (fun x y ↦
      ⟨E (WithJ.equiv J x) (J.1 (WithJ.equiv J y)), E (WithJ.equiv J x) (WithJ.equiv J y)⟩)
    (fun x x' y ↦ by ext <;> simp)
    (fun c x y ↦ by
      ext <;> simp [equiv_smul, hskew, apply_apply, starRingEnd_apply]
      ring)
    (fun x y y' ↦ by ext <;> simp)
    (fun c x y ↦ by
      ext <;> simp [equiv_smul, apply_apply]
      ring)

variable {E J} {hskew : ∀ x y, E (J.1 x) y = -E x (J.1 y)}

@[simp]
theorem re_weilHermitian (x y : WithJ V J) :
    (weilHermitian E J hskew x y).re = E (WithJ.equiv J x) (J.1 (WithJ.equiv J y)) := rfl

@[simp]
theorem im_weilHermitian (x y : WithJ V J) :
    (weilHermitian E J hskew x y).im = E (WithJ.equiv J x) (WithJ.equiv J y) := rfl

/-- `h x y = E x (J y) + ω · E x y`. -/
theorem weilHermitian_apply (x y : WithJ V J) :
    weilHermitian E J hskew x y =
      algebraMap ℚ _ (E (WithJ.equiv J x) (J.1 (WithJ.equiv J y))) +
        omega * algebraMap ℚ _ (E (WithJ.equiv J x) (WithJ.equiv J y)) := by
  ext <;> simp

/-- `h (ω x) y = ω̄ · h x y`: conjugate-linear in the first argument. -/
theorem weilHermitian_omega_smul_left (x y : WithJ V J) :
    weilHermitian E J hskew ((omega : QuadraticAlgebra ℚ a 0) • x) y =
      star omega * weilHermitian E J hskew x y := by
  rw [LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul]

/-- `h x (ω y) = ω · h x y`: linear in the second argument. -/
theorem weilHermitian_omega_smul_right (x y : WithJ V J) :
    weilHermitian E J hskew x ((omega : QuadraticAlgebra ℚ a 0) • y) =
      omega * weilHermitian E J hskew x y := by
  rw [map_smul, smul_eq_mul]

/-- `h y x = star (h x y)`: for `E` alternating, `weilHermitian E J` is Hermitian. -/
theorem isSymm_weilHermitian (hE : E.IsAlt) : (weilHermitian E J hskew).IsSymm := by
  refine LinearMap.isSymm_def.2 fun x y ↦ ?_
  have h1 := LinearMap.BilinForm.IsAlt.neg_eq hE (WithJ.equiv J x) (WithJ.equiv J y)
  have h2 := LinearMap.BilinForm.IsAlt.neg_eq hE (J.1 (WithJ.equiv J x)) (WithJ.equiv J y)
  ext <;> simp [starRingEnd_apply] <;> linarith [hskew (WithJ.equiv J x) (WithJ.equiv J y)]

/-- For `E` nondegenerate, `weilHermitian E J` is nondegenerate (`E` is its `ω`-coefficient). -/
theorem nondegenerate_weilHermitian (hnd : E.Nondegenerate) :
    (weilHermitian E J hskew).Nondegenerate := by
  refine ⟨fun x hx ↦ (WithJ.equiv J).injective ?_, fun y hy ↦ (WithJ.equiv J).injective ?_⟩
  · rw [map_zero]
    refine hnd.1 _ fun v ↦ ?_
    simpa using congrArg QuadraticAlgebra.im (hx ((WithJ.equiv J).symm v))
  · rw [map_zero]
    refine hnd.2 _ fun v ↦ ?_
    simpa using congrArg QuadraticAlgebra.im (hy ((WithJ.equiv J).symm v))

end Form

section Scale

variable {E : LinearMap.BilinForm ℚ V} {a : ℚ} {J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id}}

/-- `J` stays skew for `c • E`. -/
theorem skew_smul (c : ℚ) (hskew : ∀ x y, E (J.1 x) y = -E x (J.1 y)) :
    ∀ x y, (c • E) (J.1 x) y = -(c • E) x (J.1 y) := fun x y ↦ by
  simp [hskew]

/-- `c • E` is alternating if `E` is. -/
theorem isAlt_smul (c : ℚ) (hE : E.IsAlt) : (c • E).IsAlt := fun x ↦ by
  simp [hE.self_eq_zero x]

/-- `c • E` is nondegenerate if `E` is and `c ≠ 0`. -/
theorem nondegenerate_smul {c : ℚ} (hc : c ≠ 0) (hnd : E.Nondegenerate) :
    (c • E).Nondegenerate :=
  ⟨fun x hx ↦ hnd.1 x fun y ↦ by simpa [hc] using hx y,
    fun y hy ↦ hnd.2 y fun x ↦ by simpa [hc] using hy x⟩

/-- Scaling `E` by `c ∈ ℚ` scales the Hermitian form by `c`. -/
theorem weilHermitian_smul (c : ℚ) (hskew : ∀ x y, E (J.1 x) y = -E x (J.1 y)) :
    weilHermitian (c • E) J (skew_smul c hskew) =
      algebraMap ℚ (QuadraticAlgebra ℚ a 0) c • weilHermitian E J hskew := by
  refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
  ext <;> simp

end Scale

section Class

open HermitianForm

variable {E : LinearMap.BilinForm ℚ V} {a : ℚ} {J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id}}
  [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)] [FiniteDimensional ℚ V]

variable (E J) in
/-- The determinant class of the Weil-type Hermitian form of `(E, J)`, in `ℚˣ ⧸ Nm(Kˣ)`
(`K = ℚ(ω)`, `ω² = a`, a field because `a` is not a square). F-1569's family
`M = (3, ℚ(√−3), [−2])` is the predicate `finrank K (WithJ V J) = 6 ∧ weilDetClass E J … = [−2]`
(with signature `(3, 3)`, i.e. Weil type) on a polarized Weil-type package `(V, E, J)` with
`a = -3`: an abelian sixfold has `dim_ℚ H¹ = 12`, so `dim_K = 6`, and the `3` in `M` is half of
that. At `dim_K = 6` the class does not depend on rescaling `E` by `ℚ^×`
(`weilDetClass_smul_of_even`), on replacing `J` by `−J` (the form becomes `−conj h`, changing the
class by `[−1]^6`; not formalized here), or on using the dual form (`[δ⁻¹] = [δ]`). In odd
`K`-dimension it does depend on the scale of `E` (`weilDetClass_two_exE_ne`).

Relation to the goal: HC no distance; AV milestone no distance; F-1569's datum becomes a predicate
on `(V, E, J)`.

Source: the determinant (discriminant) of the Hermitian form of a Weil-type abelian variety,
van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, LNM 1594 (1994),
§5; `detClass` is T3's (`HodgeLean.Foundations.HermitianForm.detClass`). -/
noncomputable def weilDetClass (hskew : ∀ x y, E (J.1 x) y = -E x (J.1 y)) (hE : E.IsAlt)
    (hnd : E.Nondegenerate) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ a 0) :=
  detClass (weilHermitian E J hskew) (isSymm_weilHermitian hE) (nondegenerate_weilHermitian hnd)

/-- Scaling `E` by `c ∈ ℚˣ` multiplies the class by `[c] ^ n`, `n = dim_K V`. For `c = -1` this
is `detClass_neg`'s `[-1] ^ n`. -/
theorem weilDetClass_smul (c : ℚˣ) (hskew : ∀ x y, E (J.1 x) y = -E x (J.1 y)) (hE : E.IsAlt)
    (hnd : E.Nondegenerate) :
    weilDetClass ((c : ℚ) • E) J (skew_smul c hskew) (isAlt_smul c hE)
        (nondegenerate_smul c.ne_zero hnd) =
      ((c ^ finrank (QuadraticAlgebra ℚ a 0) (WithJ V J) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ a 0)) * weilDetClass E J hskew hE hnd := by
  rw [weilDetClass, weilDetClass, detClass, detClass, ← QuotientGroup.mk_mul]
  congr 1
  ext
  simp only [Units.val_mk0, Units.val_mul, Units.val_pow_eq_pow_val]
  rw [gramDetℚ, gramDetℚ, gramDet, gramDet, weilHermitian_smul c hskew, map_smul, Matrix.det_smul,
    Fintype.card_fin, ← map_pow, re_algebraMap_mul]

/-- Normalization is harmless in even `K`-dimension: replacing `E` by `c • E`, `c ∈ ℚˣ`, does not
change the class when `dim_K V` is even, since `c ^ n` is then a square, hence a norm. -/
theorem weilDetClass_smul_of_even (c : ℚˣ)
    (heven : Even (finrank (QuadraticAlgebra ℚ a 0) (WithJ V J)))
    (hskew : ∀ x y, E (J.1 x) y = -E x (J.1 y)) (hE : E.IsAlt) (hnd : E.Nondegenerate) :
    weilDetClass ((c : ℚ) • E) J (skew_smul c hskew) (isAlt_smul c hE)
        (nondegenerate_smul c.ne_zero hnd) = weilDetClass E J hskew hE hnd := by
  rw [weilDetClass_smul c hskew hE hnd, mul_eq_right, QuotientGroup.eq_one_iff]
  obtain ⟨k, hk⟩ := heven
  rw [hk, ← two_mul, pow_mul']
  exact sq_mem_normSubgroup _

end Class

section Examples

/-! ### Examples over `K = ℚ(√-3) = QuadraticAlgebra ℚ (-3) 0` (`ω² = -3`)

**`K`-dimension 1.** `V = ℚ²`, `J = [[0, -3], [1, 0]]`, so `J e₀ = e₁`, `J e₁ = -3 e₀` and
`J² = -3`. `E(x, y) = x₀ y₁ - x₁ y₀`. Skewness by hand: `J x = (-3 x₁, x₀)`, so
`E(J x, y) = -3 x₁ y₁ - x₀ y₀` and `E(x, J y) = x₀ y₀ + 3 x₁ y₁`, opposite. As a `K`-space,
`V = K · e₀` (`(u + v ω) • e₀ = u e₀ + v e₁`), so `{e₀}` is a `K`-basis. Then
`h(e₀, e₀) = E(e₀, J e₀) + ω E(e₀, e₀) = E(e₀, e₁) + 0 = 1`, the Gram determinant is `1`, and
`weilDetClass E J = [1]` (`weilDetClass_exE`). For `2 E` the Gram determinant is `2`, so the class
is `[2]` (`weilDetClass_two_exE`), and `[2] ≠ [1]` because `x² + 3 y² = 2` has no rational
solution (T3's `class_two_ne_one`): in odd `K`-dimension the normalization of `E` matters
(`weilDetClass_two_exE_ne`).

**`K`-dimension 2.** `V = ℚ⁴ = ℚ² ⊕ ℚ²` with `J` and `E` block-diagonal copies of the above. The
`K`-basis `{e₀, e₂}` has `h(e₀, e₀) = h(e₂, e₂) = 1`, `h(e₀, e₂) = E(e₀, e₃) + ω E(e₀, e₂) = 0`;
for `2 E` the Gram determinant is `4 = Nm(2)`, and the class does not change
(`weilDetClass_two_exE₄`, from `weilDetClass_smul_of_even`).
-/

open HermitianForm QuadraticAlgebra

/-- `J = [[0, -3], [1, 0]]` on `ℚ²`: `J (x₀, x₁) = (-3 x₁, x₀)`.

Source: explicit example, constructed here. -/
def exJ : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun x := ![-3 * x 1, x 0]
  map_add' x y := by ext i; fin_cases i <;> simp; ring
  map_smul' c x := by ext i; fin_cases i <;> simp; ring

theorem exJ_apply (x : Fin 2 → ℚ) : exJ x = ![-3 * x 1, x 0] := rfl

example : exJ ![1, 0] = ![0, 1] := by ext i; fin_cases i <;> simp [exJ_apply]

/-- `J² = -3`, bundled.

Source: explicit example, constructed here. -/
def exJ' : {J : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id} :=
  ⟨exJ, LinearMap.ext fun x ↦ by ext i; fin_cases i <;> simp [exJ_apply]⟩

/-- The standard symplectic form `E(x, y) = x₀ y₁ - x₁ y₀` on `ℚ²`.

Source: explicit example, constructed here. -/
def exE : LinearMap.BilinForm ℚ (Fin 2 → ℚ) :=
  LinearMap.mk₂ ℚ (fun x y ↦ x 0 * y 1 - x 1 * y 0)
    (fun _ _ _ ↦ by simp; ring) (fun _ _ _ ↦ by simp; ring)
    (fun _ _ _ ↦ by simp; ring) (fun _ _ _ ↦ by simp; ring)

theorem exE_apply (x y : Fin 2 → ℚ) : exE x y = x 0 * y 1 - x 1 * y 0 := rfl

example : exE ![1, 0] ![0, 1] = 1 := by simp [exE_apply]

theorem exE_skew : ∀ x y, exE (exJ'.1 x) y = -exE x (exJ'.1 y) := fun x y ↦ by
  simp [exE_apply, exJ', exJ_apply]; ring

theorem exE_isAlt : exE.IsAlt := fun x ↦ by simp [exE_apply]; ring

theorem exE_nondegenerate : exE.Nondegenerate := by
  refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · have h0 := hx ![0, 1]
    have h1 := hx ![1, 0]
    simp [exE_apply] at h0 h1
    ext i; fin_cases i <;> simp [h0, h1]
  · have h0 := hy ![0, 1]
    have h1 := hy ![1, 0]
    simp [exE_apply] at h0 h1
    ext i; fin_cases i <;> simp [h0, h1]

/-- `J` is also `E`-skew in the Rosati form: `E (J x) (J y) = 3 E x y` (`isSkew_iff`). -/
example : ∀ x y, exE (exJ x) (exJ y) = 3 * exE x y :=
  (isSkew_iff (by norm_num : (3 : ℚ) ≠ 0) exJ'.2 exE).1 exE_skew

/-- `e₀` spans `WithJ ℚ² J` over `K`: `(u + v ω) • e₀ = (u, v)`. -/
theorem exSmul (x : Fin 2 → ℚ) :
    (⟨x 0, x 1⟩ : QuadraticAlgebra ℚ (-3) 0) • (WithJ.equiv exJ').symm ![1, 0] =
      (WithJ.equiv exJ').symm x := by
  apply (WithJ.equiv exJ').injective
  rw [equiv_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  ext i; fin_cases i <;> simp [exJ', exJ_apply]

/-- The `K`-basis `{e₀}` of `WithJ ℚ² J`.

Source: explicit example, constructed here. -/
noncomputable def exBasis : Basis (Fin 1) (QuadraticAlgebra ℚ (-3) 0) (WithJ (Fin 2 → ℚ) exJ') :=
  Basis.mk (v := fun _ ↦ (WithJ.equiv exJ').symm ![1, 0])
    (linearIndependent_unique_iff.2 fun h ↦ by
      simpa using congrFun (congrArg (WithJ.equiv exJ') h) 0)
    (fun x _ ↦ by
      rw [Set.range_const, Submodule.mem_span_singleton]
      exact ⟨_, exSmul (WithJ.equiv exJ' x)⟩)

theorem equiv_exBasis (i : Fin 1) : WithJ.equiv exJ' (exBasis i) = ![1, 0] := by
  simp [exBasis]

/-- `h(e₀, e₀) = 1`. -/
theorem weilHermitian_exE_e₀ :
    weilHermitian exE exJ' exE_skew (exBasis 0) (exBasis 0) = 1 := by
  ext
  · rw [re_weilHermitian, equiv_exBasis]
    simp [exE_apply, exJ', exJ_apply]
  · rw [im_weilHermitian, equiv_exBasis]
    simp [exE_apply]

/-- The class of the standard example is `[1]`. -/
theorem weilDetClass_exE :
    weilDetClass exE exJ' exE_skew exE_isAlt exE_nondegenerate = 1 := by
  rw [weilDetClass, detClass_eq _ _ exBasis, QuotientGroup.eq_one_iff]
  convert (normSubgroup (QuadraticAlgebra ℚ (-3) 0)).one_mem
  ext
  simp [gramDetℚ, gramDet, Matrix.det_unique, LinearMap.toMatrix₂_apply, weilHermitian_exE_e₀]

example : exJ'.1 = exJ := rfl

example : WithJ.equiv exJ' (exBasis 0) = ![1, 0] := equiv_exBasis 0

example : weilHermitian exE exJ' exE_skew (exBasis 0) (exBasis 0) = 1 := weilHermitian_exE_e₀

example : weilDetClass exE exJ' exE_skew exE_isAlt exE_nondegenerate = 1 := weilDetClass_exE

/-- `dim_K (WithJ ℚ² J) = 1`. -/
theorem finrank_exJ : finrank (QuadraticAlgebra ℚ (-3) 0) (WithJ (Fin 2 → ℚ) exJ') = 1 := by
  have := finrank_withJ exJ'
  rw [Module.finrank_fin_fun] at this
  omega

/-- For `2 E` the class is `[2]`. -/
theorem weilDetClass_two_exE :
    weilDetClass ((2 : ℚ) • exE) exJ' (skew_smul 2 exE_skew) (isAlt_smul 2 exE_isAlt)
        (nondegenerate_smul two_ne_zero exE_nondegenerate) =
      ((Units.mk0 (2 : ℚ) two_ne_zero : ℚˣ) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  have := weilDetClass_smul (Units.mk0 (2 : ℚ) two_ne_zero) exE_skew exE_isAlt exE_nondegenerate
  rw [finrank_exJ, pow_one, weilDetClass_exE, mul_one] at this
  exact this

/-- Falsification: in odd `K`-dimension, replacing `E` by `2 E` changes the class. -/
theorem weilDetClass_two_exE_ne :
    weilDetClass ((2 : ℚ) • exE) exJ' (skew_smul 2 exE_skew) (isAlt_smul 2 exE_isAlt)
        (nondegenerate_smul two_ne_zero exE_nondegenerate) ≠
      weilDetClass exE exJ' exE_skew exE_isAlt exE_nondegenerate := by
  rw [weilDetClass_two_exE, weilDetClass_exE]
  exact class_two_ne_one

/-- `J₄ = J ⊕ J` on `ℚ⁴ = ℚ² ⊕ ℚ²`.

Source: explicit example, constructed here. -/
def exJ₄ : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) where
  toFun x := ![-3 * x 1, x 0, -3 * x 3, x 2]
  map_add' x y := by ext i; (fin_cases i <;> simp) <;> ring
  map_smul' c x := by ext i; (fin_cases i <;> simp) <;> ring

/-- `J₄² = -3`, bundled.

Source: explicit example, constructed here. -/
def exJ₄' : {J : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id} :=
  ⟨exJ₄, LinearMap.ext fun x ↦ by ext i; fin_cases i <;> simp [exJ₄]⟩

example : exJ₄'.1 = exJ₄ := rfl

example : exJ₄ ![1, 0, 0, 0] = ![0, 1, 0, 0] := by ext i; fin_cases i <;> simp [exJ₄]

/-- `E₄ = E ⊕ E` on `ℚ⁴`: `E₄(x, y) = x₀ y₁ - x₁ y₀ + x₂ y₃ - x₃ y₂`.

Source: explicit example, constructed here. -/
def exE₄ : LinearMap.BilinForm ℚ (Fin 4 → ℚ) :=
  LinearMap.mk₂ ℚ (fun x y ↦ x 0 * y 1 - x 1 * y 0 + (x 2 * y 3 - x 3 * y 2))
    (fun _ _ _ ↦ by simp; ring) (fun _ _ _ ↦ by simp; ring)
    (fun _ _ _ ↦ by simp; ring) (fun _ _ _ ↦ by simp; ring)

theorem exE₄_apply (x y : Fin 4 → ℚ) :
    exE₄ x y = x 0 * y 1 - x 1 * y 0 + (x 2 * y 3 - x 3 * y 2) := rfl

example : exE₄ ![0, 0, 1, 0] ![0, 0, 0, 1] = 1 := by simp [exE₄_apply]

theorem exE₄_skew : ∀ x y, exE₄ (exJ₄'.1 x) y = -exE₄ x (exJ₄'.1 y) := fun x y ↦ by
  simp [exE₄_apply, exJ₄', exJ₄]; ring

theorem exE₄_isAlt : exE₄.IsAlt := fun x ↦ by simp [exE₄_apply]; ring

theorem exE₄_nondegenerate : exE₄.Nondegenerate := by
  refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · have h0 := hx ![0, 1, 0, 0]
    have h1 := hx ![1, 0, 0, 0]
    have h2 := hx ![0, 0, 0, 1]
    have h3 := hx ![0, 0, 1, 0]
    simp [exE₄_apply] at h0 h1 h2 h3
    ext i; fin_cases i <;> simp [h0, h1, h2, h3]
  · have h0 := hy ![0, 1, 0, 0]
    have h1 := hy ![1, 0, 0, 0]
    have h2 := hy ![0, 0, 0, 1]
    have h3 := hy ![0, 0, 1, 0]
    simp [exE₄_apply] at h0 h1 h2 h3
    ext i; fin_cases i <;> simp [h0, h1, h2, h3]

/-- `dim_K (WithJ ℚ⁴ J₄) = 2`. -/
theorem finrank_exJ₄ : finrank (QuadraticAlgebra ℚ (-3) 0) (WithJ (Fin 4 → ℚ) exJ₄') = 2 := by
  have := finrank_withJ exJ₄'
  rw [Module.finrank_fin_fun] at this
  omega

/-- In `K`-dimension 2, replacing `E₄` by `2 E₄` does not change the class. -/
theorem weilDetClass_two_exE₄ :
    weilDetClass ((2 : ℚ) • exE₄) exJ₄' (skew_smul 2 exE₄_skew) (isAlt_smul 2 exE₄_isAlt)
        (nondegenerate_smul two_ne_zero exE₄_nondegenerate) =
      weilDetClass exE₄ exJ₄' exE₄_skew exE₄_isAlt exE₄_nondegenerate :=
  weilDetClass_smul_of_even (Units.mk0 (2 : ℚ) two_ne_zero) (by rw [finrank_exJ₄]; decide)
    exE₄_skew exE₄_isAlt exE₄_nondegenerate

end Examples

section Signature

open QuadraticMap QuadraticForm TensorProduct

/-- Sylvester's law of inertia, the form used here: if `M = P ⊕ N` with `Q` positive definite on
`P` and negative definite on `N`, then `sigPos Q = dim P` and `sigNeg Q = dim N`. -/
theorem sigPos_sigNeg_of_isCompl {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] {Q : QuadraticForm ℝ M} {P N : Submodule ℝ M} (hPN : IsCompl P N)
    (hP : ∀ x ∈ P, x ≠ 0 → 0 < Q x) (hN : ∀ x ∈ N, x ≠ 0 → Q x < 0) :
    sigPos Q = finrank ℝ P ∧ sigNeg Q = finrank ℝ N := by
  have hdim := Submodule.finrank_add_eq_of_isCompl hPN
  have h1 : finrank ℝ P ≤ sigPos Q :=
    le_sigPos_of_posDef Q fun x hx ↦ hP x x.2 (by simpa using hx)
  have h2 : sigPos Q + finrank ℝ N ≤ finrank ℝ M := sigPos_add_finrank_le_of_nonpos fun x hx ↦ by
    by_cases h0 : x = 0
    · simp [h0]
    · exact (hN x hx h0).le
  have h3 : finrank ℝ N ≤ sigNeg Q :=
    le_sigNeg_of_negDef Q fun x hx ↦ by
      simpa using hN x x.2 (by simpa using hx)
  have h4 : sigNeg Q + finrank ℝ P ≤ finrank ℝ M := by
    rw [← sigPos_neg]
    refine sigPos_add_finrank_le_of_nonpos fun x hx ↦ ?_
    by_cases h0 : x = 0
    · simp [h0]
    · simpa using (hP x hx h0).le
  omega

/-- The signature of `x ↦ B x (J x)` for a complex structure `I` commuting with `J`,
`J² = -s²`, `s > 0`, and `B x (I x) > 0`: it is `(dim ker (J - s I), dim ker (J + s I))`. The two
kernels are complementary: `2 s x = (s x - I J x) + (s x + I J x)`. -/
theorem sig_compl₂_of_complexStructure {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (B : LinearMap.BilinForm ℝ M) (I J : M →ₗ[ℝ] M) {s : ℝ}
    (hs : 0 < s) (hJ : ∀ x, J (J x) = -(s * s) • x) (hI : ∀ x, I (I x) = -x)
    (hIJ : ∀ x, I (J x) = J (I x)) (hpos : ∀ x, x ≠ 0 → 0 < B x (I x)) :
    sigPos (LinearMap.BilinMap.toQuadraticMap (B.compl₂ J)) = finrank ℝ (LinearMap.ker (J - s • I)) ∧
      sigNeg (LinearMap.BilinMap.toQuadraticMap (B.compl₂ J)) = finrank ℝ (LinearMap.ker (J + s • I)) := by
  have hs0 : s ≠ 0 := hs.ne'
  refine sigPos_sigNeg_of_isCompl ⟨?_, ?_⟩ (fun x hx h0 ↦ ?_) (fun x hx h0 ↦ ?_)
  · refine Submodule.disjoint_def.2 fun x hP hN ↦ ?_
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply] at hP hN
    have h2 : (s + s) • I x = 0 := by rw [add_smul]; linear_combination (norm := module) hN - hP
    have hIx : I x = 0 := (smul_eq_zero.1 h2).resolve_left (by positivity)
    rw [← neg_neg x, ← hI x, hIx, map_zero, neg_zero]
  · refine codisjoint_iff.2 (eq_top_iff.2 fun x _ ↦ ?_)
    have h2 : (s + s) • x = (s • x - I (J x)) + (s • x + I (J x)) := by module
    refine (Submodule.smul_mem_iff _ (by positivity : s + s ≠ 0)).1 ?_
    rw [h2]
    refine Submodule.add_mem_sup ?_ ?_
    · simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, map_sub,
        map_smul, ← hIJ, hJ, hI]
      module
    · simp only [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.smul_apply, map_add,
        map_smul, ← hIJ, hJ, hI]
      module
  · simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at hx
    simp only [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.compl₂_apply, hx, map_smul,
      smul_eq_mul]
    exact mul_pos hs (hpos x h0)
  · simp only [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.smul_apply,
      add_eq_zero_iff_eq_neg] at hx
    simp only [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.compl₂_apply, hx, map_neg,
      map_smul, smul_eq_mul]
    have := mul_pos hs (hpos x h0)
    linarith

variable {d : ℚ} {E : LinearMap.BilinForm ℚ V}
  {J : {J : V →ₗ[ℚ] V // J ∘ₗ J = -d • LinearMap.id}}

/-- The real quadratic form of `weilHermitian E J` is `x ↦ E_ℝ(x, J_ℝ x)`, transported along
`WithJ V J ≃ V`. -/
theorem baseChange_hermQuadForm_weilHermitian (hskew : ∀ x y, E (J.1 x) y = -E x (J.1 y)) :
    (HermitianForm.hermQuadForm (weilHermitian E J hskew)).baseChange ℝ =
      (LinearMap.BilinMap.toQuadraticMap ((E.baseChange ℝ).compl₂ (J.1.baseChange ℝ))).comp
        ((WithJ.equiv J).baseChange ℚ ℝ _ _).toLinearMap :=
  baseChange_ext fun m ↦ by
    simp [HermitianForm.hermQuadForm_apply]

/-- **The signature of the Weil-type Hermitian form** (T4 item 6). Let `I` be a complex structure
on `V_ℝ = ℝ ⊗ V` commuting with `J` and with `E_ℝ(x, I x) > 0` for `x ≠ 0`. Then
`hermSignature (weilHermitian E J) = (½ dim_ℝ V₊, ½ dim_ℝ V₋)` with
`V₊ = ker (J - √d I)` and `V₋ = ker (J + √d I)`.

Dictionary with the eigenspace statement: `V₊` with the complex structure `I` is isomorphic to
`V_s ∩ H^{1,0}` by `x ↦ x - i I x`, where `H^{1,0}` is the `i`-eigenspace of `I` on `V_ℂ` and
`V_s` the eigenspace on which `ω` acts by `s(ω) = i √d`; likewise `V₋ ≅ V_{s̄} ∩ H^{1,0}`
(proof: for `x ∈ V₊` and `v = x - i I x`, `I v = i v` and `J v = i √d v`). So this is
`(r, s) = (dim (V_s ∩ H^{1,0}), dim (V_{s̄} ∩ H^{1,0}))`, and `r = s` is `IsWeilType`. The
dictionary itself is not formalized here. The invariance `E(I x, I y) = E(x, y)` is not needed.
With the opposite convention `E(x, I x) < 0` (equivalently `E(I x, x) > 0`, as for a Riemann form
on `H₁` in Birkenhake–Lange) the ordered signature is reversed, `(r, s) ↦ (s, r)`; whether `r = s`
(`IsWeilType`) is unaffected.

Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, LNM 1594
(1994), §5 (the signature of the Hermitian form of a Weil-type polarized abelian variety); proved
here from Sylvester's law of inertia (Mathlib's `sigPos_add_finrank_le_of_nonpos`). -/
theorem hermSignature_weilHermitian [FiniteDimensional ℚ V] (hd : 0 < d)
    (hskew : ∀ x y, E (J.1 x) y = -E x (J.1 y))
    (I : ℝ ⊗[ℚ] V →ₗ[ℝ] ℝ ⊗[ℚ] V) (hI : ∀ x, I (I x) = -x)
    (hIJ : ∀ x, I (J.1.baseChange ℝ x) = J.1.baseChange ℝ (I x))
    (hpos : ∀ x, x ≠ 0 → 0 < E.baseChange ℝ x (I x)) :
    HermitianForm.hermSignature (weilHermitian E J hskew) =
      (finrank ℝ (LinearMap.ker (J.1.baseChange ℝ - √(d : ℝ) • I)) / 2,
        finrank ℝ (LinearMap.ker (J.1.baseChange ℝ + √(d : ℝ) • I)) / 2) := by
  have hs : 0 < √(d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hJ : ∀ x, J.1.baseChange ℝ (J.1.baseChange ℝ x) = -(√(d : ℝ) * √(d : ℝ)) • x := by
    intro x
    rw [Real.mul_self_sqrt (by exact_mod_cast hd.le)]
    induction x with
    | tmul r v =>
      simp only [LinearMap.baseChange_tmul]
      rw [apply_apply J v, TensorProduct.tmul_smul, ← algebraMap_smul ℝ (-d), map_neg,
        eq_ratCast]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  obtain ⟨hpos', hneg'⟩ := sig_compl₂_of_complexStructure (E.baseChange ℝ) I (J.1.baseChange ℝ) hs
    hJ hI hIJ hpos
  let e : (HermitianForm.hermQuadForm (weilHermitian E J hskew)).baseChange ℝ |>.IsometryEquiv
      (LinearMap.BilinMap.toQuadraticMap ((E.baseChange ℝ).compl₂ (J.1.baseChange ℝ))) :=
    { (WithJ.equiv J).baseChange ℚ ℝ _ _ with
      map_app' := fun x ↦ by rw [baseChange_hermQuadForm_weilHermitian]; rfl }
  rw [HermitianForm.hermSignature, (Equivalent.sigPos_eq ⟨e⟩), (Equivalent.sigNeg_eq ⟨e⟩),
    hpos', hneg']

end Signature

end WeilHermitian

end HodgeLean.Foundations
