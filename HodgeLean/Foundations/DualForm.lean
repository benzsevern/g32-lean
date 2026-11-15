import HodgeLean.Foundations.Symplectic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import HodgeLean.Foundations.WeilHermitian

/-! # The dual form of a nondegenerate 2-vector, and the Rosati condition on it

Brief `f1569`, item 1.

## Setting

`K` is a field and `V` a finite-dimensional `K`-vector space. A 2-vector `ω ∈ ⋀² V` is the
alternating form `B_ω (φ, ψ) = ψ (contract ω φ)` on `V^∨` (`Symplectic.contract`); for
`ω = a ∧ b` it is `φ a ψ b - φ b ψ a`. When `ω` is nondegenerate (`contract ω : V^∨ → V`
bijective), `B_ω` is transported along `contract ω` to a nondegenerate alternating form on `V`, the
**dual form** `E_ω (x, y) = (contract ω)⁻¹ y x`.

For an abelian variety, `V = H¹(X; ℚ)`, `ω ∈ ⋀² V ≅ H²` is the polarization class, `B_ω` is the
Riemann form on `V^∨ = H₁(X; ℚ)`, and `E_ω` is the dual of the Riemann form, on `H¹`.

## Main definitions

* `Symplectic.dualForm ω hω`: the form `E_ω` on `V`.
* `Symplectic.IsRosatiSkew ω J`: `contract ω ∘ Jᵀ = - J ∘ contract ω`, i.e. `Jᵀ` is skew for the
  form `B_ω` on `V^∨`: `B_ω (Jᵀ φ, ψ) = - B_ω (φ, Jᵀ ψ)`.

## Main results

* `contract_injective`: `contract : ⋀² V → Hom (V^∨, V)` is injective.
* `contract_map`: `contract (⋀² f ω) = f ∘ contract ω ∘ fᵀ`.
* `isAlt_dualForm`, `nondegenerate_dualForm`, `dualForm_contract_contract`
  (`E_ω (contract ω φ, contract ω ψ) = B_ω (φ, ψ)`).
* `isRosatiSkew_iff_dualForm`: `IsRosatiSkew ω J` iff `J` is skew for `E_ω`.
* `map_eq_smul_iff_isRosatiSkew`: for `J² = -d`, `d ≠ 0`, `IsRosatiSkew ω J` iff
  `⋀² J ω = d • ω`.

Relation to the goal: HC no distance; AV milestone no distance; the polarization class in `⋀² H¹`
becomes the form `(V, E, J)` that `WeilHermitian` takes.
-/

open Module

namespace HodgeLean.Foundations

namespace Symplectic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Contract

/-- `φ (contract ω φ) = 0`: the form `B_ω` on `V^∨` is alternating. -/
theorem apply_contract_self (ω : ⋀[K]^2 V) (φ : Dual K V) : φ (contract ω φ) = 0 := by
  have : (φ ∘ₗ (LinearMap.applyₗ φ : (Dual K V →ₗ[K] V) →ₗ[K] V)) ∘ₗ contract =
      (0 : ⋀[K]^2 V →ₗ[K] K) := by
    ext v
    simp [mul_comm]
  simpa using LinearMap.congr_fun this ω

/-- `B_ω` is Mathlib's pairing `⋀² V^∨ × ⋀² V → K` against `φ ∧ ψ`. -/
theorem pairingDual_ιMulti_two (ω : ⋀[K]^2 V) (φ ψ : Dual K V) :
    exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 ![φ, ψ]) ω = ψ (contract ω φ) := by
  have : exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 ![φ, ψ]) =
      ψ ∘ₗ (LinearMap.applyₗ φ : (Dual K V →ₗ[K] V) →ₗ[K] V) ∘ₗ contract := by
    ext v
    simp only [LinearMap.compAlternatingMap_apply, exteriorPower.pairingDual_ιMulti_ιMulti,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.applyₗ_apply_apply, contract_ιMulti,
      map_sub, map_smul, smul_eq_mul, Matrix.det_fin_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [this]
  rfl

variable [FiniteDimensional K V]

/-- Contraction `⋀² V → Hom (V^∨, V)` is injective: a 2-vector is determined by its form `B_ω`.
The forms `φ ∧ ψ` span `⋀² V^∨`, and Mathlib's `pairingDual` identifies `⋀² V^∨` with the dual of
`⋀² V` (`exteriorPower.bijective_pairingDual`). -/
theorem contract_injective : Function.Injective (contract : ⋀[K]^2 V →ₗ[K] (Dual K V →ₗ[K] V)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ω hω
  have h2 : ∀ x : ⋀[K]^2 (Dual K V), exteriorPower.pairingDual K V 2 x ω = 0 := by
    intro x
    have hx : x ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K 2)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
      rw [hv, pairingDual_ιMulti_two, hω]
      simp
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  refine (Module.forall_dual_apply_eq_zero_iff K ω).1 fun f => ?_
  obtain ⟨x, rfl⟩ := (exteriorPower.bijective_pairingDual K V 2).2 f
  exact h2 x

omit [FiniteDimensional K V] in
/-- `contract (⋀² f ω) = f ∘ contract ω ∘ fᵀ`. -/
theorem contract_map (f : V →ₗ[K] V) (ω : ⋀[K]^2 V) :
    contract (exteriorPower.map 2 f ω) = f ∘ₗ contract ω ∘ₗ f.dualMap := by
  have : contract ∘ₗ exteriorPower.map 2 f =
      (LinearMap.llcomp K (Dual K V) V V f ∘ₗ
        (LinearMap.llcomp K (Dual K V) (Dual K V) V).flip f.dualMap) ∘ₗ contract := by
    ext v φ
    simp [LinearMap.dualMap_apply]
  exact LinearMap.congr_fun this ω

end Contract

section DualForm

/-- `contract ω` as a linear equivalence `V^∨ ≃ V`, for nondegenerate `ω`.

Source: `Symplectic.IsNondegenerate` (T1). -/
noncomputable def contractEquiv {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) : Dual K V ≃ₗ[K] V :=
  LinearEquiv.ofBijective (contract ω) hω

@[simp]
theorem contractEquiv_apply {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (φ : Dual K V) :
    contractEquiv hω φ = contract ω φ :=
  rfl

@[simp]
theorem contractEquiv_symm_contract {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (φ : Dual K V) :
    (contractEquiv hω).symm (contract ω φ) = φ :=
  (contractEquiv hω).symm_apply_apply φ

@[simp]
theorem contract_contractEquiv_symm {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (x : V) :
    contract ω ((contractEquiv hω).symm x) = x :=
  (contractEquiv hω).apply_symm_apply x

/-- **The dual form of a nondegenerate 2-vector.** `E_ω (x, y) = (contract ω)⁻¹ y x`: the form
`B_ω (φ, ψ) = ψ (contract ω φ)` on `V^∨`, transported to `V` along `contract ω : V^∨ ≃ V`
(`dualForm_contract_contract`). For `V = H¹` and `ω` a polarization class it is the dual of the
Riemann form on `H₁ = V^∨`.

Source: the dual of a nondegenerate alternating form (Bourbaki, *Algèbre*, ch. IX, §1, the form
induced on the dual by a nondegenerate form); Birkenhake–Lange, *Complex Abelian Varieties*, 2nd
ed., Grundlehren 302, Ch. 4 (the Riemann form of a polarization, on `H₁`); the formula is fixed here
and tested on `ℚ²` (`dualForm_e₀e₁`). -/
noncomputable def dualForm {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) : LinearMap.BilinForm K V :=
  ((contractEquiv hω).symm.toLinearMap).flip

theorem dualForm_apply {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (x y : V) :
    dualForm hω x y = (contractEquiv hω).symm y x :=
  rfl

/-- `E_ω (contract ω φ, contract ω ψ) = B_ω (φ, ψ) = ψ (contract ω φ)`. -/
theorem dualForm_contract_contract {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (φ ψ : Dual K V) :
    dualForm hω (contract ω φ) (contract ω ψ) = ψ (contract ω φ) := by
  rw [dualForm_apply, contractEquiv_symm_contract]

/-- `E_ω` is alternating. -/
theorem isAlt_dualForm {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) : (dualForm hω).IsAlt := by
  intro x
  obtain ⟨φ, rfl⟩ := hω.2 x
  rw [dualForm_apply, contractEquiv_symm_contract]
  exact apply_contract_self ω φ

/-- `E_ω` is nondegenerate. -/
theorem nondegenerate_dualForm {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) :
    (dualForm hω).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · refine (Module.forall_dual_apply_eq_zero_iff K x).1 fun φ => ?_
    simpa [dualForm_apply] using hx (contract ω φ)
  · refine (contractEquiv hω).symm.injective ?_
    rw [map_zero]
    ext x
    exact hy x

end DualForm

section Rosati

/-- **The Rosati condition on a 2-vector.** `contract ω ∘ Jᵀ = - (J ∘ contract ω)`: the transpose
`Jᵀ` of `J` is skew for the form `B_ω (φ, ψ) = ψ (contract ω φ)` on `V^∨`, that is
`B_ω (Jᵀ φ, ψ) = - B_ω (φ, Jᵀ ψ)` (`isRosatiSkew_iff_skew`).

For `V = H¹(X; ℚ)`, `V^∨ = H₁(X; ℚ)`, `B_ω` the Riemann form of a polarization and `J` the action
on `H¹` of an element `f ∈ End⁰(X)`, `Jᵀ` is the rational representation of `f` on `H₁`, and the
Rosati involution `f ↦ f'` is defined by `B_ω (f x, y) = B_ω (x, f' y)`. So this condition is
`f' = -f`. For `f` with `f² = -d`, `d > 0`, generating an imaginary quadratic field `ℚ(f)`, the
Rosati involution restricted to `ℚ(f)` is complex conjugation exactly when `f' = -f`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §5.1 (the Rosati
involution) and Ch. 4 (the Riemann form); van Geemen, *An introduction to the Hodge conjecture for
abelian varieties*, LNM 1594 (1994), §5 (the compatibility of the polarization with the
`ℚ(√-d)`-action). -/
def IsRosatiSkew (ω : ⋀[K]^2 V) (J : V →ₗ[K] V) : Prop :=
  contract ω ∘ₗ J.dualMap = -(J ∘ₗ contract ω)

/-- `IsRosatiSkew ω J` says `Jᵀ` is skew for `B_ω`. -/
theorem isRosatiSkew_iff_skew (ω : ⋀[K]^2 V) (J : V →ₗ[K] V) :
    IsRosatiSkew ω J ↔
      ∀ φ ψ : Dual K V, ψ (contract ω (J.dualMap φ)) = -(J.dualMap ψ) (contract ω φ) := by
  constructor
  · intro h φ ψ
    rw [← LinearMap.comp_apply (contract ω), h]
    simp [LinearMap.dualMap_apply]
  · intro h
    ext φ
    simp only [LinearMap.comp_apply, LinearMap.neg_apply]
    refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff K
      (contract ω (J.dualMap φ) - -J (contract ω φ))).1 fun ψ => ?_)
    rw [map_sub, h, map_neg]
    simp [LinearMap.dualMap_apply]

/-- **The Rosati condition on `ω` is skewness of `J` for the dual form.** For nondegenerate `ω`,
`IsRosatiSkew ω J` iff `E_ω (J x, y) = - E_ω (x, J y)` for all `x, y ∈ V`. -/
theorem isRosatiSkew_iff_dualForm {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (J : V →ₗ[K] V) :
    IsRosatiSkew ω J ↔ ∀ x y, dualForm hω (J x) y = -dualForm hω x (J y) := by
  set e := contractEquiv hω
  -- `J` skew for `E_ω` says `Jᵀ ∘ e⁻¹ = - e⁻¹ ∘ J`.
  have key : (∀ x y, dualForm hω (J x) y = -dualForm hω x (J y)) ↔
      ∀ y, J.dualMap (e.symm y) = -e.symm (J y) := by
    constructor
    · intro h y
      ext x
      simpa [dualForm_apply, LinearMap.dualMap_apply] using h x y
    · intro h x y
      have := LinearMap.congr_fun (h y) x
      simpa [dualForm_apply, LinearMap.dualMap_apply] using this
  rw [key]
  constructor
  · intro h y
    apply e.injective
    have := LinearMap.congr_fun h (e.symm y)
    simp only [LinearMap.comp_apply, LinearMap.neg_apply] at this
    rw [map_neg]
    simpa [e] using this
  · intro h
    ext φ
    have := congrArg e (h (e φ))
    simp only [LinearEquiv.symm_apply_apply, map_neg, LinearEquiv.apply_symm_apply] at this
    simpa [e] using this

/-- **The Rosati condition as an equation in `⋀² V`.** If `J ∘ J = -d` with `d ≠ 0`, then
`IsRosatiSkew ω J` iff `⋀² J ω = d • ω`. For `d = 3` (an action of `ℚ(√-3)`) this is
`⋀² J ω = 3 ω`: the class `ω` is `J`-semi-invariant with multiplier `Nm(√-3) = 3`. Nondegeneracy of
`ω` is not needed. -/
theorem map_eq_smul_iff_isRosatiSkew [FiniteDimensional K V] {d : K} (hd : d ≠ 0) {J : V →ₗ[K] V}
    (hJ : J ∘ₗ J = -d • LinearMap.id) (ω : ⋀[K]^2 V) :
    exteriorPower.map 2 J ω = d • ω ↔ IsRosatiSkew ω J := by
  rw [← contract_injective.eq_iff, contract_map, map_smul, IsRosatiSkew]
  have hJx : ∀ x, J (J x) = -d • x := fun x => by
    simpa using LinearMap.congr_fun hJ x
  constructor
  · intro h
    ext φ
    have h1 := congrArg J (LinearMap.congr_fun h φ)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, hJx, map_smul] at h1
    simp only [LinearMap.comp_apply, LinearMap.neg_apply]
    apply smul_right_injective V hd
    simp only [smul_neg]
    rw [← h1, neg_smul, neg_neg]
  · intro h
    rw [h]
    ext φ
    simp [hJx]

end Rosati

end Symplectic

end HodgeLean.Foundations

namespace HodgeLean.Foundations

namespace Symplectic

section Examples

/-! ### Example: `ω = e₀ ∧ e₁` on `ℚ²`

`contract ω φ = φ e₀ • e₁ - φ e₁ • e₀`, so `contract ω e₀^* = e₁` and `contract ω (-e₁^*) = e₀`.
Its dual form is the standard symplectic form `x₀ y₁ - x₁ y₀`, which is `WeilHermitian.exE`
(`dualForm_e₀e₁`). With `J = WeilHermitian.exJ` (`J² = -3`) the Rosati condition holds, and
`⋀² J ω = 3 ω` (`map_exJ_e₀e₁`). -/

/-- `e₀ ∧ e₁ ∈ ⋀² ℚ²`.

Source: explicit example, constructed here. -/
noncomputable def e₀e₁ : ⋀[ℚ]^2 (Fin 2 → ℚ) :=
  exteriorPower.ιMulti ℚ 2 ![Pi.single 0 1, Pi.single 1 1]

theorem contract_e₀e₁ (φ : Dual ℚ (Fin 2 → ℚ)) :
    contract e₀e₁ φ = φ (Pi.single 0 1) • Pi.single 1 1 - φ (Pi.single 1 1) • Pi.single 0 1 := by
  simp [e₀e₁]

theorem isNondegenerate_e₀e₁ : IsNondegenerate e₀e₁ := by
  have hsurj : Function.Surjective (contract e₀e₁) := by
    intro x
    refine ⟨x 1 • LinearMap.proj 0 - x 0 • LinearMap.proj 1, ?_⟩
    rw [contract_e₀e₁]
    ext i
    fin_cases i <;> simp
  refine ⟨?_, hsurj⟩
  rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank] at hsurj
  rw [Subspace.dual_finrank_eq]

theorem dualForm_e₀e₁ : dualForm isNondegenerate_e₀e₁ = WeilHermitian.exE := by
  refine LinearMap.ext₂ fun x y => ?_
  obtain ⟨φ, rfl⟩ := isNondegenerate_e₀e₁.2 y
  rw [dualForm_apply, contractEquiv_symm_contract, WeilHermitian.exE_apply, contract_e₀e₁]
  have hx : x = x 0 • (Pi.single 0 1 : Fin 2 → ℚ) + x 1 • Pi.single 1 1 := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hx]
  simp

/-- `J = exJ` satisfies the Rosati condition for `ω = e₀ ∧ e₁`: its dual form is `exE`, for which
`exJ` is skew (`WeilHermitian.exE_skew`). -/
theorem isRosatiSkew_e₀e₁ : IsRosatiSkew e₀e₁ WeilHermitian.exJ :=
  (isRosatiSkew_iff_dualForm isNondegenerate_e₀e₁ _).2 (by
    rw [dualForm_e₀e₁]; exact WeilHermitian.exE_skew)

/-- `⋀² J (e₀ ∧ e₁) = 3 (e₀ ∧ e₁)` for `J = exJ`. -/
theorem map_exJ_e₀e₁ : exteriorPower.map 2 WeilHermitian.exJ e₀e₁ = (3 : ℚ) • e₀e₁ :=
  (map_eq_smul_iff_isRosatiSkew (by norm_num) (by exact WeilHermitian.exJ'.2) e₀e₁).2
    isRosatiSkew_e₀e₁

/-- Falsification: `J = id` (with `J² = 1 = -(-1)`) is not Rosati-skew for `e₀ ∧ e₁`, since
`⋀² id ω = ω ≠ -ω`. -/
example : ¬ IsRosatiSkew e₀e₁ (LinearMap.id : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) := by
  intro h
  have := congrFun (LinearMap.congr_fun h (LinearMap.proj 0)) 1
  simp [contract_e₀e₁] at this
  norm_num at this

end Examples

end Symplectic

end HodgeLean.Foundations
