import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
import Mathlib.LinearAlgebra.Determinant

/-! # The top power of a nondegenerate 2-vector

Foundations target T1 (`docs/roadmap/foundations.md` §4 T1, §6 Rank 3).

## Setting

`K` is a field and `V` a `K`-vector space. Only the converse (nonvanishing implies
nondegenerate) assumes `V` finite-dimensional, and the nonvanishing theorems assume `CharZero K`. A 2-vector is an element `ω` of `⋀[K]^2 V`.

## Main definitions

* `Symplectic.contract ω : Dual K V →ₗ[K] V`: contraction of `ω` with a linear form,
  `contract (a ∧ b) φ = φ a • b - φ b • a`.
* `Symplectic.IsNondegenerate ω`: `contract ω` is bijective.
* `Symplectic.wedgePow ω g : ⋀[K]^(2 * g) V`: the `g`-fold wedge power of `ω`, by the same
  recursion as Blocks' `polarizationPow`.
* `Symplectic.sympVec e f = Σᵢ eᵢ ∧ fᵢ`, and `Symplectic.interleave e f`, the family
  `e₀, f₀, e₁, f₁, …`.

## Main results

* `Symplectic.commute_of_even`, `Symplectic.wedge_comm_of_even`: wedges of even degree commute.
* `Symplectic.coe_wedgePow`: `wedgePow ω g` is `ω ^ g` in the exterior algebra.
* `Symplectic.wedgePow_sympVec`: `(Σᵢ eᵢ ∧ fᵢ)^g = g! • (e₀ ∧ f₀ ∧ ⋯)`, for any vectors;
  `Symplectic.wedgePow_sympVec_eq_zero`: higher powers vanish.
* `Symplectic.exists_sympVec_linearIndependent`: every 2-vector is `Σ eᵢ ∧ fᵢ` with the `eᵢ, fᵢ`
  linearly independent.
* `Symplectic.exists_basis_sympVec_of_isNondegenerate` (Darboux): a nondegenerate `ω` is
  `Σ eᵢ ∧ fᵢ` for a basis `e, f` (indexed by `Fin g ⊕ Fin g`), and `finrank V = 2g`;
  `Symplectic.isNondegenerate_sympVec_basis` is the converse.
* `Symplectic.isNondegenerate_iff_wedgePow_ne_zero`: for `finrank V = 2g` and `CharZero K`,
  `ω` is nondegenerate iff `wedgePow ω g ≠ 0`.

Relation to the goal: HC no distance; AV milestone no distance; `PolarizationTopPowerNonzero` is
replaced by nondegeneracy of the polarization (`HodgeLean.Adapters.Polarization`).
-/

open Module

namespace HodgeLean.Foundations

namespace Symplectic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Contract

/-- The alternating map `(a, b) ↦ (φ ↦ φ a • b - φ b • a)` behind `contract`.

Source: Bourbaki, *Algebra I*, Ch. III (interior products). -/
def contractAlt : V [⋀^Fin 2]→ₗ[K] (Dual K V →ₗ[K] V) where
  toFun v := (Dual.eval K V (v 0)).smulRight (v 1) - (Dual.eval K V (v 1)).smulRight (v 0)
  map_update_add' m i x y := by
    ext φ
    fin_cases i <;> simp <;> module
  map_update_smul' m i c x := by
    ext φ
    fin_cases i <;> simp <;> module
  map_eq_zero_of_eq' v i j hv hij := by
    ext φ
    fin_cases i <;> fin_cases j <;> simp_all

/-- Contraction of a 2-vector with a linear form: the linear map `⋀² V → Hom(V^∨, V)` with
`contract (a ∧ b) φ = φ a • b - φ b • a` (`contract_ιMulti`). Up to the sign convention, this is the
interior product `φ ⌟ ω` of a linear form with a 2-vector.

Source: Bourbaki, *Algebra I*, Ch. III (interior products). -/
noncomputable def contract : ⋀[K]^2 V →ₗ[K] (Dual K V →ₗ[K] V) :=
  exteriorPower.alternatingMapLinearEquiv contractAlt

@[simp]
theorem contract_ιMulti (v : Fin 2 → V) (φ : Dual K V) :
    contract (exteriorPower.ιMulti K 2 v) φ = φ (v 0) • v 1 - φ (v 1) • v 0 := by
  simp [contract, contractAlt]

/-- `contractAlt (e₁, e₂)` sends the second coordinate form to `-e₁`. -/
example : contractAlt ![(Pi.single 0 1 : Fin 2 → ℚ), Pi.single 1 1]
    (LinearMap.proj 1 : Dual ℚ (Fin 2 → ℚ)) = -Pi.single 0 1 := by
  simp [contractAlt]

/-- `contract (e₁ ∧ e₂)` sends the first coordinate form to `e₂`. -/
example : contract (exteriorPower.ιMulti ℚ 2 ![Pi.single 0 1, Pi.single 1 1])
    (LinearMap.proj 0 : Dual ℚ (Fin 2 → ℚ)) = Pi.single 1 1 := by
  simp

/-- A 2-vector `ω` is nondegenerate when `contract ω : V^∨ → V` is bijective. This is the
nondegeneracy of `ω`, seen as the alternating bilinear form `(φ, ψ) ↦ ψ (contract ω φ)` on `V^∨`.
It is **not** Mathlib's perfectness of `exteriorPower.wedgePairing`, which is a statement about
the pairing `⋀^k V × ⋀^(n-k) V → K` and holds for every finite free `V`.

Source: Bourbaki, *Algebra I*, Ch. III (interior products), and Bourbaki, *Algèbre*, ch. IX
(formes sesquilinéaires et formes quadratiques: alternating forms). -/
def IsNondegenerate (ω : ⋀[K]^2 V) : Prop :=
  Function.Bijective (contract ω)

end Contract

section WedgePow

/-- Casting an element of `⋀[K]^m V` along `m = n` does not change it in the exterior algebra. -/
theorem coe_cast {m n : ℕ} (h : m = n) (x : ⋀[K]^m V) :
    ((h ▸ x : ⋀[K]^n V) : ExteriorAlgebra K V) = x := by
  subst h
  rfl

/-- `exteriorPower.wedge` is the product of the exterior algebra. -/
theorem coe_wedge {m n : ℕ} (x : ⋀[K]^m V) (y : ⋀[K]^n V) :
    (exteriorPower.wedge K V m n x y : ExteriorAlgebra K V) = x * y := by
  simp [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul]

/-- The `g`-fold wedge power `ω ∧ ⋯ ∧ ω` of a 2-vector, with the canonical unit of `⋀⁰ V` as its
zeroth power. The recursion is exactly that of `HodgeBlocks.polarizationPow`.

Source: Bourbaki, *Algebra I*, Ch. III (the exterior algebra). -/
noncomputable def wedgePow (ω : ⋀[K]^2 V) : ∀ g : ℕ, ⋀[K]^(2 * g) V
  | 0 => exteriorPower.ιMulti K 0 Fin.elim0
  | g + 1 =>
      have h : 2 * g + 2 = 2 * (g + 1) := by ring
      h ▸ exteriorPower.wedge K V (2 * g) 2 (wedgePow ω g) ω

/-- In the exterior algebra, `wedgePow ω g` is `ω ^ g`. -/
theorem coe_wedgePow (ω : ⋀[K]^2 V) (g : ℕ) :
    (wedgePow ω g : ExteriorAlgebra K V) = (ω : ExteriorAlgebra K V) ^ g := by
  induction g with
  | zero => simp [wedgePow]
  | succ g ih =>
    rw [wedgePow]
    change (exteriorPower.wedge K V (2 * g) 2 (wedgePow ω g) ω : ExteriorAlgebra K V) = _
    rw [coe_wedge, ih, pow_succ]

theorem wedgePow_zero (ω : ⋀[K]^2 V) :
    wedgePow ω 0 = exteriorPower.ιMulti K 0 Fin.elim0 :=
  rfl

theorem wedgePow_one (ω : ⋀[K]^2 V) : wedgePow ω 1 = ω :=
  Subtype.ext (by rw [coe_wedgePow, pow_one])

/-- `wedgePow ω g = 0` exactly when `ω ^ g = 0` in the exterior algebra. -/
theorem wedgePow_eq_zero_iff (ω : ⋀[K]^2 V) (g : ℕ) :
    wedgePow ω g = 0 ↔ (ω : ExteriorAlgebra K V) ^ g = 0 := by
  rw [← coe_wedgePow, ZeroMemClass.coe_eq_zero]

/-- Elements of even degree commute in the exterior algebra. -/
theorem commute_of_even {a b : ℕ} (x : ⋀[K]^(2 * a) V) (y : ⋀[K]^(2 * b) V) :
    Commute (x : ExteriorAlgebra K V) y := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  simp only
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      rw [Commute, SemiconjBy, ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm]
      have : ((-1 : ℤˣ) ^ (2 * b * (2 * a))) = 1 := by
        rw [show 2 * b * (2 * a) = 2 * (2 * a * b) by ring, pow_mul]
        simp
      rw [this, one_smul]
    | zero => exact Commute.zero_right _
    | add y z _ _ h₁ h₂ => exact h₁.add_right h₂
    | smul c y _ h => exact h.smul_right c
  | zero => exact Commute.zero_left _
  | add x z _ _ h₁ h₂ => exact h₁.add_left h₂
  | smul c x _ h => exact h.smul_left c

/-- Even-degree wedges commute: `x ∧ y = y ∧ x` for `x ∈ ⋀^(2a)`, `y ∈ ⋀^(2b)`, through the cast
`2a + 2b = 2b + 2a`. -/
theorem wedge_comm_of_even {a b : ℕ} (x : ⋀[K]^(2 * a) V) (y : ⋀[K]^(2 * b) V) :
    (Nat.add_comm (2 * a) (2 * b) ▸ exteriorPower.wedge K V (2 * a) (2 * b) x y :
        ⋀[K]^(2 * b + 2 * a) V) =
      exteriorPower.wedge K V (2 * b) (2 * a) y x := by
  apply Subtype.ext
  rw [coe_cast, coe_wedge, coe_wedge]
  exact commute_of_even x y

/-- Two 2-vectors commute in the exterior algebra. -/
theorem commute_two (x y : ⋀[K]^2 V) : Commute (x : ExteriorAlgebra K V) y :=
  commute_of_even (a := 1) (b := 1) x y

/-- `(e₁ ∧ e₂) ∧ (e₃ ∧ e₄) = (e₃ ∧ e₄) ∧ (e₁ ∧ e₂)` in `⋀⁴ ℚ⁴`. -/
example :
    exteriorPower.wedge ℚ (Fin 4 → ℚ) 2 2
        (exteriorPower.ιMulti ℚ 2 ![Pi.single 0 1, Pi.single 1 1])
        (exteriorPower.ιMulti ℚ 2 ![Pi.single 2 1, Pi.single 3 1]) =
      exteriorPower.wedge ℚ (Fin 4 → ℚ) 2 2
        (exteriorPower.ιMulti ℚ 2 ![Pi.single 2 1, Pi.single 3 1])
        (exteriorPower.ιMulti ℚ 2 ![Pi.single 0 1, Pi.single 1 1]) :=
  wedge_comm_of_even (a := 1) (b := 1) _ _

/-- The first wedge power of `e₁ ∧ e₂` is itself. -/
example : wedgePow (exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 2 → ℚ), Pi.single 1 1]) 1 =
    exteriorPower.ιMulti ℚ 2 ![Pi.single 0 1, Pi.single 1 1] :=
  wedgePow_one _

end WedgePow

section Expansion

/-- The index map `Fin (2 * g) → Fin g ⊕ Fin g` behind `interleave`: `2i ↦ inl i`, `2i+1 ↦ inr i`.
It orders a symplectic basis as `e₁, f₁, …, e_g, f_g`.

Source: Lang, *Algebra*, Ch. XV (alternating forms: the symplectic basis). -/
def interleaveIdx (g : ℕ) (i : Fin (2 * g)) : Fin g ⊕ Fin g :=
  if (i : ℕ) % 2 = 0 then .inl ⟨i / 2, by omega⟩ else .inr ⟨i / 2, by omega⟩

example : interleaveIdx 2 3 = .inr 1 := by decide

theorem interleaveIdx_injective (g : ℕ) : Function.Injective (interleaveIdx g) := by
  intro i j h
  unfold interleaveIdx at h
  split_ifs at h with hi hj hj <;> simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq] at h <;> ext <;> omega

/-- The interleaved family `e₀, f₀, e₁, f₁, …, e_{g-1}, f_{g-1}` of `2g` vectors.

Source: Lang, *Algebra*, Ch. XV (alternating forms: the symplectic basis). -/
def interleave {g : ℕ} (e f : Fin g → V) : Fin (2 * g) → V :=
  Sum.elim e f ∘ interleaveIdx g

example : interleave ![(1 : ℚ), 2] ![3, 4] = ![1, 3, 2, 4] := by
  ext i
  fin_cases i <;> rfl

/-- The 2-vector `Σᵢ eᵢ ∧ fᵢ` of two families `e, f : Fin g → V`; for a basis `e, f` it is the
standard symplectic 2-vector.

Source: Bourbaki, *Algebra I*, Ch. III (exterior algebra); Lang, *Algebra*, Ch. XV
(alternating forms: the symplectic basis). -/
noncomputable def sympVec {g : ℕ} (e f : Fin g → V) : ⋀[K]^2 V :=
  ∑ i, exteriorPower.ιMulti K 2 ![e i, f i]

example (a b : V) : sympVec (K := K) ![a] ![b] = exteriorPower.ιMulti K 2 ![a, b] := by
  simp [sympVec]

theorem coe_ιMulti_two (a b : V) :
    (exteriorPower.ιMulti K 2 ![a, b] : ExteriorAlgebra K V) =
      ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K b := by
  simp [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]

theorem ιMulti_two_mul_self (a b : V) :
    (exteriorPower.ιMulti K 2 ![a, b] : ExteriorAlgebra K V) *
      (exteriorPower.ιMulti K 2 ![a, b] : ExteriorAlgebra K V) = 0 := by
  rw [coe_ιMulti_two]
  have h := ExteriorAlgebra.ι_add_mul_swap (R := K) b a
  calc ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K b * (ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K b)
      = ExteriorAlgebra.ι K a * (ExteriorAlgebra.ι K b * ExteriorAlgebra.ι K a +
          ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K b) * ExteriorAlgebra.ι K b -
        ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K a *
          (ExteriorAlgebra.ι K b * ExteriorAlgebra.ι K b) := by
        simp only [mul_add, add_mul, mul_assoc]
        abel
    _ = 0 := by rw [h, ExteriorAlgebra.ι_sq_zero, ExteriorAlgebra.ι_sq_zero]; simp

theorem ιMulti_interleave_succ {g : ℕ} (e f : Fin (g + 1) → V) :
    ExteriorAlgebra.ιMulti K (2 * (g + 1)) (interleave e f) =
      ExteriorAlgebra.ιMulti K (2 * g) (interleave (e ∘ Fin.castSucc) (f ∘ Fin.castSucc)) *
        (ExteriorAlgebra.ι K (e (Fin.last g)) * ExteriorAlgebra.ι K (f (Fin.last g))) := by
  have h2 : ExteriorAlgebra.ι K (e (Fin.last g)) * ExteriorAlgebra.ι K (f (Fin.last g)) =
      ExteriorAlgebra.ιMulti K 2 ![e (Fin.last g), f (Fin.last g)] := by
    simp [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  rw [h2, ExteriorAlgebra.ιMulti_mul_ιMulti]
  change ExteriorAlgebra.ιMulti K (2 * g + 2) (interleave e f) = _
  congr 1
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    simp only [interleave, interleaveIdx, Function.comp_apply, Fin.val_castAdd]
    split_ifs <;> simp [Fin.castSucc]
  · erw [Fin.append_right]
    fin_cases j <;> simp [interleave, interleaveIdx, Fin.last]
    congr 1
    ext
    simp only
    omega

/-- If `p` commutes with `A` and `p * p = 0`, then `(A + p) ^ (m + 1) = A ^ (m + 1) +
(m + 1) • (A ^ m * p)`. -/
theorem add_pow_of_sq_eq_zero {A : Type*} [Ring A] {a p : A} (hc : Commute a p) (hp : p * p = 0)
    (m : ℕ) : (a + p) ^ (m + 1) = a ^ (m + 1) + (m + 1) • (a ^ m * p) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : a ^ m * p * a = a ^ (m + 1) * p := by
      rw [mul_assoc, ← hc.eq, ← mul_assoc, ← pow_succ]
    have h2 : a ^ m * p * p = 0 := by rw [mul_assoc, hp, mul_zero]
    rw [pow_succ, ih]
    simp only [mul_add, add_mul, smul_mul_assoc, h1, h2, ← pow_succ, smul_zero, add_zero]
    module

/-- The expansion of `(Σᵢ eᵢ ∧ fᵢ) ^ g` in the exterior algebra, together with the vanishing of the
next power. -/
theorem pow_sympVec (g : ℕ) (e f : Fin g → V) :
    (sympVec (K := K) e f : ExteriorAlgebra K V) ^ g =
        g.factorial • ExteriorAlgebra.ιMulti K (2 * g) (interleave e f) ∧
      (sympVec (K := K) e f : ExteriorAlgebra K V) ^ (g + 1) = 0 := by
  induction g with
  | zero =>
    simp [sympVec]
  | succ g ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (e ∘ Fin.castSucc) (f ∘ Fin.castSucc)
    have hsum : (sympVec (K := K) e f : ExteriorAlgebra K V) =
        (sympVec (K := K) (e ∘ Fin.castSucc) (f ∘ Fin.castSucc) : ExteriorAlgebra K V) +
          (exteriorPower.ιMulti K 2 ![e (Fin.last g), f (Fin.last g)] : ExteriorAlgebra K V) := by
      rw [sympVec, Fin.sum_univ_castSucc, Submodule.coe_add]
      rfl
    have hc := commute_two (sympVec (K := K) (e ∘ Fin.castSucc) (f ∘ Fin.castSucc))
      (exteriorPower.ιMulti K 2 ![e (Fin.last g), f (Fin.last g)])
    have hp := ιMulti_two_mul_self (K := K) (e (Fin.last g)) (f (Fin.last g))
    rw [hsum]
    constructor
    · rw [add_pow_of_sq_eq_zero hc hp, ih₂, zero_add, ih₁, smul_mul_assoc, smul_smul,
        ιMulti_interleave_succ, coe_ιMulti_two, Nat.factorial_succ]
    · rw [add_pow_of_sq_eq_zero hc hp, pow_succ _ (g + 1), ih₂]
      simp

/-- **The expansion.** `(Σᵢ eᵢ ∧ fᵢ) ^ g = g! • (e₁ ∧ f₁ ∧ ⋯ ∧ e_g ∧ f_g)`, for any vectors. -/
theorem wedgePow_sympVec {g : ℕ} (e f : Fin g → V) :
    wedgePow (sympVec (K := K) e f) g =
      g.factorial • exteriorPower.ιMulti K (2 * g) (interleave e f) := by
  apply Subtype.ext
  rw [coe_wedgePow, (pow_sympVec g e f).1]
  rfl

/-- Powers of `Σ_{i < r} eᵢ ∧ fᵢ` beyond the `r`-th vanish. -/
theorem wedgePow_sympVec_eq_zero {r k : ℕ} (hk : r < k) (e f : Fin r → V) :
    wedgePow (sympVec (K := K) e f) k = 0 := by
  rw [wedgePow_eq_zero_iff, show k = (r + 1) + (k - (r + 1)) by omega, pow_add,
    (pow_sympVec r e f).2, zero_mul]

end Expansion

section Darboux

theorem sympVec_zero (e f : Fin 0 → V) : sympVec (K := K) e f = 0 := by
  simp [sympVec]

theorem sympVec_append {m n : ℕ} (a b : Fin m → V) (a' b' : Fin n → V) :
    sympVec (K := K) (Fin.append a a') (Fin.append b b') = sympVec a b + sympVec a' b' := by
  simp [sympVec, Fin.sum_univ_add]

theorem ιMulti_two_smul_left (c : K) (a b : V) :
    exteriorPower.ιMulti K 2 ![c • a, b] = c • exteriorPower.ιMulti K 2 ![a, b] := by
  apply Subtype.ext
  simp only [Submodule.coe_smul, coe_ιMulti_two, map_smul, smul_mul_assoc]

theorem sympVec_smul (c : K) {m : ℕ} (a b : Fin m → V) :
    c • sympVec (K := K) a b = sympVec (c • a) b := by
  simp [sympVec, Finset.smul_sum, ιMulti_two_smul_left]

theorem ι_mul_ι_swap (a b : V) :
    ExteriorAlgebra.ι K b * ExteriorAlgebra.ι K a =
      -(ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K b) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap b a)

theorem sympVec_neg_swap {m : ℕ} (a b : Fin m → V) :
    sympVec (K := K) (-b) a = sympVec a b := by
  apply Subtype.ext
  simp only [sympVec, Submodule.coe_sum, coe_ιMulti_two, Pi.neg_apply, map_neg, neg_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ι_mul_ι_swap (a i) (b i), neg_neg]

/-- Every 2-vector is a finite sum of decomposable ones. -/
theorem exists_eq_sympVec (ω : ⋀[K]^2 V) : ∃ (m : ℕ) (a b : Fin m → V), ω = sympVec a b := by
  have hω : ω ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K 2 (M := V))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine ⟨1, ![v 0], ![v 1], ?_⟩
    simp only [sympVec, Finset.univ_unique, Finset.sum_singleton]
    congr 1
    ext i
    fin_cases i <;> rfl
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, (sympVec_zero _ _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, a, b, rfl⟩ := hx
    obtain ⟨n, a', b', rfl⟩ := hy
    exact ⟨m + n, Fin.append a a', Fin.append b b', (sympVec_append a b a' b').symm⟩
  | smul c x _ hx =>
    obtain ⟨m, a, b, rfl⟩ := hx
    exact ⟨m, c • a, b, sympVec_smul c a b⟩

/-- One reduction step: if `a k = Σⱼ (αⱼ aⱼ + βⱼ bⱼ) + γ b_k` (sums over `j ≠ k`), then
`Σᵢ aᵢ ∧ bᵢ = Σ_{j ≠ k} (aⱼ - βⱼ b_k) ∧ (bⱼ + αⱼ b_k)`. -/
theorem sympVec_reduce {m : ℕ} (a b : Fin (m + 1) → V) (k : Fin (m + 1)) (α β : Fin m → K)
    (γ : K) (hk : a k = ∑ j, (α j • a (k.succAbove j) + β j • b (k.succAbove j)) + γ • b k) :
    sympVec (K := K) a b = sympVec (fun j => a (k.succAbove j) - β j • b k)
      (fun j => b (k.succAbove j) + α j • b k) := by
  apply Subtype.ext
  simp only [sympVec, Submodule.coe_sum, coe_ιMulti_two]
  rw [Fin.sum_univ_succAbove _ k, hk]
  have hterm : ∀ j, ExteriorAlgebra.ι K (a (k.succAbove j) - β j • b k) *
        ExteriorAlgebra.ι K (b (k.succAbove j) + α j • b k) =
      ExteriorAlgebra.ι K (a (k.succAbove j)) * ExteriorAlgebra.ι K (b (k.succAbove j)) +
        (α j • ExteriorAlgebra.ι K (a (k.succAbove j)) +
          β j • ExteriorAlgebra.ι K (b (k.succAbove j))) * ExteriorAlgebra.ι K (b k) := by
    intro j
    simp only [map_add, map_sub, map_smul, add_mul, mul_add, sub_mul, smul_mul_assoc,
      mul_smul_comm, ExteriorAlgebra.ι_sq_zero, smul_zero, ι_mul_ι_swap (b (k.succAbove j)) (b k)]
    module
  simp only [hterm]
  simp only [Finset.sum_add_distrib, map_add, map_sum, map_smul, add_mul, Finset.sum_mul,
    smul_mul_assoc, ExteriorAlgebra.ι_sq_zero, smul_zero, add_zero]
  abel

theorem exists_sympVec_pred_of_rel {m : ℕ} (a b : Fin (m + 1) → V) (c₁ c₂ : Fin (m + 1) → K)
    (h : ∑ i, c₁ i • a i + ∑ i, c₂ i • b i = 0) (k : Fin (m + 1)) (hk : c₁ k ≠ 0) :
    ∃ a' b' : Fin m → V, sympVec (K := K) a b = sympVec a' b' := by
  refine ⟨_, _, sympVec_reduce a b k (fun j => -(c₁ k)⁻¹ * c₁ (k.succAbove j))
    (fun j => -(c₁ k)⁻¹ * c₂ (k.succAbove j)) (-(c₁ k)⁻¹ * c₂ k) ?_⟩
  rw [Fin.sum_univ_succAbove _ k, Fin.sum_univ_succAbove _ k] at h
  have h' : c₁ k • a k = -(∑ j, c₁ (k.succAbove j) • a (k.succAbove j) +
      (c₂ k • b k + ∑ j, c₂ (k.succAbove j) • b (k.succAbove j))) := by
    rw [eq_neg_iff_add_eq_zero, ← h]
    abel
  rw [← inv_smul_smul₀ hk (a k), h']
  simp only [smul_neg, smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib, neg_mul,
    neg_smul, Finset.sum_neg_distrib]
  abel

/-- **Normal form of a 2-vector.** Every `ω ∈ ⋀² V` is `Σ_{i < r} eᵢ ∧ fᵢ` with
`e₁, …, e_r, f₁, …, f_r` linearly independent. -/
theorem exists_sympVec_linearIndependent (ω : ⋀[K]^2 V) :
    ∃ (r : ℕ) (e f : Fin r → V), LinearIndependent K (Sum.elim e f) ∧ ω = sympVec e f := by
  obtain ⟨m, a, b, rfl⟩ := exists_eq_sympVec ω
  induction m with
  | zero => exact ⟨0, a, b, linearIndependent_empty_type, rfl⟩
  | succ m ih =>
    by_cases hli : LinearIndependent K (Sum.elim a b)
    · exact ⟨_, a, b, hli, rfl⟩
    rw [Fintype.not_linearIndependent_iff] at hli
    obtain ⟨c, hc, x, hx⟩ := hli
    rw [Fintype.sum_sum_type] at hc
    simp only [Sum.elim_inl, Sum.elim_inr] at hc
    rcases x with k | k
    · obtain ⟨a', b', h⟩ := exists_sympVec_pred_of_rel a b (fun i => c (.inl i))
        (fun i => c (.inr i)) hc k hx
      rw [h]
      exact ih a' b'
    · obtain ⟨a', b', h⟩ := exists_sympVec_pred_of_rel (-b) a (fun i => -c (.inr i))
        (fun i => c (.inl i)) (by simp only [Pi.neg_apply, smul_neg, neg_smul, neg_neg]; rw [← hc]; abel)
        k (neg_ne_zero.2 hx)
      rw [← sympVec_neg_swap, h]
      exact ih a' b'

theorem contract_sympVec {r : ℕ} (e f : Fin r → V) (φ : Dual K V) :
    contract (sympVec (K := K) e f) φ = ∑ i, (φ (e i) • f i - φ (f i) • e i) := by
  simp [sympVec]

theorem contract_sympVec_mem_span {r : ℕ} (e f : Fin r → V) (φ : Dual K V) :
    contract (sympVec (K := K) e f) φ ∈ Submodule.span K (Set.range (Sum.elim e f)) := by
  rw [contract_sympVec]
  refine Submodule.sum_mem _ fun i _ => Submodule.sub_mem _ ?_ ?_
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inr i, rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl i, rfl⟩)

/-- In a basis `e, f` with `ω = Σ eᵢ ∧ fᵢ`, contraction with the coordinate `eᵢ^*` gives `fᵢ`. -/
theorem contract_sympVec_coord_inl {g : ℕ} (b : Basis (Fin g ⊕ Fin g) K V) (i : Fin g) :
    contract (sympVec (K := K) (b ∘ Sum.inl) (b ∘ Sum.inr)) (b.coord (.inl i)) = b (.inr i) := by
  simp [contract_sympVec, Finsupp.single_apply]

/-- In a basis `e, f` with `ω = Σ eᵢ ∧ fᵢ`, contraction with the coordinate `fᵢ^*` gives `-eᵢ`. -/
theorem contract_sympVec_coord_inr {g : ℕ} (b : Basis (Fin g ⊕ Fin g) K V) (i : Fin g) :
    contract (sympVec (K := K) (b ∘ Sum.inl) (b ∘ Sum.inr)) (b.coord (.inr i)) = -b (.inl i) := by
  simp [contract_sympVec, Finsupp.single_apply]

/-- The standard symplectic 2-vector of a basis `e₁, …, e_g, f₁, …, f_g` is nondegenerate. -/
theorem isNondegenerate_sympVec_basis {g : ℕ} (b : Basis (Fin g ⊕ Fin g) K V) :
    IsNondegenerate (sympVec (K := K) (b ∘ Sum.inl) (b ∘ Sum.inr)) := by
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hsurj : Function.Surjective (contract (sympVec (K := K) (b ∘ Sum.inl) (b ∘ Sum.inr))) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨x | x, rfl⟩
    · exact ⟨-b.coord (.inr x), by rw [map_neg, contract_sympVec_coord_inr, neg_neg]⟩
    · exact ⟨b.coord (.inl x), contract_sympVec_coord_inl b x⟩
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    Subspace.dual_finrank_eq).2 hsurj, hsurj⟩

/-- **Darboux normal form.** A nondegenerate 2-vector `ω` lives on an even-dimensional space
`V`, `finrank V = 2g`, and there is a basis `e₁, …, e_g, f₁, …, f_g` of `V` (indexed by
`Fin g ⊕ Fin g`: `eᵢ = b (inl i)`, `fᵢ = b (inr i)`) with `ω = Σᵢ eᵢ ∧ fᵢ`.

Source: Lang, *Algebra*, Ch. XV (structure of bilinear forms: alternating forms), for the
nondegenerate alternating form that `ω` defines on `V^∨`; Bourbaki, *Algèbre*, ch. IX. -/
theorem exists_basis_sympVec_of_isNondegenerate {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) :
    ∃ (g : ℕ) (b : Basis (Fin g ⊕ Fin g) K V),
      finrank K V = 2 * g ∧ ω = sympVec (b ∘ Sum.inl) (b ∘ Sum.inr) := by
  obtain ⟨r, e, f, hli, rfl⟩ := exists_sympVec_linearIndependent ω
  have hsp : ⊤ ≤ Submodule.span K (Set.range (Sum.elim e f)) := by
    rintro v -
    obtain ⟨φ, rfl⟩ := hω.2 v
    exact contract_sympVec_mem_span e f φ
  refine ⟨r, Basis.mk hli hsp, ?_, ?_⟩
  · rw [finrank_eq_card_basis (Basis.mk hli hsp)]
    simp only [Fintype.card_sum, Fintype.card_fin]
    ring
  · congr 1 <;> ext <;> simp

/-- A 2-vector is nondegenerate iff it is `Σ eᵢ ∧ fᵢ` for a basis `e, f`. -/
theorem isNondegenerate_iff_exists_basis {ω : ⋀[K]^2 V} :
    IsNondegenerate ω ↔ ∃ (g : ℕ) (b : Basis (Fin g ⊕ Fin g) K V),
      ω = sympVec (b ∘ Sum.inl) (b ∘ Sum.inr) := by
  constructor
  · intro hω
    obtain ⟨g, b, -, h⟩ := exists_basis_sympVec_of_isNondegenerate hω
    exact ⟨g, b, h⟩
  · rintro ⟨g, b, rfl⟩
    exact isNondegenerate_sympVec_basis b

end Darboux

section TopPower

/-- The wedge of the vectors of a basis indexed by `Fin n` is nonzero. -/
theorem ιMulti_basis_ne_zero {n : ℕ} (b : Basis (Fin n) K V) :
    exteriorPower.ιMulti K n b ≠ 0 := by
  intro h
  have := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) h
  simp [Basis.det_self] at this

theorem interleaveIdx_bijective (g : ℕ) : Function.Bijective (interleaveIdx g) :=
  (Fintype.bijective_iff_injective_and_card _).2
    ⟨interleaveIdx_injective g, by simp only [Fintype.card_fin, Fintype.card_sum]; ring⟩

/-- The interleaved family `b (inl 0), b (inr 0), b (inl 1), …` of a basis indexed by
`Fin g ⊕ Fin g` is a basis indexed by `Fin (2 * g)`.

Source: Lang, *Algebra*, Ch. XV (alternating forms: the symplectic basis). -/
noncomputable def interleaveBasis {g : ℕ} (b : Basis (Fin g ⊕ Fin g) K V) :
    Basis (Fin (2 * g)) K V :=
  b.reindex (Equiv.ofBijective _ (interleaveIdx_bijective g)).symm

theorem coe_interleaveBasis {g : ℕ} (b : Basis (Fin g ⊕ Fin g) K V) :
    ⇑(interleaveBasis b) = interleave (b ∘ Sum.inl) (b ∘ Sum.inr) := by
  ext i
  simp only [interleaveBasis, Basis.reindex_apply, Equiv.symm_symm, Equiv.ofBijective_apply,
    interleave, Function.comp_apply]
  cases interleaveIdx g i <;> rfl

example : interleaveBasis (Pi.basisFun ℚ (Fin 1 ⊕ Fin 1)) 1 = Pi.single (.inr 0) 1 := by
  rw [coe_interleaveBasis]
  simp [interleave, interleaveIdx]

/-- A nondegenerate 2-vector on a space of dimension `2g` has nonzero `g`-th wedge power. -/
theorem wedgePow_ne_zero_of_isNondegenerate [CharZero K] {ω : ⋀[K]^2 V} {g : ℕ}
    (hω : IsNondegenerate ω) (hg : finrank K V = 2 * g) : wedgePow ω g ≠ 0 := by
  obtain ⟨g', b, hg', rfl⟩ := exists_basis_sympVec_of_isNondegenerate hω
  obtain rfl : g' = g := by omega
  rw [wedgePow_sympVec, ← coe_interleaveBasis, ← Nat.cast_smul_eq_nsmul K]
  exact smul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    (ιMulti_basis_ne_zero _)

/-- A 2-vector on a space of dimension `2g` whose `g`-th wedge power is nonzero is
nondegenerate. -/
theorem isNondegenerate_of_wedgePow_ne_zero [FiniteDimensional K V] {ω : ⋀[K]^2 V} {g : ℕ}
    (hg : finrank K V = 2 * g) (h : wedgePow ω g ≠ 0) : IsNondegenerate ω := by
  obtain ⟨r, e, f, hli, rfl⟩ := exists_sympVec_linearIndependent ω
  have hr : r + r ≤ 2 * g := by
    simpa [hg] using hli.fintype_card_le_finrank
  obtain rfl : r = g := by
    by_contra hne
    exact h (wedgePow_sympVec_eq_zero (by omega) e f)
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [hg, two_mul])
  have hb := isNondegenerate_sympVec_basis (Basis.mk hli hsp.ge)
  convert hb using 2 <;> ext <;> simp

/-- **Top power criterion.** On a space of dimension `2g` over a field of characteristic zero,
a 2-vector is nondegenerate iff its `g`-th wedge power is nonzero. -/
theorem isNondegenerate_iff_wedgePow_ne_zero [CharZero K] [FiniteDimensional K V]
    {ω : ⋀[K]^2 V} {g : ℕ} (hg : finrank K V = 2 * g) :
    IsNondegenerate ω ↔ wedgePow ω g ≠ 0 :=
  ⟨fun hω => wedgePow_ne_zero_of_isNondegenerate hω hg,
    isNondegenerate_of_wedgePow_ne_zero hg⟩

/-- A space carrying a nondegenerate 2-vector has even dimension. -/
theorem even_finrank_of_isNondegenerate {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) :
    Even (finrank K V) := by
  obtain ⟨g, -, hg, -⟩ := exists_basis_sympVec_of_isNondegenerate hω
  exact ⟨g, by omega⟩

end TopPower

section Examples

/-- `ω = e₁ ∧ e₂ + e₃ ∧ e₄` on `ℚ⁴` is the symplectic 2-vector of `(e₁, e₃)`, `(e₂, e₄)`. -/
theorem ex4_eq_sympVec :
    exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 4 → ℚ), Pi.single 1 1] +
        exteriorPower.ιMulti ℚ 2 ![(Pi.single 2 1 : Fin 4 → ℚ), Pi.single 3 1] =
      sympVec ![(Pi.single 0 1 : Fin 4 → ℚ), Pi.single 2 1] ![Pi.single 1 1, Pi.single 3 1] := by
  simp [sympVec, Fin.sum_univ_two]

theorem pi_basisFun_four :
    ⇑(Pi.basisFun ℚ (Fin 4)) = ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1] := by
  ext i : 1
  fin_cases i <;> simp

/-- `ω = e₁ ∧ e₂ + e₃ ∧ e₄` on `ℚ⁴`: `ω ∧ ω = 2 • (e₁ ∧ e₂ ∧ e₃ ∧ e₄)`. -/
example :
    wedgePow (exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 4 → ℚ), Pi.single 1 1] +
        exteriorPower.ιMulti ℚ 2 ![(Pi.single 2 1 : Fin 4 → ℚ), Pi.single 3 1]) 2 =
      2 • exteriorPower.ιMulti ℚ 4
        ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1] := by
  rw [ex4_eq_sympVec, wedgePow_sympVec]
  congr 2
  ext i : 1
  fin_cases i <;> rfl

/-- `ω = e₁ ∧ e₂ + e₃ ∧ e₄` on `ℚ⁴`: `ω ∧ ω ≠ 0`. -/
example :
    wedgePow (exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 4 → ℚ), Pi.single 1 1] +
        exteriorPower.ιMulti ℚ 2 ![(Pi.single 2 1 : Fin 4 → ℚ), Pi.single 3 1]) 2 ≠ 0 := by
  rw [ex4_eq_sympVec, wedgePow_sympVec, ← Nat.cast_smul_eq_nsmul ℚ]
  refine smul_ne_zero (by simp [Nat.factorial]) ?_
  convert ιMulti_basis_ne_zero (Pi.basisFun ℚ (Fin 4)) using 2
  rw [pi_basisFun_four]
  ext i : 1
  fin_cases i <;> rfl

/-- `ω = e₁ ∧ e₂ + e₃ ∧ e₄` on `ℚ⁴` is nondegenerate. -/
example :
    IsNondegenerate (exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 4 → ℚ), Pi.single 1 1] +
        exteriorPower.ιMulti ℚ 2 ![(Pi.single 2 1 : Fin 4 → ℚ), Pi.single 3 1]) := by
  rw [ex4_eq_sympVec]
  let σ : Fin 2 ⊕ Fin 2 ≃ Fin 4 :=
    { toFun := Sum.elim ![0, 2] ![1, 3]
      invFun := ![.inl 0, .inr 0, .inl 1, .inr 1]
      left_inv := by decide
      right_inv := by decide }
  let b : Basis (Fin 2 ⊕ Fin 2) ℚ (Fin 4 → ℚ) := (Pi.basisFun ℚ (Fin 4)).reindex σ.symm
  convert isNondegenerate_sympVec_basis b using 2 <;> ext i : 1 <;> fin_cases i <;>
    simp [b, σ]

/-- Falsification: `ω = e₁ ∧ e₂` on `ℚ⁴` has `ω ∧ ω = 0`. -/
example : wedgePow (exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 4 → ℚ), Pi.single 1 1]) 2 = 0 := by
  have : exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 4 → ℚ), Pi.single 1 1] =
      sympVec ![(Pi.single 0 1 : Fin 4 → ℚ)] ![Pi.single 1 1] := by
    simp [sympVec]
  rw [this]
  exact wedgePow_sympVec_eq_zero (by norm_num) _ _

/-- Falsification: `ω = e₁ ∧ e₂` on `ℚ⁴` is degenerate. -/
example : ¬ IsNondegenerate (exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 4 → ℚ), Pi.single 1 1]) := by
  intro h
  apply wedgePow_ne_zero_of_isNondegenerate h (g := 2) (by simp)
  have : exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 4 → ℚ), Pi.single 1 1] =
      sympVec ![(Pi.single 0 1 : Fin 4 → ℚ)] ![Pi.single 1 1] := by
    simp [sympVec]
  rw [this]
  exact wedgePow_sympVec_eq_zero (by norm_num) _ _

/-- `g = 1`: on `ℚ²`, `ω = e₁ ∧ e₂` has `wedgePow ω 1 = ω`. -/
example : wedgePow (exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 2 → ℚ), Pi.single 1 1]) 1 =
    exteriorPower.ιMulti ℚ 2 ![Pi.single 0 1, Pi.single 1 1] :=
  wedgePow_one _

/-- `g = 1`: on `ℚ²`, `ω = e₁ ∧ e₂` is nondegenerate. -/
example : IsNondegenerate (exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 2 → ℚ), Pi.single 1 1]) := by
  refine isNondegenerate_of_wedgePow_ne_zero (g := 1) (by simp) ?_
  rw [wedgePow_one]
  convert ιMulti_basis_ne_zero (Pi.basisFun ℚ (Fin 2)) using 2
  ext i : 1
  fin_cases i <;> simp

/-- Odd dimension: no 2-vector on `ℚ³` is nondegenerate. -/
example (ω : ⋀[ℚ]^2 (Fin 3 → ℚ)) : ¬ IsNondegenerate ω := by
  intro h
  have := even_finrank_of_isNondegenerate h
  simp at this
  exact absurd this (by decide)

end Examples

end Symplectic

end HodgeLean.Foundations
