import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import HodgeLean.Foundations.Symplectic

/-! # Linear Hard Lefschetz on the exterior algebra

Foundations target T2 (`docs/roadmap/foundations.md` §4 T2).

## Setting

`K` is a field of characteristic zero, `V` a `K`-vector space with `finrank K V = 2 * g`, and
`ω : ⋀[K]^2 V` a nondegenerate 2-vector (`Symplectic.IsNondegenerate`).

## Main definitions

* `Lefschetz.castDeg h : ⋀[K]^m V ≃ₗ[K] ⋀[K]^n V` for `h : m = n`, the identity of the exterior
  algebra read between two names of the same degree. It is the one degree cast of this file.
* `Lefschetz.lefschetz ω r k : ⋀[K]^k V →ₗ[K] ⋀[K]^(k + 2 * r) V`, `x ↦ ω^r ∧ x`.
* `Lefschetz.interior φ`: contraction with a linear form `φ`, an antiderivation of the exterior
  algebra of degree `-1` (Mathlib's `CliffordAlgebra.contractLeft` at the zero quadratic form).
* `Lefschetz.dualLefschetz b = Σᵢ ι_{fᵢ^*} ι_{eᵢ^*}` for a basis `e, f`: the dual Lefschetz
  operator `Λ`, contraction with the dual bivector, of degree `-2`.
* `Lefschetz.lefschetzEquiv hω hg hk : ⋀[K]^k V ≃ₗ[K] ⋀[K]^(2 * g - k) V`, the Hard Lefschetz
  isomorphism.

## Main results

* `Lefschetz.pow_injective_of_comm`: an abstract `sl₂` lemma without complete reducibility. On a
  graded family `P k`, operators `L` (degree `+2`) and `Λ` (degree `-2`, zero on `P 0`, `P 1`)
  with `[Λ, L] = (g - k)` on `P k` make `L^j` injective on `P k` whenever `j + k ≤ g`.
* `Lefschetz.dualLefschetz_comm`: in a Darboux basis, `[Λ, ω ∧ -] = (g - k)` on `⋀^k V`.
* `Lefschetz.lefschetz_injective`, `Lefschetz.lefschetz_bijective`: for `k ≤ g`,
  `ω^(g - k) ∧ - : ⋀^k V → ⋀^(2g - k) V` is injective, and bijective by the dimension count
  `C(2g, k) = C(2g, 2g - k)`.

## Route

Item 2 of the brief follows the `sl₂` route, not the combinatorial one. The combinatorial route
needs the graded tensor splitting `⋀(P₁ ⊕ ⋯ ⊕ P_g) ≅ ⊗ ⋀Pᵢ` (`ExteriorAlgebra.prodEquivTensor` is
for two factors, with a graded tensor product whose API is thin), an induction on `g` through it,
and then the Boolean-lattice inclusion-rank statement, which is itself an `sl₂` argument. The
`sl₂` route needs only Mathlib's contraction `CliffordAlgebra.contractLeft` and its Leibniz rule
`contractLeft_ι_mul`, the Darboux basis of T1, and T1's `contract`: the commutator of a
contraction with `ω ∧ -` is wedging with `contract ω φ`, so `[Λ, L] = g - N` with `N` the number
operator, `N = k` on `⋀^k`.

Relation to the goal: HC no distance; AV milestone no distance. In `HodgeLean.Adapters.Lefschetz`,
O3 `HardLefschetz` for abelian `X` reduces to the torus theorem C7 (`TorusCohomology`) plus
nondegeneracy of the polarization's preimage in `⋀²H¹`, neither of which is proved here; the
bijectivity half of `HodgeBlocks.HardLefschetzFromDegreeTwo` reduces to nondegeneracy of the
polarization alone (on the exterior model).
-/

open Module

namespace HodgeLean.Foundations

namespace Lefschetz

open Symplectic

section Sl2

variable {K : Type*} [Field K] [CharZero K] {E : Type*} [AddCommGroup E] [Module K E]

/-- The commutator of `Λ` with a power of `L`: on `P k`,
`Λ L^(j+1) = L^(j+1) Λ + (j + 1)(g - k - j) L^j`. -/
theorem comm_pow (P : ℕ → Submodule K E) (L Λ : Module.End K E) (g : ℕ)
    (hL : ∀ k, ∀ x ∈ P k, L x ∈ P (k + 2))
    (hcomm : ∀ k, ∀ x ∈ P k, Λ (L x) - L (Λ x) = ((g : K) - k) • x) (k : ℕ) :
    ∀ (j : ℕ), ∀ x ∈ P k, Λ ((L ^ (j + 1)) x) =
      (L ^ (j + 1)) (Λ x) + (((j : K) + 1) * ((g : K) - k - j)) • (L ^ j) x := by
  have hLp : ∀ j, ∀ x ∈ P k, (L ^ j) x ∈ P (k + 2 * j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      exact hL _ _ (ih x hx)
  intro j
  induction j with
  | zero =>
    intro x hx
    have := hcomm k x hx
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, CharP.cast_eq_zero, sub_zero,
      one_mul]
    rw [← this]
    abel
  | succ j ih =>
    intro x hx
    rw [pow_succ' L (j + 1), Module.End.mul_apply, Module.End.mul_apply]
    have h1 := hcomm _ _ (hLp (j + 1) x hx)
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, ih x hx, map_add, map_smul, ← Module.End.mul_apply L (L ^ j), ← pow_succ']
    rw [add_left_comm, ← add_smul]
    congr 2
    push_cast
    ring

/-- **Injectivity from an `sl₂`-commutator, without complete reducibility.** Let `P k` be a
family of subspaces of `E`, `L` an operator raising the index by `2` and `Λ` one lowering it by
`2` (and vanishing on `P 0` and `P 1`), with `[Λ, L] = (g - k)` on `P k`. Then `L^j` is injective
on `P k` whenever `j + k ≤ g`.

The proof is by strong induction on `k` and then on `j`: if `L^(j+1) x = 0`, then
`L^(j+2) (Λ x) = 0` by `comm_pow`, so `Λ x = 0` by induction on `k`, and then `comm_pow` leaves
`(j + 1)(g - k - j) L^j x = 0` with a nonzero coefficient.

Source: Huybrechts, *Complex Geometry*, §1.2 (Lefschetz decomposition on the exterior algebra,
the `sl₂`-commutator computation); Voisin I, Ch. 6 (the Lefschetz decomposition). -/
theorem pow_injective_of_comm (P : ℕ → Submodule K E) (L Λ : Module.End K E) (g : ℕ)
    (hL : ∀ k, ∀ x ∈ P k, L x ∈ P (k + 2))
    (hΛ : ∀ k, ∀ x ∈ P (k + 2), Λ x ∈ P k)
    (hΛ0 : ∀ x ∈ P 0, Λ x = 0) (hΛ1 : ∀ x ∈ P 1, Λ x = 0)
    (hcomm : ∀ k, ∀ x ∈ P k, Λ (L x) - L (Λ x) = ((g : K) - k) • x) (k : ℕ) :
    ∀ j, j + k ≤ g → ∀ x ∈ P k, (L ^ j) x = 0 → x = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro j
  induction j with
  | zero => simp
  | succ j ihj =>
    intro hjk x hx h0
    have hc := comm_pow P L Λ g hL hcomm k j x hx
    rw [h0, map_zero] at hc
    have hΛx : Λ x = 0 := by
      have h2 : (L ^ (j + 2)) (Λ x) = 0 := by
        rw [pow_succ', Module.End.mul_apply, eq_neg_of_add_eq_zero_left hc.symm, map_neg,
          map_smul, ← Module.End.mul_apply, ← pow_succ', h0, smul_zero, neg_zero]
      rcases k with _ | _ | k
      · exact hΛ0 x hx
      · exact hΛ1 x hx
      · exact IH k (by omega) (j + 2) (by omega) (Λ x) (hΛ k x hx) h2
    rw [hΛx, map_zero, zero_add] at hc
    have hne : ((j : K) + 1) * ((g : K) - k - j) ≠ 0 := by
      have : ((g : K) - k - j) = ((g - k - j : ℕ) : K) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      rw [this]
      exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero j) (by exact_mod_cast (by omega))
    exact ihj (by omega) x hx ((smul_eq_zero.mp hc.symm).resolve_left hne)

/-- The shape of the conclusion on the zero space: a vector of `⊥` killed by `L ^ 0` is zero. (This
illustrates the conclusion only; it does not invoke `pow_injective_of_comm`.) -/
example (x : E) (hx : x ∈ (⊥ : Submodule K E)) : ((0 : Module.End K E) ^ 0) x = 0 → x = 0 :=
  fun _ => (Submodule.mem_bot K).1 hx

end Sl2

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Cast

/-- The identification `⋀[K]^m V ≃ₗ[K] ⋀[K]^n V` along `m = n`: both are the same submodule of the
exterior algebra, and the map is the identity on it.

Source: Bourbaki, *Algebra I*, Ch. III (the exterior algebra and its grading). -/
noncomputable def castDeg {m n : ℕ} (h : m = n) : ⋀[K]^m V ≃ₗ[K] ⋀[K]^n V :=
  LinearEquiv.ofEq _ _ (by rw [h])

@[simp] theorem coe_castDeg {m n : ℕ} (h : m = n) (x : ⋀[K]^m V) :
    (castDeg h x : ExteriorAlgebra K V) = x :=
  rfl

example (x : ⋀[ℚ]^(1 + 1) (Fin 2 → ℚ)) :
    ((castDeg (by norm_num : 1 + 1 = 2) x : ⋀[ℚ]^2 (Fin 2 → ℚ)) : ExteriorAlgebra ℚ (Fin 2 → ℚ)) =
      (x : ExteriorAlgebra ℚ (Fin 2 → ℚ)) :=
  rfl

end Cast

section Degree

/-- `⋀^(k+1) V = V ∧ ⋀^k V`: induction over its generators `v ∧ y`. -/
theorem mem_succ_induction {k : ℕ} {p : ExteriorAlgebra K V → Prop} {x : ExteriorAlgebra K V}
    (hx : x ∈ ⋀[K]^(k + 1) V)
    (mul : ∀ v : V, ∀ y ∈ ⋀[K]^k V, p (ExteriorAlgebra.ι K v * y))
    (add : ∀ x y, p x → p y → p (x + y)) : p x := by
  change x ∈ LinearMap.range (ExteriorAlgebra.ι K : V →ₗ[K] _) ^ (k + 1) at hx
  rw [pow_succ'] at hx
  refine Submodule.mul_induction_on hx (fun m hm n hn => ?_) add
  obtain ⟨v, rfl⟩ := hm
  exact mul v n hn

theorem ι_mul_mem {k : ℕ} (v : V) {y : ExteriorAlgebra K V} (hy : y ∈ ⋀[K]^k V) :
    ExteriorAlgebra.ι K v * y ∈ ⋀[K]^(k + 1) V := by
  change _ ∈ LinearMap.range (ExteriorAlgebra.ι K : V →ₗ[K] _) ^ (k + 1)
  rw [pow_succ']
  exact Submodule.mul_mem_mul ⟨v, rfl⟩ hy

theorem mul_mem_of_mem_two {k : ℕ} {w x : ExteriorAlgebra K V} (hw : w ∈ ⋀[K]^2 V)
    (hx : x ∈ ⋀[K]^k V) : w * x ∈ ⋀[K]^(k + 2) V := by
  change _ ∈ LinearMap.range (ExteriorAlgebra.ι K : V →ₗ[K] _) ^ (k + 2)
  rw [add_comm, pow_add]
  exact Submodule.mul_mem_mul hw hx

theorem mul_mem_of_mem {m k : ℕ} {w x : ExteriorAlgebra K V} (hw : w ∈ ⋀[K]^m V)
    (hx : x ∈ ⋀[K]^k V) : w * x ∈ ⋀[K]^(m + k) V := by
  change _ ∈ LinearMap.range (ExteriorAlgebra.ι K : V →ₗ[K] _) ^ (m + k)
  rw [pow_add]
  exact Submodule.mul_mem_mul hw hx

end Degree

section Lefschetz

/-- **The Lefschetz operator** `L^r : ⋀^k V → ⋀^(k + 2r) V`, `x ↦ ω^r ∧ x`: the wedge with
`wedgePow ω r`, read in degree `k + 2r` through `castDeg`.

Source: Huybrechts, *Complex Geometry*, §1.2 (the Lefschetz operator on the exterior algebra);
Voisin I, Ch. 6. -/
noncomputable def lefschetz (ω : ⋀[K]^2 V) (r k : ℕ) : ⋀[K]^k V →ₗ[K] ⋀[K]^(k + 2 * r) V :=
  (castDeg (Nat.add_comm (2 * r) k)).toLinearMap ∘ₗ
    exteriorPower.wedge K V (2 * r) k (wedgePow ω r)

/-- In the exterior algebra, `lefschetz ω r k x` is `ω ^ r * x`. -/
theorem coe_lefschetz (ω : ⋀[K]^2 V) (r k : ℕ) (x : ⋀[K]^k V) :
    (lefschetz ω r k x : ExteriorAlgebra K V) = (ω : ExteriorAlgebra K V) ^ r * x := by
  simp only [lefschetz, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    coe_castDeg, coe_wedge, coe_wedgePow]

/-- `L^0` is the identity, through the cast `k = k + 2 * 0`. -/
theorem lefschetz_zero (ω : ⋀[K]^2 V) (k : ℕ) :
    lefschetz ω 0 k = (castDeg (by ring : k = k + 2 * 0)).toLinearMap :=
  LinearMap.ext fun x => Subtype.ext (by rw [coe_lefschetz, pow_zero, one_mul]; rfl)

/-- `L^1` is `ω ∧ -`. -/
theorem coe_lefschetz_one (ω : ⋀[K]^2 V) (k : ℕ) (x : ⋀[K]^k V) :
    (lefschetz ω 1 k x : ExteriorAlgebra K V) = ω * x := by
  rw [coe_lefschetz, pow_one]

/-- `L^r ∘ L^s = L^(r + s)`, through the cast `k + 2s + 2r = k + 2(r + s)`. -/
theorem lefschetz_comp (ω : ⋀[K]^2 V) (r s k : ℕ) :
    lefschetz ω r (k + 2 * s) ∘ₗ lefschetz ω s k =
      (castDeg (by ring : k + 2 * (r + s) = k + 2 * s + 2 * r)).toLinearMap ∘ₗ
        lefschetz ω (r + s) k :=
  LinearMap.ext fun x => Subtype.ext (by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, coe_castDeg,
      coe_lefschetz, ← mul_assoc, ← pow_add])

/-- `L^1` sends the unit `1 ∈ ⋀⁰ ℚ²` to `ω = e₁ ∧ e₂`. -/
example : (lefschetz (exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 2 → ℚ), Pi.single 1 1]) 1 0
      (exteriorPower.ιMulti ℚ 0 Fin.elim0) : ExteriorAlgebra ℚ (Fin 2 → ℚ)) =
    exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 2 → ℚ), Pi.single 1 1] := by
  rw [coe_lefschetz_one]
  simp

end Lefschetz

section Interior

/-- **Interior product** with a linear form `φ`: the antiderivation of the exterior algebra with
`ι_φ (v ∧ y) = φ v • y - v ∧ ι_φ y`. It is Mathlib's `CliffordAlgebra.contractLeft` at the zero
quadratic form.

Source: Bourbaki, *Algebra I*, Ch. III, §11 (interior products); Huybrechts, *Complex Geometry*,
§1.2 (contraction on the exterior algebra). -/
noncomputable def interior (φ : Dual K V) : Module.End K (ExteriorAlgebra K V) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) φ

theorem interior_ι_mul (φ : Dual K V) (v : V) (y : ExteriorAlgebra K V) :
    interior φ (ExteriorAlgebra.ι K v * y) = φ v • y - ExteriorAlgebra.ι K v * interior φ y :=
  CliffordAlgebra.contractLeft_ι_mul _ _ _

/-- `ι_φ v = φ v` for a vector `v`. -/
theorem interior_ι (φ : Dual K V) (v : V) :
    interior φ (ExteriorAlgebra.ι K v) = algebraMap K _ (φ v) :=
  CliffordAlgebra.contractLeft_ι _ φ v

/-- On `ℚ²`, `ι_{e₁^*} (e₁ ∧ e₂) = e₂`. -/
example : interior ((Pi.basisFun ℚ (Fin 2)).coord 0)
    (ExteriorAlgebra.ι ℚ (Pi.single 0 1) * ExteriorAlgebra.ι ℚ (Pi.single 1 1)) =
      ExteriorAlgebra.ι ℚ (Pi.single 1 1) := by
  simp [interior_ι_mul, interior_ι]

/-- The interior product kills `⋀⁰ V`. -/
theorem interior_of_mem_zero (φ : Dual K V) {x : ExteriorAlgebra K V} (hx : x ∈ ⋀[K]^0 V) :
    interior φ x = 0 := by
  change x ∈ LinearMap.range (ExteriorAlgebra.ι K : V →ₗ[K] _) ^ 0 at hx
  simp only [pow_zero] at hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
  exact CliffordAlgebra.contractLeft_algebraMap (Q := (0 : QuadraticForm K V)) (d := φ) r

/-- The interior product lowers degree by one. -/
theorem interior_mem (φ : Dual K V) (k : ℕ) :
    ∀ {x : ExteriorAlgebra K V}, x ∈ ⋀[K]^(k + 1) V → interior φ x ∈ ⋀[K]^k V := by
  induction k with
  | zero =>
    intro x hx
    refine mem_succ_induction (p := fun x => interior φ x ∈ ⋀[K]^0 V) hx (fun v y hy => ?_)
      (fun x y hx hy => ?_)
    · rw [interior_ι_mul, interior_of_mem_zero φ hy, mul_zero, sub_zero]
      exact Submodule.smul_mem _ _ hy
    · rw [map_add]
      exact Submodule.add_mem _ hx hy
  | succ k ih =>
    intro x hx
    refine mem_succ_induction (p := fun x => interior φ x ∈ ⋀[K]^(k + 1) V) hx
      (fun v y hy => ?_) (fun x y hx hy => ?_)
    · rw [interior_ι_mul]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) (ι_mul_mem v (ih hy))
    · rw [map_add]
      exact Submodule.add_mem _ hx hy

/-- **The number operator.** For a basis `b` with coordinate forms `b.coord j`,
`Σⱼ bⱼ ∧ ι_{bⱼ^*} y = k • y` on `⋀^k V`. -/
theorem sum_ι_mul_interior {ι' : Type*} [Fintype ι'] (b : Basis ι' K V) :
    ∀ (k : ℕ) {y : ExteriorAlgebra K V}, y ∈ ⋀[K]^k V →
      ∑ j, ExteriorAlgebra.ι K (b j) * interior (b.coord j) y = (k : K) • y
  | 0, y, hy => by simp [interior_of_mem_zero _ hy]
  | k + 1, y, hy => by
    refine mem_succ_induction (p := fun y => ∑ j, ExteriorAlgebra.ι K (b j) *
      interior (b.coord j) y = ((k + 1 : ℕ) : K) • y) hy (fun v y hy => ?_) (fun x y hx hy => ?_)
    · simp only [interior_ι_mul, mul_sub, mul_smul_comm]
      rw [Finset.sum_sub_distrib]
      have h1 : ∑ j, b.coord j v • (ExteriorAlgebra.ι K (b j) * y) =
          ExteriorAlgebra.ι K v * y := by
        simp only [← smul_mul_assoc, ← Finset.sum_mul, ← map_smul, ← map_sum, Basis.coord_apply,
          b.sum_repr]
      have h2 : ∑ j, ExteriorAlgebra.ι K (b j) * (ExteriorAlgebra.ι K v * interior (b.coord j) y) =
          -(ExteriorAlgebra.ι K v * ∑ j, ExteriorAlgebra.ι K (b j) * interior (b.coord j) y) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, ← mul_assoc, ι_mul_ι_swap, neg_mul]
      rw [h1, h2, sum_ι_mul_interior b k hy, sub_neg_eq_add, mul_smul_comm]
      push_cast
      rw [add_smul, one_smul, add_comm]
    · simp only [map_add, mul_add, Finset.sum_add_distrib, smul_add, hx, hy]

/-- `[ι_φ, ω ∧ -] = contract ω φ ∧ -` for `ω = Σ eᵢ ∧ fᵢ`: the commutator of a contraction with
the Lefschetz operator is wedging with the vector `contract ω φ` of T1. -/
theorem interior_sympVec_mul {r : ℕ} (e f : Fin r → V) (φ : Dual K V) (y : ExteriorAlgebra K V) :
    interior φ ((sympVec (K := K) e f : ExteriorAlgebra K V) * y) =
      (sympVec (K := K) e f : ExteriorAlgebra K V) * interior φ y +
        ExteriorAlgebra.ι K (contract (sympVec (K := K) e f) φ) * y := by
  rw [contract_sympVec, sympVec]
  simp only [Submodule.coe_sum, Finset.sum_mul, map_sum, coe_ιMulti_two, mul_assoc,
    interior_ι_mul, map_sub, map_smul, sub_mul, smul_mul_assoc, mul_sub, mul_smul_comm,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  abel

end Interior

section DualLefschetz

variable {g : ℕ}

/-- **The dual Lefschetz operator** `Λ = Σᵢ ι_{fᵢ^*} ι_{eᵢ^*}` of a basis `e, f` (indexed by
`Fin g ⊕ Fin g`, `eᵢ = b (inl i)`, `fᵢ = b (inr i)`): contraction with the dual bivector
`Σᵢ eᵢ^* ∧ fᵢ^*`, of degree `-2`.

Source: Huybrechts, *Complex Geometry*, §1.2 (the dual Lefschetz operator `Λ` on the exterior
algebra); Voisin I, Ch. 6. -/
noncomputable def dualLefschetz (b : Basis (Fin g ⊕ Fin g) K V) : Module.End K (ExteriorAlgebra K V) :=
  ∑ i, interior (b.coord (.inr i)) * interior (b.coord (.inl i))

/-- On `ℚ²` with `e = e₁`, `f = e₂`, `Λ` sends `e₁ ∧ e₂` to `1`. -/
example : dualLefschetz (Pi.basisFun ℚ (Fin 1 ⊕ Fin 1))
    (ExteriorAlgebra.ι ℚ (Pi.single (.inl 0) 1) * ExteriorAlgebra.ι ℚ (Pi.single (.inr 0) 1)) = 1 := by
  simp [dualLefschetz, Module.End.mul_apply, interior_ι_mul, interior_ι]

theorem dualLefschetz_mem (b : Basis (Fin g ⊕ Fin g) K V) (k : ℕ) {x : ExteriorAlgebra K V}
    (hx : x ∈ ⋀[K]^(k + 2) V) : dualLefschetz b x ∈ ⋀[K]^k V := by
  rw [dualLefschetz, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ => interior_mem _ k (interior_mem _ (k + 1) hx)

theorem dualLefschetz_of_mem_zero (b : Basis (Fin g ⊕ Fin g) K V) {x : ExteriorAlgebra K V}
    (hx : x ∈ ⋀[K]^0 V) : dualLefschetz b x = 0 := by
  simp [dualLefschetz, Module.End.mul_apply, interior_of_mem_zero _ hx]

theorem dualLefschetz_of_mem_one (b : Basis (Fin g ⊕ Fin g) K V) {x : ExteriorAlgebra K V}
    (hx : x ∈ ⋀[K]^1 V) : dualLefschetz b x = 0 := by
  simp [dualLefschetz, Module.End.mul_apply, interior_of_mem_zero _ (interior_mem _ 0 hx)]

/-- **The `sl₂` relation.** For `ω = Σᵢ eᵢ ∧ fᵢ` in a basis `e, f`, `[Λ, ω ∧ -] = (g - k)` on
`⋀^k V`.

Source: Huybrechts, *Complex Geometry*, §1.2 (the commutator `[Λ, L] = H` on the exterior
algebra). -/
theorem dualLefschetz_comm (b : Basis (Fin g ⊕ Fin g) K V) (k : ℕ) {y : ExteriorAlgebra K V}
    (hy : y ∈ ⋀[K]^k V) :
    dualLefschetz b ((sympVec (K := K) (b ∘ Sum.inl) (b ∘ Sum.inr) : ExteriorAlgebra K V) * y) -
        (sympVec (K := K) (b ∘ Sum.inl) (b ∘ Sum.inr) : ExteriorAlgebra K V) *
          dualLefschetz b y = ((g : K) - k) • y := by
  set ω := sympVec (K := K) (b ∘ Sum.inl) (b ∘ Sum.inr)
  have hi : ∀ i, interior (b.coord (.inr i)) (interior (b.coord (.inl i)) ((ω : _) * y)) -
      (ω : ExteriorAlgebra K V) * interior (b.coord (.inr i)) (interior (b.coord (.inl i)) y) =
      y - (ExteriorAlgebra.ι K (b (.inl i)) * interior (b.coord (.inl i)) y +
        ExteriorAlgebra.ι K (b (.inr i)) * interior (b.coord (.inr i)) y) := by
    intro i
    rw [interior_sympVec_mul, map_add, interior_sympVec_mul, interior_ι_mul,
      contract_sympVec_coord_inl, contract_sympVec_coord_inr]
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same, one_smul, map_neg,
      neg_mul]
    abel
  have hsum := sum_ι_mul_interior b k hy
  rw [Fintype.sum_sum_type] at hsum
  simp only [dualLefschetz, LinearMap.sum_apply, Module.End.mul_apply, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  simp only [hi]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, sub_smul, Nat.cast_smul_eq_nsmul K g]

end DualLefschetz

section HardLefschetz

variable [CharZero K] {g : ℕ}

/-- **Linear Hard Lefschetz, injectivity.** For a nondegenerate `ω` on a space of dimension `2g`
and `k ≤ g`, `ω^(g - k) ∧ - : ⋀^k V → ⋀^(k + 2(g - k)) V` is injective.

Source: Huybrechts, *Complex Geometry*, §1.2 (Lefschetz decomposition on the exterior algebra);
Voisin I, Ch. 6. -/
theorem lefschetz_injective {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (hg : finrank K V = 2 * g)
    {k : ℕ} (hk : k ≤ g) : Function.Injective (lefschetz ω (g - k) k) := by
  obtain ⟨g', b, hg', rfl⟩ := exists_basis_sympVec_of_isNondegenerate hω
  obtain rfl : g' = g := by omega
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  have h0 := congrArg Subtype.val hx
  rw [coe_lefschetz, ZeroMemClass.coe_zero] at h0
  refine pow_injective_of_comm (fun k => ⋀[K]^k V)
    (LinearMap.mulLeft K (sympVec (K := K) (b ∘ Sum.inl) (b ∘ Sum.inr) : ExteriorAlgebra K V))
    (dualLefschetz b) g' (fun k x hx => mul_mem_of_mem_two (SetLike.coe_mem _) hx)
    (fun k x hx => dualLefschetz_mem b k hx) (fun x hx => dualLefschetz_of_mem_zero b hx)
    (fun x hx => dualLefschetz_of_mem_one b hx) (fun k x hx => dualLefschetz_comm b k hx) k
    (g' - k) (by omega) x x.2 ?_
  rw [LinearMap.pow_mulLeft, LinearMap.mulLeft_apply, h0]

/-- `k + 2(g - k) = 2g - k` for `k ≤ g`. -/
theorem add_two_mul_sub {k : ℕ} (hk : k ≤ g) : k + 2 * (g - k) = 2 * g - k := by
  omega

/-- **Linear Hard Lefschetz.** For a nondegenerate `ω` on a space of dimension `2g` and `k ≤ g`,
`ω^(g - k) ∧ - : ⋀^k V → ⋀^(k + 2(g - k)) V` is bijective: injective, between spaces of the
same dimension `C(2g, k) = C(2g, 2g - k)`.

Source: Huybrechts, *Complex Geometry*, §1.2 (Lefschetz decomposition on the exterior algebra);
Voisin I, Ch. 6. -/
theorem lefschetz_bijective {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (hg : finrank K V = 2 * g)
    {k : ℕ} (hk : k ≤ g) : Function.Bijective (lefschetz ω (g - k) k) := by
  obtain ⟨g', b, -, -⟩ := exists_basis_sympVec_of_isNondegenerate hω
  have : Module.Finite K V := Module.Finite.of_basis b
  have hinj := lefschetz_injective hω hg hk
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [exteriorPower.finrank_eq, exteriorPower.finrank_eq, hg, add_two_mul_sub hk,
    Nat.choose_symm (by omega)]

/-- **The Hard Lefschetz isomorphism** `⋀^k V ≃ₗ[K] ⋀^m V`, `x ↦ ω^(g - k) ∧ x`, for a
nondegenerate `ω` on a space of dimension `2g`, `k ≤ g`, and any name `m` of the degree
`k + 2(g - k)`.

Source: Huybrechts, *Complex Geometry*, §1.2 (Lefschetz decomposition on the exterior algebra);
Voisin I, Ch. 6. -/
noncomputable def lefschetzEquivOfEq {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω)
    (hg : finrank K V = 2 * g) {k m : ℕ} (hk : k ≤ g) (h : k + 2 * (g - k) = m) :
    ⋀[K]^k V ≃ₗ[K] ⋀[K]^m V :=
  (LinearEquiv.ofBijective (lefschetz ω (g - k) k) (lefschetz_bijective hω hg hk)).trans
    (castDeg h)

theorem coe_lefschetzEquivOfEq {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω)
    (hg : finrank K V = 2 * g) {k m : ℕ} (hk : k ≤ g) (h : k + 2 * (g - k) = m) (x : ⋀[K]^k V) :
    (lefschetzEquivOfEq hω hg hk h x : ExteriorAlgebra K V) =
      (ω : ExteriorAlgebra K V) ^ (g - k) * x :=
  coe_lefschetz ω (g - k) k x

/-- **The Hard Lefschetz isomorphism** `⋀^k V ≃ₗ[K] ⋀^(2g - k) V`, `x ↦ ω^(g - k) ∧ x`, for a
nondegenerate `ω` on a space of dimension `2g` and `k ≤ g`.

Source: Huybrechts, *Complex Geometry*, §1.2 (Lefschetz decomposition on the exterior algebra);
Voisin I, Ch. 6. -/
noncomputable def lefschetzEquiv {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω)
    (hg : finrank K V = 2 * g) {k : ℕ} (hk : k ≤ g) : ⋀[K]^k V ≃ₗ[K] ⋀[K]^(2 * g - k) V :=
  lefschetzEquivOfEq hω hg hk (add_two_mul_sub hk)

theorem coe_lefschetzEquiv {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω)
    (hg : finrank K V = 2 * g) {k : ℕ} (hk : k ≤ g) (x : ⋀[K]^k V) :
    (lefschetzEquiv hω hg hk x : ExteriorAlgebra K V) = (ω : ExteriorAlgebra K V) ^ (g - k) * x :=
  coe_lefschetz ω (g - k) k x

end HardLefschetz

section Examples

/-- `e₁ ∧ e₂` on `ℚ²` is nondegenerate. -/
theorem isNondegenerate_ex2 :
    IsNondegenerate (exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 2 → ℚ), Pi.single 1 1]) := by
  refine isNondegenerate_of_wedgePow_ne_zero (g := 1) (by simp) ?_
  rw [wedgePow_one]
  convert ιMulti_basis_ne_zero (Pi.basisFun ℚ (Fin 2)) using 2
  ext i : 1
  fin_cases i <;> simp

/-- `e₁ ∧ e₂ + e₃ ∧ e₄` on `ℚ⁴` is nondegenerate. -/
theorem isNondegenerate_ex4 :
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

/-- `g = 1`, `k = 0`: Hard Lefschetz `ℚ ≅ ⋀²ℚ²` is `1 ↦ ω`, for `ω = e₁ ∧ e₂`. -/
example : (lefschetzEquiv isNondegenerate_ex2 (g := 1) (by simp) (k := 0) (Nat.zero_le _)
      (exteriorPower.ιMulti ℚ 0 Fin.elim0) : ExteriorAlgebra ℚ (Fin 2 → ℚ)) =
    exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 2 → ℚ), Pi.single 1 1] := by
  rw [coe_lefschetzEquiv]
  simp

/-- The same isomorphism through `lefschetzEquivOfEq`, with the target degree named `m = 2`. -/
example : (lefschetzEquivOfEq isNondegenerate_ex2 (g := 1) (by simp) (k := 0) (m := 2)
      (Nat.zero_le _) (by norm_num) (exteriorPower.ιMulti ℚ 0 Fin.elim0) :
      ExteriorAlgebra ℚ (Fin 2 → ℚ)) =
    exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 2 → ℚ), Pi.single 1 1] := by
  rw [coe_lefschetzEquivOfEq]
  simp

/-- `g = 2`, `k = 1`: for `ω = e₁ ∧ e₂ + e₃ ∧ e₄` on `ℚ⁴` (that is, `e₁ ∧ f₁ + e₂ ∧ f₂`),
`x ↦ ω ∧ x : ⋀¹ ℚ⁴ → ⋀³ ℚ⁴` is a bijection. -/
example : Function.Bijective
    (lefschetz (exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 4 → ℚ), Pi.single 1 1] +
        exteriorPower.ιMulti ℚ 2 ![(Pi.single 2 1 : Fin 4 → ℚ), Pi.single 3 1]) 1 1) :=
  lefschetz_bijective isNondegenerate_ex4 (g := 2) (by simp) (k := 1) (by norm_num)

/-- **Falsification.** For the degenerate `ω = e₁ ∧ e₂` on `ℚ⁴`, `x ↦ ω ∧ x : ⋀¹ → ⋀³` is not
injective: `e₁ ↦ 0`. -/
example : ¬ Function.Injective
    (lefschetz (exteriorPower.ιMulti ℚ 2 ![(Pi.single 0 1 : Fin 4 → ℚ), Pi.single 1 1]) 1 1) := by
  intro h
  have hne : exteriorPower.ιMulti ℚ 1 ![(Pi.single 0 1 : Fin 4 → ℚ)] ≠ 0 := by
    intro h0
    have := congrArg (exteriorPower.oneEquiv ℚ (Fin 4 → ℚ)) h0
    rw [exteriorPower.oneEquiv_ιMulti, map_zero] at this
    simpa using congrFun this 0
  refine hne (h (Subtype.ext ?_))
  rw [coe_lefschetz_one, map_zero, ZeroMemClass.coe_zero, coe_ιMulti_two]
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  simp only [Matrix.cons_val_zero, mul_assoc]
  rw [ι_mul_ι_swap, mul_neg, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, neg_zero]

end Examples

end Lefschetz

end HodgeLean.Foundations
