import HodgeLean.Foundations.Program.KernelFramesFamilyFrameValues
import Mathlib.RingTheory.LaurentSeries

/-! # B6-5 stage 5d, family part: Laurent expansions of the principal-part vectors

Laurent expansions of rational functions at a point (`b65q_L`), the binomial expansion of
`(s − b)^{−m}`, the identification of each row of the two Laurent systems with a Laurent
coefficient of `K(s) · v(s)` for the coefficient series `K` (`b65q_principal_row`,
`b65q_beta_row`), lower bounds on orders from the kernel conditions, and the duality of the
q- and r-coefficient series.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Polynomial Matrix
open scoped LaurentSeries RatFunc
namespace HodgeLean.Foundations.Program

/-- Translation `X ↦ X + a` of rational functions. -/
def b65q_shift (a : ℂ) : RatFunc ℂ →+* RatFunc ℂ :=
  RatFunc.mapRingHom (Polynomial.compRingHom (X + C a))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ fun f g h ↦ by
      have : taylor a f = taylor a g := by simpa [taylor_apply] using h
      exact taylor_injective a this)

/-- The Laurent expansion at `a`, in the variable `X − a`. -/
def b65q_L (a : ℂ) : RatFunc ℂ →+* LaurentSeries ℂ :=
  (algebraMap (RatFunc ℂ) (LaurentSeries ℂ)).comp (b65q_shift a)

theorem b65q_shift_algebraMap (a : ℂ) (g : ℂ[X]) :
    b65q_shift a (algebraMap ℂ[X] (RatFunc ℂ) g) = algebraMap ℂ[X] (RatFunc ℂ) (taylor a g) := by
  have := RatFunc.map_apply_div (Polynomial.compRingHom (X + C a))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ fun f g h ↦ by
      have : taylor a f = taylor a g := by simpa [taylor_apply] using h
      exact taylor_injective a this) g 1
  simp only [map_one, div_one] at this
  rw [taylor_apply]
  exact this

theorem b65q_L_algebraMap (a : ℂ) (g : ℂ[X]) :
    b65q_L a (algebraMap ℂ[X] (RatFunc ℂ) g) =
      HahnSeries.ofPowerSeries ℤ ℂ (taylor a g : PowerSeries ℂ) := by
  rw [b65q_L, RingHom.comp_apply, b65q_shift_algebraMap]
  exact (RatFunc.coe_coe _).symm

theorem b65q_L_C (a c : ℂ) : b65q_L a (RatFunc.C c) = HahnSeries.C c := by
  rw [← RatFunc.algebraMap_C, b65q_L_algebraMap, taylor_C, Polynomial.coe_C]
  simp

theorem b65q_L_X_sub_C (a b : ℂ) :
    b65q_L a (RatFunc.X - RatFunc.C b) =
      HahnSeries.single 1 1 + HahnSeries.C (a - b) := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub, b65q_L_algebraMap]
  simp [taylor_X, taylor_C]
  ring

/-- The expansion of `(Z + c)^{−m}`: coefficients `(−1)^l C(m+l−1, l) c^{−m−l}`. -/
def b65q_G (c : ℂ) (m : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun l ↦ (-1) ^ l * ((m + l - 1).choose l : ℂ) * ((c ^ (m + l))⁻¹)

theorem b65q_G_zero (c : ℂ) : b65q_G c 0 = 1 := by
  ext l
  rcases l with _ | l
  · simp [b65q_G]
  · simp [b65q_G, PowerSeries.coeff_one, Nat.choose_eq_zero_of_lt]

theorem b65q_G_succ {c : ℂ} (hc : c ≠ 0) (m : ℕ) :
    (PowerSeries.X + PowerSeries.C c) * b65q_G c (m + 1) = b65q_G c m := by
  ext l
  rcases l with _ | l
  · simp only [b65q_G, add_mul, map_add, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, zero_add]
    simp
    field_simp
    ring
  · rw [add_mul, map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul]
    simp only [b65q_G, PowerSeries.coeff_mk]
    have hp : ((m + 1 + (l + 1) - 1).choose (l + 1) : ℂ) =
        ((m + 1 + l - 1).choose l : ℂ) + ((m + (l + 1) - 1).choose (l + 1) : ℂ) := by
      rw [show m + 1 + (l + 1) - 1 = (m + l) + 1 by omega, show m + 1 + l - 1 = m + l by omega,
        show m + (l + 1) - 1 = m + l by omega, Nat.choose_succ_succ]
      push_cast; ring
    rw [hp]
    have hc' : ∀ k : ℕ, c ^ k ≠ 0 := fun k ↦ pow_ne_zero _ hc
    field_simp
    ring

theorem b65q_G_mul_pow {c : ℂ} (hc : c ≠ 0) (m : ℕ) :
    b65q_G c m * (PowerSeries.X + PowerSeries.C c) ^ m = 1 := by
  induction m with
  | zero => simp [b65q_G_zero]
  | succ m ih =>
    have : b65q_G c (m + 1) * (PowerSeries.X + PowerSeries.C c) ^ (m + 1) =
        ((PowerSeries.X + PowerSeries.C c) * b65q_G c (m + 1)) *
          (PowerSeries.X + PowerSeries.C c) ^ m := by ring
    rw [this, b65q_G_succ hc, ih]

theorem b65q_L_inv_pow_ne {a b : ℂ} (h : a ≠ b) (m : ℕ) :
    b65q_L a ((RatFunc.X - RatFunc.C b) ^ m)⁻¹ = HahnSeries.ofPowerSeries ℤ ℂ (b65q_G (a - b) m) := by
  rw [map_inv₀, map_pow, b65q_L_X_sub_C]
  have hc : a - b ≠ 0 := sub_ne_zero.mpr h
  have := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) (b65q_G_mul_pow hc m)
  rw [map_mul, map_pow, map_add, HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C,
    map_one (HahnSeries.ofPowerSeries ℤ ℂ)] at this
  exact (eq_inv_of_mul_eq_one_left this).symm

theorem b65q_L_inv_pow_eq (a : ℂ) (m : ℕ) :
    b65q_L a ((RatFunc.X - RatFunc.C a) ^ m)⁻¹ = HahnSeries.single (-(m : ℤ)) 1 := by
  rw [map_inv₀, map_pow, b65q_L_X_sub_C, sub_self, map_zero, add_zero]
  rw [← RatFunc.single_one_eq_pow, HahnSeries.inv_single, inv_one]

theorem b65q_ofPS_coeff (A : PowerSeries ℂ) (n : ℤ) :
    (HahnSeries.ofPowerSeries ℤ ℂ A).coeff n = if 0 ≤ n then PowerSeries.coeff n.toNat A else 0 := by
  have := PowerSeries.coeff_coe (f := A) n
  rw [show ((A : LaurentSeries ℂ)) = HahnSeries.ofPowerSeries ℤ ℂ A from rfl] at this
  rw [this]
  split_ifs with h1 h2 h2
  · omega
  · rfl
  · rw [show n.natAbs = n.toNat by omega]
  · omega

theorem b65q_coeff_mul_single (A : PowerSeries ℂ) (n : ℤ) (m : ℕ) :
    (HahnSeries.ofPowerSeries ℤ ℂ A * HahnSeries.single (-(m : ℤ)) 1).coeff n =
      if 0 ≤ n + m then PowerSeries.coeff (n + m).toNat A else 0 := by
  rw [HahnSeries.coeff_mul_single, mul_one, b65q_ofPS_coeff, show n - -(m : ℤ) = n + m by ring]

theorem b65q_coeff_mul_ofPS (A B : PowerSeries ℂ) (n : ℤ) :
    (HahnSeries.ofPowerSeries ℤ ℂ A * HahnSeries.ofPowerSeries ℤ ℂ B).coeff n =
      if 0 ≤ n then ∑ l ∈ Finset.range (n.toNat + 1),
        PowerSeries.coeff (n.toNat - l) A * PowerSeries.coeff l B else 0 := by
  rw [← map_mul, b65q_ofPS_coeff]
  split_ifs
  · rw [PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp [mul_comm]
  · rfl

/-- The power series of the entry `(j, i)` of a sequence of matrices. -/
def b65q_Kps (K : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (j i : Fin 4) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ K n j i

/-- The formal Laurent vector `K(s) · v(s)` at `a`, component `j`. -/
def b65q_KL (a : ℂ) (K : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (v : Fin 4 → RatFunc ℂ) (j : Fin 4) :
    LaurentSeries ℂ :=
  ∑ i : Fin 4, HahnSeries.ofPowerSeries ℤ ℂ (b65q_Kps K j i) * b65q_L a (v i)

theorem b65q_L_div (a c : ℂ) (Y : RatFunc ℂ) :
    b65q_L a (RatFunc.C c / Y) = HahnSeries.C c * b65q_L a Y⁻¹ := by
  rw [div_eq_mul_inv, map_mul, b65q_L_C]

/-- The column `4b + i` of a principal-part system. -/
def b65q_e36 : Fin 9 × Fin 4 ≃ Fin 36 := finProdFinEquiv

theorem b65q_e36_val (b : Fin 9) (i : Fin 4) : (b65q_e36 (b, i)).val = i.val + 4 * b.val := rfl

theorem b65q_principalEntry_term (t : Fin 4 ⊕ Fin 12 → ℂ) (K : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℂ)
    (k j : Fin 4) (n : ℤ) (b : Fin 9) (i : Fin 4)
    (ht : ∀ b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b')) :
    b65q_principalEntry t K k j n (b65q_e36 (b, i)) =
      (HahnSeries.ofPowerSeries ℤ ℂ (b65q_Kps (K k) j i) *
        b65q_L (t (Sum.inl k)) ((RatFunc.X - RatFunc.C (t (Sum.inl (b65k_poleIndex b)))) ^
          b65k_poleOrder b)⁻¹).coeff n := by
  have h1 : (⟨(b65q_e36 (b, i)).val / 4, by omega⟩ : Fin 9) = b := by
    ext; simp only [b65q_e36_val]; omega
  have h2 : (⟨(b65q_e36 (b, i)).val % 4, by omega⟩ : Fin 4) = i := by
    ext; simp only [b65q_e36_val]; omega
  unfold b65q_principalEntry
  rw [h1, h2]
  by_cases hb : b65k_poleIndex b = k
  · rw [if_pos hb, hb, b65q_L_inv_pow_eq, b65q_coeff_mul_single]
    simp [b65q_Kps]
  · rw [if_neg hb, b65q_L_inv_pow_ne (ht _ hb), b65q_coeff_mul_ofPS]
    split_ifs
    · refine Finset.sum_congr rfl fun l _ ↦ ?_
      simp [b65q_Kps, b65q_G]
    · rfl

/-- **Rows of the principal-part systems are Laurent coefficients.** -/
theorem b65q_principal_row (t : Fin 4 ⊕ Fin 12 → ℂ) (K : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℂ)
    (k j : Fin 4) (n : ℤ) (c : Fin 36 → ℂ)
    (ht : ∀ b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b')) :
    ∑ col : Fin 36, b65q_principalEntry t K k j n col * c col =
      (b65q_KL (t (Sum.inl k)) (K k) (b65q_principal t c) j).coeff n := by
  rw [← Equiv.sum_comp b65q_e36, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [b65q_KL, b65q_principal, map_sum, b65q_L_div, Finset.mul_sum, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [b65q_principalEntry_term t K k j n b i ht, mul_left_comm, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul, smul_eq_mul, mul_comm]
  congr 2
  ext; simp [b65q_e36_val]; omega

/-- The column `6e + v` of the beta block. -/
def b65q_e12 : Fin 2 × Fin 6 ≃ Fin 12 := finProdFinEquiv

theorem b65q_e12_val (e : Fin 2) (v : Fin 6) : (b65q_e12 (e, v)).val = v.val + 6 * e.val := rfl

/-- The moving-pole part `Σ_t β(node_t) w_t/(s − t)` of a q-vector. -/
def b65q_betaPart (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (j : Fin 4) : RatFunc ℂ :=
  ∑ x : Fin 12, RatFunc.C ((∑ v : Fin 6,
      d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val) * w x j) /
    (RatFunc.X - RatFunc.C (t (Sum.inr x)))

theorem b65q_qVector_eq (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (j : Fin 4) : b65q_qVector t node w d j =
      b65q_principal t (fun i ↦ d ⟨i.val, by omega⟩) j + b65q_betaPart t node w d j := rfl

theorem b65q_beta_term (a b β : ℂ) (h : a ≠ b) (A : PowerSeries ℂ) (n : ℤ) :
    (HahnSeries.ofPowerSeries ℤ ℂ A * b65q_L a (RatFunc.C β / (RatFunc.X - RatFunc.C b))).coeff n =
      β * (if 0 ≤ n then ∑ l ∈ Finset.range (n.toNat + 1),
        PowerSeries.coeff (n.toNat - l) A * (-((b - a) ^ (l + 1))⁻¹) else 0) := by
  rw [b65q_L_div, ← pow_one (RatFunc.X - RatFunc.C b), b65q_L_inv_pow_ne h, mul_left_comm,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, b65q_coeff_mul_ofPS]
  congr 1
  split_ifs
  · refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [b65q_G, PowerSeries.coeff_mk]
    have hab : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    rw [show 1 + l - 1 = l by omega, Nat.choose_self, show a - b = (-1) * (b - a) by ring,
      show 1 + l = l + 1 by ring, mul_pow, pow_succ (-1 : ℂ) l]
    have h1 : ((-1 : ℂ) ^ l) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hsq : ((-1 : ℂ)) ^ (l * 2) = 1 := by rw [mul_comm, pow_mul]; norm_num
    have h2 : (b - a) ^ (l + 1) ≠ 0 := pow_ne_zero _ hab
    field_simp
    ring
  · rfl

theorem b65q_betaEntry_e12 (t : Fin 4 ⊕ Fin 12 → ℂ) (K : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℂ)
    (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ) (k j : Fin 4) (n : ℤ) (e : Fin 2) (v : Fin 6) :
    b65q_betaEntry t K node w k j n ⟨(b65q_e12 (e, v)).val / 6, by omega⟩
      ⟨(b65q_e12 (e, v)).val % 6, by omega⟩ = b65q_betaEntry t K node w k j n e v := by
  congr 1 <;> ext <;> simp only [b65q_e12_val] <;> omega

/-- **Rows of the beta block are Laurent coefficients.** -/
theorem b65q_beta_row (t : Fin 4 ⊕ Fin 12 → ℂ) (K : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℂ)
    (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ) (k j : Fin 4) (n : ℤ) (d : Fin 48 → ℂ)
    (ht : ∀ x, t (Sum.inl k) ≠ t (Sum.inr x)) :
    ∑ c : Fin 12, b65q_betaEntry t K node w k j n ⟨c.val / 6, by omega⟩ ⟨c.val % 6, by omega⟩ *
        d ⟨36 + c.val, by omega⟩ =
      (b65q_KL (t (Sum.inl k)) (K k) (b65q_betaPart t node w d) j).coeff n := by
  set β : Fin 12 → ℂ := fun x ↦ ∑ v : Fin 6,
    d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val
  set S : Fin 12 → ℂ := fun x ↦ if 0 ≤ n then ∑ l ∈ Finset.range (n.toNat + 1),
    (K k (n.toNat - l) *ᵥ w x) j * -((t (Sum.inr x) - t (Sum.inl k)) ^ (l + 1))⁻¹ else 0
  have hR : (b65q_KL (t (Sum.inl k)) (K k) (b65q_betaPart t node w d) j).coeff n =
      ∑ x, β x * S x := by
    simp only [b65q_KL, b65q_betaPart, map_sum, Finset.mul_sum, HahnSeries.coeff_sum]
    rw [Finset.sum_comm]
    simp only [b65q_beta_term _ _ _ (ht _)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [S, β]
    split_ifs
    · simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, b65q_Kps,
        PowerSeries.coeff_mk]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      ring
    · simp
  have hkey : ∀ e v, b65q_betaEntry t K node w k j n e v =
      ∑ x, if b65q_fibreIndex x = e then node x ^ v.val * S x else 0 := by
    intro e v
    unfold b65q_betaEntry
    simp only [S]
    split_ifs <;> simp
  have hL : ∑ c : Fin 12, b65q_betaEntry t K node w k j n ⟨c.val / 6, by omega⟩
      ⟨c.val % 6, by omega⟩ * d ⟨36 + c.val, by omega⟩ = ∑ x, β x * S x := by
    rw [← Equiv.sum_comp b65q_e12, Fintype.sum_prod_type]
    simp only [b65q_betaEntry_e12]
    simp only [hkey, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_congr rfl fun e _ ↦ Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, β, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    have : (⟨36 + (b65q_e12 (b65q_fibreIndex x, v)).val, by omega⟩ : Fin 48) =
        ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ := by
      ext; simp only [b65q_e12_val]; omega
    rw [this]; ring
  rw [hL, hR]

theorem b65q_KL_add (a : ℂ) (K : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (u v : Fin 4 → RatFunc ℂ) (j : Fin 4) :
    b65q_KL a K (fun i ↦ u i + v i) j = b65q_KL a K u j + b65q_KL a K v j := by
  simp only [b65q_KL, map_add, mul_add, Finset.sum_add_distrib]

theorem b65q_rSystem_row (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : Fin 36 → ℂ) (r : Fin 41)
    (ht : ∀ k b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b')) :
    (b65q_rSystem t A P *ᵥ c) ⟨r.val, by omega⟩ =
      (b65q_KL (t (Sum.inl (b65q_rRow r).1)) (b65q_rCoeff t A P (b65q_rRow r).1)
        (b65q_principal t c) (b65q_rRow r).2.1).coeff (b65q_rRow r).2.2 := by
  rw [← b65q_principal_row _ _ _ _ _ _ (ht _)]
  unfold Matrix.mulVec dotProduct
  refine Finset.sum_congr rfl fun col _ ↦ ?_
  simp only [b65q_rSystem, dif_pos r.isLt]

theorem b65q_qSystem_row (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (r : Fin 53)
    (ht : ∀ k b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b'))
    (ht' : ∀ k x, t (Sum.inl k) ≠ t (Sum.inr x)) :
    (b65q_qSystem t A P node w *ᵥ d) ⟨r.val, by omega⟩ =
      (b65q_KL (t (Sum.inl (b65q_qRow r).1)) (b65q_qCoeff t A P (b65q_qRow r).1)
        (b65q_qVector t node w d) (b65q_qRow r).2.1).coeff (b65q_qRow r).2.2 := by
  rw [show b65q_qVector t node w d = fun i ↦ b65q_principal t (fun i ↦ d ⟨i.val, by omega⟩) i +
    b65q_betaPart t node w d i from rfl, b65q_KL_add, HahnSeries.coeff_add, ← b65q_principal_row _ _ _ _ _ _ (ht _),
    ← b65q_beta_row _ _ _ _ _ _ _ _ (ht' _)]
  unfold Matrix.mulVec dotProduct
  rw [Fin.sum_univ_add (a := 36) (b := 12)]
  congr 1
  · refine Finset.sum_congr rfl fun c _ ↦ ?_
    simp only [b65q_qSystem, dif_pos r.isLt, Fin.coe_castAdd, dif_pos c.isLt]
    rfl
  · refine Finset.sum_congr rfl fun c _ ↦ ?_
    have hc : ¬ (Fin.natAdd 36 c : Fin 48).val < 36 := by simp
    simp only [b65q_qSystem, dif_pos r.isLt, dif_neg hc]
    congr 2 <;> ext <;> simp

/-- `f` has order at least `n`. -/
def b65q_ge (f : LaurentSeries ℂ) (n : ℤ) : Prop := ((n : ℤ) : WithTop ℤ) ≤ f.orderTop

theorem b65q_ge_iff (f : LaurentSeries ℂ) (n : ℤ) : b65q_ge f n ↔ ∀ m : ℤ, m < n → f.coeff m = 0 := by
  rw [b65q_ge, HahnSeries.le_orderTop_iff_forall]
  exact ⟨fun h m hm ↦ h m (by exact_mod_cast hm), fun h m hm ↦ h m (by exact_mod_cast hm)⟩

theorem b65q_ge_mono {f : LaurentSeries ℂ} {n m : ℤ} (h : b65q_ge f n) (hmn : m ≤ n) :
    b65q_ge f m := le_trans (by exact_mod_cast hmn) h

theorem b65q_ge_zero (n : ℤ) : b65q_ge 0 n := by simp [b65q_ge]

theorem b65q_ge_add {f g : LaurentSeries ℂ} {n : ℤ} (hf : b65q_ge f n) (hg : b65q_ge g n) :
    b65q_ge (f + g) n := le_trans (le_min hf hg) HahnSeries.min_orderTop_le_orderTop_add

theorem b65q_ge_sum {ι : Type*} (S : Finset ι) {f : ι → LaurentSeries ℂ} {n : ℤ}
    (h : ∀ i ∈ S, b65q_ge (f i) n) : b65q_ge (∑ i ∈ S, f i) n := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using b65q_ge_zero n
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact b65q_ge_add (h a (Finset.mem_insert_self a S)) (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

theorem b65q_ge_mul {f g : LaurentSeries ℂ} {n m : ℤ} (hf : b65q_ge f n) (hg : b65q_ge g m) :
    b65q_ge (f * g) (n + m) := by
  rw [b65q_ge, HahnSeries.orderTop_mul, WithTop.coe_add]
  exact add_le_add hf hg

theorem b65q_ge_ofPS (A : PowerSeries ℂ) : b65q_ge (HahnSeries.ofPowerSeries ℤ ℂ A) 0 := by
  rw [b65q_ge_iff]
  intro m hm
  rw [b65q_ofPS_coeff, if_neg (by omega)]

theorem b65q_ge_C (c : ℂ) : b65q_ge (HahnSeries.C c) 0 := by
  rw [← HahnSeries.ofPowerSeries_C]; exact b65q_ge_ofPS _

theorem b65q_ge_single (m : ℤ) (c : ℂ) : b65q_ge (HahnSeries.single m c) m := by
  rw [b65q_ge]; exact HahnSeries.orderTop_single_le

theorem b65q_ge_smul {f : LaurentSeries ℂ} {n : ℤ} (c : ℂ) (h : b65q_ge f n) : b65q_ge (c • f) n := by
  rw [← HahnSeries.C_mul_eq_smul]; simpa using b65q_ge_mul (b65q_ge_C c) h

theorem b65q_ge_L_inv_pow (a b : ℂ) (m : ℕ) :
    b65q_ge (b65q_L a ((RatFunc.X - RatFunc.C b) ^ m)⁻¹) (if a = b then -(m : ℤ) else 0) := by
  split_ifs with h
  · subst h; rw [b65q_L_inv_pow_eq]; exact b65q_ge_single _ _
  · rw [b65q_L_inv_pow_ne h]; exact b65q_ge_ofPS _

theorem b65q_ge_L_poly (a : ℂ) (g : ℂ[X]) : b65q_ge (b65q_L a (algebraMap ℂ[X] (RatFunc ℂ) g)) 0 := by
  rw [b65q_L_algebraMap]; exact b65q_ge_ofPS _

/-- The `s`-order of a fixed principal part at a pole: at least `−3`. -/
theorem b65q_ge_L_principal (t : Fin 4 ⊕ Fin 12 → ℂ) (c : Fin 36 → ℂ) (a : ℂ) (i : Fin 4) :
    b65q_ge (b65q_L a (b65q_principal t c i)) (-3) := by
  simp only [b65q_principal, map_sum, b65q_L_div]
  refine b65q_ge_sum _ fun b _ ↦ ?_
  have h := b65q_ge_mul (b65q_ge_C (c ⟨4 * b.val + i.val, by omega⟩))
    (b65q_ge_L_inv_pow a (t (Sum.inl (b65k_poleIndex b))) (b65k_poleOrder b))
  refine b65q_ge_mono h ?_
  have := b65q_poleOrder_le b
  split_ifs <;> omega

theorem b65q_ge_KL {a : ℂ} {K : ℕ → Matrix (Fin 4) (Fin 4) ℂ} {v : Fin 4 → RatFunc ℂ} {n : ℤ}
    (hv : ∀ i, b65q_ge (b65q_L a (v i)) n) (j : Fin 4) : b65q_ge (b65q_KL a K v j) n := by
  refine b65q_ge_sum _ fun i _ ↦ ?_
  simpa using b65q_ge_mul (b65q_ge_ofPS (b65q_Kps K j i)) (hv i)

/-- The floors `⌊λ_{k,j}⌋` and `⌊−λ_{k,j}⌋` of the fixed-pole exponents. -/
def b65q_rFloor : Fin 4 → Fin 4 → ℤ :=
  ![![-2, -1, -1, 1], ![-3, -2, -2, 3], ![-2, -2, 2, 2], ![-2, -2, 2, 2]]

def b65q_qFloor : Fin 4 → Fin 4 → ℤ :=
  ![![1, 1, 1, -2], ![3, 2, 2, -3], ![2, 2, -2, -2], ![2, 2, -2, -2]]

theorem b65q_rRow_cover : ∀ k j : Fin 4, ∀ m : Fin 7, (m : ℤ) - 3 < b65q_rFloor k j →
    ∃ r : Fin 41, b65q_rRow r = (k, j, (m : ℤ) - 3) := by decide

theorem b65q_qRow_cover : ∀ k j : Fin 4, ∀ m : Fin 7, (m : ℤ) - 3 < b65q_qFloor k j →
    ∃ r : Fin 53, b65q_qRow r = (k, j, (m : ℤ) - 3) := by decide

theorem b65q_floor_le (k j : Fin 4) : b65q_rFloor k j ≤ 3 ∧ b65q_qFloor k j ≤ 3 := by
  revert k j; decide

theorem b65q_floor_sum (k j : Fin 4) :
    (if k = 0 then -1 else 0) ≤ b65q_rFloor k j + b65q_qFloor k j := by
  revert k j; decide

theorem b65q_r_order (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : Fin 36 → ℂ) (hc : b65q_rSystem t A P *ᵥ c = 0)
    (ht : ∀ k b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b')) (k j : Fin 4) :
    b65q_ge (b65q_KL (t (Sum.inl k)) (b65q_rCoeff t A P k) (b65q_principal t c) j)
      (b65q_rFloor k j) := by
  rw [b65q_ge_iff]
  intro m hm
  by_cases hm3 : m < -3
  · exact (b65q_ge_iff _ _).mp (b65q_ge_KL (fun i ↦ b65q_ge_L_principal t c _ i) j) m hm3
  · have hfl := (b65q_floor_le k j).1
    obtain ⟨r, hr⟩ := b65q_rRow_cover k j ⟨(m + 3).toNat, by omega⟩ (by simp; omega)
    have h := b65q_rSystem_row t A P c r ht
    rw [hc, hr] at h
    simp only [Pi.zero_apply] at h
    rw [show ((⟨(m + 3).toNat, by omega⟩ : Fin 7) : ℤ) - 3 = m by simp; omega] at h
    exact h.symm

theorem b65q_ge_L_betaPart (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (a : ℂ) (ha : ∀ x, a ≠ t (Sum.inr x)) (i : Fin 4) :
    b65q_ge (b65q_L a (b65q_betaPart t node w d i)) 0 := by
  simp only [b65q_betaPart, map_sum]
  refine b65q_ge_sum _ fun x _ ↦ ?_
  rw [← pow_one (RatFunc.X - RatFunc.C (t (Sum.inr x))), b65q_L_div, b65q_L_inv_pow_ne (ha x)]
  simpa using b65q_ge_mul (b65q_ge_C _) (b65q_ge_ofPS _)

theorem b65q_q_order (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (hd : b65q_qSystem t A P node w *ᵥ d = 0)
    (ht : ∀ k b', b' ≠ k → t (Sum.inl k) ≠ t (Sum.inl b'))
    (ht' : ∀ k x, t (Sum.inl k) ≠ t (Sum.inr x)) (k j : Fin 4) :
    b65q_ge (b65q_KL (t (Sum.inl k)) (b65q_qCoeff t A P k) (b65q_qVector t node w d) j)
      (b65q_qFloor k j) := by
  rw [b65q_ge_iff]
  intro m hm
  by_cases hm3 : m < -3
  · refine (b65q_ge_iff _ _).mp (b65q_ge_KL (fun i ↦ ?_) j) m hm3
    rw [b65q_qVector_eq, map_add]
    exact b65q_ge_add (b65q_ge_L_principal t _ _ i)
      (b65q_ge_mono (b65q_ge_L_betaPart t node w d _ (ht' k) i) (by norm_num))
  · have hfl := (b65q_floor_le k j).2
    obtain ⟨r, hr⟩ := b65q_qRow_cover k j ⟨(m + 3).toNat, by omega⟩ (by simp; omega)
    have h := b65q_qSystem_row t A P node w d r ht ht'
    rw [hd, hr] at h
    simp only [Pi.zero_apply] at h
    rw [show ((⟨(m + 3).toNat, by omega⟩ : Fin 7) : ℤ) - 3 = m by simp; omega] at h
    exact h.symm

theorem b65q_seriesInvUpTo_stable (H : ℕ → Matrix (Fin 4) (Fin 4) ℂ) {n N : ℕ} (h : n ≤ N) :
    b65q_seriesInvUpTo H N n = b65q_seriesInv H n := by
  induction N with
  | zero => rw [Nat.le_zero.mp h]; rfl
  | succ N ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · rw [b65q_seriesInvUpTo, Function.update_of_ne (by omega), ih (by omega)]
    · subst h; rfl

theorem b65q_seriesInv_mul (H : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (h0 : H 0 = 1) (N : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N, H p.1 * b65q_seriesInv H p.2 = if N = 0 then 1 else 0 := by
  rcases N with _ | N
  · simp [h0, b65q_seriesInv, b65q_seriesInvUpTo]
  · rw [Finset.Nat.sum_antidiagonal_succ, if_neg (by omega), h0, one_mul]
    have hs : b65q_seriesInv H (N + 1) =
        -∑ m ∈ Finset.range (N + 1), H (m + 1) * b65q_seriesInv H (N - m) := by
      rw [b65q_seriesInv, b65q_seriesInvUpTo, Function.update_self]
      congr 1
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      rw [b65q_seriesInvUpTo_stable H (by omega)]
    rw [hs, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp

theorem b65q_gauge_zero_coeff (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) : b65q_gauge t A P k 0 = 1 := by
  simp [b65q_gauge, b65q_gaugeUpTo]

/-- **The q- and r-coefficient series are dual**: `Σ_j (PH)ᵀ_{ji} (H⁻¹P⁻¹)_{jl} = δ_{il}`. -/
theorem b65q_coeff_pair (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) (hP : P k * (P k)⁻¹ = 1) (i l : Fin 4) :
    ∑ j : Fin 4, b65q_Kps (b65q_qCoeff t A P k) j i * b65q_Kps (b65q_rCoeff t A P k) j l =
      if i = l then 1 else 0 := by
  ext N
  simp only [map_sum, PowerSeries.coeff_mul, b65q_Kps, PowerSeries.coeff_mk, b65q_qCoeff,
    b65q_rCoeff, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  have hH := b65q_seriesInv_mul (b65q_gauge t A (P k) k) (b65q_gauge_zero_coeff t A (P k) k) N
  have : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N, ∑ j : Fin 4,
      (P k * b65q_gauge t A (P k) k p.1) i j *
        (b65q_seriesInv (b65q_gauge t A (P k) k) p.2 * (P k)⁻¹) j l =
      (P k * (∑ p ∈ Finset.HasAntidiagonal.antidiagonal N, b65q_gauge t A (P k) k p.1 *
        b65q_seriesInv (b65q_gauge t A (P k) k) p.2) * (P k)⁻¹) i l := by
    rw [Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [show P k * (b65q_gauge t A (P k) k p.1 * b65q_seriesInv (b65q_gauge t A (P k) k) p.2) *
      (P k)⁻¹ = (P k * b65q_gauge t A (P k) k p.1) *
        (b65q_seriesInv (b65q_gauge t A (P k) k) p.2 * (P k)⁻¹) by noncomm_ring]
    rw [Matrix.mul_apply]
  rw [this, hH]
  split_ifs with h1 h2 h2
  · subst h1; simp [hP, h2]
  · subst h1; simp [hP, Matrix.one_apply, h2]
  · simp [PowerSeries.coeff_one, h1]
  · simp [PowerSeries.coeff_one, h1]

/-- **The pairing of formal Laurent vectors.** -/
theorem b65q_KL_pair (a : ℂ) (Kq Kr : ℕ → Matrix (Fin 4) (Fin 4) ℂ)
    (hK : ∀ i l, ∑ j : Fin 4, b65q_Kps Kq j i * b65q_Kps Kr j l = if i = l then 1 else 0)
    (u v : Fin 4 → RatFunc ℂ) :
    ∑ j : Fin 4, b65q_KL a Kq u j * b65q_KL a Kr v j = b65q_L a (∑ j : Fin 4, u j * v j) := by
  simp only [b65q_KL, Finset.sum_mul, Finset.mul_sum, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have : ∀ y, ∑ x : Fin 4, HahnSeries.ofPowerSeries ℤ ℂ (b65q_Kps Kq x y) * b65q_L a (u y) *
      (HahnSeries.ofPowerSeries ℤ ℂ (b65q_Kps Kr x i) * b65q_L a (v i)) =
      b65q_L a (u y) * b65q_L a (v i) *
        HahnSeries.ofPowerSeries ℤ ℂ (∑ j : Fin 4, b65q_Kps Kq j y * b65q_Kps Kr j i) := by
    intro y
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul]; ring
  rw [Finset.sum_comm, Finset.sum_congr rfl fun y _ ↦ this y]
  simp only [hK]
  rw [Finset.sum_eq_single i (fun l _ hl ↦ by simp [hl]) (by simp)]
  simp

end HodgeLean.Foundations.Program
