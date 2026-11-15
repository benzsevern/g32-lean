import HodgeLean.Papers.PapersSupplyDefs
import HodgeLean.Papers.PapersMore

/-! # Proofs for the compact paper results, batch 5

The `_aux` theorems behind the frozen spec `HodgeLean/Papers/PapersSupply.lean`
(`docs/specs/PapersSupply.md`).
-/

namespace HodgeLean.Papers

theorem papers_g32_galois_inner_aux {k : Type*} [Field k] {H : Type*} [Group H] [Fintype H] (γ : k →+* k) (χ : H →* kˣ) (t : ℕ) (hγ : ∀ h, γ (χ h : k) = (χ h : k) ^ t) (f : H → k) :
    γ (papersInner f (papersLinChar χ)) = papersInner (fun h => γ (f h)) (papersLinChar (χ ^ t)) := by
  simp only [papersInner, papersLinChar, map_mul, map_inv₀, map_natCast, map_sum, hγ,
    MonoidHom.pow_apply, Units.val_pow_eq_pow_val]

/-- The character of `papersLinRep χ` is `χ`. -/
private theorem papers_linRep_char {k : Type*} [Field k] {H : Type*} [Group H] (χ : H →* kˣ)
    (h : H) : (papersLinRep χ).character h = (χ h : k) := by
  change LinearMap.trace k k (Algebra.lmul k k (χ h : k)) = _
  rw [← Algebra.trace_apply, Algebra.trace_self_apply]

/-- The character of `papersResRep H V` is the restriction of the character of `V`. -/
private theorem papers_resRep_char {k : Type*} [Field k] {G : Type*} [Group G] (H : Subgroup G)
    (V : FDRep k G) (h : H) : (papersResRep H V).character h = V.character h := rfl

theorem papers_g32_mult_eq_inner_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] (H : Subgroup G) [Fintype H] (V : FDRep k G) (χ : H →* kˣ) :
    papersInner (papersRes H V.character) (papersLinChar χ) = (papersMult H V χ : k) := by
  have : Invertible (Nat.card H : k) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [papersMult, ← FDRep.scalar_product_char_eq_finrank_equivariant, papersInner,
    Nat.card_eq_fintype_card]
  simp only [papersRes, papersLinChar, papers_linRep_char, papers_resRep_char]

theorem papers_g32_galois_mult_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] (H : Subgroup G) [Fintype H] (τ : FDRep k G) (γ : k →+* k) (χ : H →* kˣ) (t : ℕ) (hγ : ∀ h, γ (χ h : k) = (χ h : k) ^ t) :
    papersInner (papersRes H fun g => γ (τ.character g)) (papersLinChar (χ ^ t)) = (papersMult H τ χ : k) := by
  change papersInner (fun h => γ (papersRes H τ.character h)) (papersLinChar (χ ^ t)) = _
  rw [← papers_g32_galois_inner_aux γ χ t hγ, papers_g32_mult_eq_inner_aux, map_natCast]

theorem papers_g32_galois_mult_fix_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] (H : Subgroup G) [Fintype H] (τ : FDRep k G) (γ : k →+* k) (χ : H →* kˣ) (t : ℕ) (hγ : ∀ h, γ (χ h : k) = (χ h : k) ^ t) (hfix : ∀ g, γ (τ.character g) = τ.character g) :
    papersMult H τ (χ ^ t) = papersMult H τ χ := by
  have h := papers_g32_galois_mult_aux H τ γ χ t hγ
  simp only [hfix] at h
  exact Nat.cast_injective (R := k) ((papers_g32_mult_eq_inner_aux H τ (χ ^ t)).symm.trans h)

theorem papers_g32_galois_mult_swap_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] (H : Subgroup G) [Fintype H] (τ τbar : FDRep k G) (γ : k →+* k) (χ : H →* kˣ) (t : ℕ) (hγ : ∀ h, γ (χ h : k) = (χ h : k) ^ t) (hswap : ∀ g, γ (τ.character g) = τbar.character g) :
    papersMult H τbar (χ ^ t) = papersMult H τ χ := by
  have h := papers_g32_galois_mult_aux H τ γ χ t hγ
  simp only [hswap] at h
  exact Nat.cast_injective (R := k) ((papers_g32_mult_eq_inner_aux H τbar (χ ^ t)).symm.trans h)

theorem papers_g32_sign_fix_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] {ι κ : Type*} (τ τbar : ι → FDRep k G) (η : κ → FDRep k G) (H : Subgroup G) [Fintype H] (γ : k →+* k) (χ : H →* kˣ) (t : ℕ) (hγ : ∀ h, γ (χ h : k) = (χ h : k) ^ t) (hτ : ∀ i g, γ ((τ i).character g) = (τ i).character g) (hτbar : ∀ i g, γ ((τbar i).character g) = (τbar i).character g) (hη : ∀ j g, γ ((η j).character g) = (η j).character g) :
    papersA τ τbar η H (χ ^ t) = papersA τ τbar η H χ := by
  simp only [papersA, papers_g32_galois_mult_fix_aux H _ γ χ t hγ (hτ _),
    papers_g32_galois_mult_fix_aux H _ γ χ t hγ (hτbar _),
    papers_g32_galois_mult_fix_aux H _ γ χ t hγ (hη _)]

theorem papers_g32_sign_swap_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] {ι κ : Type*} (τ τbar : ι → FDRep k G) (η : κ → FDRep k G) (H : Subgroup G) [Fintype H] (γ : k →+* k) (χ : H →* kˣ) (t : ℕ) (hγ : ∀ h, γ (χ h : k) = (χ h : k) ^ t) (hτ : ∀ i g, γ ((τ i).character g) = (τbar i).character g) (hτbar : ∀ i g, γ ((τbar i).character g) = (τ i).character g) (hη : ∀ j g, γ ((η j).character g) = (η j).character g) :
    (papersA τ τbar η H (χ ^ t)).1 = -(papersA τ τbar η H χ).1 ∧ (papersA τ τbar η H (χ ^ t)).2 = (papersA τ τbar η H χ).2 := by
  refine ⟨funext fun i => ?_, funext fun j => ?_⟩
  · simp only [papersA, Pi.neg_apply, papers_g32_galois_mult_swap_aux H _ _ γ χ t hγ (hτ i),
      papers_g32_galois_mult_swap_aux H _ _ γ χ t hγ (hτbar i)]
    ring
  · simp only [papersA, papers_g32_galois_mult_fix_aux H _ γ χ t hγ (hη j)]

theorem papers_g32_sign_free_vanish_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] {ι κ : Type*} (τ τbar : ι → FDRep k G) (η : κ → FDRep k G) (H : Subgroup G) [Fintype H] (γ₁ γ₂ : k →+* k) (χ : H →* kˣ) (t : ℕ) (hγ₁ : ∀ h, γ₁ (χ h : k) = (χ h : k) ^ t) (hγ₂ : ∀ h, γ₂ (χ h : k) = (χ h : k) ^ t) (hfix : ∀ i g, γ₁ ((τ i).character g) = (τ i).character g ∧ γ₁ ((τbar i).character g) = (τbar i).character g) (hswap : ∀ i g, γ₂ ((τ i).character g) = (τbar i).character g ∧ γ₂ ((τbar i).character g) = (τ i).character g) :
    (papersA τ τbar η H χ).1 = 0 := by
  funext i
  have h1 := papers_g32_galois_mult_fix_aux H _ γ₁ χ t hγ₁ fun g => (hfix i g).1
  have h2 := papers_g32_galois_mult_fix_aux H _ γ₁ χ t hγ₁ fun g => (hfix i g).2
  have h3 := papers_g32_galois_mult_swap_aux H _ _ γ₂ χ t hγ₂ fun g => (hswap i g).1
  have h4 := papers_g32_galois_mult_swap_aux H _ _ γ₂ χ t hγ₂ fun g => (hswap i g).2
  simp only [papersA, Pi.zero_apply]
  omega

theorem papers_g32_kvalued_fix_aux {k : Type*} [Field k] [CharZero k] (ω : k) (γ : k →+* k) (hγ : γ ω = ω) (x : k) (hx : ∃ a b : ℚ, x = a + b * ω) :
    γ x = x := by
  obtain ⟨a, b, rfl⟩ := hx
  simp only [map_add, map_mul, map_ratCast, hγ]

theorem papers_g32_kvalued_swap_aux {k : Type*} [Field k] [CharZero k] (ω : k) (hω : ω ^ 2 + ω + 1 = 0) (γ : k →+* k) (hγ : γ ω = ω ^ 2) (x y : k) (hxy : ∃ a b : ℚ, x = a + b * ω ∧ y = a + b * ω ^ 2) :
    γ x = y ∧ γ y = x := by
  obtain ⟨a, b, rfl, rfl⟩ := hxy
  refine ⟨by simp only [map_add, map_mul, map_ratCast, hγ], ?_⟩
  simp only [map_add, map_mul, map_ratCast, map_pow, hγ]
  linear_combination (b : k) * ω * (ω - 1) * hω

open IsCyclotomicExtension in
theorem papers_g32_conj_printed_fails_aux :
    letI := Fintype.ofFinite (rootsOfUnity 5 (CyclotomicField 5 ℚ)); ∃ γ : CyclotomicField 5 ℚ →+* CyclotomicField 5 ℚ, (∀ h : rootsOfUnity 5 (CyclotomicField 5 ℚ), γ ((h : (CyclotomicField 5 ℚ)ˣ) : CyclotomicField 5 ℚ) = ((h : (CyclotomicField 5 ℚ)ˣ) : CyclotomicField 5 ℚ) ^ 2) ∧ papersInner (fun h : rootsOfUnity 5 (CyclotomicField 5 ℚ) => ((h : (CyclotomicField 5 ℚ)ˣ) : CyclotomicField 5 ℚ) ^ 2) (papersLinChar ((rootsOfUnity 5 (CyclotomicField 5 ℚ)).subtype ^ 2)) ≠ papersInner (fun h : rootsOfUnity 5 (CyclotomicField 5 ℚ) => γ (((h : (CyclotomicField 5 ℚ)ˣ) : CyclotomicField 5 ℚ) ^ 2)) (papersLinChar (rootsOfUnity 5 (CyclotomicField 5 ℚ)).subtype) := by
  let _ := Fintype.ofFinite (rootsOfUnity 5 (CyclotomicField 5 ℚ))
  have : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  let σ : Gal(CyclotomicField 5 ℚ/ℚ) := (Rat.galEquivZMod 5 (CyclotomicField 5 ℚ)).symm (ZMod.unitOfCoprime 2 (by norm_num))
  have hσ : ∀ h : rootsOfUnity 5 (CyclotomicField 5 ℚ), σ ((h : (CyclotomicField 5 ℚ)ˣ) : (CyclotomicField 5 ℚ)) = ((h : (CyclotomicField 5 ℚ)ˣ) : (CyclotomicField 5 ℚ)) ^ 2 := by
    intro h
    have hx : ((h : (CyclotomicField 5 ℚ)ˣ) : (CyclotomicField 5 ℚ)) ^ 5 = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 5 _).mp h.2, Units.val_one]
    rw [Rat.galEquivZMod_apply_of_pow_eq 5 (CyclotomicField 5 ℚ) σ hx]
    simp only [σ, MulEquiv.apply_symm_apply]
    rfl
  have hζ := zeta_spec 5 ℚ (CyclotomicField 5 ℚ)
  have hcard : (Fintype.card (rootsOfUnity 5 (CyclotomicField 5 ℚ)) : (CyclotomicField 5 ℚ)) = 5 := by
    rw [Fintype.card_eq_nat_card, hζ.card_rootsOfUnity]; norm_num
  have hsum : ∑ h : rootsOfUnity 5 (CyclotomicField 5 ℚ), ((h : (CyclotomicField 5 ℚ)ˣ) : (CyclotomicField 5 ℚ)) ^ 3 = 0 := by
    set S := ∑ h : rootsOfUnity 5 (CyclotomicField 5 ℚ), ((h : (CyclotomicField 5 ℚ)ˣ) : (CyclotomicField 5 ℚ)) ^ 3
    have hS : S = zeta 5 ℚ (CyclotomicField 5 ℚ) ^ 3 * S := by
      rw [Finset.mul_sum]
      symm
      refine Fintype.sum_equiv (Equiv.mulLeft hζ.toRootsOfUnity) _ _ fun h => ?_
      simp [mul_pow]
    have h3 : zeta 5 ℚ (CyclotomicField 5 ℚ) ^ 3 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have : (zeta 5 ℚ (CyclotomicField 5 ℚ) ^ 3 - 1) * S = 0 := by linear_combination -hS
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h3)
  refine ⟨σ.toRingEquiv.toRingHom, fun h => hσ h, ?_⟩
  simp only [papersInner, papersLinChar, MonoidHom.pow_apply, Subgroup.coe_subtype,
    Units.val_pow_eq_pow_val, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_pow]
  have e1 : ∀ h : rootsOfUnity 5 (CyclotomicField 5 ℚ),
      ((h : (CyclotomicField 5 ℚ)ˣ) : CyclotomicField 5 ℚ) ^ 2 *
        ((h⁻¹ : rootsOfUnity 5 (CyclotomicField 5 ℚ)) : (CyclotomicField 5 ℚ)ˣ) ^ 2 = 1 := by
    intro h
    rw [← mul_pow, Subgroup.coe_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]
  have e2 : ∀ h : rootsOfUnity 5 (CyclotomicField 5 ℚ),
      σ.toRingEquiv ((h : (CyclotomicField 5 ℚ)ˣ) : CyclotomicField 5 ℚ) ^ 2 *
        ((h⁻¹ : rootsOfUnity 5 (CyclotomicField 5 ℚ)) : (CyclotomicField 5 ℚ)ˣ) =
        ((h : (CyclotomicField 5 ℚ)ˣ) : CyclotomicField 5 ℚ) ^ 3 := by
    intro h
    have hu := ((h : (CyclotomicField 5 ℚ)ˣ)).ne_zero
    rw [AlgEquiv.coe_toRingEquiv, hσ, Subgroup.coe_inv, Units.val_inv_eq_inv_val]
    field_simp
  rw [Finset.sum_congr rfl fun h _ => e1 h, Finset.sum_congr rfl fun h _ => e2 h, hsum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
  norm_num

theorem papers_tt_conj_inner_aux {k : Type*} [Field k] {G : Type*} [Group G] (H : Subgroup G) [Fintype H] (f : G → k) (χ : H →* kˣ) :
    papersInner (papersRes H f) (papersLinChar χ⁻¹) = papersInner (papersRes H fun g => f g⁻¹) (papersLinChar χ) := by
  simp only [papersInner, papersRes, papersLinChar, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    map_inv, inv_inv]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv H) _ _ fun h => by simp

theorem papers_tt_conj_mult_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] (H : Subgroup G) [Fintype H] (τ τbar : FDRep k G) (hbar : ∀ g, τbar.character g = τ.character g⁻¹) (χ : H →* kˣ) :
    papersMult H τ χ⁻¹ = papersMult H τbar χ := by
  apply Nat.cast_injective (R := k)
  rw [← papers_g32_mult_eq_inner_aux, ← papers_g32_mult_eq_inner_aux, papers_tt_conj_inner_aux]
  simp only [← hbar]

theorem papers_tt_conj_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] {ι κ : Type*} (τ τbar : ι → FDRep k G) (η : κ → FDRep k G) (hbar : ∀ i g, (τbar i).character g = (τ i).character g⁻¹) (hη : ∀ j g, (η j).character g⁻¹ = (η j).character g) (H : Subgroup G) [Fintype H] (χ : H →* kˣ) :
    (papersA τ τbar η H χ⁻¹).1 = -(papersA τ τbar η H χ).1 ∧ (papersA τ τbar η H χ⁻¹).2 = (papersA τ τbar η H χ).2 := by
  refine ⟨funext fun i => ?_, funext fun j => ?_⟩
  · have h1 := papers_tt_conj_mult_aux H _ _ (hbar i) χ
    have h2 := papers_tt_conj_mult_aux H (τbar i) (τ i) (fun g => by rw [hbar, inv_inv]) χ
    simp only [papersA, Pi.neg_apply, h1, h2]
    ring
  · simp only [papersA, papers_tt_conj_mult_aux H (η j) (η j) (fun g => (hη j g).symm) χ]

/-- A sum over `G` of a function extended by zero off `H` is the sum over `H`. -/
theorem papers_sum_dite_subgroup {k : Type*} [Field k] {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] [DecidablePred (· ∈ H)] (F : H → k) :
    ∑ y : G, (if hy : y ∈ H then F ⟨y, hy⟩ else 0) = ∑ h : H, F h := by
  rw [Finset.sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight (by simp)) _ _ (fun _ => rfl)

theorem papers_g34_frobenius_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] (ψ : H → k) (f : G → k) (hf : ∀ g x, f (x * g * x⁻¹) = f g) :
    papersInner (papersIndCF H ψ) f = papersInner ψ (papersRes H f) := by
  classical
  have hG : (Fintype.card G : k) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have key : ∀ x : G, ∑ g : G, (if hx : x * g * x⁻¹ ∈ H then ψ ⟨_, hx⟩ else 0) * f g⁻¹ =
      ∑ h : H, ψ h * f (h⁻¹ : H) := by
    intro x
    have h1 : ∀ g : G, (if hx : x * g * x⁻¹ ∈ H then ψ ⟨_, hx⟩ else 0) * f g⁻¹ =
        (fun y : G => if hy : y ∈ H then ψ ⟨y, hy⟩ * f y⁻¹ else 0) (x * g * x⁻¹) := by
      intro g
      simp only
      split_ifs
      · rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, hf]
      · rw [zero_mul]
    rw [Fintype.sum_congr _ _ h1,
      Fintype.sum_bijective (fun g => x * g * x⁻¹) (MulAut.conj x).bijective _
        (fun y : G => if hy : y ∈ H then ψ ⟨y, hy⟩ * f y⁻¹ else 0) (fun _ => rfl)]
    exact papers_sum_dite_subgroup H (fun h => ψ h * f (h⁻¹ : H))
  have h2 : ∑ g : G, ((Fintype.card H : k)⁻¹ *
      ∑ x : G, if hx : x * g * x⁻¹ ∈ H then ψ ⟨_, hx⟩ else 0) * f g⁻¹ =
      (Fintype.card H : k)⁻¹ * ∑ x : G, ∑ g : G,
        (if hx : x * g * x⁻¹ ∈ H then ψ ⟨_, hx⟩ else 0) * f g⁻¹ := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_assoc, Finset.sum_mul]
  simp only [papersInner, papersIndCF, papersRes]
  rw [h2]
  simp only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The pairing `papersInner` is symmetric. -/
theorem papersInner_comm {k : Type*} [Field k] {H : Type*} [Group H] [Fintype H]
    (f ψ : H → k) : papersInner f ψ = papersInner ψ f := by
  unfold papersInner
  congr 1
  refine Fintype.sum_equiv (Equiv.inv H) _ _ fun h => ?_
  simp [mul_comm]

theorem papers_g34_a_ind_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] [Fintype G] {ι κ : Type*} (τ τbar : ι → FDRep k G) (η : κ → FDRep k G) (H : Subgroup G) [Fintype H] (χ : H →* kˣ) :
    papersACF τ τbar η (papersIndCF H (papersLinChar χ)) = (fun i => ((papersA τ τbar η H χ).1 i : k), fun j => (papersMult H (η j) χ : k)) := by
  have h : ∀ V : FDRep k G, papersInner (papersIndCF H (papersLinChar χ)) V.character =
      (papersMult H V χ : k) := by
    intro V
    rw [papers_g34_frobenius_aux H _ _ fun g x => FDRep.char_conj V g x, papersInner_comm,
      papers_g32_mult_eq_inner_aux]
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [papersACF, papersA, h]
    push_cast
    rfl
  · simp only [papersACF, h]

/-- The pairing `papersInner` is linear in its first argument. -/
theorem papersInner_sum_left {k : Type*} [Field k] {H : Type*} [Group H] [Fintype H]
    {N : ℕ} (c : Fin N → k) (F : Fin N → H → k) (ψ : H → k) :
    papersInner (fun h => ∑ i, c i * F i h) ψ = ∑ i, c i * papersInner (F i) ψ := by
  simp only [papersInner, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun h _ => ?_
  ring

theorem papers_g34_a_brauer_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] [Fintype G] {ι κ : Type*} (τ τbar : ι → FDRep k G) (η : κ → FDRep k G) (σ : FDRep k G) {N : ℕ} (Hs : Fin N → Subgroup G) [∀ i, Fintype (Hs i)] (lam : (i : Fin N) → Hs i →* kˣ) (n : Fin N → ℤ) (hbrauer : ∀ g, σ.character g = ∑ i, (n i : k) * papersIndCF (Hs i) (papersLinChar (lam i)) g) :
    papersACF τ τbar η σ.character = ∑ i, (n i : k) • ((fun i' => ((papersA τ τbar η (Hs i) (lam i)).1 i' : k)), fun j => (papersMult (Hs i) (η j) (lam i) : k)) := by
  have hσ : σ.character = fun g => ∑ i, (n i : k) * papersIndCF (Hs i) (papersLinChar (lam i)) g :=
    funext hbrauer
  simp_rw [← papers_g34_a_ind_aux τ τbar η]
  rw [hσ]
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [papersACF, papersInner_sum_left, Prod.fst_sum, Finset.sum_apply, Prod.smul_fst,
      Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib, mul_sub]
  · simp only [papersACF, papersInner_sum_left, Prod.snd_sum, Finset.sum_apply, Prod.smul_snd,
      Pi.smul_apply, smul_eq_mul]

theorem papers_g34_order_two_free_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] {ι κ : Type*} (τ τbar : ι → FDRep k G) (η : κ → FDRep k G) (hbar : ∀ i g, (τbar i).character g = (τ i).character g⁻¹) (B : Subgroup G) [Fintype B] (lam : B →* kˣ) (hlam : lam ^ 2 = 1) :
    (papersA τ τbar η B lam).1 = 0 := by
  have h2 : ∀ b, lam b * lam b = 1 := fun b => by
    rw [← pow_two, ← MonoidHom.pow_apply, hlam, MonoidHom.one_apply]
  have hinv : lam⁻¹ = lam :=
    MonoidHom.ext fun b => by rw [MonoidHom.inv_apply, inv_eq_of_mul_eq_one_right (h2 b)]
  funext i
  simp only [papersA, Pi.zero_apply]
  rw [← papers_tt_conj_mult_aux B (τ i) (τbar i) (hbar i) lam, hinv, sub_self]

/-- A finite-dimensional space with a nondegenerate alternating form has even dimension. -/
theorem papers_even_finrank_of_isAlt {k : Type*} [Field k] [CharZero k] {M : Type*} [AddCommGroup M]
    [Module k M] [FiniteDimensional k M] (β : LinearMap.BilinForm k M) (halt : β.IsAlt)
    (hnd : β.Nondegenerate) : Even (Module.finrank k M) := by
  set b := Module.finBasis k M
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  set A := LinearMap.BilinForm.toMatrix b β
  have hT : A.transpose = -A := by
    ext i j
    simp only [A, Matrix.transpose_apply, Matrix.neg_apply, LinearMap.BilinForm.toMatrix_apply]
    exact (halt.neg_eq _ _).symm
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have h1 : A.det = -A.det := by
    conv_lhs => rw [← Matrix.det_transpose, hT, Matrix.det_neg, Fintype.card_fin, hodd.neg_one_pow]
    simp
  exact hdet (by linear_combination (exp := 1) h1 / 2)
theorem papers_g34_quat_mult_even_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] (η : FDRep k G) (β : LinearMap.BilinForm k η) (hβalt : β.IsAlt) (hβnd : β.Nondegenerate) (hβinv : ∀ g x y, β (η.ρ g x) (η.ρ g y) = β x y) (B : Subgroup G) [Fintype B] (lam : B →* kˣ) (hlam : lam ^ 2 = 1) :
    Even (papersMult B η lam) := by
  classical
  have hcard : (Fintype.card B : k) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hl : ∀ b : B, ((lam b⁻¹ : kˣ) : k) = lam b := by
    intro b
    have h2 : lam b * lam b = 1 := by
      rw [← pow_two, ← MonoidHom.pow_apply, hlam, MonoidHom.one_apply]
    rw [map_inv, inv_eq_of_mul_eq_one_right h2]
  let W : Submodule k η :=
    { carrier := {v | ∀ b : B, η.ρ b v = ((lam b : kˣ) : k) • v}
      add_mem' := by
        intro x y hx hy b
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [map_add, hx, hy, smul_add]
      zero_mem' := by intro b; simp
      smul_mem' := by
        intro c x hx b
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [map_smul, hx, smul_comm] }
  let e : η →ₗ[k] η := (Fintype.card B : k)⁻¹ • ∑ b : B, ((lam b⁻¹ : kˣ) : k) • η.ρ b
  have he : ∀ v, e v = (Fintype.card B : k)⁻¹ • ∑ b : B, ((lam b⁻¹ : kˣ) : k) • η.ρ b v := by
    intro v
    simp [e, LinearMap.sum_apply]
  have he_mem : ∀ v, e v ∈ W := by
    intro v c
    show η.ρ c (e v) = ((lam c : kˣ) : k) • e v
    rw [he, map_smul, map_sum, smul_comm ((lam c : kˣ) : k) (Fintype.card B : k)⁻¹]
    congr 1
    rw [Finset.smul_sum]
    refine Fintype.sum_bijective (fun b : B => c * b) (Group.mulLeft_bijective c) _ _ ?_
    intro b
    rw [map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul]
    simp only [Subgroup.coe_mul, mul_inv_rev, map_mul,
      Units.val_mul]
    congr 1
    rw [mul_comm, mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, mul_one]
  have he_fix : ∀ v ∈ W, e v = v := by
    intro v hv
    rw [he]
    have : ∀ b : B, ((lam b⁻¹ : kˣ) : k) • η.ρ b v = v := by
      intro b
      rw [hv b, smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul,
      inv_mul_cancel₀ hcard, one_smul]
  have hproj : LinearMap.IsProj W e := ⟨he_mem, he_fix⟩
  have htr : LinearMap.trace k η e = (papersMult B η lam : k) := by
    rw [← papers_g32_mult_eq_inner_aux]
    simp only [e, map_smul, map_sum, papersInner, papersRes, papersLinChar, FDRep.character,
      smul_eq_mul, mul_comm]
  have hfin : papersMult B η lam = Module.finrank k W := by
    exact_mod_cast htr.symm.trans hproj.trace
  have hadj : ∀ x y, β (e x) y = β x (e y) := by
    intro x y
    rw [he, he, map_smul, map_smul, LinearMap.smul_apply, map_sum, map_sum,
      LinearMap.sum_apply]
    congr 1
    refine Fintype.sum_bijective (·⁻¹) inv_involutive.bijective _ _ ?_
    intro b
    rw [map_smul, map_smul, LinearMap.smul_apply]
    simp only [hl, inv_inv]
    congr 1
    rw [← hβinv (b⁻¹ : B) (η.ρ b x) y, ← Module.End.mul_apply, ← map_mul]
    simp
  rw [hfin]
  refine papers_even_finrank_of_isAlt (β.restrict W) (fun x => hβalt x) ⟨?_, ?_⟩
  · intro w hw
    refine Subtype.ext (hβnd.1 w fun y => ?_)
    rw [← he_fix w w.2, hadj]
    exact hw ⟨e y, he_mem y⟩
  · intro w hw
    refine Subtype.ext (hβnd.2 w fun y => ?_)
    rw [← he_fix w w.2, ← hadj]
    exact hw ⟨e y, he_mem y⟩
theorem papers_g34_order_two_quat_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] {ι κ : Type*} (τ τbar : ι → FDRep k G) (η : κ → FDRep k G) (hforms : ∀ j, ∃ β : LinearMap.BilinForm k (η j), β.IsAlt ∧ β.Nondegenerate ∧ ∀ g x y, β ((η j).ρ g x) ((η j).ρ g y) = β x y) (B : Subgroup G) [Fintype B] (lam : B →* kˣ) (hlam : lam ^ 2 = 1) :
    (papersA τ τbar η B lam).2 = 0 := by
  funext j
  obtain ⟨β, halt, hnd, hinv⟩ := hforms j
  exact (papers_g34_quat_mult_even_aux (η j) β halt hnd hinv B lam hlam).natCast_zmod_two

theorem papers_g34_order_two_vanish_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] {ι κ : Type*} (τ τbar : ι → FDRep k G) (η : κ → FDRep k G) (hbar : ∀ i g, (τbar i).character g = (τ i).character g⁻¹) (hforms : ∀ j, ∃ β : LinearMap.BilinForm k (η j), β.IsAlt ∧ β.Nondegenerate ∧ ∀ g x y, β ((η j).ρ g x) ((η j).ρ g y) = β x y) (B : Subgroup G) [Fintype B] (lam : B →* kˣ) (hlam : lam ^ 2 = 1) :
    papersA τ τbar η B lam = 0 :=
  Prod.ext (papers_g34_order_two_free_aux τ τbar η hbar B lam hlam)
    (papers_g34_order_two_quat_aux τ τbar η hforms B lam hlam)

theorem papers_g34_quat_needs_alt_aux :
    ∃ β : LinearMap.BilinForm ℚ (FDRep.of (Representation.trivial ℚ Unit ℚ)), β.Nondegenerate ∧ (∀ g x y, β ((FDRep.of (Representation.trivial ℚ Unit ℚ)).ρ g x) ((FDRep.of (Representation.trivial ℚ Unit ℚ)).ρ g y) = β x y) ∧ ¬ Even (papersMult ⊤ (FDRep.of (Representation.trivial ℚ Unit ℚ)) 1) := by
  refine ⟨LinearMap.mul ℚ ℚ, ⟨fun x hx => ?_, fun y hy => ?_⟩, fun g x y => ?_, ?_⟩
  · simpa using hx 1
  · simpa using hy 1
  · simp
  · let _ : Fintype (⊤ : Subgroup Unit) := Fintype.ofFinite _
    have h := papers_g32_mult_eq_inner_aux (⊤ : Subgroup Unit)
      (FDRep.of (Representation.trivial ℚ Unit ℚ)) 1
    have h1 : papersMult ⊤ (FDRep.of (Representation.trivial ℚ Unit ℚ)) 1 = 1 := by
      have : papersInner (papersRes ⊤ (FDRep.of (Representation.trivial ℚ Unit ℚ)).character)
          (papersLinChar (1 : (⊤ : Subgroup Unit) →* ℚˣ)) = 1 := by
        have hc : Fintype.card (⊤ : Subgroup Unit) = 1 :=
          Fintype.card_eq_one_iff.mpr ⟨1, fun _ => Subsingleton.elim _ _⟩
        simp only [papersInner, papersRes, papersLinChar, hc, MonoidHom.one_apply, Units.val_one]
        rw [Fintype.sum_subsingleton _ (1 : (⊤ : Subgroup Unit))]
        simp only [Nat.cast_one, inv_one, one_mul, mul_one, OneMemClass.coe_one, FDRep.char_one]
        exact_mod_cast Module.finrank_self ℚ
      exact_mod_cast h.symm.trans this
    rw [h1]
    decide

/-- Two surjections out of the same type with the same fibres have targets of equal cardinality. -/

theorem natCard_eq_of_surj_fibres {X A B : Type*} (p : X → A) (q : X → B)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (h : ∀ a b, p a = p b ↔ q a = q b) : Nat.card A = Nat.card B := by
  refine Nat.card_congr (Equiv.ofBijective (fun a => q (Function.surjInv hp a)) ⟨?_, ?_⟩)
  · intro a b hab
    have := (h _ _).2 hab
    rwa [Function.surjInv_eq hp, Function.surjInv_eq hp] at this
  · intro b
    obtain ⟨x, rfl⟩ := hq b
    refine ⟨p x, (h _ _).1 ?_⟩
    rw [Function.surjInv_eq hp]

theorem papers_g34_orbits_doubleCoset_aux {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) = Nat.card (DoubleCoset.Quotient (H : Set G) (Subgroup.zpowers g : Set G)) := by
  refine natCard_eq_of_surj_fibres
    (fun x : G => (Quotient.mk'' ((x⁻¹ : G) : G ⧸ H) :
      Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))))
    (DoubleCoset.mk H (Subgroup.zpowers g)) ?_ ?_ ?_
  · intro q
    induction q using Quotient.inductionOn' with | h c => ?_
    induction c using QuotientGroup.induction_on with | H x => ?_
    exact ⟨x⁻¹, by simp⟩
  · intro q
    exact ⟨q.out, DoubleCoset.out_eq' q⟩
  · intro a b
    rw [DoubleCoset.eq'', DoubleCoset.rel_iff, Quotient.eq'', MulAction.orbitRel_apply,
      MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨⟨k, hk⟩, hka⟩
      rw [Subgroup.mk_smul, MulAction.Quotient.smul_coe, QuotientGroup.eq] at hka
      refine ⟨_, hka, k, hk, ?_⟩
      simp only [smul_eq_mul]; group
    · rintro ⟨h, hh, k, hk, rfl⟩
      refine ⟨⟨k, hk⟩, ?_⟩
      rw [Subgroup.mk_smul, MulAction.Quotient.smul_coe, QuotientGroup.eq]
      simpa [mul_assoc] using hh

/-- `g ^ ℓ x H = x H` for `ℓ` the period of `x H` under `g`, so `x⁻¹ g ^ ℓ x ∈ H`. -/

theorem conj_pow_minimalPeriod_mem {G : Type*} [Group G] (H : Subgroup G) (g x : G) :
    x⁻¹ * g ^ Function.minimalPeriod (g • ·) (x : G ⧸ H) * x ∈ H := by
  have h : g ^ Function.minimalPeriod (g • ·) (x : G ⧸ H) • (x : G ⧸ H) = x := by
    have := Function.isPeriodicPt_minimalPeriod (g • ·) (x : G ⧸ H)
    rwa [Function.IsPeriodicPt, Function.IsFixedPt, smul_iterate] at this
  rw [MulAction.Quotient.smul_coe, smul_eq_mul] at h
  simpa [mul_assoc] using QuotientGroup.eq.mp h.symm

/-- The exponent value `χ(x⁻¹ g^ℓ x)` of the supplier `(H, χ)` at a representative `x` of an orbit
of `⟨g⟩` on `G ⧸ H`, `ℓ` the period of `x H`. It does not depend on the representative.
Source: G34 v1.5, Section 4, paragraph after Definition 4.1 (the local monodromy `x g_j^ℓ x⁻¹`). -/
noncomputable def papersExpVal {G : Type*} [Group G] {m : ℕ} (H : Subgroup G)
    (χ : H →* Multiplicative (ZMod m)) (g x : G) : ZMod m :=
  Multiplicative.toAdd (χ ⟨_, conj_pow_minimalPeriod_mem H g x⟩)

example {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    papersExpVal H (1 : H →* Multiplicative (ZMod 3)) 1 x = 0 := rfl

/-- Periods of `g` at two points agree once the `g ^ n`-fixedness agrees. -/

theorem minimalPeriod_smul_eq {G X : Type*} [Group G] [MulAction G X] (g : G) (a b : X)
    (h : ∀ n : ℕ, g ^ n • a = a ↔ g ^ n • b = b) :
    Function.minimalPeriod (g • ·) a = Function.minimalPeriod (g • ·) b := by
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro n
  simp only [Function.IsPeriodicPt, Function.IsFixedPt, smul_iterate]
  exact h n

theorem papersExpVal_mul_right {G : Type*} [Group G] {m : ℕ} (H : Subgroup G)
    (χ : H →* Multiplicative (ZMod m)) (g x h : G) (hh : h ∈ H) :
    papersExpVal H χ g (x * h) = papersExpVal H χ g x := by
  have hc : ((x * h : G) : G ⧸ H) = x := by
    rw [QuotientGroup.eq]; simpa using hh
  unfold papersExpVal
  have : (⟨_, conj_pow_minimalPeriod_mem H g (x * h)⟩ : H) =
      (⟨h, hh⟩ : H)⁻¹ * ⟨_, conj_pow_minimalPeriod_mem H g x⟩ * ⟨h, hh⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc]
    group
  rw [this]
  congr 1
  rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]

theorem papersExpVal_mul_left {G : Type*} [Group G] {m : ℕ} (H : Subgroup G)
    (χ : H →* Multiplicative (ZMod m)) (g x : G) (j : ℤ) :
    papersExpVal H χ g (g ^ j * x) = papersExpVal H χ g x := by
  have hp : Function.minimalPeriod (g • ·) ((g ^ j * x : G) : G ⧸ H) =
      Function.minimalPeriod (g • ·) (x : G ⧸ H) := by
    apply minimalPeriod_smul_eq
    intro n
    simp only [MulAction.Quotient.smul_coe, smul_eq_mul]
    rw [← mul_assoc, ← zpow_natCast, ← zpow_add, add_comm, zpow_add, mul_assoc, zpow_natCast]
    constructor
    · intro h
      have := congrArg (fun c : G ⧸ H => g ^ (-j) • c) h
      simpa [MulAction.Quotient.smul_coe, ← mul_assoc, ← zpow_add] using this
    · intro h
      have := congrArg (fun c : G ⧸ H => g ^ j • c) h
      simpa [MulAction.Quotient.smul_coe, mul_assoc] using this
  unfold papersExpVal
  congr 2
  apply Subtype.ext
  simp only [hp]
  rw [mul_inv_rev, ← zpow_natCast]
  have : g ^ (-j) * (g ^ ((Function.minimalPeriod (g • ·) (x : G ⧸ H) : ℕ) : ℤ) * (g ^ j * x)) =
      g ^ ((Function.minimalPeriod (g • ·) (x : G ⧸ H) : ℕ) : ℤ) * x := by
    rw [← mul_assoc, ← mul_assoc, ← zpow_add, ← zpow_add]; congr 2; ring
  rw [zpow_neg] at this
  simp only [mul_assoc] at this ⊢
  rw [this]

/-- The value at an orbit equals the value at any representative of it. -/

theorem papersExpVal_eq {G : Type*} [Group G] {m : ℕ} (H : Subgroup G)
    (χ : H →* Multiplicative (ZMod m)) (g : G)
    (q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) (x : G)
    (hx : Quotient.mk'' (x : G ⧸ H) = q) :
    Multiplicative.toAdd (χ (papersLocalMonodromy H g q)) = papersExpVal H χ g x := by
  have h0 : Multiplicative.toAdd (χ (papersLocalMonodromy H g q)) =
      papersExpVal H χ g q.out.out := by
    unfold papersExpVal papersLocalMonodromy
    congr 3
    rw [QuotientGroup.out_eq']
  rw [h0]
  have hrel : Quotient.mk'' (q.out.out : G ⧸ H) =
      (Quotient.mk'' (x : G ⧸ H) : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) := by
    rw [hx, QuotientGroup.out_eq', Quotient.out_eq']
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨⟨k, hk⟩, hka⟩ := hrel
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  rw [Subgroup.mk_smul, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq] at hka
  have : q.out.out = g ^ j * x * ((g ^ j * x)⁻¹ * q.out.out) := by group
  rw [this, papersExpVal_mul_right H χ g _ _ hka, papersExpVal_mul_left]

theorem papersExpVal_neg {G : Type*} [Group G] {m : ℕ} (H : Subgroup G)
    (χ : H →* Multiplicative (ZMod m)) (g w x : G) (hw : w * g * w⁻¹ = g⁻¹) :
    papersExpVal H χ g (w * x) = - papersExpVal H χ g x := by
  have hw' : ∀ n : ℕ, w⁻¹ * g ^ n * w = (g ^ n)⁻¹ := by
    intro n
    have h1 : w⁻¹ * g * w = g⁻¹ := by
      have := congrArg (fun y => w⁻¹ * y⁻¹ * w) hw
      simp only [mul_inv_rev, inv_inv] at this
      simpa [mul_assoc] using this.symm
    rw [← inv_pow, ← h1]
    simpa using (conj_pow (a := w⁻¹) (b := g) (i := n)).symm
  have hp : Function.minimalPeriod (g • ·) ((w * x : G) : G ⧸ H) =
      Function.minimalPeriod (g • ·) (x : G ⧸ H) := by
    apply minimalPeriod_smul_eq
    intro n
    simp only [MulAction.Quotient.smul_coe, smul_eq_mul]
    have e : g ^ n * (w * x) = w * ((g ^ n)⁻¹ * x) := by
      rw [← hw' n]; group
    rw [e, QuotientGroup.eq, QuotientGroup.eq]
    constructor
    · intro h
      have := H.inv_mem h
      simpa [mul_assoc] using this
    · intro h
      have := H.inv_mem h
      simpa [mul_assoc] using this
  unfold papersExpVal
  rw [← toAdd_inv, ← map_inv]
  congr 2
  apply Subtype.ext
  simp only [hp, Subgroup.coe_inv]
  set ℓ := Function.minimalPeriod (g • ·) (x : G ⧸ H)
  rw [show (w * x)⁻¹ * g ^ ℓ * (w * x) = x⁻¹ * (w⁻¹ * g ^ ℓ * w) * x by group, hw' ℓ]
  group

/-- If `w g w⁻¹ = g⁻¹` then `w` normalises `⟨g⟩`. -/

theorem conj_mem_zpowers_of_conj_inv {G : Type*} [Group G] (g w k : G) (hw : w * g * w⁻¹ = g⁻¹)
    (hk : k ∈ Subgroup.zpowers g) : w * k * w⁻¹ ∈ Subgroup.zpowers g := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  have e := map_zpow (MulAut.conj w) g j
  simp only [MulAut.conj_apply] at e
  rw [e, hw]
  exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers g)) j

/-- The orbit map `⟨g⟩ x H ↦ ⟨g⟩ w x H` for `w g w⁻¹ = g⁻¹`. -/

theorem orbit_smul_rel {G : Type*} [Group G] (H : Subgroup G) (g w : G) (hw : w * g * w⁻¹ = g⁻¹)
    (a b : G ⧸ H) (hab : MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H) a b) :
    MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H) (w • a) (w • b) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
  obtain ⟨⟨k, hk⟩, hka⟩ := hab
  refine ⟨⟨w * k * w⁻¹, conj_mem_zpowers_of_conj_inv g w k hw hk⟩, ?_⟩
  rw [Subgroup.mk_smul] at hka ⊢
  rw [← hka, ← mul_smul, ← mul_smul, inv_mul_cancel_right]

theorem papers_g34_exps_neg_stable_aux {G : Type*} [Group G] [Finite G] {m : ℕ} (H : Subgroup G) (χ : H →* Multiplicative (ZMod m)) (g w : G) (hw : w * g * w⁻¹ = g⁻¹) :
    (papersExps H χ g).map Neg.neg = papersExps H χ g := by
  have hw₁ : w⁻¹ * g * w⁻¹⁻¹ = g⁻¹ := by
    rw [inv_inv]
    calc w⁻¹ * g * w = (w⁻¹ * g⁻¹ * w)⁻¹ := by group
      _ = (w⁻¹ * (w * g * w⁻¹) * w)⁻¹ := by rw [hw]
      _ = g⁻¹ := by group
  let φ : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)) →
      Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)) :=
    Quotient.map' (w • ·) (orbit_smul_rel H g w hw)
  have hφ : Function.Bijective φ := by
    rw [← Finite.injective_iff_bijective]
    intro a b hab
    induction a using Quotient.inductionOn' with | h a => ?_
    induction b using Quotient.inductionOn' with | h b => ?_
    have := orbit_smul_rel H g w⁻¹ hw₁ _ _ (Quotient.exact' hab)
    simp only [inv_smul_smul] at this
    exact Quotient.sound' this
  have hv : ∀ q, Multiplicative.toAdd (χ (papersLocalMonodromy H g (φ q))) =
      - Multiplicative.toAdd (χ (papersLocalMonodromy H g q)) := by
    intro q
    rw [papersExpVal_eq H χ g q q.out.out (by rw [QuotientGroup.out_eq', Quotient.out_eq']),
      papersExpVal_eq H χ g (φ q) (w * q.out.out), papersExpVal_neg H χ g w _ hw]
    conv_rhs => rw [← Quotient.out_eq' q, ← QuotientGroup.out_eq' q.out]
    rfl
  let _ : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) :=
    Fintype.ofFinite _
  have hS : (Finset.univ.val.map fun q => Multiplicative.toAdd (χ (papersLocalMonodromy H g q))).map
      Neg.neg = Finset.univ.val.map fun q => Multiplicative.toAdd (χ (papersLocalMonodromy H g q)) := by
    rw [Multiset.map_map]
    simp only [Function.comp_def, ← hv]
    rw [show (fun x => Multiplicative.toAdd (χ (papersLocalMonodromy H g (φ x)))) =
        (fun q => Multiplicative.toAdd (χ (papersLocalMonodromy H g q))) ∘
          (Equiv.ofBijective φ hφ) from rfl, ← Multiset.map_map,
      Multiset.map_univ_val_equiv (Equiv.ofBijective φ hφ)]
  unfold papersExps
  generalize (Finset.univ.val.map fun q => Multiplicative.toAdd (χ (papersLocalMonodromy H g q))) = S at hS ⊢
  calc (S.filter (· ≠ 0)).map Neg.neg = (S.filter ((· ≠ 0) ∘ Neg.neg)).map Neg.neg := by
        congr 1; apply Multiset.filter_congr; intro x _; simp
    _ = (S.map Neg.neg).filter (· ≠ 0) := (Multiset.filter_map _ _ _).symm
    _ = S.filter (· ≠ 0) := by rw [hS]

/-- Dropping the zeros does not change the sum of a multiset. -/

theorem multiset_sum_filter_ne_zero {M : Type*} [AddCommMonoid M] [DecidableEq M]
    (s : Multiset M) : (s.filter (· ≠ 0)).sum = s.sum := by
  conv_rhs => rw [← Multiset.filter_add_not (· ≠ 0) s]
  have h0 : (s.filter fun a => ¬a ≠ 0).sum = 0 :=
    Multiset.sum_eq_zero fun x hx => by simpa using (Multiset.mem_filter.mp hx).2
  rw [Multiset.sum_add, h0, add_zero]

theorem papers_g34_exps_sum_transfer_aux {G : Type*} [Group G] [Finite G] {m : ℕ} (H : Subgroup G) (χ : H →* Multiplicative (ZMod m)) (g : G) :
    (papersExps H χ g).sum = Multiplicative.toAdd (χ.transfer g) := by
  let := Fintype.ofFinite (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)))
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  unfold papersExps
  rw [multiset_sum_filter_ne_zero]
  rfl

/-- The exponents of a tuple sum to the transfer of the product of the tuple. -/

theorem papersExpsTuple_sum_eq_transfer {G : Type*} [Group G] [Finite G] {m : ℕ}
    (H : Subgroup G) (χ : H →* Multiplicative (ZMod m)) (gs : List G) :
    (papersExpsTuple H χ gs).sum = Multiplicative.toAdd (χ.transfer gs.prod) := by
  induction gs with
  | nil => simp [papersExpsTuple]
  | cons g gs ih =>
    have : papersExpsTuple H χ (g :: gs) = papersExps H χ g + papersExpsTuple H χ gs := by
      simp [papersExpsTuple]
    rw [this, Multiset.sum_add, ih, papers_g34_exps_sum_transfer_aux, List.prod_cons, map_mul,
      toAdd_mul]

theorem papers_g34_exps_sum_zero_aux {G : Type*} [Group G] [Finite G] {m : ℕ} (H : Subgroup G) (χ : H →* Multiplicative (ZMod m)) (gs : List G) (hprod : gs.prod = 1) :
    (papersExpsTuple H χ gs).sum = 0 := by
  rw [papersExpsTuple_sum_eq_transfer, hprod, map_one, toAdd_one]

theorem papersExpsTuple_cons {G : Type*} [Group G] [Finite G] {m : ℕ} (H : Subgroup G)
    (χ : H →* Multiplicative (ZMod m)) (g : G) (gs : List G) :
    papersExpsTuple H χ (g :: gs) = papersExps H χ g + papersExpsTuple H χ gs := by
  simp [papersExpsTuple]

/-- The exponents of a tuple of real elements are stable under negation. -/

theorem papersExpsTuple_neg {G : Type*} [Group G] [Finite G] {m : ℕ} (H : Subgroup G)
    (χ : H →* Multiplicative (ZMod m)) (gs : List G)
    (hreal : ∀ g ∈ gs, ∃ w : G, w * g * w⁻¹ = g⁻¹) :
    (papersExpsTuple H χ gs).map Neg.neg = papersExpsTuple H χ gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨w, hw⟩ := hreal g List.mem_cons_self
    rw [papersExpsTuple_cons, Multiset.map_add, papers_g34_exps_neg_stable_aux H χ g w hw,
      ih fun g' hg' => hreal g' (List.mem_cons_of_mem _ hg')]

/-- The exponents of a tuple are nonzero. -/

theorem papersExpsTuple_ne_zero {G : Type*} [Group G] [Finite G] {m : ℕ} (H : Subgroup G)
    (χ : H →* Multiplicative (ZMod m)) (gs : List G) : ∀ a ∈ papersExpsTuple H χ gs, a ≠ 0 := by
  induction gs with
  | nil => simp [papersExpsTuple]
  | cons g gs ih =>
    intro a ha
    rw [papersExpsTuple_cons, Multiset.mem_add] at ha
    rcases ha with ha | ha
    · exact (Multiset.mem_filter.mp ha).2
    · exact ih a ha

/-- The exponent list of a tuple of real elements with product one lies in `1, …, m − 1`, is
stable under `a ↦ m − a` and sums to `0` modulo `m`: the hypotheses of papers4's results. -/

theorem papersExpsList_hyps {G : Type*} [Group G] [Finite G] {m : ℕ} [NeZero m] (H : Subgroup G)
    (χ : H →* Multiplicative (ZMod m)) (gs : List G)
    (hreal : ∀ g ∈ gs, ∃ w : G, w * g * w⁻¹ = g⁻¹) (hprod : gs.prod = 1) :
    (∀ a ∈ papersExpsList H χ gs, 0 < a ∧ a < m) ∧ ExpsNegStable m (papersExpsList H χ gs) ∧
      (papersExpsList H χ gs).sum % m = 0 := by
  have hnz := papersExpsTuple_ne_zero H χ gs
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [papersExpsList, Multiset.mem_toList, Multiset.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact ⟨ZMod.val_pos.mpr (hnz b hb), ZMod.val_lt b⟩
  · unfold ExpsNegStable papersExpsList
    rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.map_map]
    conv_rhs => rw [← papersExpsTuple_neg H χ gs hreal, Multiset.map_map]
    refine Multiset.map_congr rfl fun a ha => ?_
    have : NeZero a := ⟨hnz a ha⟩
    exact (ZMod.val_neg_of_ne_zero a).symm
  · apply Nat.mod_eq_zero_of_dvd
    rw [← ZMod.natCast_eq_zero_iff, papersExpsList, ← Multiset.sum_coe, Multiset.coe_toList,
      Nat.cast_multiset_sum, Multiset.map_map]
    simp only [Function.comp_def, ZMod.natCast_zmod_val, Multiset.map_id']
    exact papers_g34_exps_sum_zero_aux H χ gs hprod

theorem papers_g34_exps_tuple_simple_aux {G : Type*} [Group G] [Finite G] {m : ℕ} [NeZero m] (H : Subgroup G) (χ : H →* Multiplicative (ZMod m)) (gs : List G) (hreal : ∀ g ∈ gs, ∃ w : G, w * g * w⁻¹ = g⁻¹) (hprod : gs.prod = 1) :
    IsSimpleExps m (papersExpsList H χ gs) := by
  obtain ⟨h1, h2, h3⟩ := papersExpsList_hyps H χ gs hreal hprod
  exact papers_g34_exps_simple m _ h1 h2 h3

theorem papers_g34_exps_tuple_admissible_aux {G : Type*} [Group G] [Finite G] {m : ℕ} [NeZero m] (H : Subgroup G) (χ : H →* Multiplicative (ZMod m)) (gs : List G) (hreal : ∀ g ∈ gs, ∃ w : G, w * g * w⁻¹ = g⁻¹) (hprod : gs.prod = 1) (q : ℕ) (hh : 0 < (2 * q - 2 + (papersExpsList H χ gs).length : ℤ)) :
    SupplierAdmissible m q (papersExpsList H χ gs) := by
  obtain ⟨h1, h2, h3⟩ := papersExpsList_hyps H χ gs hreal hprod
  exact papers_g34_real_supplier_admissible m q _ h1 h2 h3 hh

/-- On a commutative group with `H = ⊤`, the exponents at `g` are the single value `χ g`
(dropped if `0`). -/

theorem papersExps_top {G : Type*} [CommGroup G] [Finite G] {m : ℕ}
    (χ : (⊤ : Subgroup G) →* Multiplicative (ZMod m)) (g : G) :
    papersExps ⊤ χ g = ({Multiplicative.toAdd (χ ⟨g, Subgroup.mem_top g⟩)} : Multiset (ZMod m)).filter (· ≠ 0) := by
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  let q₀ : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ (⊤ : Subgroup G))) := Quotient.mk'' (1 : G)
  have hsub : ∀ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ (⊤ : Subgroup G))), q = q₀ := by
    intro q
    induction q using Quotient.inductionOn' with | h c => exact congrArg _ (Subsingleton.elim _ _)
  have hval : ∀ q, papersLocalMonodromy ⊤ g q = ⟨g, Subgroup.mem_top g⟩ := by
    intro q
    have h1 : Function.minimalPeriod (g • ·) q.out = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mpr (Subsingleton.elim _ _)
    apply Subtype.ext
    simp only [papersLocalMonodromy, h1, pow_one]
    rw [mul_comm, mul_inv_cancel_left]
  unfold papersExps
  simp only [hval, Multiset.map_const', Finset.card_val, Finset.card_univ]
  rw [Fintype.card_eq_nat_card, Nat.card_eq_one_iff_exists.mpr ⟨q₀, hsub⟩, Multiset.replicate_one]

theorem papers_g34_exps_tuple_real_needed_aux :
    ([Multiplicative.ofAdd 1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1] : List (Multiplicative (ZMod 3))).prod = 1 ∧ ¬ (∀ g ∈ ([Multiplicative.ofAdd 1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1] : List (Multiplicative (ZMod 3))), ∃ w : Multiplicative (ZMod 3), w * g * w⁻¹ = g⁻¹) ∧ ¬ IsSimpleExps 3 (papersExpsList (⊤ : Subgroup (Multiplicative (ZMod 3))) (⊤ : Subgroup (Multiplicative (ZMod 3))).subtype [Multiplicative.ofAdd 1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1]) := by
  refine ⟨by decide, by decide, not_isSimpleExps_of_odd _ _ ?_⟩
  have h : papersExps (⊤ : Subgroup (Multiplicative (ZMod 3))) (⊤ : Subgroup (Multiplicative (ZMod 3))).subtype (Multiplicative.ofAdd 1) = {1} := by
    rw [papersExps_top]; decide
  simp only [papersExpsList, papersExpsTuple, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, h, Multiset.length_toList, Multiset.card_map]
  decide

theorem papers_g34_exps_tuple_prod_needed_aux :
    (∀ g ∈ ([Multiplicative.ofAdd 2] : List (Multiplicative (ZMod 4))), ∃ w : Multiplicative (ZMod 4), w * g * w⁻¹ = g⁻¹) ∧ ([Multiplicative.ofAdd 2] : List (Multiplicative (ZMod 4))).prod ≠ 1 ∧ ¬ IsSimpleExps 4 (papersExpsList (⊤ : Subgroup (Multiplicative (ZMod 4))) (⊤ : Subgroup (Multiplicative (ZMod 4))).subtype [Multiplicative.ofAdd 2]) := by
  refine ⟨by decide, by decide, ?_⟩
  have h : papersExps (⊤ : Subgroup (Multiplicative (ZMod 4))) (⊤ : Subgroup (Multiplicative (ZMod 4))).subtype (Multiplicative.ofAdd 2) = {2} := by
    rw [papersExps_top]; decide
  have hl : papersExpsList (⊤ : Subgroup (Multiplicative (ZMod 4))) (⊤ : Subgroup (Multiplicative (ZMod 4))).subtype [Multiplicative.ofAdd 2] = [2] := by
    simp only [papersExpsList, papersExpsTuple, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, h, add_zero, Multiset.map_singleton, Multiset.toList_singleton]
    rfl
  rw [hl]
  exact papers_g34_exps_sum_needed.2.2.2

end HodgeLean.Papers
