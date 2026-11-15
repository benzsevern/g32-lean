import HodgeLean.Foundations.Program.G32PropFourSixCharacterCheck
import HodgeLean.Foundations.Program.G32PropFourSixPacked0003

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

theorem g32p_polynomialPairing_mult {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H] (V : FDRep ℂ G) (χ : H →* ℂˣ)
    (m : ℕ) (multiplicity : ℤ)
    (xs : List (ℕ × HurwitzPrymRex_Zw × ℕ)) (modulus quotient : List ℤ) (z : ℂ)
    (hroot : g32p_coeffEval z modulus = 0)
    (hsum : (∑ h : H, V.character h * (χ h⁻¹ : ℂ)) =
      (xs.map (fun x => (x.1 : ℂ) *
        HurwitzPrymRex_ev (z ^ (m / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hcheck : g32p_cyclotomicPairingCheck (Fintype.card H) multiplicity
      (g32p_pairingCoefficients m xs) modulus quotient = true) :
    (papersMult H V χ : ℤ) = multiplicity := by
  apply Int.cast_injective (α := ℂ)
  simp only [Int.cast_natCast]
  rw [← papers_g32_mult_eq_inner]
  change (Fintype.card H : ℂ)⁻¹ * (∑ h : H, V.character h * (χ h⁻¹ : ℂ)) = _
  rw [hsum, ← g32p_pairingCoefficients_eval,
    g32p_cyclotomicPairingCheck_sound _ _ _ _ _ z hroot hcheck]
  have hn : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

theorem g32p_polynomialPairing_free {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H] (V W : FDRep ℂ G) (χ : H →* ℂˣ)
    (m : ℕ) (coordinate : ℤ)
    (xs : List (ℕ × HurwitzPrymRex_Zw × ℕ)) (modulus quotient : List ℤ) (z : ℂ)
    (hroot : g32p_coeffEval z modulus = 0)
    (hsum : (∑ h : H, (V.character h - W.character h) * (χ h⁻¹ : ℂ)) =
      (xs.map (fun x => (x.1 : ℂ) *
        HurwitzPrymRex_ev (z ^ (m / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hcheck : g32p_cyclotomicPairingCheck (Fintype.card H) coordinate
      (g32p_pairingCoefficients m xs) modulus quotient = true) :
    (papersMult H V χ : ℤ) - papersMult H W χ = coordinate := by
  apply Int.cast_injective (α := ℂ)
  simp only [Int.cast_sub, Int.cast_natCast]
  rw [← papers_g32_mult_eq_inner, ← papers_g32_mult_eq_inner]
  change (Fintype.card H : ℂ)⁻¹ * (∑ h : H, V.character h * (χ h⁻¹ : ℂ)) -
    (Fintype.card H : ℂ)⁻¹ * (∑ h : H, W.character h * (χ h⁻¹ : ℂ)) = _
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  rw [hsum, ← g32p_pairingCoefficients_eval,
    g32p_cyclotomicPairingCheck_sound _ _ _ _ _ z hroot hcheck]
  have hn : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

theorem g32p_characterSum_fibers {H : Type*} [Group H] [Fintype H] {c : ℕ}
    (classify : H → Fin c) (sizes : Fin c → ℕ)
    (traces : Fin c → HurwitzPrymRex_Zw) (exponents : Fin c → ℕ)
    (f : H → ℂ) (χ : H →* ℂˣ) (z w : ℂ)
    (hcard : ∀ i, Fintype.card {h : H // classify h = i} = sizes i)
    (htrace : ∀ h, f h = HurwitzPrymRex_ev w (traces (classify h)))
    (hcharacter : ∀ h, (χ h⁻¹ : ℂ) = z ^ exponents (classify h)) :
    (∑ h, f h * (χ h⁻¹ : ℂ)) =
      ∑ i, (sizes i : ℂ) * HurwitzPrymRex_ev w (traces i) * z ^ exponents i := by
  classical
  calc
    _ = ∑ h, HurwitzPrymRex_ev w (traces (classify h)) * z ^ exponents (classify h) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [htrace, hcharacter]
    _ = ∑ i, ∑ _h : {h : H // classify h = i},
        HurwitzPrymRex_ev w (traces i) * z ^ exponents i :=
      (Fintype.sum_fiberwise' classify
        (fun i => HurwitzPrymRex_ev w (traces i) * z ^ exponents i)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, mul_assoc]

theorem g32p_polynomialPairing_mult_of_fibers {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H] (V : FDRep ℂ G) (χ : H →* ℂˣ)
    {c : ℕ} (classify : H → Fin c) (sizes : Fin c → ℕ)
    (traces : Fin c → HurwitzPrymRex_Zw) (exponents : Fin c → ℕ)
    (m : ℕ) (multiplicity : ℤ) (modulus quotient : List ℤ) (z : ℂ)
    (hcard : ∀ i, Fintype.card {h : H // classify h = i} = sizes i)
    (htrace : ∀ h : H, V.character h = HurwitzPrymRex_ev (z ^ (m / 3)) (traces (classify h)))
    (hcharacter : ∀ h, (χ h⁻¹ : ℂ) = z ^ exponents (classify h))
    (hroot : g32p_coeffEval z modulus = 0)
    (hcheck : g32p_cyclotomicPairingCheck (Fintype.card H) multiplicity
      (g32p_pairingCoefficients m (List.ofFn fun i => (sizes i, traces i, exponents i)))
      modulus quotient = true) :
    (papersMult H V χ : ℤ) = multiplicity := by
  apply g32p_polynomialPairing_mult H V χ m multiplicity _ modulus quotient z hroot _ hcheck
  simp only [List.map_ofFn, List.sum_ofFn]
  exact g32p_characterSum_fibers classify sizes traces exponents
    (fun h => V.character h) χ z (z ^ (m / 3)) hcard htrace hcharacter

theorem g32p_determinant_pairing_test :
    papersMult g32p_determinantSupplier.H g32p_determinantRep
      (g32p_complexCharacter g32p_determinantSupplier) = 1 := by
  classical
  rw [g32p_determinantSupplier_complexCharacter]
  change papersMult ⊤ (papersLinRep g32p_determinant)
    (g32p_determinant.comp (⊤ : Subgroup g32p_G).subtype) = 1
  letI := Fintype.ofFinite (⊤ : Subgroup g32p_G)
  have hc : Fintype.card (⊤ : Subgroup g32p_G) = 155520 := by
    rw [← Nat.card_eq_fintype_card]
    exact g32p_determinantSupplier_order
  apply g32p_pairingCheck_mult _ _ _ 1 [(155520, ⟨1, 0⟩, ⟨1, 0⟩)]
  · have ht (h : (⊤ : Subgroup g32p_G)) :
        (papersLinRep g32p_determinant).character h *
          ((g32p_determinant.comp (⊤ : Subgroup g32p_G).subtype) h⁻¹ : ℂ) = 1 := by
      rw [g32p_linRep_character]
      change (g32p_determinant h : ℂ) * (g32p_determinant (h : g32p_G)⁻¹ : ℂ) = 1
      rw [map_inv, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _)]
    simp only [ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hc]
    norm_num [HurwitzPrymRex_ev]
  · rw [hc]
    decide

end HodgeLean.Foundations.Program
