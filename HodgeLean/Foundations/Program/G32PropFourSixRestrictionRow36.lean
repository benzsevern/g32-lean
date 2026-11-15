import HodgeLean.Foundations.Program.G32PropFourSixRowComparison
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0005

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row36_pairingTerms : Fin 48 → List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  ![g32p_row36_terms_0, g32p_row36_terms_1, g32p_row36_terms_2, g32p_row36_terms_3, g32p_row36_terms_4, g32p_row36_terms_5, g32p_row36_terms_6, g32p_row36_terms_7, g32p_row36_terms_8, g32p_row36_terms_9, g32p_row36_terms_10, g32p_row36_terms_11, g32p_row36_terms_12, g32p_row36_terms_13, g32p_row36_terms_14, g32p_row36_terms_15, g32p_row36_terms_16, g32p_row36_terms_17, g32p_row36_terms_18, g32p_row36_terms_19, g32p_row36_terms_20, g32p_row36_terms_21, g32p_row36_terms_22, g32p_row36_terms_23, g32p_row36_terms_24, g32p_row36_terms_25, g32p_row36_terms_26, g32p_row36_terms_27, g32p_row36_terms_28, g32p_row36_terms_29, g32p_row36_terms_30, g32p_row36_terms_31, g32p_row36_terms_32, g32p_row36_terms_33, g32p_row36_terms_34, g32p_row36_terms_35, g32p_row36_terms_36, g32p_row36_terms_37, g32p_row36_terms_38, g32p_row36_terms_39, g32p_row36_terms_40, g32p_row36_terms_41, g32p_row36_terms_42, g32p_row36_terms_43, g32p_row36_terms_44, g32p_row36_terms_45, g32p_row36_terms_46, g32p_row36_terms_47]

def g32p_row36_pairingQuotients : Fin 48 → List ℤ :=
  ![[0, 64, 0, 64, 0, -128], [], [], [], [], [], [], [0, 64, 0, 64, 0, -128], [], [], [], [0, 128, 0, 128, 0, -256], [], [], [], [], [], [], [], [], [0, 128, 0, 128, 0, -256], [0, 64, 0, 64, 0, -128], [], [0, 128, 0, 128, 0, -256], [0, 128, 0, 128, 0, -256], [-384, -448, -128, 192, 256, 128], [], [], [], [], [-384, -448, -128, 192, 256, 128], [-384, -448, -128, 192, 256, 128], [], [-384, -448, -128, 192, 256, 128], [-384, -448, -128, 192, 256, 128], [], [], [], [], [-384, -320, -128, 320, 256, -128], [-384, -384, -128, 256, 256], [], [], [-384, -448, -128, 192, 256, 128], [], [], [], []]

def g32p_row36_freeCoordinates : Fin 44 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1]

def g32p_row36_quaternionicMultiplicities : Fin 4 → ℤ :=
  ![0, 0, 0, 0]

theorem g32p_row36_pairingFree (j : Fin 44) :
    g32p_cyclotomicPairingCheck 384 (g32p_row36_freeCoordinates j)
      (g32p_pairingCoefficients 6 (g32p_row36_pairingTerms ⟨j.val, by omega⟩))
      [1, -1, 1] (g32p_row36_pairingQuotients ⟨j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row36_pairing_0
  · exact g32p_row36_pairing_1
  · exact g32p_row36_pairing_2
  · exact g32p_row36_pairing_3
  · exact g32p_row36_pairing_4
  · exact g32p_row36_pairing_5
  · exact g32p_row36_pairing_6
  · exact g32p_row36_pairing_7
  · exact g32p_row36_pairing_8
  · exact g32p_row36_pairing_9
  · exact g32p_row36_pairing_10
  · exact g32p_row36_pairing_11
  · exact g32p_row36_pairing_12
  · exact g32p_row36_pairing_13
  · exact g32p_row36_pairing_14
  · exact g32p_row36_pairing_15
  · exact g32p_row36_pairing_16
  · exact g32p_row36_pairing_17
  · exact g32p_row36_pairing_18
  · exact g32p_row36_pairing_19
  · exact g32p_row36_pairing_20
  · exact g32p_row36_pairing_21
  · exact g32p_row36_pairing_22
  · exact g32p_row36_pairing_23
  · exact g32p_row36_pairing_24
  · exact g32p_row36_pairing_25
  · exact g32p_row36_pairing_26
  · exact g32p_row36_pairing_27
  · exact g32p_row36_pairing_28
  · exact g32p_row36_pairing_29
  · exact g32p_row36_pairing_30
  · exact g32p_row36_pairing_31
  · exact g32p_row36_pairing_32
  · exact g32p_row36_pairing_33
  · exact g32p_row36_pairing_34
  · exact g32p_row36_pairing_35
  · exact g32p_row36_pairing_36
  · exact g32p_row36_pairing_37
  · exact g32p_row36_pairing_38
  · exact g32p_row36_pairing_39
  · exact g32p_row36_pairing_40
  · exact g32p_row36_pairing_41
  · exact g32p_row36_pairing_42
  · exact g32p_row36_pairing_43

theorem g32p_row36_pairingQuat (j : Fin 4) :
    g32p_cyclotomicPairingCheck 384 (g32p_row36_quaternionicMultiplicities j)
      (g32p_pairingCoefficients 6 (g32p_row36_pairingTerms ⟨44 + j.val, by omega⟩))
      [1, -1, 1] (g32p_row36_pairingQuotients ⟨44 + j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row36_pairing_44
  · exact g32p_row36_pairing_45
  · exact g32p_row36_pairing_46
  · exact g32p_row36_pairing_47

theorem g32p_row36_restriction_of_sums {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H]
    (τ τbar : Fin 44 → FDRep ℂ G) (θ : Fin 4 → FDRep ℂ G) (χ : H →* ℂˣ)
    (z : ℂ) (hz : IsPrimitiveRoot z 6) (horder : Fintype.card H = 384)
    (hfree : ∀ j : Fin 44,
      (∑ h : H, ((τ j).character h - (τbar j).character h) * (χ h⁻¹ : ℂ)) =
        ((g32p_row36_pairingTerms ⟨j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hquat : ∀ j : Fin 4,
      (∑ h : H, (θ j).character h * (χ h⁻¹ : ℂ)) =
        ((g32p_row36_pairingTerms ⟨44 + j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum) :
    ∃ v ∈ g32VectorTable,
      v.i = 36 ∧ papersA τ τbar θ H χ = g32SparseVec v.coords := by
  obtain ⟨v, hv, hi, hc⟩ := g32p_row36_coordinates
  refine ⟨v, hv, hi, ?_⟩
  rw [hc]
  refine (g32p_polynomialPairing_row H τ τbar θ χ 6
    g32p_row36_freeCoordinates g32p_row36_quaternionicMultiplicities
    g32p_row36_pairingTerms [1, -1, 1] g32p_row36_pairingQuotients z
    (g32p_pairing_modulus_six hz) hfree hquat
    (by rw [horder]; exact g32p_row36_pairingFree)
    (by rw [horder]; exact g32p_row36_pairingQuat)).trans ?_
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j <;> rfl

end HodgeLean.Foundations.Program
