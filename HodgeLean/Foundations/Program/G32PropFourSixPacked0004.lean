import HodgeLean.Foundations.Program.G32PropFourSixPacked0003
import HodgeLean.Papers.PapersG32CertificatesDefs

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row16_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 11), (1, ⟨-1, -2⟩, 14), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 10), (1, ⟨1, 2⟩, 13)]

theorem g32p_row16_pairing_0 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_0)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -2] = true := by
  decide +kernel

def g32p_row16_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row16_pairing_1 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_1)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row16_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 5), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 13), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 8), (1, ⟨1, 2⟩, 11), (1, ⟨1, 2⟩, 14), (1, ⟨4, 8⟩, 10)]

theorem g32p_row16_pairing_2 :
    g32p_cyclotomicPairingCheck 15 (1)
      (g32p_pairingCoefficients 15 g32p_row16_terms_2)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-15, -16, -15, 0, 0, 10, 9, 10, 0, 0, 0, 2] = true := by
  decide +kernel

def g32p_row16_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 5), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 13), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 8), (1, ⟨1, 2⟩, 11), (1, ⟨1, 2⟩, 14), (1, ⟨4, 8⟩, 10)]

theorem g32p_row16_pairing_3 :
    g32p_cyclotomicPairingCheck 15 (1)
      (g32p_pairingCoefficients 15 g32p_row16_terms_3)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-15, -16, -15, 0, 0, 10, 9, 10, 0, 0, 0, 2] = true := by
  decide +kernel

def g32p_row16_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row16_pairing_4 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_4)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row16_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 5), (1, ⟨5, 10⟩, 10)]

theorem g32p_row16_pairing_5 :
    g32p_cyclotomicPairingCheck 15 (1)
      (g32p_pairingCoefficients 15 g32p_row16_terms_5)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-15, -15, -15, 0, 0, 10, 10, 10] = true := by
  decide +kernel

def g32p_row16_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 5), (1, ⟨5, 10⟩, 10)]

theorem g32p_row16_pairing_6 :
    g32p_cyclotomicPairingCheck 15 (1)
      (g32p_pairingCoefficients 15 g32p_row16_terms_6)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-15, -15, -15, 0, 0, 10, 10, 10] = true := by
  decide +kernel

def g32p_row16_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 5), (1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 11), (1, ⟨-1, -2⟩, 14), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 13), (1, ⟨6, 12⟩, 10)]

theorem g32p_row16_pairing_7 :
    g32p_cyclotomicPairingCheck 15 (1)
      (g32p_pairingCoefficients 15 g32p_row16_terms_7)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-15, -14, -15, 0, 0, 10, 11, 10, 0, 0, 0, -2] = true := by
  decide +kernel

def g32p_row16_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row16_pairing_8 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_8)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row16_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 5), (1, ⟨10, 20⟩, 10)]

theorem g32p_row16_pairing_9 :
    g32p_cyclotomicPairingCheck 15 (2)
      (g32p_pairingCoefficients 15 g32p_row16_terms_9)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-30, -30, -30, 0, 0, 20, 20, 20] = true := by
  decide +kernel

def g32p_row16_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 5), (1, ⟨10, 20⟩, 10)]

theorem g32p_row16_pairing_10 :
    g32p_cyclotomicPairingCheck 15 (2)
      (g32p_pairingCoefficients 15 g32p_row16_terms_10)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-30, -30, -30, 0, 0, 20, 20, 20] = true := by
  decide +kernel

def g32p_row16_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 5), (1, ⟨15, 30⟩, 10)]

theorem g32p_row16_pairing_11 :
    g32p_cyclotomicPairingCheck 15 (3)
      (g32p_pairingCoefficients 15 g32p_row16_terms_11)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-45, -45, -45, 0, 0, 30, 30, 30] = true := by
  decide +kernel

def g32p_row16_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 5), (1, ⟨15, 30⟩, 10)]

theorem g32p_row16_pairing_12 :
    g32p_cyclotomicPairingCheck 15 (3)
      (g32p_pairingCoefficients 15 g32p_row16_terms_12)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-45, -45, -45, 0, 0, 30, 30, 30] = true := by
  decide +kernel

def g32p_row16_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row16_pairing_13 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_13)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row16_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row16_pairing_14 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_14)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row16_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 5), (1, ⟨20, 40⟩, 10)]

theorem g32p_row16_pairing_15 :
    g32p_cyclotomicPairingCheck 15 (4)
      (g32p_pairingCoefficients 15 g32p_row16_terms_15)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-60, -60, -60, 0, 0, 40, 40, 40] = true := by
  decide +kernel

def g32p_row16_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 5), (1, ⟨20, 40⟩, 10)]

theorem g32p_row16_pairing_16 :
    g32p_cyclotomicPairingCheck 15 (4)
      (g32p_pairingCoefficients 15 g32p_row16_terms_16)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-60, -60, -60, 0, 0, 40, 40, 40] = true := by
  decide +kernel

def g32p_row16_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 5), (1, ⟨20, 40⟩, 10)]

theorem g32p_row16_pairing_17 :
    g32p_cyclotomicPairingCheck 15 (4)
      (g32p_pairingCoefficients 15 g32p_row16_terms_17)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-60, -60, -60, 0, 0, 40, 40, 40] = true := by
  decide +kernel

def g32p_row16_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 5), (1, ⟨20, 40⟩, 10)]

theorem g32p_row16_pairing_18 :
    g32p_cyclotomicPairingCheck 15 (4)
      (g32p_pairingCoefficients 15 g32p_row16_terms_18)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-60, -60, -60, 0, 0, 40, 40, 40] = true := by
  decide +kernel

def g32p_row16_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 5), (1, ⟨20, 40⟩, 10)]

theorem g32p_row16_pairing_19 :
    g32p_cyclotomicPairingCheck 15 (4)
      (g32p_pairingCoefficients 15 g32p_row16_terms_19)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-60, -60, -60, 0, 0, 40, 40, 40] = true := by
  decide +kernel

def g32p_row16_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 5), (1, ⟨20, 40⟩, 10)]

theorem g32p_row16_pairing_20 :
    g32p_cyclotomicPairingCheck 15 (4)
      (g32p_pairingCoefficients 15 g32p_row16_terms_20)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-60, -60, -60, 0, 0, 40, 40, 40] = true := by
  decide +kernel

def g32p_row16_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 5), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 13), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 8), (1, ⟨1, 2⟩, 11), (1, ⟨1, 2⟩, 14), (1, ⟨24, 48⟩, 10)]

theorem g32p_row16_pairing_21 :
    g32p_cyclotomicPairingCheck 15 (5)
      (g32p_pairingCoefficients 15 g32p_row16_terms_21)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-75, -76, -75, 0, 0, 50, 49, 50, 0, 0, 0, 2] = true := by
  decide +kernel

def g32p_row16_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row16_pairing_22 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_22)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row16_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 5), (1, ⟨30, 60⟩, 10)]

theorem g32p_row16_pairing_23 :
    g32p_cyclotomicPairingCheck 15 (6)
      (g32p_pairingCoefficients 15 g32p_row16_terms_23)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-90, -90, -90, 0, 0, 60, 60, 60] = true := by
  decide +kernel

def g32p_row16_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 5), (1, ⟨30, 60⟩, 10)]

theorem g32p_row16_pairing_24 :
    g32p_cyclotomicPairingCheck 15 (6)
      (g32p_pairingCoefficients 15 g32p_row16_terms_24)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-90, -90, -90, 0, 0, 60, 60, 60] = true := by
  decide +kernel

def g32p_row16_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 5), (1, ⟨30, 60⟩, 10)]

theorem g32p_row16_pairing_25 :
    g32p_cyclotomicPairingCheck 15 (6)
      (g32p_pairingCoefficients 15 g32p_row16_terms_25)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-90, -90, -90, 0, 0, 60, 60, 60] = true := by
  decide +kernel

def g32p_row16_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row16_pairing_26 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_26)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row16_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 5), (1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 11), (1, ⟨-1, -2⟩, 14), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 13), (1, ⟨36, 72⟩, 10)]

theorem g32p_row16_pairing_27 :
    g32p_cyclotomicPairingCheck 15 (7)
      (g32p_pairingCoefficients 15 g32p_row16_terms_27)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-105, -104, -105, 0, 0, 70, 71, 70, 0, 0, 0, -2] = true := by
  decide +kernel

def g32p_row16_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 5), (1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 11), (1, ⟨-1, -2⟩, 14), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 13), (1, ⟨36, 72⟩, 10)]

theorem g32p_row16_pairing_28 :
    g32p_cyclotomicPairingCheck 15 (7)
      (g32p_pairingCoefficients 15 g32p_row16_terms_28)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-105, -104, -105, 0, 0, 70, 71, 70, 0, 0, 0, -2] = true := by
  decide +kernel

def g32p_row16_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row16_pairing_29 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_29)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row16_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 5), (1, ⟨40, 80⟩, 10)]

theorem g32p_row16_pairing_30 :
    g32p_cyclotomicPairingCheck 15 (8)
      (g32p_pairingCoefficients 15 g32p_row16_terms_30)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-120, -120, -120, 0, 0, 80, 80, 80] = true := by
  decide +kernel

def g32p_row16_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 5), (1, ⟨40, 80⟩, 10)]

theorem g32p_row16_pairing_31 :
    g32p_cyclotomicPairingCheck 15 (8)
      (g32p_pairingCoefficients 15 g32p_row16_terms_31)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-120, -120, -120, 0, 0, 80, 80, 80] = true := by
  decide +kernel

def g32p_row16_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row16_pairing_32 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_32)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row16_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 5), (1, ⟨45, 90⟩, 10)]

theorem g32p_row16_pairing_33 :
    g32p_cyclotomicPairingCheck 15 (9)
      (g32p_pairingCoefficients 15 g32p_row16_terms_33)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-135, -135, -135, 0, 0, 90, 90, 90] = true := by
  decide +kernel

def g32p_row16_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 5), (1, ⟨45, 90⟩, 10)]

theorem g32p_row16_pairing_34 :
    g32p_cyclotomicPairingCheck 15 (9)
      (g32p_pairingCoefficients 15 g32p_row16_terms_34)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-135, -135, -135, 0, 0, 90, 90, 90] = true := by
  decide +kernel

def g32p_row16_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row16_pairing_35 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_35)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row16_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 5), (1, ⟨60, 120⟩, 10)]

theorem g32p_row16_pairing_36 :
    g32p_cyclotomicPairingCheck 15 (12)
      (g32p_pairingCoefficients 15 g32p_row16_terms_36)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-180, -180, -180, 0, 0, 120, 120, 120] = true := by
  decide +kernel

def g32p_row16_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 5), (1, ⟨60, 120⟩, 10)]

theorem g32p_row16_pairing_37 :
    g32p_cyclotomicPairingCheck 15 (12)
      (g32p_pairingCoefficients 15 g32p_row16_terms_37)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-180, -180, -180, 0, 0, 120, 120, 120] = true := by
  decide +kernel

def g32p_row16_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 5), (1, ⟨60, 120⟩, 10)]

theorem g32p_row16_pairing_38 :
    g32p_cyclotomicPairingCheck 15 (12)
      (g32p_pairingCoefficients 15 g32p_row16_terms_38)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-180, -180, -180, 0, 0, 120, 120, 120] = true := by
  decide +kernel

def g32p_row16_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 5), (1, ⟨60, 120⟩, 10)]

theorem g32p_row16_pairing_39 :
    g32p_cyclotomicPairingCheck 15 (12)
      (g32p_pairingCoefficients 15 g32p_row16_terms_39)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-180, -180, -180, 0, 0, 120, 120, 120] = true := by
  decide +kernel

def g32p_row16_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 5), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 13), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 8), (1, ⟨1, 2⟩, 11), (1, ⟨1, 2⟩, 14), (1, ⟨64, 128⟩, 10)]

theorem g32p_row16_pairing_40 :
    g32p_cyclotomicPairingCheck 15 (13)
      (g32p_pairingCoefficients 15 g32p_row16_terms_40)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-195, -196, -195, 0, 0, 130, 129, 130, 0, 0, 0, 2] = true := by
  decide +kernel

def g32p_row16_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 5), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 13), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 8), (1, ⟨1, 2⟩, 11), (1, ⟨1, 2⟩, 14), (1, ⟨64, 128⟩, 10)]

theorem g32p_row16_pairing_41 :
    g32p_cyclotomicPairingCheck 15 (13)
      (g32p_pairingCoefficients 15 g32p_row16_terms_41)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-195, -196, -195, 0, 0, 130, 129, 130, 0, 0, 0, 2] = true := by
  decide +kernel

def g32p_row16_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 5), (1, ⟨80, 160⟩, 10)]

theorem g32p_row16_pairing_42 :
    g32p_cyclotomicPairingCheck 15 (16)
      (g32p_pairingCoefficients 15 g32p_row16_terms_42)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-240, -240, -240, 0, 0, 160, 160, 160] = true := by
  decide +kernel

def g32p_row16_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 5), (1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 11), (1, ⟨-1, -2⟩, 14), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 13), (1, ⟨81, 162⟩, 10)]

theorem g32p_row16_pairing_43 :
    g32p_cyclotomicPairingCheck 15 (16)
      (g32p_pairingCoefficients 15 g32p_row16_terms_43)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-240, -239, -240, 0, 0, 160, 161, 160, 0, 0, 0, -2] = true := by
  decide +kernel

def g32p_row16_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 5), (1, ⟨20, 0⟩, 10)]

theorem g32p_row16_pairing_44 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_44)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [20, 20, 20] = true := by
  decide +kernel

def g32p_row16_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 5), (1, ⟨60, 0⟩, 10)]

theorem g32p_row16_pairing_45 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_45)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [60, 60, 60] = true := by
  decide +kernel

def g32p_row16_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-1, 0⟩, 1), (1, ⟨-1, 0⟩, 2), (1, ⟨-1, 0⟩, 3), (1, ⟨-1, 0⟩, 4), (1, ⟨-1, 0⟩, 6), (1, ⟨-1, 0⟩, 7), (1, ⟨-1, 0⟩, 8), (1, ⟨-1, 0⟩, 9), (1, ⟨-1, 0⟩, 11), (1, ⟨-1, 0⟩, 12), (1, ⟨-1, 0⟩, 13), (1, ⟨-1, 0⟩, 14), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 5), (1, ⟨64, 0⟩, 10)]

theorem g32p_row16_pairing_46 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_46)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [64, 63, 62, -3, -3, -2, -1] = true := by
  decide +kernel

def g32p_row16_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 5), (1, ⟨80, 0⟩, 10)]

theorem g32p_row16_pairing_47 :
    g32p_cyclotomicPairingCheck 15 (0)
      (g32p_pairingCoefficients 15 g32p_row16_terms_47)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [80, 80, 80] = true := by
  decide +kernel

theorem g32p_row16_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 16 ∧ g32SparseVec v.coords =
        (![0, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 3, 3, 0, 0, 4, 4, 4, 4, 4, 4, 5, 0, 6, 6, 6, 0, 7, 7, 0, 8, 8, 0, 9, 9, 0, 12, 12, 12, 12, 13, 13, 16, 16],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨16, 1, [(3, 1), (4, 1), (6, 1), (7, 1), (8, 1), (10, 2), (11, 2), (12, 3), (13, 3), (16, 4), (17, 4), (18, 4), (19, 4), (20, 4), (21, 4), (22, 5), (24, 6), (25, 6), (26, 6), (28, 7), (29, 7), (31, 8), (32, 8), (34, 9), (35, 9), (37, 12), (38, 12), (39, 12), (40, 12), (41, 13), (42, 13), (43, 16), (44, 16)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row17_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(216, ⟨-1, -2⟩, 2), (216, ⟨-1, -2⟩, 5), (216, ⟨1, 2⟩, 1), (216, ⟨1, 2⟩, 4)]

theorem g32p_row17_pairing_0 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_0)
      [1, -1, 1] [0, 216, 0, 216, 0, -432] = true := by
  decide +kernel

def g32p_row17_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 4), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 4), (12, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4)]

theorem g32p_row17_pairing_1 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (8, ⟨-3, -6⟩, 0), (12, ⟨-2, -4⟩, 0), (22, ⟨-2, -4⟩, 2), (22, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 0), (40, ⟨-1, -2⟩, 2), (40, ⟨-1, -2⟩, 4), (24, ⟨1, 2⟩, 0), (40, ⟨1, 2⟩, 2), (40, ⟨1, 2⟩, 4), (12, ⟨2, 4⟩, 0), (22, ⟨2, 4⟩, 2), (22, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row17_pairing_2 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (8, ⟨-3, -6⟩, 0), (12, ⟨-2, -4⟩, 0), (22, ⟨-2, -4⟩, 2), (22, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 0), (40, ⟨-1, -2⟩, 2), (40, ⟨-1, -2⟩, 4), (24, ⟨1, 2⟩, 0), (40, ⟨1, 2⟩, 2), (40, ⟨1, 2⟩, 4), (12, ⟨2, 4⟩, 0), (22, ⟨2, 4⟩, 2), (22, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row17_pairing_3 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 4), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 4), (12, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4)]

theorem g32p_row17_pairing_4 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 2), (24, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 0), (108, ⟨-1, -2⟩, 1), (66, ⟨-1, -2⟩, 2), (56, ⟨-1, -2⟩, 4), (108, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (108, ⟨1, 2⟩, 1), (56, ⟨1, 2⟩, 2), (66, ⟨1, 2⟩, 4), (108, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 4)]

theorem g32p_row17_pairing_5 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 2), (24, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 0), (108, ⟨-1, -2⟩, 1), (66, ⟨-1, -2⟩, 2), (56, ⟨-1, -2⟩, 4), (108, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (108, ⟨1, 2⟩, 1), (56, ⟨1, 2⟩, 2), (66, ⟨1, 2⟩, 4), (108, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 4)]

theorem g32p_row17_pairing_6 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 2), (12, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (18, ⟨-2, -4⟩, 2), (36, ⟨-2, -4⟩, 4), (36, ⟨-2, -4⟩, 5), (72, ⟨-1, -2⟩, 1), (72, ⟨-1, -2⟩, 2), (36, ⟨-1, -2⟩, 4), (36, ⟨1, 2⟩, 2), (72, ⟨1, 2⟩, 4), (72, ⟨1, 2⟩, 5), (36, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (18, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 2), (12, ⟨3, 6⟩, 4), (2, ⟨6, 12⟩, 4)]

theorem g32p_row17_pairing_7 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 2), (32, ⟨-3, -6⟩, 4), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 4)]

theorem g32p_row17_pairing_8 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (8, ⟨-5, -10⟩, 4), (32, ⟨-3, -6⟩, 0), (36, ⟨-2, -4⟩, 1), (36, ⟨-2, -4⟩, 2), (26, ⟨-2, -4⟩, 4), (72, ⟨-1, -2⟩, 2), (72, ⟨-1, -2⟩, 4), (72, ⟨-1, -2⟩, 5), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 2), (72, ⟨1, 2⟩, 4), (26, ⟨2, 4⟩, 2), (36, ⟨2, 4⟩, 4), (36, ⟨2, 4⟩, 5), (32, ⟨3, 6⟩, 0), (8, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 4)]

theorem g32p_row17_pairing_9 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (8, ⟨-5, -10⟩, 4), (32, ⟨-3, -6⟩, 0), (36, ⟨-2, -4⟩, 1), (36, ⟨-2, -4⟩, 2), (26, ⟨-2, -4⟩, 4), (72, ⟨-1, -2⟩, 2), (72, ⟨-1, -2⟩, 4), (72, ⟨-1, -2⟩, 5), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 2), (72, ⟨1, 2⟩, 4), (26, ⟨2, 4⟩, 2), (36, ⟨2, 4⟩, 4), (36, ⟨2, 4⟩, 5), (32, ⟨3, 6⟩, 0), (8, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 4)]

theorem g32p_row17_pairing_10 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (12, ⟨-7, -14⟩, 2), (42, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (36, ⟨-3, -6⟩, 5), (24, ⟨-2, -4⟩, 4), (72, ⟨-1, -2⟩, 2), (108, ⟨-1, -2⟩, 5), (108, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 4), (24, ⟨2, 4⟩, 2), (36, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (42, ⟨3, 6⟩, 4), (12, ⟨7, 14⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row17_pairing_11 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_11)
      [1, -1, 1] [0, 216, 0, 216, 0, -432] = true := by
  decide +kernel

def g32p_row17_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (16, ⟨-6, -12⟩, 2), (12, ⟨-3, -6⟩, 2), (72, ⟨-2, -4⟩, 2), (216, ⟨-1, -2⟩, 1), (90, ⟨-1, -2⟩, 4), (90, ⟨1, 2⟩, 2), (216, ⟨1, 2⟩, 5), (72, ⟨2, 4⟩, 4), (12, ⟨3, 6⟩, 4), (16, ⟨6, 12⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row17_pairing_12 :
    g32p_cyclotomicPairingCheck 1296 (1)
      (g32p_pairingCoefficients 6 g32p_row17_terms_12)
      [1, -1, 1] [-1296, -1512, -432, 648, 864, 432] = true := by
  decide +kernel

def g32p_row17_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 2), (32, ⟨-3, -6⟩, 4), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 4)]

theorem g32p_row17_pairing_13 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 4), (36, ⟨-2, -4⟩, 0), (36, ⟨-2, -4⟩, 2), (36, ⟨-2, -4⟩, 4), (36, ⟨2, 4⟩, 0), (36, ⟨2, 4⟩, 2), (36, ⟨2, 4⟩, 4), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 2), (8, ⟨6, 12⟩, 4)]

theorem g32p_row17_pairing_14 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-7, -14⟩, 2), (8, ⟨-7, -14⟩, 4), (24, ⟨-3, -6⟩, 2), (24, ⟨-3, -6⟩, 4), (18, ⟨-2, -4⟩, 2), (18, ⟨-2, -4⟩, 4), (18, ⟨2, 4⟩, 2), (18, ⟨2, 4⟩, 4), (24, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 4), (8, ⟨7, 14⟩, 2), (8, ⟨7, 14⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row17_pairing_15 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-6, -12⟩, 0), (4, ⟨-5, -10⟩, 2), (4, ⟨-5, -10⟩, 4), (6, ⟨-4, -8⟩, 2), (6, ⟨-4, -8⟩, 4), (36, ⟨-2, -4⟩, 0), (52, ⟨-1, -2⟩, 2), (52, ⟨-1, -2⟩, 4), (52, ⟨1, 2⟩, 2), (52, ⟨1, 2⟩, 4), (36, ⟨2, 4⟩, 0), (6, ⟨4, 8⟩, 2), (6, ⟨4, 8⟩, 4), (4, ⟨5, 10⟩, 2), (4, ⟨5, 10⟩, 4), (8, ⟨6, 12⟩, 0), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row17_pairing_16 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (4, ⟨-8, -16⟩, 2), (4, ⟨-8, -16⟩, 4), (4, ⟨-5, -10⟩, 2), (4, ⟨-5, -10⟩, 4), (32, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 4), (18, ⟨-2, -4⟩, 2), (18, ⟨-2, -4⟩, 4), (18, ⟨2, 4⟩, 2), (18, ⟨2, 4⟩, 4), (32, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 2), (12, ⟨3, 6⟩, 4), (4, ⟨5, 10⟩, 2), (4, ⟨5, 10⟩, 4), (4, ⟨8, 16⟩, 2), (4, ⟨8, 16⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row17_pairing_17 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-6, -12⟩, 0), (4, ⟨-5, -10⟩, 2), (4, ⟨-5, -10⟩, 4), (6, ⟨-4, -8⟩, 2), (6, ⟨-4, -8⟩, 4), (36, ⟨-2, -4⟩, 0), (52, ⟨-1, -2⟩, 2), (52, ⟨-1, -2⟩, 4), (52, ⟨1, 2⟩, 2), (52, ⟨1, 2⟩, 4), (36, ⟨2, 4⟩, 0), (6, ⟨4, 8⟩, 2), (6, ⟨4, 8⟩, 4), (4, ⟨5, 10⟩, 2), (4, ⟨5, 10⟩, 4), (8, ⟨6, 12⟩, 0), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row17_pairing_18 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (4, ⟨-8, -16⟩, 2), (4, ⟨-8, -16⟩, 4), (4, ⟨-5, -10⟩, 2), (4, ⟨-5, -10⟩, 4), (32, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 4), (18, ⟨-2, -4⟩, 2), (18, ⟨-2, -4⟩, 4), (18, ⟨2, 4⟩, 2), (18, ⟨2, 4⟩, 4), (32, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 2), (12, ⟨3, 6⟩, 4), (4, ⟨5, 10⟩, 2), (4, ⟨5, 10⟩, 4), (4, ⟨8, 16⟩, 2), (4, ⟨8, 16⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row17_pairing_19 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 2), (12, ⟨-5, -10⟩, 2), (30, ⟨-4, -8⟩, 2), (36, ⟨-4, -8⟩, 5), (16, ⟨-2, -4⟩, 2), (48, ⟨-2, -4⟩, 4), (84, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 4), (72, ⟨-1, -2⟩, 5), (72, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (84, ⟨1, 2⟩, 4), (48, ⟨2, 4⟩, 2), (16, ⟨2, 4⟩, 4), (36, ⟨4, 8⟩, 1), (30, ⟨4, 8⟩, 4), (12, ⟨5, 10⟩, 4), (2, ⟨20, 40⟩, 4)]

theorem g32p_row17_pairing_20 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_20)
      [1, -1, 1] [0, 216, 0, 216, 0, -432] = true := by
  decide +kernel

def g32p_row17_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 2), (12, ⟨-8, -16⟩, 2), (16, ⟨-6, -12⟩, 2), (24, ⟨-3, -6⟩, 2), (72, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 4), (24, ⟨1, 2⟩, 2), (72, ⟨2, 4⟩, 4), (24, ⟨3, 6⟩, 4), (16, ⟨6, 12⟩, 4), (12, ⟨8, 16⟩, 4), (2, ⟨24, 48⟩, 4)]

theorem g32p_row17_pairing_21 :
    g32p_cyclotomicPairingCheck 1296 (1)
      (g32p_pairingCoefficients 6 g32p_row17_terms_21)
      [1, -1, 1] [-1296, -1296, -432, 864, 864] = true := by
  decide +kernel

def g32p_row17_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (12, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 4), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 4), (12, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4)]

theorem g32p_row17_pairing_22 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (8, ⟨-9, -18⟩, 0), (12, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 4), (8, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 2), (24, ⟨-2, -4⟩, 4), (36, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (72, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (72, ⟨-1, -2⟩, 4), (24, ⟨1, 2⟩, 0), (72, ⟨1, 2⟩, 2), (12, ⟨1, 2⟩, 4), (72, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 0), (36, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (18, ⟨2, 4⟩, 4), (12, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (8, ⟨6, 12⟩, 2), (12, ⟨6, 12⟩, 4), (8, ⟨9, 18⟩, 0), (2, ⟨30, 60⟩, 4)]

theorem g32p_row17_pairing_23 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_23)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (8, ⟨-9, -18⟩, 0), (12, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 4), (8, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 2), (24, ⟨-2, -4⟩, 4), (36, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (72, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (72, ⟨-1, -2⟩, 4), (24, ⟨1, 2⟩, 0), (72, ⟨1, 2⟩, 2), (12, ⟨1, 2⟩, 4), (72, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 0), (36, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (18, ⟨2, 4⟩, 4), (12, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (8, ⟨6, 12⟩, 2), (12, ⟨6, 12⟩, 4), (8, ⟨9, 18⟩, 0), (2, ⟨30, 60⟩, 4)]

theorem g32p_row17_pairing_24 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_24)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (12, ⟨-10, -20⟩, 4), (52, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 2), (36, ⟨-2, -4⟩, 5), (72, ⟨-1, -2⟩, 1), (132, ⟨-1, -2⟩, 4), (132, ⟨1, 2⟩, 2), (72, ⟨1, 2⟩, 5), (36, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 4), (52, ⟨3, 6⟩, 4), (12, ⟨10, 20⟩, 2), (2, ⟨30, 60⟩, 4)]

theorem g32p_row17_pairing_25 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (24, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 2), (24, ⟨-3, -6⟩, 4), (24, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 4), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4)]

theorem g32p_row17_pairing_26 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 4), (24, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 4), (24, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 2), (12, ⟨3, 6⟩, 4), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row17_pairing_27 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 4), (24, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 4), (24, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 2), (12, ⟨3, 6⟩, 4), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row17_pairing_28 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 4), (36, ⟨-2, -4⟩, 0), (36, ⟨-2, -4⟩, 2), (36, ⟨-2, -4⟩, 4), (36, ⟨2, 4⟩, 0), (36, ⟨2, 4⟩, 2), (36, ⟨2, 4⟩, 4), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 2), (8, ⟨6, 12⟩, 4)]

theorem g32p_row17_pairing_29 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (20, ⟨-8, -16⟩, 4), (8, ⟨-6, -12⟩, 0), (36, ⟨-2, -4⟩, 0), (36, ⟨-2, -4⟩, 2), (20, ⟨-2, -4⟩, 4), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 4), (36, ⟨2, 4⟩, 0), (20, ⟨2, 4⟩, 2), (36, ⟨2, 4⟩, 4), (8, ⟨6, 12⟩, 0), (20, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 4)]

theorem g32p_row17_pairing_30 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (20, ⟨-8, -16⟩, 4), (8, ⟨-6, -12⟩, 0), (36, ⟨-2, -4⟩, 0), (36, ⟨-2, -4⟩, 2), (20, ⟨-2, -4⟩, 4), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 4), (36, ⟨2, 4⟩, 0), (20, ⟨2, 4⟩, 2), (36, ⟨2, 4⟩, 4), (8, ⟨6, 12⟩, 0), (20, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 4)]

theorem g32p_row17_pairing_31 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (24, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 2), (24, ⟨-3, -6⟩, 4), (24, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 4), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4)]

theorem g32p_row17_pairing_32 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (24, ⟨-3, -6⟩, 0), (36, ⟨-3, -6⟩, 1), (54, ⟨-3, -6⟩, 4), (108, ⟨-1, -2⟩, 5), (108, ⟨1, 2⟩, 1), (24, ⟨3, 6⟩, 0), (54, ⟨3, 6⟩, 2), (36, ⟨3, 6⟩, 5), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 4), (2, ⟨45, 90⟩, 4)]

theorem g32p_row17_pairing_33 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (24, ⟨-3, -6⟩, 0), (36, ⟨-3, -6⟩, 1), (54, ⟨-3, -6⟩, 4), (108, ⟨-1, -2⟩, 5), (108, ⟨1, 2⟩, 1), (24, ⟨3, 6⟩, 0), (54, ⟨3, 6⟩, 2), (36, ⟨3, 6⟩, 5), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 4), (2, ⟨45, 90⟩, 4)]

theorem g32p_row17_pairing_34 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (12, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 4), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 4), (12, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4)]

theorem g32p_row17_pairing_35 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-9, -18⟩, 0), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 4), (16, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 4), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 4), (12, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 4), (8, ⟨9, 18⟩, 0), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row17_pairing_36 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (6, ⟨-6, -12⟩, 2), (6, ⟨-6, -12⟩, 4), (32, ⟨-3, -6⟩, 2), (32, ⟨-3, -6⟩, 4), (32, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 4), (6, ⟨6, 12⟩, 2), (6, ⟨6, 12⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row17_pairing_37 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-9, -18⟩, 0), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 4), (16, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 4), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 4), (12, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 4), (8, ⟨9, 18⟩, 0), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row17_pairing_38 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 2), (16, ⟨-6, -12⟩, 2), (18, ⟨-4, -8⟩, 2), (12, ⟨-4, -8⟩, 4), (36, ⟨-4, -8⟩, 5), (36, ⟨-3, -6⟩, 4), (48, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 2), (48, ⟨-1, -2⟩, 4), (72, ⟨-1, -2⟩, 5), (72, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (36, ⟨1, 2⟩, 4), (48, ⟨2, 4⟩, 4), (36, ⟨3, 6⟩, 2), (36, ⟨4, 8⟩, 1), (12, ⟨4, 8⟩, 2), (18, ⟨4, 8⟩, 4), (16, ⟨6, 12⟩, 4), (2, ⟨60, 120⟩, 4)]

theorem g32p_row17_pairing_39 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_39)
      [1, -1, 1] [0, 216, 0, 216, 0, -432] = true := by
  decide +kernel

def g32p_row17_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 2), (16, ⟨-8, -16⟩, 4), (12, ⟨-4, -8⟩, 2), (24, ⟨-2, -4⟩, 4), (24, ⟨2, 4⟩, 2), (12, ⟨4, 8⟩, 4), (16, ⟨8, 16⟩, 2), (2, ⟨64, 128⟩, 4)]

theorem g32p_row17_pairing_40 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (8, ⟨-8, -16⟩, 2), (8, ⟨-8, -16⟩, 4), (6, ⟨-4, -8⟩, 2), (6, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (6, ⟨4, 8⟩, 2), (6, ⟨4, 8⟩, 4), (8, ⟨8, 16⟩, 2), (8, ⟨8, 16⟩, 4), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 4)]

theorem g32p_row17_pairing_41 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (8, ⟨-8, -16⟩, 2), (8, ⟨-8, -16⟩, 4), (12, ⟨-4, -8⟩, 2), (12, ⟨-4, -8⟩, 4), (6, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 4), (6, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 4), (12, ⟨4, 8⟩, 2), (12, ⟨4, 8⟩, 4), (8, ⟨8, 16⟩, 2), (8, ⟨8, 16⟩, 4), (1, ⟨80, 160⟩, 2), (1, ⟨80, 160⟩, 4)]

theorem g32p_row17_pairing_42 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 2), (12, ⟨-9, -18⟩, 2), (36, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 4), (108, ⟨-1, -2⟩, 1), (108, ⟨1, 2⟩, 5), (18, ⟨3, 6⟩, 2), (36, ⟨3, 6⟩, 5), (12, ⟨9, 18⟩, 4), (2, ⟨81, 162⟩, 4)]

theorem g32p_row17_pairing_43 :
    g32p_cyclotomicPairingCheck 1296 (1)
      (g32p_pairingCoefficients 6 g32p_row17_terms_43)
      [1, -1, 1] [-1296, -1512, -432, 648, 864, 432] = true := by
  decide +kernel

def g32p_row17_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 4), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 2), (8, ⟨-7, 0⟩, 4), (24, ⟨-3, 0⟩, 0), (24, ⟨-3, 0⟩, 2), (24, ⟨-3, 0⟩, 4), (18, ⟨-2, 0⟩, 0), (18, ⟨-2, 0⟩, 2), (18, ⟨-2, 0⟩, 4), (18, ⟨2, 0⟩, 0), (18, ⟨2, 0⟩, 2), (18, ⟨2, 0⟩, 4), (24, ⟨3, 0⟩, 0), (24, ⟨3, 0⟩, 2), (24, ⟨3, 0⟩, 4), (8, ⟨7, 0⟩, 0), (8, ⟨7, 0⟩, 2), (8, ⟨7, 0⟩, 4), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row17_pairing_44 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 4), (6, ⟨-6, 0⟩, 0), (6, ⟨-6, 0⟩, 2), (6, ⟨-6, 0⟩, 4), (32, ⟨-3, 0⟩, 0), (32, ⟨-3, 0⟩, 2), (32, ⟨-3, 0⟩, 4), (32, ⟨3, 0⟩, 0), (32, ⟨3, 0⟩, 2), (32, ⟨3, 0⟩, 4), (6, ⟨6, 0⟩, 0), (6, ⟨6, 0⟩, 2), (6, ⟨6, 0⟩, 4), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row17_pairing_45 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 4), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 2), (8, ⟨-8, 0⟩, 4), (6, ⟨-4, 0⟩, 0), (6, ⟨-4, 0⟩, 2), (6, ⟨-4, 0⟩, 4), (12, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 2), (12, ⟨-2, 0⟩, 4), (12, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 2), (12, ⟨2, 0⟩, 4), (6, ⟨4, 0⟩, 0), (6, ⟨4, 0⟩, 2), (6, ⟨4, 0⟩, 4), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 2), (8, ⟨8, 0⟩, 4), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row17_pairing_46 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row17_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 4), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 2), (8, ⟨-8, 0⟩, 4), (12, ⟨-4, 0⟩, 0), (12, ⟨-4, 0⟩, 2), (12, ⟨-4, 0⟩, 4), (6, ⟨-2, 0⟩, 0), (6, ⟨-2, 0⟩, 2), (6, ⟨-2, 0⟩, 4), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 2), (6, ⟨2, 0⟩, 4), (12, ⟨4, 0⟩, 0), (12, ⟨4, 0⟩, 2), (12, ⟨4, 0⟩, 4), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 2), (8, ⟨8, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row17_pairing_47 :
    g32p_cyclotomicPairingCheck 1296 (0)
      (g32p_pairingCoefficients 6 g32p_row17_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row17_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 17 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨17, -1, [(13, 1), (22, 1), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row18_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-1, -2⟩, 0), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 3), (2, ⟨-1, -2⟩, 4), (2, ⟨-1, -2⟩, 5), (2, ⟨1, 2⟩, 0), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 3), (2, ⟨1, 2⟩, 4), (2, ⟨1, 2⟩, 5)]

theorem g32p_row18_pairing_0 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row18_pairing_1 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-4, -8⟩, 0), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (2, ⟨4, 8⟩, 0)]

theorem g32p_row18_pairing_2 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-4, -8⟩, 0), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (2, ⟨4, 8⟩, 0)]

theorem g32p_row18_pairing_3 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-2, -4⟩, 5), (6, ⟨2, 4⟩, 1)]

theorem g32p_row18_pairing_4 :
    g32p_cyclotomicPairingCheck 36 (-1)
      (g32p_pairingCoefficients 6 g32p_row18_terms_4)
      [1, -1, 1] [36, 48, 12, -12, -24, -24] = true := by
  decide +kernel

def g32p_row18_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 0), (2, ⟨-3, -6⟩, 3), (2, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 4), (2, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 5), (2, ⟨2, 4⟩, 1), (2, ⟨3, 6⟩, 3), (2, ⟨5, 10⟩, 0)]

theorem g32p_row18_pairing_5 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 0), (2, ⟨-3, -6⟩, 3), (2, ⟨-2, -4⟩, 1), (2, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 4), (2, ⟨2, 4⟩, 5), (2, ⟨3, 6⟩, 3), (2, ⟨5, 10⟩, 0)]

theorem g32p_row18_pairing_6 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 0), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-2, -4⟩, 3), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 5), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 5), (2, ⟨2, 4⟩, 3), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨6, 12⟩, 0)]

theorem g32p_row18_pairing_7 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row18_pairing_8 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 0), (2, ⟨-2, -4⟩, 3), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 4), (2, ⟨-1, -2⟩, 5), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 4), (2, ⟨1, 2⟩, 5), (2, ⟨2, 4⟩, 3), (2, ⟨10, 20⟩, 0)]

theorem g32p_row18_pairing_9 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 0), (2, ⟨-2, -4⟩, 3), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 4), (2, ⟨-1, -2⟩, 5), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 4), (2, ⟨1, 2⟩, 5), (2, ⟨2, 4⟩, 3), (2, ⟨10, 20⟩, 0)]

theorem g32p_row18_pairing_10 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 0), (2, ⟨-7, -14⟩, 3), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 5), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 5), (2, ⟨7, 14⟩, 3), (2, ⟨15, 30⟩, 0)]

theorem g32p_row18_pairing_11 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_11)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 0), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 3), (2, ⟨-1, -2⟩, 5), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 3), (2, ⟨1, 2⟩, 5), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨15, 30⟩, 0)]

theorem g32p_row18_pairing_12 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row18_pairing_13 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row18_pairing_14 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (2, ⟨20, 40⟩, 0)]

theorem g32p_row18_pairing_15 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (2, ⟨-4, -8⟩, 2), (2, ⟨-4, -8⟩, 4), (2, ⟨4, 8⟩, 2), (2, ⟨4, 8⟩, 4), (2, ⟨20, 40⟩, 0)]

theorem g32p_row18_pairing_16 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (2, ⟨20, 40⟩, 0)]

theorem g32p_row18_pairing_17 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (2, ⟨-4, -8⟩, 2), (2, ⟨-4, -8⟩, 4), (2, ⟨4, 8⟩, 2), (2, ⟨4, 8⟩, 4), (2, ⟨20, 40⟩, 0)]

theorem g32p_row18_pairing_18 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (2, ⟨20, 40⟩, 0)]

theorem g32p_row18_pairing_19 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (2, ⟨-5, -10⟩, 2), (2, ⟨-5, -10⟩, 4), (2, ⟨-4, -8⟩, 3), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 5), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 5), (2, ⟨4, 8⟩, 3), (2, ⟨5, 10⟩, 2), (2, ⟨5, 10⟩, 4), (2, ⟨20, 40⟩, 0)]

theorem g32p_row18_pairing_20 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 0), (2, ⟨-8, -16⟩, 3), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 5), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 5), (2, ⟨8, 16⟩, 3), (2, ⟨24, 48⟩, 0)]

theorem g32p_row18_pairing_21 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-2, -4⟩, 1), (6, ⟨2, 4⟩, 5)]

theorem g32p_row18_pairing_22 :
    g32p_cyclotomicPairingCheck 36 (1)
      (g32p_pairingCoefficients 6 g32p_row18_terms_22)
      [1, -1, 1] [-36, -48, -12, 12, 24, 24] = true := by
  decide +kernel

def g32p_row18_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 0), (2, ⟨-6, -12⟩, 3), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 1), (4, ⟨1, 2⟩, 5), (2, ⟨2, 4⟩, 1), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨6, 12⟩, 3), (2, ⟨30, 60⟩, 0)]

theorem g32p_row18_pairing_23 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_23)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 0), (2, ⟨-6, -12⟩, 3), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-2, -4⟩, 1), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 1), (2, ⟨2, 4⟩, 5), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨6, 12⟩, 3), (2, ⟨30, 60⟩, 0)]

theorem g32p_row18_pairing_24 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_24)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 0), (2, ⟨-10, -20⟩, 3), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 5), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 5), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨10, 20⟩, 3), (2, ⟨30, 60⟩, 0)]

theorem g32p_row18_pairing_25 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row18_pairing_26 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-36, -72⟩, 0), (2, ⟨36, 72⟩, 0)]

theorem g32p_row18_pairing_27 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-36, -72⟩, 0), (2, ⟨36, 72⟩, 0)]

theorem g32p_row18_pairing_28 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-2, -4⟩, 5), (6, ⟨2, 4⟩, 1)]

theorem g32p_row18_pairing_29 :
    g32p_cyclotomicPairingCheck 36 (-1)
      (g32p_pairingCoefficients 6 g32p_row18_terms_29)
      [1, -1, 1] [36, 48, 12, -12, -24, -24] = true := by
  decide +kernel

def g32p_row18_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 0), (2, ⟨-8, -16⟩, 3), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (2, ⟨-2, -4⟩, 5), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (2, ⟨2, 4⟩, 5), (2, ⟨8, 16⟩, 3), (2, ⟨40, 80⟩, 0)]

theorem g32p_row18_pairing_30 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 0), (2, ⟨-8, -16⟩, 3), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (2, ⟨-2, -4⟩, 5), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (2, ⟨2, 4⟩, 5), (2, ⟨8, 16⟩, 3), (2, ⟨40, 80⟩, 0)]

theorem g32p_row18_pairing_31 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row18_pairing_32 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 0), (2, ⟨-3, -6⟩, 3), (2, ⟨3, 6⟩, 3), (2, ⟨45, 90⟩, 0)]

theorem g32p_row18_pairing_33 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 0), (2, ⟨-3, -6⟩, 3), (2, ⟨3, 6⟩, 3), (2, ⟨45, 90⟩, 0)]

theorem g32p_row18_pairing_34 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row18_pairing_35 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 0), (2, ⟨60, 120⟩, 0)]

theorem g32p_row18_pairing_36 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 0), (2, ⟨-6, -12⟩, 2), (2, ⟨-6, -12⟩, 4), (2, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 4), (2, ⟨60, 120⟩, 0)]

theorem g32p_row18_pairing_37 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 0), (2, ⟨60, 120⟩, 0)]

theorem g32p_row18_pairing_38 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 0), (2, ⟨-4, -8⟩, 3), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 5), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 5), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨4, 8⟩, 3), (2, ⟨60, 120⟩, 0)]

theorem g32p_row18_pairing_39 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 0), (2, ⟨-4, -8⟩, 2), (2, ⟨-4, -8⟩, 4), (2, ⟨4, 8⟩, 2), (2, ⟨4, 8⟩, 4), (2, ⟨64, 128⟩, 0)]

theorem g32p_row18_pairing_40 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 0), (2, ⟨-4, -8⟩, 2), (2, ⟨-4, -8⟩, 4), (2, ⟨4, 8⟩, 2), (2, ⟨4, 8⟩, 4), (2, ⟨64, 128⟩, 0)]

theorem g32p_row18_pairing_41 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-80, -160⟩, 0), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (2, ⟨80, 160⟩, 0)]

theorem g32p_row18_pairing_42 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 0), (2, ⟨-9, -18⟩, 3), (2, ⟨9, 18⟩, 3), (2, ⟨81, 162⟩, 0)]

theorem g32p_row18_pairing_43 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_43)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-20, 0⟩, 0), (3, ⟨-2, 0⟩, 2), (3, ⟨-2, 0⟩, 4), (3, ⟨2, 0⟩, 2), (3, ⟨2, 0⟩, 4), (3, ⟨20, 0⟩, 0)]

theorem g32p_row18_pairing_44 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-60, 0⟩, 0), (3, ⟨-6, 0⟩, 2), (3, ⟨-6, 0⟩, 4), (3, ⟨6, 0⟩, 2), (3, ⟨6, 0⟩, 4), (3, ⟨60, 0⟩, 0)]

theorem g32p_row18_pairing_45 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-64, 0⟩, 0), (3, ⟨-4, 0⟩, 2), (3, ⟨-4, 0⟩, 4), (3, ⟨4, 0⟩, 2), (3, ⟨4, 0⟩, 4), (3, ⟨64, 0⟩, 0)]

theorem g32p_row18_pairing_46 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row18_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-80, 0⟩, 0), (3, ⟨-2, 0⟩, 2), (3, ⟨-2, 0⟩, 4), (3, ⟨2, 0⟩, 2), (3, ⟨2, 0⟩, 4), (3, ⟨80, 0⟩, 0)]

theorem g32p_row18_pairing_47 :
    g32p_cyclotomicPairingCheck 36 (0)
      (g32p_pairingCoefficients 6 g32p_row18_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row18_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 18 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨18, -1, [(5, -1), (23, 1), (30, -1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row19_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(64, ⟨-1, -2⟩, 0), (64, ⟨-1, -2⟩, 1), (64, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 3), (64, ⟨-1, -2⟩, 4), (64, ⟨-1, -2⟩, 5), (64, ⟨1, 2⟩, 0), (64, ⟨1, 2⟩, 1), (64, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 3), (64, ⟨1, 2⟩, 4), (64, ⟨1, 2⟩, 5)]

theorem g32p_row19_pairing_0 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row19_pairing_1 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (32, ⟨-2, -4⟩, 0), (28, ⟨-2, -4⟩, 2), (28, ⟨-2, -4⟩, 4), (32, ⟨2, 4⟩, 0), (28, ⟨2, 4⟩, 2), (28, ⟨2, 4⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row19_pairing_2 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (32, ⟨-2, -4⟩, 0), (28, ⟨-2, -4⟩, 2), (28, ⟨-2, -4⟩, 4), (32, ⟨2, 4⟩, 0), (28, ⟨2, 4⟩, 2), (28, ⟨2, 4⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row19_pairing_3 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 3), (32, ⟨-2, -4⟩, 4), (32, ⟨-2, -4⟩, 5), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 3), (32, ⟨2, 4⟩, 4), (32, ⟨2, 4⟩, 5)]

theorem g32p_row19_pairing_4 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 4), (32, ⟨-2, -4⟩, 4), (32, ⟨-2, -4⟩, 5), (64, ⟨-1, -2⟩, 0), (80, ⟨-1, -2⟩, 1), (92, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 3), (32, ⟨-1, -2⟩, 4), (40, ⟨-1, -2⟩, 5), (64, ⟨1, 2⟩, 0), (40, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 3), (92, ⟨1, 2⟩, 4), (80, ⟨1, 2⟩, 5), (32, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row19_pairing_5 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 4), (32, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (64, ⟨-1, -2⟩, 0), (112, ⟨-1, -2⟩, 1), (124, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 5), (64, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (64, ⟨1, 2⟩, 3), (124, ⟨1, 2⟩, 4), (112, ⟨1, 2⟩, 5), (32, ⟨2, 4⟩, 4), (32, ⟨2, 4⟩, 5), (2, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row19_pairing_6 :
    g32p_cyclotomicPairingCheck 1152 (1)
      (g32p_pairingCoefficients 6 g32p_row19_terms_6)
      [1, -1, 1] [-1152, -1344, -384, 576, 768, 384] = true := by
  decide +kernel

def g32p_row19_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 2), (32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 4), (8, ⟨-2, -4⟩, 1), (60, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (64, ⟨-1, -2⟩, 3), (32, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 3), (32, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (60, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 4)]

theorem g32p_row19_pairing_7 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row19_pairing_8 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (8, ⟨-2, -4⟩, 1), (26, ⟨-2, -4⟩, 2), (36, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (64, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 3), (32, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (64, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 3), (32, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (26, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row19_pairing_9 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (8, ⟨-2, -4⟩, 1), (26, ⟨-2, -4⟩, 2), (36, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (64, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 3), (32, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (64, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 3), (32, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (26, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row19_pairing_10 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (2, ⟨-7, -14⟩, 2), (8, ⟨-7, -14⟩, 5), (36, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 5), (32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 3), (32, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 4), (48, ⟨-1, -2⟩, 5), (48, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 3), (32, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 1), (36, ⟨3, 6⟩, 4), (8, ⟨7, 14⟩, 1), (2, ⟨7, 14⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row19_pairing_11 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_11)
      [1, -1, 1] [0, 192, 0, 192, 0, -384] = true := by
  decide +kernel

def g32p_row19_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (32, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 2), (32, ⟨-3, -6⟩, 4), (32, ⟨-1, -2⟩, 0), (64, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 3), (38, ⟨-1, -2⟩, 4), (64, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 0), (64, ⟨1, 2⟩, 1), (38, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 3), (32, ⟨1, 2⟩, 4), (64, ⟨1, 2⟩, 5), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row19_pairing_12 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row19_pairing_13 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row19_pairing_14 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (32, ⟨-2, -4⟩, 0), (28, ⟨-2, -4⟩, 2), (28, ⟨-2, -4⟩, 4), (32, ⟨2, 4⟩, 0), (28, ⟨2, 4⟩, 2), (28, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row19_pairing_15 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (32, ⟨-4, -8⟩, 0), (16, ⟨-4, -8⟩, 2), (16, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (32, ⟨4, 8⟩, 0), (16, ⟨4, 8⟩, 2), (16, ⟨4, 8⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row19_pairing_16 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (32, ⟨-2, -4⟩, 0), (28, ⟨-2, -4⟩, 2), (28, ⟨-2, -4⟩, 4), (32, ⟨2, 4⟩, 0), (28, ⟨2, 4⟩, 2), (28, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row19_pairing_17 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (32, ⟨-4, -8⟩, 0), (16, ⟨-4, -8⟩, 2), (16, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (32, ⟨4, 8⟩, 0), (16, ⟨4, 8⟩, 2), (16, ⟨4, 8⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row19_pairing_18 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (32, ⟨-2, -4⟩, 0), (28, ⟨-2, -4⟩, 2), (28, ⟨-2, -4⟩, 4), (32, ⟨2, 4⟩, 0), (28, ⟨2, 4⟩, 2), (28, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row19_pairing_19 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 2), (32, ⟨-5, -10⟩, 0), (32, ⟨-5, -10⟩, 4), (38, ⟨-4, -8⟩, 2), (16, ⟨-4, -8⟩, 5), (32, ⟨-1, -2⟩, 0), (64, ⟨-1, -2⟩, 1), (64, ⟨-1, -2⟩, 3), (32, ⟨-1, -2⟩, 4), (32, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 3), (64, ⟨1, 2⟩, 5), (16, ⟨4, 8⟩, 1), (38, ⟨4, 8⟩, 4), (32, ⟨5, 10⟩, 0), (32, ⟨5, 10⟩, 2), (2, ⟨20, 40⟩, 4)]

theorem g32p_row19_pairing_20 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 2), (2, ⟨-8, -16⟩, 2), (8, ⟨-8, -16⟩, 5), (32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 3), (32, ⟨-2, -4⟩, 4), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 3), (32, ⟨2, 4⟩, 5), (8, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 4), (2, ⟨24, 48⟩, 4)]

theorem g32p_row19_pairing_21 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 3), (32, ⟨-2, -4⟩, 4), (32, ⟨-2, -4⟩, 5), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 3), (32, ⟨2, 4⟩, 4), (32, ⟨2, 4⟩, 5)]

theorem g32p_row19_pairing_22 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (2, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 5), (32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 2), (60, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 4), (40, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 0), (64, ⟨-1, -2⟩, 3), (32, ⟨-1, -2⟩, 4), (64, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 0), (64, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 3), (40, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (60, ⟨2, 4⟩, 4), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 4), (8, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row19_pairing_23 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_23)
      [1, -1, 1] [0, 192, 0, 192, 0, -384] = true := by
  decide +kernel

def g32p_row19_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (2, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 5), (32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 2), (32, ⟨-2, -4⟩, 1), (92, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 3), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (64, ⟨1, 2⟩, 3), (32, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 1), (92, ⟨2, 4⟩, 4), (32, ⟨2, 4⟩, 5), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 4), (8, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row19_pairing_24 :
    g32p_cyclotomicPairingCheck 1152 (1)
      (g32p_pairingCoefficients 6 g32p_row19_terms_24)
      [1, -1, 1] [-1152, -1152, -384, 768, 768] = true := by
  decide +kernel

def g32p_row19_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (8, ⟨-10, -20⟩, 1), (2, ⟨-10, -20⟩, 4), (32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 4), (36, ⟨-2, -4⟩, 2), (24, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 3), (64, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 0), (64, ⟨1, 2⟩, 1), (64, ⟨1, 2⟩, 3), (32, ⟨1, 2⟩, 4), (8, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (36, ⟨2, 4⟩, 4), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 2), (2, ⟨10, 20⟩, 2), (8, ⟨10, 20⟩, 5), (2, ⟨30, 60⟩, 4)]

theorem g32p_row19_pairing_25 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row19_pairing_26 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row19_pairing_27 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row19_pairing_28 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 3), (32, ⟨-2, -4⟩, 4), (32, ⟨-2, -4⟩, 5), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 3), (32, ⟨2, 4⟩, 4), (32, ⟨2, 4⟩, 5)]

theorem g32p_row19_pairing_29 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (8, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 4), (32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 3), (64, ⟨-2, -4⟩, 4), (32, ⟨-2, -4⟩, 5), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (64, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 3), (32, ⟨2, 4⟩, 4), (2, ⟨8, 16⟩, 2), (8, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row19_pairing_30 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (8, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 4), (64, ⟨-2, -4⟩, 0), (64, ⟨-2, -4⟩, 1), (64, ⟨-2, -4⟩, 2), (64, ⟨2, 4⟩, 0), (64, ⟨2, 4⟩, 4), (64, ⟨2, 4⟩, 5), (2, ⟨8, 16⟩, 2), (8, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row19_pairing_31 :
    g32p_cyclotomicPairingCheck 1152 (1)
      (g32p_pairingCoefficients 6 g32p_row19_terms_31)
      [1, -1, 1] [-1152, -1344, -384, 576, 768, 384] = true := by
  decide +kernel

def g32p_row19_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row19_pairing_32 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (16, ⟨-3, -6⟩, 1), (38, ⟨-3, -6⟩, 4), (24, ⟨-1, -2⟩, 2), (48, ⟨-1, -2⟩, 5), (48, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 4), (38, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row19_pairing_33 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (16, ⟨-3, -6⟩, 1), (38, ⟨-3, -6⟩, 4), (24, ⟨-1, -2⟩, 2), (48, ⟨-1, -2⟩, 5), (48, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 4), (38, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row19_pairing_34 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row19_pairing_35 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row19_pairing_36 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (32, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 2), (16, ⟨-6, -12⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (32, ⟨6, 12⟩, 0), (16, ⟨6, 12⟩, 2), (16, ⟨6, 12⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row19_pairing_37 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row19_pairing_38 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 2), (8, ⟨-4, -8⟩, 1), (36, ⟨-4, -8⟩, 2), (2, ⟨-4, -8⟩, 4), (8, ⟨-4, -8⟩, 5), (32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 2), (32, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 3), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (64, ⟨1, 2⟩, 3), (32, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 4), (8, ⟨4, 8⟩, 1), (2, ⟨4, 8⟩, 2), (36, ⟨4, 8⟩, 4), (8, ⟨4, 8⟩, 5), (2, ⟨60, 120⟩, 4)]

theorem g32p_row19_pairing_39 :
    g32p_cyclotomicPairingCheck 1152 (1)
      (g32p_pairingCoefficients 6 g32p_row19_terms_39)
      [1, -1, 1] [-1152, -1152, -384, 768, 768] = true := by
  decide +kernel

def g32p_row19_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 2), (32, ⟨-4, -8⟩, 0), (32, ⟨-4, -8⟩, 4), (32, ⟨4, 8⟩, 0), (32, ⟨4, 8⟩, 2), (2, ⟨64, 128⟩, 4)]

theorem g32p_row19_pairing_40 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (32, ⟨-4, -8⟩, 0), (16, ⟨-4, -8⟩, 2), (16, ⟨-4, -8⟩, 4), (32, ⟨4, 8⟩, 0), (16, ⟨4, 8⟩, 2), (16, ⟨4, 8⟩, 4), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 4)]

theorem g32p_row19_pairing_41 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (32, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 4), (32, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 2), (16, ⟨2, 4⟩, 4), (1, ⟨80, 160⟩, 2), (1, ⟨80, 160⟩, 4)]

theorem g32p_row19_pairing_42 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 2), (2, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 5), (8, ⟨-3, -6⟩, 1), (60, ⟨-3, -6⟩, 4), (48, ⟨-1, -2⟩, 1), (48, ⟨1, 2⟩, 5), (60, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 5), (8, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 4), (2, ⟨81, 162⟩, 4)]

theorem g32p_row19_pairing_43 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_43)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 4), (44, ⟨-2, 0⟩, 0), (44, ⟨-2, 0⟩, 2), (44, ⟨-2, 0⟩, 4), (44, ⟨2, 0⟩, 0), (44, ⟨2, 0⟩, 2), (44, ⟨2, 0⟩, 4), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row19_pairing_44 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 4), (32, ⟨-6, 0⟩, 0), (32, ⟨-6, 0⟩, 2), (32, ⟨-6, 0⟩, 4), (12, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 2), (12, ⟨-2, 0⟩, 4), (12, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 2), (12, ⟨2, 0⟩, 4), (32, ⟨6, 0⟩, 0), (32, ⟨6, 0⟩, 2), (32, ⟨6, 0⟩, 4), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row19_pairing_45 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 4), (32, ⟨-4, 0⟩, 0), (32, ⟨-4, 0⟩, 2), (32, ⟨-4, 0⟩, 4), (32, ⟨4, 0⟩, 0), (32, ⟨4, 0⟩, 2), (32, ⟨4, 0⟩, 4), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row19_pairing_46 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row19_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 4), (32, ⟨-2, 0⟩, 0), (32, ⟨-2, 0⟩, 2), (32, ⟨-2, 0⟩, 4), (32, ⟨2, 0⟩, 0), (32, ⟨2, 0⟩, 2), (32, ⟨2, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row19_pairing_47 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row19_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row19_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 19 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨19, -1, [(7, 1), (25, 1), (32, 1), (40, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row20_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (8, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5)]

theorem g32p_row20_pairing_0 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 4), (12, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 4), (12, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 4), (12, ⟨1, 2⟩, 5), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 4)]

theorem g32p_row20_pairing_1 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-4, -8⟩, 0), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 3), (2, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (7, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (7, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 3), (2, ⟨2, 4⟩, 4), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (2, ⟨4, 8⟩, 0)]

theorem g32p_row20_pairing_2 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-4, -8⟩, 0), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 3), (2, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (7, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (7, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 3), (2, ⟨2, 4⟩, 4), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (2, ⟨4, 8⟩, 0)]

theorem g32p_row20_pairing_3 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-3, -6⟩, 4), (24, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨-1, -2⟩, 4), (12, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (6, ⟨3, 6⟩, 2)]

theorem g32p_row20_pairing_4 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_4)
      [1, -1, 1] [0, -24, 0, -24, 0, 48] = true := by
  decide +kernel

def g32p_row20_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 0), (2, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 4), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (4, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (10, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (10, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (2, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 0)]

theorem g32p_row20_pairing_5 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 0), (2, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 2), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (4, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (10, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (10, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (2, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 4), (2, ⟨5, 10⟩, 0)]

theorem g32p_row20_pairing_6 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 0), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (6, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (8, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨6, 12⟩, 0)]

theorem g32p_row20_pairing_7 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(12, ⟨-3, -6⟩, 2), (24, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 4), (12, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 5), (12, ⟨3, 6⟩, 4)]

theorem g32p_row20_pairing_8 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 6 g32p_row20_terms_8)
      [1, -1, 1] [-144, -168, -48, 72, 96, 48] = true := by
  decide +kernel

def g32p_row20_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 0), (2, ⟨-5, -10⟩, 4), (4, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 3), (2, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 3), (2, ⟨2, 4⟩, 4), (4, ⟨3, 6⟩, 4), (2, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 0)]

theorem g32p_row20_pairing_9 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 0), (2, ⟨-5, -10⟩, 2), (4, ⟨-3, -6⟩, 4), (6, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 3), (2, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 3), (2, ⟨2, 4⟩, 4), (4, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 4), (2, ⟨10, 20⟩, 0)]

theorem g32p_row20_pairing_10 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 0), (2, ⟨-7, -14⟩, 0), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (4, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨7, 14⟩, 0), (2, ⟨15, 30⟩, 0)]

theorem g32p_row20_pairing_11 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_11)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 0), (2, ⟨-6, -12⟩, 2), (2, ⟨-6, -12⟩, 4), (4, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 3), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (2, ⟨-1, -2⟩, 0), (2, ⟨1, 2⟩, 0), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (4, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 3), (2, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 4), (2, ⟨15, 30⟩, 0)]

theorem g32p_row20_pairing_12 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 4), (12, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 4), (12, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 4), (12, ⟨1, 2⟩, 5), (6, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 4)]

theorem g32p_row20_pairing_13 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 4), (3, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 4), (3, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 4), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 4)]

theorem g32p_row20_pairing_14 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (2, ⟨-7, -14⟩, 2), (2, ⟨-7, -14⟩, 4), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (8, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨7, 14⟩, 2), (2, ⟨7, 14⟩, 4), (2, ⟨20, 40⟩, 0)]

theorem g32p_row20_pairing_15 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 4), (1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 4), (4, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (7, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (7, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 3), (1, ⟨2, 4⟩, 4), (1, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 4), (2, ⟨20, 40⟩, 0)]

theorem g32p_row20_pairing_16 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (1, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 4), (1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 4), (3, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (8, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 4), (1, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨8, 16⟩, 2), (1, ⟨8, 16⟩, 4), (2, ⟨20, 40⟩, 0)]

theorem g32p_row20_pairing_17 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 4), (1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 4), (4, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (7, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (7, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 3), (1, ⟨2, 4⟩, 4), (1, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 4), (2, ⟨20, 40⟩, 0)]

theorem g32p_row20_pairing_18 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (1, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 4), (1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 4), (3, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (8, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 4), (1, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨8, 16⟩, 2), (1, ⟨8, 16⟩, 4), (2, ⟨20, 40⟩, 0)]

theorem g32p_row20_pairing_19 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (2, ⟨-4, -8⟩, 0), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (2, ⟨4, 8⟩, 0), (2, ⟨20, 40⟩, 0)]

theorem g32p_row20_pairing_20 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 0), (2, ⟨-8, -16⟩, 0), (2, ⟨-6, -12⟩, 2), (2, ⟨-6, -12⟩, 4), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (2, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 4), (2, ⟨8, 16⟩, 0), (2, ⟨24, 48⟩, 0)]

theorem g32p_row20_pairing_21 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-9, -18⟩, 4), (24, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 4), (18, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 5), (6, ⟨9, 18⟩, 2)]

theorem g32p_row20_pairing_22 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 6 g32p_row20_terms_22)
      [1, -1, 1] [144, 120, 48, -120, -96, 48] = true := by
  decide +kernel

def g32p_row20_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 0), (2, ⟨-9, -18⟩, 2), (2, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 4), (2, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (2, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 3), (2, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 4), (2, ⟨30, 60⟩, 0)]

theorem g32p_row20_pairing_23 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_23)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 0), (2, ⟨-9, -18⟩, 4), (2, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 2), (2, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 3), (8, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (2, ⟨2, 4⟩, 4), (2, ⟨3, 6⟩, 4), (2, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 4), (2, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 0)]

theorem g32p_row20_pairing_24 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_24)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 0), (2, ⟨-10, -20⟩, 0), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (8, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨10, 20⟩, 0), (2, ⟨30, 60⟩, 0)]

theorem g32p_row20_pairing_25 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 2), (3, ⟨-9, -18⟩, 4), (3, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 4), (12, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 4), (12, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 4), (12, ⟨1, 2⟩, 5), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 4), (3, ⟨9, 18⟩, 2), (3, ⟨9, 18⟩, 4)]

theorem g32p_row20_pairing_26 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-36, -72⟩, 0), (2, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 4), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (8, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 4), (2, ⟨36, 72⟩, 0)]

theorem g32p_row20_pairing_27 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-36, -72⟩, 0), (2, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 4), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (8, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 4), (2, ⟨36, 72⟩, 0)]

theorem g32p_row20_pairing_28 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-6, -12⟩, 4), (6, ⟨-2, -4⟩, 4), (6, ⟨2, 4⟩, 2), (6, ⟨6, 12⟩, 2)]

theorem g32p_row20_pairing_29 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 6 g32p_row20_terms_29)
      [1, -1, 1] [144, 144, 48, -96, -96] = true := by
  decide +kernel

def g32p_row20_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 0), (2, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 2), (2, ⟨-6, -12⟩, 4), (2, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (4, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (2, ⟨6, 12⟩, 2), (2, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 4), (2, ⟨40, 80⟩, 0)]

theorem g32p_row20_pairing_30 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 0), (2, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 4), (2, ⟨-6, -12⟩, 2), (4, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (2, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (2, ⟨6, 12⟩, 4), (2, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 0)]

theorem g32p_row20_pairing_31 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-9, -18⟩, 4), (6, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 4), (6, ⟨3, 6⟩, 4), (6, ⟨9, 18⟩, 2)]

theorem g32p_row20_pairing_32 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 6 g32p_row20_terms_32)
      [1, -1, 1] [144, 168, 48, -72, -96, -48] = true := by
  decide +kernel

def g32p_row20_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 0), (2, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 4), (2, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (4, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (2, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 4), (2, ⟨45, 90⟩, 0)]

theorem g32p_row20_pairing_33 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 0), (2, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 4), (2, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (4, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (2, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 4), (2, ⟨45, 90⟩, 0)]

theorem g32p_row20_pairing_34 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 2), (3, ⟨-9, -18⟩, 4), (12, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 4), (12, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 4), (12, ⟨1, 2⟩, 5), (3, ⟨9, 18⟩, 2), (3, ⟨9, 18⟩, 4)]

theorem g32p_row20_pairing_35 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 0), (1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 4), (1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 4), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 3), (1, ⟨2, 4⟩, 4), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 4), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 4), (2, ⟨60, 120⟩, 0)]

theorem g32p_row20_pairing_36 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 0), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (8, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (2, ⟨60, 120⟩, 0)]

theorem g32p_row20_pairing_37 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 0), (1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 4), (1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 4), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 3), (1, ⟨2, 4⟩, 4), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 4), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 4), (2, ⟨60, 120⟩, 0)]

theorem g32p_row20_pairing_38 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 0), (2, ⟨-6, -12⟩, 2), (2, ⟨-6, -12⟩, 4), (2, ⟨-4, -8⟩, 0), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (2, ⟨4, 8⟩, 0), (2, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 4), (2, ⟨60, 120⟩, 0)]

theorem g32p_row20_pairing_39 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 0), (2, ⟨-8, -16⟩, 2), (2, ⟨-8, -16⟩, 4), (2, ⟨8, 16⟩, 2), (2, ⟨8, 16⟩, 4), (2, ⟨64, 128⟩, 0)]

theorem g32p_row20_pairing_40 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 0), (2, ⟨-8, -16⟩, 2), (2, ⟨-8, -16⟩, 4), (2, ⟨8, 16⟩, 2), (2, ⟨8, 16⟩, 4), (2, ⟨64, 128⟩, 0)]

theorem g32p_row20_pairing_41 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-80, -160⟩, 0), (2, ⟨-8, -16⟩, 2), (2, ⟨-8, -16⟩, 4), (2, ⟨8, 16⟩, 2), (2, ⟨8, 16⟩, 4), (2, ⟨80, 160⟩, 0)]

theorem g32p_row20_pairing_42 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 0), (2, ⟨-9, -18⟩, 0), (4, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 3), (4, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 3), (2, ⟨9, 18⟩, 0), (2, ⟨81, 162⟩, 0)]

theorem g32p_row20_pairing_43 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_43)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-20, 0⟩, 0), (3, ⟨-7, 0⟩, 2), (3, ⟨-7, 0⟩, 4), (3, ⟨-3, 0⟩, 2), (3, ⟨-3, 0⟩, 4), (6, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 3), (12, ⟨-1, 0⟩, 1), (6, ⟨-1, 0⟩, 2), (6, ⟨-1, 0⟩, 4), (12, ⟨-1, 0⟩, 5), (12, ⟨1, 0⟩, 1), (6, ⟨1, 0⟩, 2), (6, ⟨1, 0⟩, 4), (12, ⟨1, 0⟩, 5), (6, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 3), (3, ⟨3, 0⟩, 2), (3, ⟨3, 0⟩, 4), (3, ⟨7, 0⟩, 2), (3, ⟨7, 0⟩, 4), (3, ⟨20, 0⟩, 0)]

theorem g32p_row20_pairing_44 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-60, 0⟩, 0), (6, ⟨-3, 0⟩, 2), (6, ⟨-3, 0⟩, 4), (6, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 3), (12, ⟨-1, 0⟩, 1), (6, ⟨-1, 0⟩, 2), (6, ⟨-1, 0⟩, 4), (12, ⟨-1, 0⟩, 5), (12, ⟨1, 0⟩, 1), (6, ⟨1, 0⟩, 2), (6, ⟨1, 0⟩, 4), (12, ⟨1, 0⟩, 5), (6, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 3), (6, ⟨3, 0⟩, 2), (6, ⟨3, 0⟩, 4), (3, ⟨60, 0⟩, 0)]

theorem g32p_row20_pairing_45 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-64, 0⟩, 0), (3, ⟨-8, 0⟩, 2), (3, ⟨-8, 0⟩, 4), (3, ⟨8, 0⟩, 2), (3, ⟨8, 0⟩, 4), (3, ⟨64, 0⟩, 0)]

theorem g32p_row20_pairing_46 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row20_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-80, 0⟩, 0), (3, ⟨-8, 0⟩, 2), (3, ⟨-8, 0⟩, 4), (3, ⟨8, 0⟩, 2), (3, ⟨8, 0⟩, 4), (3, ⟨80, 0⟩, 0)]

theorem g32p_row20_pairing_47 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row20_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row20_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 20 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨20, 1, [(9, 1), (23, -1), (30, -1), (33, -1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row21_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(108, ⟨-1, -2⟩, 0), (108, ⟨-1, -2⟩, 1), (108, ⟨-1, -2⟩, 2), (108, ⟨1, 2⟩, 0), (108, ⟨1, 2⟩, 1), (108, ⟨1, 2⟩, 2)]

theorem g32p_row21_pairing_0 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (72, ⟨-1, -2⟩, 0), (72, ⟨-1, -2⟩, 1), (72, ⟨-1, -2⟩, 2), (72, ⟨1, 2⟩, 0), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row21_pairing_1 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (30, ⟨-2, -4⟩, 0), (22, ⟨-2, -4⟩, 1), (22, ⟨-2, -4⟩, 2), (78, ⟨-1, -2⟩, 0), (85, ⟨-1, -2⟩, 1), (85, ⟨-1, -2⟩, 2), (78, ⟨1, 2⟩, 0), (85, ⟨1, 2⟩, 1), (85, ⟨1, 2⟩, 2), (30, ⟨2, 4⟩, 0), (22, ⟨2, 4⟩, 1), (22, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row21_pairing_2 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (34, ⟨-2, -4⟩, 1), (34, ⟨-2, -4⟩, 2), (66, ⟨-1, -2⟩, 0), (91, ⟨-1, -2⟩, 1), (91, ⟨-1, -2⟩, 2), (66, ⟨1, 2⟩, 0), (91, ⟨1, 2⟩, 1), (91, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (34, ⟨2, 4⟩, 1), (34, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row21_pairing_3 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (72, ⟨-1, -2⟩, 0), (72, ⟨-1, -2⟩, 1), (72, ⟨-1, -2⟩, 2), (72, ⟨1, 2⟩, 0), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row21_pairing_4 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (2, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (86, ⟨-2, -4⟩, 1), (30, ⟨-2, -4⟩, 2), (66, ⟨-1, -2⟩, 0), (42, ⟨-1, -2⟩, 1), (92, ⟨-1, -2⟩, 2), (66, ⟨1, 2⟩, 0), (92, ⟨1, 2⟩, 1), (42, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (30, ⟨2, 4⟩, 1), (86, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (2, ⟨5, 10⟩, 2)]

theorem g32p_row21_pairing_5 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (2, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 2), (30, ⟨-2, -4⟩, 0), (50, ⟨-2, -4⟩, 1), (42, ⟨-2, -4⟩, 2), (78, ⟨-1, -2⟩, 0), (66, ⟨-1, -2⟩, 1), (56, ⟨-1, -2⟩, 2), (78, ⟨1, 2⟩, 0), (56, ⟨1, 2⟩, 1), (66, ⟨1, 2⟩, 2), (30, ⟨2, 4⟩, 0), (42, ⟨2, 4⟩, 1), (50, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 2)]

theorem g32p_row21_pairing_6 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (12, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (12, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row21_pairing_7 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(44, ⟨-3, -6⟩, 0), (44, ⟨-3, -6⟩, 1), (44, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (44, ⟨3, 6⟩, 0), (44, ⟨3, 6⟩, 1), (44, ⟨3, 6⟩, 2)]

theorem g32p_row21_pairing_8 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (6, ⟨-5, -10⟩, 1), (2, ⟨-5, -10⟩, 2), (20, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 1), (24, ⟨-2, -4⟩, 0), (36, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 0), (174, ⟨-1, -2⟩, 1), (30, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (30, ⟨1, 2⟩, 1), (174, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (20, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 1), (6, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 2)]

theorem g32p_row21_pairing_9 :
    g32p_cyclotomicPairingCheck 972 (1)
      (g32p_pairingCoefficients 3 g32p_row21_terms_9)
      [1, 1, 1] [-972, 648] = true := by
  decide +kernel

def g32p_row21_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (6, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 2), (20, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 2), (42, ⟨-2, -4⟩, 1), (20, ⟨-2, -4⟩, 2), (102, ⟨-1, -2⟩, 0), (84, ⟨-1, -2⟩, 1), (66, ⟨-1, -2⟩, 2), (102, ⟨1, 2⟩, 0), (66, ⟨1, 2⟩, 1), (84, ⟨1, 2⟩, 2), (20, ⟨2, 4⟩, 1), (42, ⟨2, 4⟩, 2), (20, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (6, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 1), (2, ⟨10, 20⟩, 2)]

theorem g32p_row21_pairing_10 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (18, ⟨-7, -14⟩, 1), (12, ⟨-3, -6⟩, 0), (54, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 2), (12, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (54, ⟨3, 6⟩, 2), (18, ⟨7, 14⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row21_pairing_11 :
    g32p_cyclotomicPairingCheck 972 (1)
      (g32p_pairingCoefficients 3 g32p_row21_terms_11)
      [1, 1, 1] [-972, 648] = true := by
  decide +kernel

def g32p_row21_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (6, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (6, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 2), (36, ⟨-2, -4⟩, 0), (36, ⟨-2, -4⟩, 1), (36, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (36, ⟨2, 4⟩, 0), (36, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (6, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row21_pairing_12 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(44, ⟨-3, -6⟩, 0), (44, ⟨-3, -6⟩, 1), (44, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (44, ⟨3, 6⟩, 0), (44, ⟨3, 6⟩, 1), (44, ⟨3, 6⟩, 2)]

theorem g32p_row21_pairing_13 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (54, ⟨-2, -4⟩, 0), (54, ⟨-2, -4⟩, 1), (54, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (54, ⟨2, 4⟩, 0), (54, ⟨2, 4⟩, 1), (54, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2)]

theorem g32p_row21_pairing_14 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (6, ⟨-7, -14⟩, 0), (5, ⟨-7, -14⟩, 1), (5, ⟨-7, -14⟩, 2), (18, ⟨-3, -6⟩, 0), (27, ⟨-3, -6⟩, 1), (27, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 0), (30, ⟨-2, -4⟩, 1), (30, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 0), (30, ⟨2, 4⟩, 1), (30, ⟨2, 4⟩, 2), (18, ⟨3, 6⟩, 0), (27, ⟨3, 6⟩, 1), (27, ⟨3, 6⟩, 2), (6, ⟨7, 14⟩, 0), (5, ⟨7, 14⟩, 1), (5, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row21_pairing_15 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (6, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (6, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (42, ⟨-1, -2⟩, 0), (103, ⟨-1, -2⟩, 1), (103, ⟨-1, -2⟩, 2), (42, ⟨1, 2⟩, 0), (103, ⟨1, 2⟩, 1), (103, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (6, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (6, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row21_pairing_16 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (6, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (38, ⟨-3, -6⟩, 0), (21, ⟨-3, -6⟩, 1), (21, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 0), (30, ⟨-2, -4⟩, 1), (30, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 0), (30, ⟨2, 4⟩, 1), (30, ⟨2, 4⟩, 2), (38, ⟨3, 6⟩, 0), (21, ⟨3, 6⟩, 1), (21, ⟨3, 6⟩, 2), (6, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row21_pairing_17 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (6, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (84, ⟨-1, -2⟩, 0), (82, ⟨-1, -2⟩, 1), (82, ⟨-1, -2⟩, 2), (84, ⟨1, 2⟩, 0), (82, ⟨1, 2⟩, 1), (82, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (6, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row21_pairing_18 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (6, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (20, ⟨-3, -6⟩, 0), (30, ⟨-3, -6⟩, 1), (30, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 0), (30, ⟨-2, -4⟩, 1), (30, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 0), (30, ⟨2, 4⟩, 1), (30, ⟨2, 4⟩, 2), (20, ⟨3, 6⟩, 0), (30, ⟨3, 6⟩, 1), (30, ⟨3, 6⟩, 2), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (6, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row21_pairing_19 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 1), (6, ⟨-5, -10⟩, 0), (6, ⟨-5, -10⟩, 2), (18, ⟨-4, -8⟩, 1), (24, ⟨-2, -4⟩, 0), (22, ⟨-2, -4⟩, 1), (42, ⟨-2, -4⟩, 2), (78, ⟨-1, -2⟩, 0), (42, ⟨-1, -2⟩, 1), (84, ⟨-1, -2⟩, 2), (78, ⟨1, 2⟩, 0), (84, ⟨1, 2⟩, 1), (42, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (42, ⟨2, 4⟩, 1), (22, ⟨2, 4⟩, 2), (18, ⟨4, 8⟩, 2), (6, ⟨5, 10⟩, 0), (6, ⟨5, 10⟩, 1), (2, ⟨20, 40⟩, 2)]

theorem g32p_row21_pairing_20 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_20)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 1), (18, ⟨-8, -16⟩, 1), (6, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (6, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (48, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (36, ⟨-2, -4⟩, 0), (36, ⟨-2, -4⟩, 1), (36, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 2), (36, ⟨2, 4⟩, 0), (36, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (6, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (48, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (18, ⟨8, 16⟩, 2), (2, ⟨24, 48⟩, 2)]

theorem g32p_row21_pairing_21 :
    g32p_cyclotomicPairingCheck 972 (1)
      (g32p_pairingCoefficients 3 g32p_row21_terms_21)
      [1, 1, 1] [-972, 648] = true := by
  decide +kernel

def g32p_row21_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row21_pairing_22 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_22)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (24, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (12, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (36, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (54, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (54, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (12, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 1), (24, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (6, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row21_pairing_23 :
    g32p_cyclotomicPairingCheck 972 (1)
      (g32p_pairingCoefficients 3 g32p_row21_terms_23)
      [1, 1, 1] [-972, 648] = true := by
  decide +kernel

def g32p_row21_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 2), (6, ⟨-6, -12⟩, 0), (18, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 0), (36, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (54, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (54, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (36, ⟨2, 4⟩, 1), (6, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (18, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (6, ⟨9, 18⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row21_pairing_24 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (18, ⟨-10, -20⟩, 2), (18, ⟨-3, -6⟩, 0), (52, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 2), (54, ⟨-1, -2⟩, 0), (54, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (54, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (54, ⟨1, 2⟩, 2), (18, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (52, ⟨3, 6⟩, 2), (18, ⟨10, 20⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row21_pairing_25 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (36, ⟨-3, -6⟩, 0), (36, ⟨-3, -6⟩, 1), (36, ⟨-3, -6⟩, 2), (36, ⟨3, 6⟩, 0), (36, ⟨3, 6⟩, 1), (36, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row21_pairing_26 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (36, ⟨-3, -6⟩, 0), (18, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 2), (36, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (18, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row21_pairing_27 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (2, ⟨-9, -18⟩, 0), (7, ⟨-9, -18⟩, 1), (7, ⟨-9, -18⟩, 2), (18, ⟨-3, -6⟩, 0), (27, ⟨-3, -6⟩, 1), (27, ⟨-3, -6⟩, 2), (18, ⟨3, 6⟩, 0), (27, ⟨3, 6⟩, 1), (27, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 0), (7, ⟨9, 18⟩, 1), (7, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row21_pairing_28 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (54, ⟨-2, -4⟩, 0), (54, ⟨-2, -4⟩, 1), (54, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (54, ⟨2, 4⟩, 0), (54, ⟨2, 4⟩, 1), (54, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2)]

theorem g32p_row21_pairing_29 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (6, ⟨-8, -16⟩, 0), (20, ⟨-8, -16⟩, 2), (2, ⟨-6, -12⟩, 0), (6, ⟨-6, -12⟩, 2), (42, ⟨-2, -4⟩, 0), (48, ⟨-2, -4⟩, 1), (38, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (120, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (120, ⟨1, 2⟩, 2), (42, ⟨2, 4⟩, 0), (38, ⟨2, 4⟩, 1), (48, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 1), (6, ⟨8, 16⟩, 0), (20, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 2)]

theorem g32p_row21_pairing_30 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (6, ⟨-8, -16⟩, 1), (20, ⟨-8, -16⟩, 2), (2, ⟨-6, -12⟩, 0), (6, ⟨-6, -12⟩, 1), (48, ⟨-2, -4⟩, 0), (42, ⟨-2, -4⟩, 1), (38, ⟨-2, -4⟩, 2), (60, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (60, ⟨-1, -2⟩, 2), (60, ⟨1, 2⟩, 0), (60, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (48, ⟨2, 4⟩, 0), (38, ⟨2, 4⟩, 1), (42, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 2), (20, ⟨8, 16⟩, 1), (6, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 2)]

theorem g32p_row21_pairing_31 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (36, ⟨-3, -6⟩, 0), (36, ⟨-3, -6⟩, 1), (36, ⟨-3, -6⟩, 2), (36, ⟨3, 6⟩, 0), (36, ⟨3, 6⟩, 1), (36, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row21_pairing_32 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (36, ⟨-3, -6⟩, 0), (54, ⟨-3, -6⟩, 2), (36, ⟨3, 6⟩, 0), (54, ⟨3, 6⟩, 1), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row21_pairing_33 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (2, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (12, ⟨-9, -18⟩, 2), (18, ⟨-3, -6⟩, 0), (36, ⟨-3, -6⟩, 1), (36, ⟨-3, -6⟩, 2), (18, ⟨3, 6⟩, 0), (36, ⟨3, 6⟩, 1), (36, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 0), (12, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row21_pairing_34 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row21_pairing_35 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (12, ⟨-3, -6⟩, 0), (28, ⟨-3, -6⟩, 1), (28, ⟨-3, -6⟩, 2), (27, ⟨-2, -4⟩, 1), (27, ⟨-2, -4⟩, 2), (54, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (54, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (27, ⟨2, 4⟩, 1), (27, ⟨2, 4⟩, 2), (12, ⟨3, 6⟩, 0), (28, ⟨3, 6⟩, 1), (28, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row21_pairing_36 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (6, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (24, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 1), (32, ⟨-3, -6⟩, 2), (24, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 1), (32, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row21_pairing_37 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (6, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (31, ⟨-3, -6⟩, 1), (31, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (6, ⟨3, 6⟩, 0), (31, ⟨3, 6⟩, 1), (31, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row21_pairing_38 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 1), (6, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (6, ⟨-6, -12⟩, 2), (18, ⟨-4, -8⟩, 2), (12, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (48, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 0), (36, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (12, ⟨3, 6⟩, 0), (48, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (18, ⟨4, 8⟩, 1), (6, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨60, 120⟩, 2)]

theorem g32p_row21_pairing_39 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_39)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 1), (6, ⟨-8, -16⟩, 0), (6, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (6, ⟨-4, -8⟩, 0), (6, ⟨-4, -8⟩, 2), (6, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (48, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (6, ⟨2, 4⟩, 0), (48, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (6, ⟨4, 8⟩, 0), (6, ⟨4, 8⟩, 1), (6, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 1), (6, ⟨8, 16⟩, 2), (2, ⟨64, 128⟩, 2)]

theorem g32p_row21_pairing_40 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_40)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (6, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (6, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (6, ⟨-2, -4⟩, 0), (27, ⟨-2, -4⟩, 1), (27, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (27, ⟨2, 4⟩, 1), (27, ⟨2, 4⟩, 2), (6, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (6, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 2)]

theorem g32p_row21_pairing_41 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (6, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (6, ⟨-4, -8⟩, 0), (27, ⟨-4, -8⟩, 1), (27, ⟨-4, -8⟩, 2), (6, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (6, ⟨4, 8⟩, 0), (27, ⟨4, 8⟩, 1), (27, ⟨4, 8⟩, 2), (6, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 1), (1, ⟨80, 160⟩, 2)]

theorem g32p_row21_pairing_42 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 1), (18, ⟨-9, -18⟩, 1), (18, ⟨9, 18⟩, 2), (2, ⟨81, 162⟩, 2)]

theorem g32p_row21_pairing_43 :
    g32p_cyclotomicPairingCheck 972 (1)
      (g32p_pairingCoefficients 3 g32p_row21_terms_43)
      [1, 1, 1] [-972, 648] = true := by
  decide +kernel

def g32p_row21_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 2), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 1), (8, ⟨-7, 0⟩, 2), (36, ⟨-3, 0⟩, 0), (36, ⟨-3, 0⟩, 1), (36, ⟨-3, 0⟩, 2), (36, ⟨-2, 0⟩, 0), (36, ⟨-2, 0⟩, 1), (36, ⟨-2, 0⟩, 2), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 2), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 2), (36, ⟨2, 0⟩, 0), (36, ⟨2, 0⟩, 1), (36, ⟨2, 0⟩, 2), (36, ⟨3, 0⟩, 0), (36, ⟨3, 0⟩, 1), (36, ⟨3, 0⟩, 2), (8, ⟨7, 0⟩, 0), (8, ⟨7, 0⟩, 1), (8, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 1), (1, ⟨20, 0⟩, 2)]

theorem g32p_row21_pairing_44 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 2), (6, ⟨-6, 0⟩, 0), (6, ⟨-6, 0⟩, 1), (6, ⟨-6, 0⟩, 2), (44, ⟨-3, 0⟩, 0), (44, ⟨-3, 0⟩, 1), (44, ⟨-3, 0⟩, 2), (44, ⟨3, 0⟩, 0), (44, ⟨3, 0⟩, 1), (44, ⟨3, 0⟩, 2), (6, ⟨6, 0⟩, 0), (6, ⟨6, 0⟩, 1), (6, ⟨6, 0⟩, 2), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 1), (1, ⟨60, 0⟩, 2)]

theorem g32p_row21_pairing_45 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 2), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 2), (6, ⟨-4, 0⟩, 0), (6, ⟨-4, 0⟩, 1), (6, ⟨-4, 0⟩, 2), (30, ⟨-2, 0⟩, 0), (30, ⟨-2, 0⟩, 1), (30, ⟨-2, 0⟩, 2), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 2), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 2), (30, ⟨2, 0⟩, 0), (30, ⟨2, 0⟩, 1), (30, ⟨2, 0⟩, 2), (6, ⟨4, 0⟩, 0), (6, ⟨4, 0⟩, 1), (6, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 1), (1, ⟨64, 0⟩, 2)]

theorem g32p_row21_pairing_46 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row21_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 2), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 2), (30, ⟨-4, 0⟩, 0), (30, ⟨-4, 0⟩, 1), (30, ⟨-4, 0⟩, 2), (6, ⟨-2, 0⟩, 0), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 2), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 2), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 2), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 1), (6, ⟨2, 0⟩, 2), (30, ⟨4, 0⟩, 0), (30, ⟨4, 0⟩, 1), (30, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 1), (1, ⟨80, 0⟩, 2)]

theorem g32p_row21_pairing_47 :
    g32p_cyclotomicPairingCheck 972 (0)
      (g32p_pairingCoefficients 3 g32p_row21_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row21_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 21 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨21, 1, [(10, 1), (12, 1), (22, 1), (24, 1), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row22_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(96, ⟨-1, -2⟩, 2), (96, ⟨-1, -2⟩, 5), (96, ⟨1, 2⟩, 1), (96, ⟨1, 2⟩, 4)]

theorem g32p_row22_pairing_0 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_0)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row22_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row22_pairing_1 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row22_pairing_2 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row22_pairing_3 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 4), (16, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 2), (16, ⟨2, 4⟩, 4)]

theorem g32p_row22_pairing_4 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (10, ⟨-3, -6⟩, 4), (16, ⟨-2, -4⟩, 0), (48, ⟨-1, -2⟩, 1), (52, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 4), (48, ⟨-1, -2⟩, 5), (48, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (52, ⟨1, 2⟩, 4), (48, ⟨1, 2⟩, 5), (16, ⟨2, 4⟩, 0), (10, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 4)]

theorem g32p_row22_pairing_5 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (10, ⟨-3, -6⟩, 4), (16, ⟨-2, -4⟩, 0), (48, ⟨-1, -2⟩, 1), (52, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 4), (48, ⟨-1, -2⟩, 5), (48, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (52, ⟨1, 2⟩, 4), (48, ⟨1, 2⟩, 5), (16, ⟨2, 4⟩, 0), (10, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 4)]

theorem g32p_row22_pairing_6 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 2), (16, ⟨-3, -6⟩, 2), (20, ⟨-2, -4⟩, 2), (10, ⟨-2, -4⟩, 4), (48, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (16, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 4), (48, ⟨2, 4⟩, 1), (10, ⟨2, 4⟩, 2), (20, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 4), (2, ⟨6, 12⟩, 4)]

theorem g32p_row22_pairing_7 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_7)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row22_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row22_pairing_8 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (24, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (20, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 4), (32, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 4), (24, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 2), (10, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row22_pairing_9 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (24, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (20, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 4), (32, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 4), (24, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 2), (10, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row22_pairing_10 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (10, ⟨-7, -14⟩, 2), (20, ⟨-3, -6⟩, 2), (24, ⟨-3, -6⟩, 5), (32, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 5), (48, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 5), (32, ⟨2, 4⟩, 2), (24, ⟨3, 6⟩, 1), (20, ⟨3, 6⟩, 4), (10, ⟨7, 14⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row22_pairing_11 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_11)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row22_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (16, ⟨-3, -6⟩, 2), (24, ⟨-3, -6⟩, 5), (72, ⟨-1, -2⟩, 1), (78, ⟨-1, -2⟩, 4), (78, ⟨1, 2⟩, 2), (72, ⟨1, 2⟩, 5), (24, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row22_pairing_12 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row22_pairing_13 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row22_pairing_14 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (12, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row22_pairing_15 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-4, -8⟩, 2), (8, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (8, ⟨4, 8⟩, 2), (8, ⟨4, 8⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row22_pairing_16 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (12, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row22_pairing_17 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-4, -8⟩, 2), (8, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (8, ⟨4, 8⟩, 2), (8, ⟨4, 8⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row22_pairing_18 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (12, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row22_pairing_19 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 2), (16, ⟨-5, -10⟩, 2), (30, ⟨-4, -8⟩, 2), (24, ⟨-4, -8⟩, 5), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 4), (24, ⟨4, 8⟩, 1), (30, ⟨4, 8⟩, 4), (16, ⟨5, 10⟩, 4), (2, ⟨20, 40⟩, 4)]

theorem g32p_row22_pairing_20 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row22_terms_20)
      [1, -1, 1] [-576, -480, -192, 480, 384, -192] = true := by
  decide +kernel

def g32p_row22_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 2), (10, ⟨-8, -16⟩, 2), (32, ⟨-2, -4⟩, 2), (32, ⟨2, 4⟩, 4), (10, ⟨8, 16⟩, 4), (2, ⟨24, 48⟩, 4)]

theorem g32p_row22_pairing_21 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row22_terms_21)
      [1, -1, 1] [-576, -576, -192, 384, 384] = true := by
  decide +kernel

def g32p_row22_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 4), (16, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 2), (16, ⟨2, 4⟩, 4)]

theorem g32p_row22_pairing_22 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (10, ⟨-6, -12⟩, 2), (16, ⟨-3, -6⟩, 4), (16, ⟨-2, -4⟩, 0), (20, ⟨-2, -4⟩, 2), (48, ⟨-2, -4⟩, 5), (16, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 4), (32, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (16, ⟨2, 4⟩, 0), (48, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 2), (10, ⟨6, 12⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row22_pairing_23 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_23)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row22_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (10, ⟨-6, -12⟩, 2), (16, ⟨-3, -6⟩, 4), (16, ⟨-2, -4⟩, 0), (20, ⟨-2, -4⟩, 2), (48, ⟨-2, -4⟩, 5), (16, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 4), (32, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (16, ⟨2, 4⟩, 0), (48, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 2), (10, ⟨6, 12⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row22_pairing_24 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_24)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row22_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (10, ⟨-10, -20⟩, 4), (16, ⟨-3, -6⟩, 2), (24, ⟨-2, -4⟩, 1), (20, ⟨-2, -4⟩, 2), (24, ⟨-2, -4⟩, 5), (48, ⟨-1, -2⟩, 4), (48, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (16, ⟨3, 6⟩, 4), (10, ⟨10, 20⟩, 2), (2, ⟨30, 60⟩, 4)]

theorem g32p_row22_pairing_25 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row22_pairing_26 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row22_pairing_27 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row22_pairing_28 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 4), (16, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 2), (16, ⟨2, 4⟩, 4)]

theorem g32p_row22_pairing_29 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (10, ⟨-8, -16⟩, 4), (16, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 4), (16, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 2), (16, ⟨2, 4⟩, 4), (10, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 4)]

theorem g32p_row22_pairing_30 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (10, ⟨-8, -16⟩, 4), (16, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 4), (16, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 2), (16, ⟨2, 4⟩, 4), (10, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 4)]

theorem g32p_row22_pairing_31 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row22_pairing_32 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (24, ⟨-3, -6⟩, 1), (30, ⟨-3, -6⟩, 4), (72, ⟨-1, -2⟩, 5), (72, ⟨1, 2⟩, 1), (30, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row22_pairing_33 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (24, ⟨-3, -6⟩, 1), (30, ⟨-3, -6⟩, 4), (72, ⟨-1, -2⟩, 5), (72, ⟨1, 2⟩, 1), (30, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row22_pairing_34 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row22_pairing_35 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row22_pairing_36 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (8, ⟨6, 12⟩, 2), (8, ⟨6, 12⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row22_pairing_37 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row22_pairing_38 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 2), (20, ⟨-4, -8⟩, 2), (10, ⟨-4, -8⟩, 4), (24, ⟨-4, -8⟩, 5), (16, ⟨-3, -6⟩, 4), (16, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 4), (32, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (16, ⟨3, 6⟩, 2), (24, ⟨4, 8⟩, 1), (10, ⟨4, 8⟩, 2), (20, ⟨4, 8⟩, 4), (2, ⟨60, 120⟩, 4)]

theorem g32p_row22_pairing_39 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_39)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row22_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 2), (16, ⟨-4, -8⟩, 2), (16, ⟨4, 8⟩, 4), (2, ⟨64, 128⟩, 4)]

theorem g32p_row22_pairing_40 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row22_terms_40)
      [1, -1, 1] [-576, -576, -192, 384, 384] = true := by
  decide +kernel

def g32p_row22_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (8, ⟨-4, -8⟩, 2), (8, ⟨-4, -8⟩, 4), (8, ⟨4, 8⟩, 2), (8, ⟨4, 8⟩, 4), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 4)]

theorem g32p_row22_pairing_41 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (1, ⟨80, 160⟩, 2), (1, ⟨80, 160⟩, 4)]

theorem g32p_row22_pairing_42 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 2), (10, ⟨-9, -18⟩, 2), (48, ⟨-3, -6⟩, 1), (20, ⟨-3, -6⟩, 4), (48, ⟨-1, -2⟩, 1), (48, ⟨1, 2⟩, 5), (20, ⟨3, 6⟩, 2), (48, ⟨3, 6⟩, 5), (10, ⟨9, 18⟩, 4), (2, ⟨81, 162⟩, 4)]

theorem g32p_row22_pairing_43 :
    g32p_cyclotomicPairingCheck 576 (2)
      (g32p_pairingCoefficients 6 g32p_row22_terms_43)
      [1, -1, 1] [-1152, -1344, -384, 576, 768, 384] = true := by
  decide +kernel

def g32p_row22_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 4), (8, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (12, ⟨-2, 0⟩, 3), (8, ⟨-2, 0⟩, 4), (12, ⟨-2, 0⟩, 5), (8, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (12, ⟨2, 0⟩, 3), (8, ⟨2, 0⟩, 4), (12, ⟨2, 0⟩, 5), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row22_pairing_44 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 4), (8, ⟨-6, 0⟩, 0), (8, ⟨-6, 0⟩, 2), (8, ⟨-6, 0⟩, 4), (12, ⟨-2, 0⟩, 1), (12, ⟨-2, 0⟩, 3), (12, ⟨-2, 0⟩, 5), (12, ⟨2, 0⟩, 1), (12, ⟨2, 0⟩, 3), (12, ⟨2, 0⟩, 5), (8, ⟨6, 0⟩, 0), (8, ⟨6, 0⟩, 2), (8, ⟨6, 0⟩, 4), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row22_pairing_45 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 4), (8, ⟨-4, 0⟩, 0), (8, ⟨-4, 0⟩, 2), (8, ⟨-4, 0⟩, 4), (8, ⟨4, 0⟩, 0), (8, ⟨4, 0⟩, 2), (8, ⟨4, 0⟩, 4), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row22_pairing_46 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row22_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 4), (8, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 2), (8, ⟨-2, 0⟩, 4), (8, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 2), (8, ⟨2, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row22_pairing_47 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row22_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row22_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 22 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨22, -1, [(21, 1), (22, 1), (41, 1), (44, 2)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row23_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2)]

theorem g32p_row23_pairing_0 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (6, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2)]

theorem g32p_row23_pairing_1 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-4, -8⟩, 0), (2, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (5, ⟨-2, -4⟩, 1), (5, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 1), (5, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (2, ⟨4, 8⟩, 0)]

theorem g32p_row23_pairing_2 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-4, -8⟩, 0), (2, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (5, ⟨-2, -4⟩, 1), (5, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 1), (5, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (2, ⟨4, 8⟩, 0)]

theorem g32p_row23_pairing_3 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 2), (6, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1)]

theorem g32p_row23_pairing_4 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 0), (4, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨5, 10⟩, 0)]

theorem g32p_row23_pairing_5 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 0), (4, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 0)]

theorem g32p_row23_pairing_6 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 0), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (2, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0)]

theorem g32p_row23_pairing_7 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(12, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (12, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 2)]

theorem g32p_row23_pairing_8 :
    g32p_cyclotomicPairingCheck 108 (1)
      (g32p_pairingCoefficients 3 g32p_row23_terms_8)
      [1, 1, 1] [-108, 72] = true := by
  decide +kernel

def g32p_row23_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 0), (2, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 2), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (6, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (10, ⟨-1, -2⟩, 2), (2, ⟨1, 2⟩, 0), (10, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 1), (2, ⟨10, 20⟩, 0)]

theorem g32p_row23_pairing_9 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 0), (2, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 1), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨-1, -2⟩, 0), (10, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (2, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (10, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (2, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 0)]

theorem g32p_row23_pairing_10 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 0), (2, ⟨-7, -14⟩, 0), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (2, ⟨7, 14⟩, 0), (2, ⟨15, 30⟩, 0)]

theorem g32p_row23_pairing_11 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_11)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 0), (4, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (2, ⟨-1, -2⟩, 0), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 2), (2, ⟨1, 2⟩, 0), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 2), (2, ⟨15, 30⟩, 0)]

theorem g32p_row23_pairing_12 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(12, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (12, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2)]

theorem g32p_row23_pairing_13 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (6, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (6, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2)]

theorem g32p_row23_pairing_14 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (4, ⟨-7, -14⟩, 0), (2, ⟨-7, -14⟩, 1), (2, ⟨-7, -14⟩, 2), (4, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (4, ⟨7, 14⟩, 0), (2, ⟨7, 14⟩, 1), (2, ⟨7, 14⟩, 2), (2, ⟨20, 40⟩, 0)]

theorem g32p_row23_pairing_15 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (2, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (2, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (2, ⟨-4, -8⟩, 1), (2, ⟨-4, -8⟩, 2), (2, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨4, 8⟩, 1), (2, ⟨4, 8⟩, 2), (2, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (2, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (2, ⟨20, 40⟩, 0)]

theorem g32p_row23_pairing_16 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (2, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (2, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (6, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (6, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (2, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (2, ⟨20, 40⟩, 0)]

theorem g32p_row23_pairing_17 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (2, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (2, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (2, ⟨-4, -8⟩, 1), (2, ⟨-4, -8⟩, 2), (2, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨4, 8⟩, 1), (2, ⟨4, 8⟩, 2), (2, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (2, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (2, ⟨20, 40⟩, 0)]

theorem g32p_row23_pairing_18 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (2, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (2, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (6, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (6, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (2, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (2, ⟨20, 40⟩, 0)]

theorem g32p_row23_pairing_19 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 0), (2, ⟨-5, -10⟩, 1), (2, ⟨-5, -10⟩, 2), (2, ⟨-4, -8⟩, 0), (8, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (2, ⟨4, 8⟩, 0), (2, ⟨5, 10⟩, 1), (2, ⟨5, 10⟩, 2), (2, ⟨20, 40⟩, 0)]

theorem g32p_row23_pairing_20 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_20)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 0), (2, ⟨-8, -16⟩, 0), (4, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 2), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 2), (2, ⟨8, 16⟩, 0), (2, ⟨24, 48⟩, 0)]

theorem g32p_row23_pairing_21 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_21)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 2), (6, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨2, 4⟩, 1), (6, ⟨9, 18⟩, 0), (6, ⟨9, 18⟩, 1)]

theorem g32p_row23_pairing_22 :
    g32p_cyclotomicPairingCheck 108 (-2)
      (g32p_pairingCoefficients 3 g32p_row23_terms_22)
      [1, 1, 1] [216, -144] = true := by
  decide +kernel

def g32p_row23_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 0), (2, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (4, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 2), (2, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (2, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (2, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 0)]

theorem g32p_row23_pairing_23 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_23)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 0), (2, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 2), (4, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 1), (2, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (2, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 1), (2, ⟨30, 60⟩, 0)]

theorem g32p_row23_pairing_24 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 0), (2, ⟨-10, -20⟩, 0), (4, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (4, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (4, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (2, ⟨10, 20⟩, 0), (2, ⟨30, 60⟩, 0)]

theorem g32p_row23_pairing_25 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (6, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (6, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (6, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2)]

theorem g32p_row23_pairing_26 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-36, -72⟩, 0), (4, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (2, ⟨-9, -18⟩, 2), (4, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (4, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (4, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨36, 72⟩, 0)]

theorem g32p_row23_pairing_27 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-36, -72⟩, 0), (4, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (2, ⟨-9, -18⟩, 2), (4, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (4, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (4, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨36, 72⟩, 0)]

theorem g32p_row23_pairing_28 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-6, -12⟩, 0), (6, ⟨-6, -12⟩, 2), (6, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (6, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 1)]

theorem g32p_row23_pairing_29 :
    g32p_cyclotomicPairingCheck 108 (-1)
      (g32p_pairingCoefficients 3 g32p_row23_terms_29)
      [1, 1, 1] [108, -72] = true := by
  decide +kernel

def g32p_row23_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 0), (4, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (2, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 2), (6, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (4, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 0)]

theorem g32p_row23_pairing_30 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 0), (4, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 2), (2, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 1), (6, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 2), (4, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 0)]

theorem g32p_row23_pairing_31 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 2), (6, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 2), (6, ⟨9, 18⟩, 0), (6, ⟨9, 18⟩, 1)]

theorem g32p_row23_pairing_32 :
    g32p_cyclotomicPairingCheck 108 (-1)
      (g32p_pairingCoefficients 3 g32p_row23_terms_32)
      [1, 1, 1] [108, -72] = true := by
  decide +kernel

def g32p_row23_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 0), (4, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (2, ⟨-9, -18⟩, 2), (6, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (6, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (4, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 0)]

theorem g32p_row23_pairing_33 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 0), (4, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (2, ⟨-9, -18⟩, 2), (6, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (6, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (4, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 0)]

theorem g32p_row23_pairing_34 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (6, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2)]

theorem g32p_row23_pairing_35 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 0), (2, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (2, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (2, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (2, ⟨60, 120⟩, 0)]

theorem g32p_row23_pairing_36 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 0), (2, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 2), (2, ⟨60, 120⟩, 0)]

theorem g32p_row23_pairing_37 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 0), (2, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (2, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (2, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (2, ⟨60, 120⟩, 0)]

theorem g32p_row23_pairing_38 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 0), (4, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (2, ⟨-4, -8⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (2, ⟨4, 8⟩, 0), (4, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 2), (2, ⟨60, 120⟩, 0)]

theorem g32p_row23_pairing_39 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_39)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 0), (4, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (2, ⟨-4, -8⟩, 1), (2, ⟨-4, -8⟩, 2), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨4, 8⟩, 1), (2, ⟨4, 8⟩, 2), (4, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (2, ⟨64, 128⟩, 0)]

theorem g32p_row23_pairing_40 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_40)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 0), (4, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (2, ⟨-4, -8⟩, 1), (2, ⟨-4, -8⟩, 2), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨4, 8⟩, 1), (2, ⟨4, 8⟩, 2), (4, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (2, ⟨64, 128⟩, 0)]

theorem g32p_row23_pairing_41 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-80, -160⟩, 0), (4, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (2, ⟨-4, -8⟩, 1), (2, ⟨-4, -8⟩, 2), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨4, 8⟩, 1), (2, ⟨4, 8⟩, 2), (4, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (2, ⟨80, 160⟩, 0)]

theorem g32p_row23_pairing_42 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 0), (2, ⟨-9, -18⟩, 0), (2, ⟨9, 18⟩, 0), (2, ⟨81, 162⟩, 0)]

theorem g32p_row23_pairing_43 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_43)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-20, 0⟩, 0), (6, ⟨-7, 0⟩, 0), (3, ⟨-7, 0⟩, 1), (3, ⟨-7, 0⟩, 2), (6, ⟨-3, 0⟩, 0), (3, ⟨-3, 0⟩, 1), (3, ⟨-3, 0⟩, 2), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 2), (6, ⟨2, 0⟩, 1), (6, ⟨2, 0⟩, 2), (6, ⟨3, 0⟩, 0), (3, ⟨3, 0⟩, 1), (3, ⟨3, 0⟩, 2), (6, ⟨7, 0⟩, 0), (3, ⟨7, 0⟩, 1), (3, ⟨7, 0⟩, 2), (3, ⟨20, 0⟩, 0)]

theorem g32p_row23_pairing_44 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-60, 0⟩, 0), (3, ⟨-6, 0⟩, 1), (3, ⟨-6, 0⟩, 2), (12, ⟨-3, 0⟩, 0), (6, ⟨-3, 0⟩, 1), (6, ⟨-3, 0⟩, 2), (12, ⟨3, 0⟩, 0), (6, ⟨3, 0⟩, 1), (6, ⟨3, 0⟩, 2), (3, ⟨6, 0⟩, 1), (3, ⟨6, 0⟩, 2), (3, ⟨60, 0⟩, 0)]

theorem g32p_row23_pairing_45 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-64, 0⟩, 0), (6, ⟨-8, 0⟩, 0), (3, ⟨-8, 0⟩, 1), (3, ⟨-8, 0⟩, 2), (3, ⟨-4, 0⟩, 1), (3, ⟨-4, 0⟩, 2), (3, ⟨-2, 0⟩, 1), (3, ⟨-2, 0⟩, 2), (3, ⟨2, 0⟩, 1), (3, ⟨2, 0⟩, 2), (3, ⟨4, 0⟩, 1), (3, ⟨4, 0⟩, 2), (6, ⟨8, 0⟩, 0), (3, ⟨8, 0⟩, 1), (3, ⟨8, 0⟩, 2), (3, ⟨64, 0⟩, 0)]

theorem g32p_row23_pairing_46 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row23_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-80, 0⟩, 0), (6, ⟨-8, 0⟩, 0), (3, ⟨-8, 0⟩, 1), (3, ⟨-8, 0⟩, 2), (3, ⟨-4, 0⟩, 1), (3, ⟨-4, 0⟩, 2), (3, ⟨-2, 0⟩, 1), (3, ⟨-2, 0⟩, 2), (3, ⟨2, 0⟩, 1), (3, ⟨2, 0⟩, 2), (3, ⟨4, 0⟩, 1), (3, ⟨4, 0⟩, 2), (6, ⟨8, 0⟩, 0), (3, ⟨8, 0⟩, 1), (3, ⟨8, 0⟩, 2), (3, ⟨80, 0⟩, 0)]

theorem g32p_row23_pairing_47 :
    g32p_cyclotomicPairingCheck 108 (0)
      (g32p_pairingCoefficients 3 g32p_row23_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row23_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 23 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨23, 1, [(9, 1), (23, -2), (30, -1), (33, -1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row24_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(192, ⟨-1, -2⟩, 2), (192, ⟨-1, -2⟩, 5), (192, ⟨1, 2⟩, 1), (192, ⟨1, 2⟩, 4)]

theorem g32p_row24_pairing_0 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_0)
      [1, -1, 1] [0, 192, 0, 192, 0, -384] = true := by
  decide +kernel

def g32p_row24_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 4), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 4)]

theorem g32p_row24_pairing_1 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (32, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (64, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 4), (64, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row24_pairing_2 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (32, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (64, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 4), (64, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row24_pairing_3 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row24_pairing_4 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (24, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 4), (64, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 1), (60, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 1), (60, ⟨1, 2⟩, 4), (144, ⟨1, 2⟩, 5), (64, ⟨2, 4⟩, 4), (2, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row24_pairing_5 :
    g32p_cyclotomicPairingCheck 1152 (1)
      (g32p_pairingCoefficients 6 g32p_row24_terms_5)
      [1, -1, 1] [-1152, -1344, -384, 576, 768, 384] = true := by
  decide +kernel

def g32p_row24_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (24, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 4), (64, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 1), (60, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 1), (60, ⟨1, 2⟩, 4), (144, ⟨1, 2⟩, 5), (64, ⟨2, 4⟩, 4), (2, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row24_pairing_6 :
    g32p_cyclotomicPairingCheck 1152 (1)
      (g32p_pairingCoefficients 6 g32p_row24_terms_6)
      [1, -1, 1] [-1152, -1344, -384, 576, 768, 384] = true := by
  decide +kernel

def g32p_row24_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 2), (24, ⟨-2, -4⟩, 1), (60, ⟨-2, -4⟩, 2), (66, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (24, ⟨2, 4⟩, 1), (66, ⟨2, 4⟩, 2), (60, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (2, ⟨6, 12⟩, 4)]

theorem g32p_row24_pairing_7 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row24_pairing_8 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (24, ⟨-2, -4⟩, 1), (26, ⟨-2, -4⟩, 2), (36, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (64, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 4), (64, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 4), (24, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (26, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row24_pairing_9 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (24, ⟨-2, -4⟩, 1), (26, ⟨-2, -4⟩, 2), (36, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (64, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 4), (64, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 4), (24, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (26, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row24_pairing_10 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (2, ⟨-7, -14⟩, 2), (24, ⟨-7, -14⟩, 5), (100, ⟨-3, -6⟩, 2), (24, ⟨-3, -6⟩, 5), (64, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 4), (144, ⟨-1, -2⟩, 5), (144, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 4), (24, ⟨3, 6⟩, 1), (100, ⟨3, 6⟩, 4), (24, ⟨7, 14⟩, 1), (2, ⟨7, 14⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row24_pairing_11 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_11)
      [1, -1, 1] [0, 384, 0, 384, 0, -768] = true := by
  decide +kernel

def g32p_row24_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (24, ⟨-3, -6⟩, 2), (64, ⟨-2, -4⟩, 2), (192, ⟨-1, -2⟩, 1), (38, ⟨-1, -2⟩, 4), (38, ⟨1, 2⟩, 2), (192, ⟨1, 2⟩, 5), (64, ⟨2, 4⟩, 4), (24, ⟨3, 6⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row24_pairing_12 :
    g32p_cyclotomicPairingCheck 1152 (1)
      (g32p_pairingCoefficients 6 g32p_row24_terms_12)
      [1, -1, 1] [-1152, -1344, -384, 576, 768, 384] = true := by
  decide +kernel

def g32p_row24_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row24_pairing_13 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 4), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 4)]

theorem g32p_row24_pairing_14 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (44, ⟨-2, -4⟩, 2), (44, ⟨-2, -4⟩, 4), (44, ⟨2, 4⟩, 2), (44, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row24_pairing_15 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (32, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (64, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 4), (64, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row24_pairing_16 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (44, ⟨-2, -4⟩, 2), (44, ⟨-2, -4⟩, 4), (44, ⟨2, 4⟩, 2), (44, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row24_pairing_17 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (32, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (64, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 4), (64, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row24_pairing_18 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (44, ⟨-2, -4⟩, 2), (44, ⟨-2, -4⟩, 4), (44, ⟨2, 4⟩, 2), (44, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row24_pairing_19 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 2), (38, ⟨-4, -8⟩, 2), (48, ⟨-4, -8⟩, 5), (64, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 4), (64, ⟨1, 2⟩, 2), (64, ⟨1, 2⟩, 4), (48, ⟨4, 8⟩, 1), (38, ⟨4, 8⟩, 4), (2, ⟨20, 40⟩, 4)]

theorem g32p_row24_pairing_20 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_20)
      [1, -1, 1] [0, 192, 0, 192, 0, -384] = true := by
  decide +kernel

def g32p_row24_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 2), (2, ⟨-8, -16⟩, 2), (24, ⟨-8, -16⟩, 5), (64, ⟨-3, -6⟩, 2), (64, ⟨-1, -2⟩, 4), (64, ⟨1, 2⟩, 2), (64, ⟨3, 6⟩, 4), (24, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 4), (2, ⟨24, 48⟩, 4)]

theorem g32p_row24_pairing_21 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_21)
      [1, -1, 1] [0, 192, 0, 192, 0, -384] = true := by
  decide +kernel

def g32p_row24_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row24_pairing_22 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (2, ⟨-6, -12⟩, 2), (24, ⟨-6, -12⟩, 5), (60, ⟨-2, -4⟩, 2), (24, ⟨-2, -4⟩, 5), (24, ⟨2, 4⟩, 1), (60, ⟨2, 4⟩, 4), (24, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row24_pairing_23 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_23)
      [1, -1, 1] [0, 192, 0, 192, 0, -384] = true := by
  decide +kernel

def g32p_row24_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (2, ⟨-6, -12⟩, 2), (24, ⟨-6, -12⟩, 5), (60, ⟨-2, -4⟩, 2), (24, ⟨-2, -4⟩, 5), (24, ⟨2, 4⟩, 1), (60, ⟨2, 4⟩, 4), (24, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row24_pairing_24 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_24)
      [1, -1, 1] [0, 192, 0, 192, 0, -384] = true := by
  decide +kernel

def g32p_row24_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (24, ⟨-10, -20⟩, 1), (2, ⟨-10, -20⟩, 4), (64, ⟨-3, -6⟩, 2), (36, ⟨-2, -4⟩, 2), (24, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (64, ⟨-1, -2⟩, 4), (64, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (36, ⟨2, 4⟩, 4), (64, ⟨3, 6⟩, 4), (2, ⟨10, 20⟩, 2), (24, ⟨10, 20⟩, 5), (2, ⟨30, 60⟩, 4)]

theorem g32p_row24_pairing_25 :
    g32p_cyclotomicPairingCheck 1152 (1)
      (g32p_pairingCoefficients 6 g32p_row24_terms_25)
      [1, -1, 1] [-1152, -1344, -384, 576, 768, 384] = true := by
  decide +kernel

def g32p_row24_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row24_pairing_26 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row24_pairing_27 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row24_pairing_28 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row24_pairing_29 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (24, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 4), (128, ⟨-1, -2⟩, 2), (128, ⟨1, 2⟩, 4), (2, ⟨8, 16⟩, 2), (24, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row24_pairing_30 :
    g32p_cyclotomicPairingCheck 1152 (1)
      (g32p_pairingCoefficients 6 g32p_row24_terms_30)
      [1, -1, 1] [-1152, -1344, -384, 576, 768, 384] = true := by
  decide +kernel

def g32p_row24_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (24, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 4), (128, ⟨-1, -2⟩, 2), (128, ⟨1, 2⟩, 4), (2, ⟨8, 16⟩, 2), (24, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row24_pairing_31 :
    g32p_cyclotomicPairingCheck 1152 (1)
      (g32p_pairingCoefficients 6 g32p_row24_terms_31)
      [1, -1, 1] [-1152, -1344, -384, 576, 768, 384] = true := by
  decide +kernel

def g32p_row24_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row24_pairing_32 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (48, ⟨-3, -6⟩, 1), (38, ⟨-3, -6⟩, 4), (24, ⟨-1, -2⟩, 2), (144, ⟨-1, -2⟩, 5), (144, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 4), (38, ⟨3, 6⟩, 2), (48, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row24_pairing_33 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (48, ⟨-3, -6⟩, 1), (38, ⟨-3, -6⟩, 4), (24, ⟨-1, -2⟩, 2), (144, ⟨-1, -2⟩, 5), (144, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 4), (38, ⟨3, 6⟩, 2), (48, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row24_pairing_34 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 4), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 4)]

theorem g32p_row24_pairing_35 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (32, ⟨-3, -6⟩, 2), (32, ⟨-3, -6⟩, 4), (32, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (32, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 4), (32, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (32, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row24_pairing_36 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row24_pairing_37 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (32, ⟨-3, -6⟩, 2), (32, ⟨-3, -6⟩, 4), (32, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (32, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 4), (32, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (32, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row24_pairing_38 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 2), (24, ⟨-4, -8⟩, 1), (36, ⟨-4, -8⟩, 2), (2, ⟨-4, -8⟩, 4), (24, ⟨-4, -8⟩, 5), (64, ⟨-3, -6⟩, 4), (64, ⟨-1, -2⟩, 4), (64, ⟨1, 2⟩, 2), (64, ⟨3, 6⟩, 2), (24, ⟨4, 8⟩, 1), (2, ⟨4, 8⟩, 2), (36, ⟨4, 8⟩, 4), (24, ⟨4, 8⟩, 5), (2, ⟨60, 120⟩, 4)]

theorem g32p_row24_pairing_39 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 2), (64, ⟨-2, -4⟩, 4), (64, ⟨2, 4⟩, 2), (2, ⟨64, 128⟩, 4)]

theorem g32p_row24_pairing_40 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (32, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 4), (32, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 4), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 4)]

theorem g32p_row24_pairing_41 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (32, ⟨-4, -8⟩, 2), (32, ⟨-4, -8⟩, 4), (32, ⟨4, 8⟩, 2), (32, ⟨4, 8⟩, 4), (1, ⟨80, 160⟩, 2), (1, ⟨80, 160⟩, 4)]

theorem g32p_row24_pairing_42 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 2), (2, ⟨-9, -18⟩, 2), (24, ⟨-9, -18⟩, 5), (24, ⟨-3, -6⟩, 1), (60, ⟨-3, -6⟩, 4), (144, ⟨-1, -2⟩, 1), (144, ⟨1, 2⟩, 5), (60, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 5), (24, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 4), (2, ⟨81, 162⟩, 4)]

theorem g32p_row24_pairing_43 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_43)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 4), (44, ⟨-2, 0⟩, 0), (44, ⟨-2, 0⟩, 2), (44, ⟨-2, 0⟩, 4), (44, ⟨2, 0⟩, 0), (44, ⟨2, 0⟩, 2), (44, ⟨2, 0⟩, 4), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row24_pairing_44 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 4), (12, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 2), (12, ⟨-2, 0⟩, 4), (12, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 2), (12, ⟨2, 0⟩, 4), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row24_pairing_45 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 4), (32, ⟨-2, 0⟩, 0), (32, ⟨-2, 0⟩, 2), (32, ⟨-2, 0⟩, 4), (32, ⟨2, 0⟩, 0), (32, ⟨2, 0⟩, 2), (32, ⟨2, 0⟩, 4), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row24_pairing_46 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row24_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 4), (32, ⟨-4, 0⟩, 0), (32, ⟨-4, 0⟩, 2), (32, ⟨-4, 0⟩, 4), (32, ⟨4, 0⟩, 0), (32, ⟨4, 0⟩, 2), (32, ⟨4, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row24_pairing_47 :
    g32p_cyclotomicPairingCheck 1152 (0)
      (g32p_pairingCoefficients 6 g32p_row24_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row24_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 24 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨24, -1, [(6, 1), (7, 1), (13, 1), (26, 1), (31, 1), (32, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row25_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(96, ⟨-1, -2⟩, 2), (96, ⟨-1, -2⟩, 5), (96, ⟨1, 2⟩, 1), (96, ⟨1, 2⟩, 4)]

theorem g32p_row25_pairing_0 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_0)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row25_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row25_pairing_1 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row25_pairing_2 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row25_pairing_3 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 3), (16, ⟨-2, -4⟩, 5), (16, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 3), (16, ⟨2, 4⟩, 5)]

theorem g32p_row25_pairing_4 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (4, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 4), (16, ⟨-2, -4⟩, 3), (40, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (40, ⟨-1, -2⟩, 4), (52, ⟨-1, -2⟩, 5), (52, ⟨1, 2⟩, 1), (40, ⟨1, 2⟩, 2), (48, ⟨1, 2⟩, 4), (40, ⟨1, 2⟩, 5), (16, ⟨2, 4⟩, 3), (6, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row25_pairing_5 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (4, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 4), (16, ⟨-2, -4⟩, 3), (40, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (40, ⟨-1, -2⟩, 4), (52, ⟨-1, -2⟩, 5), (52, ⟨1, 2⟩, 1), (40, ⟨1, 2⟩, 2), (48, ⟨1, 2⟩, 4), (40, ⟨1, 2⟩, 5), (16, ⟨2, 4⟩, 3), (6, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row25_pairing_6 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 2), (16, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 4), (36, ⟨-2, -4⟩, 5), (16, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (36, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (16, ⟨3, 6⟩, 4), (2, ⟨6, 12⟩, 4)]

theorem g32p_row25_pairing_7 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_7)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row25_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row25_pairing_8 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (12, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 4), (28, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (32, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (28, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row25_pairing_9 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (12, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 4), (28, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (32, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (28, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row25_pairing_10 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (6, ⟨-7, -14⟩, 2), (4, ⟨-7, -14⟩, 5), (32, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 5), (32, ⟨-2, -4⟩, 1), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (32, ⟨2, 4⟩, 5), (12, ⟨3, 6⟩, 1), (32, ⟨3, 6⟩, 4), (4, ⟨7, 14⟩, 1), (6, ⟨7, 14⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row25_pairing_11 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row25_terms_11)
      [1, -1, 1] [-576, -576, -192, 384, 384] = true := by
  decide +kernel

def g32p_row25_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (16, ⟨-3, -6⟩, 2), (24, ⟨-3, -6⟩, 5), (72, ⟨-1, -2⟩, 1), (78, ⟨-1, -2⟩, 4), (78, ⟨1, 2⟩, 2), (72, ⟨1, 2⟩, 5), (24, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row25_pairing_12 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row25_pairing_13 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row25_pairing_14 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (12, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row25_pairing_15 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-4, -8⟩, 2), (8, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (8, ⟨4, 8⟩, 2), (8, ⟨4, 8⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row25_pairing_16 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (12, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row25_pairing_17 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-4, -8⟩, 2), (8, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (8, ⟨4, 8⟩, 2), (8, ⟨4, 8⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row25_pairing_18 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (12, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row25_pairing_19 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 2), (16, ⟨-5, -10⟩, 2), (38, ⟨-4, -8⟩, 2), (16, ⟨-4, -8⟩, 5), (16, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 4), (16, ⟨4, 8⟩, 1), (38, ⟨4, 8⟩, 4), (16, ⟨5, 10⟩, 4), (2, ⟨20, 40⟩, 4)]

theorem g32p_row25_pairing_20 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row25_terms_20)
      [1, -1, 1] [-576, -480, -192, 480, 384, -192] = true := by
  decide +kernel

def g32p_row25_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 2), (6, ⟨-8, -16⟩, 2), (4, ⟨-8, -16⟩, 5), (32, ⟨-2, -4⟩, 5), (32, ⟨2, 4⟩, 1), (4, ⟨8, 16⟩, 1), (6, ⟨8, 16⟩, 4), (2, ⟨24, 48⟩, 4)]

theorem g32p_row25_pairing_21 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_21)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row25_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 3), (16, ⟨-2, -4⟩, 5), (16, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 3), (16, ⟨2, 4⟩, 5)]

theorem g32p_row25_pairing_22 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (6, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 5), (16, ⟨-3, -6⟩, 4), (32, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 3), (36, ⟨-2, -4⟩, 5), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 5), (36, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 3), (32, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 1), (6, ⟨6, 12⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row25_pairing_23 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_23)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row25_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (6, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 5), (16, ⟨-3, -6⟩, 4), (32, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 3), (36, ⟨-2, -4⟩, 5), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 5), (36, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 3), (32, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 1), (6, ⟨6, 12⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row25_pairing_24 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_24)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row25_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (4, ⟨-10, -20⟩, 1), (6, ⟨-10, -20⟩, 4), (16, ⟨-3, -6⟩, 2), (24, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 4), (16, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (16, ⟨3, 6⟩, 4), (6, ⟨10, 20⟩, 2), (4, ⟨10, 20⟩, 5), (2, ⟨30, 60⟩, 4)]

theorem g32p_row25_pairing_25 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row25_terms_25)
      [1, -1, 1] [-576, -672, -192, 288, 384, 192] = true := by
  decide +kernel

def g32p_row25_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row25_pairing_26 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row25_pairing_27 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row25_pairing_28 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 3), (16, ⟨-2, -4⟩, 5), (16, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 3), (16, ⟨2, 4⟩, 5)]

theorem g32p_row25_pairing_29 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (4, ⟨-8, -16⟩, 1), (6, ⟨-8, -16⟩, 4), (16, ⟨-2, -4⟩, 3), (16, ⟨-2, -4⟩, 4), (16, ⟨-2, -4⟩, 5), (16, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (16, ⟨2, 4⟩, 3), (6, ⟨8, 16⟩, 2), (4, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row25_pairing_30 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (4, ⟨-8, -16⟩, 1), (6, ⟨-8, -16⟩, 4), (16, ⟨-2, -4⟩, 3), (16, ⟨-2, -4⟩, 4), (16, ⟨-2, -4⟩, 5), (16, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (16, ⟨2, 4⟩, 3), (6, ⟨8, 16⟩, 2), (4, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row25_pairing_31 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row25_pairing_32 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (16, ⟨-3, -6⟩, 1), (38, ⟨-3, -6⟩, 4), (24, ⟨-1, -2⟩, 2), (48, ⟨-1, -2⟩, 5), (48, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 4), (38, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row25_pairing_33 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (16, ⟨-3, -6⟩, 1), (38, ⟨-3, -6⟩, 4), (24, ⟨-1, -2⟩, 2), (48, ⟨-1, -2⟩, 5), (48, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 4), (38, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row25_pairing_34 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row25_pairing_35 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row25_pairing_36 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (8, ⟨6, 12⟩, 2), (8, ⟨6, 12⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row25_pairing_37 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 5), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row25_pairing_38 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 2), (4, ⟨-4, -8⟩, 1), (32, ⟨-4, -8⟩, 2), (6, ⟨-4, -8⟩, 4), (12, ⟨-4, -8⟩, 5), (16, ⟨-3, -6⟩, 4), (32, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (16, ⟨3, 6⟩, 2), (12, ⟨4, 8⟩, 1), (6, ⟨4, 8⟩, 2), (32, ⟨4, 8⟩, 4), (4, ⟨4, 8⟩, 5), (2, ⟨60, 120⟩, 4)]

theorem g32p_row25_pairing_39 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row25_terms_39)
      [1, -1, 1] [-576, -576, -192, 384, 384] = true := by
  decide +kernel

def g32p_row25_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 2), (16, ⟨-4, -8⟩, 2), (16, ⟨4, 8⟩, 4), (2, ⟨64, 128⟩, 4)]

theorem g32p_row25_pairing_40 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row25_terms_40)
      [1, -1, 1] [-576, -576, -192, 384, 384] = true := by
  decide +kernel

def g32p_row25_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (8, ⟨-4, -8⟩, 2), (8, ⟨-4, -8⟩, 4), (8, ⟨4, 8⟩, 2), (8, ⟨4, 8⟩, 4), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 4)]

theorem g32p_row25_pairing_41 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (1, ⟨80, 160⟩, 2), (1, ⟨80, 160⟩, 4)]

theorem g32p_row25_pairing_42 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 2), (6, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 5), (36, ⟨-3, -6⟩, 1), (32, ⟨-3, -6⟩, 4), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 4), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 5), (32, ⟨3, 6⟩, 2), (36, ⟨3, 6⟩, 5), (4, ⟨9, 18⟩, 1), (6, ⟨9, 18⟩, 4), (2, ⟨81, 162⟩, 4)]

theorem g32p_row25_pairing_43 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row25_terms_43)
      [1, -1, 1] [-576, -672, -192, 288, 384, 192] = true := by
  decide +kernel

def g32p_row25_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 4), (8, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (12, ⟨-2, 0⟩, 3), (8, ⟨-2, 0⟩, 4), (12, ⟨-2, 0⟩, 5), (8, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (12, ⟨2, 0⟩, 3), (8, ⟨2, 0⟩, 4), (12, ⟨2, 0⟩, 5), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row25_pairing_44 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 4), (8, ⟨-6, 0⟩, 0), (8, ⟨-6, 0⟩, 2), (8, ⟨-6, 0⟩, 4), (12, ⟨-2, 0⟩, 1), (12, ⟨-2, 0⟩, 3), (12, ⟨-2, 0⟩, 5), (12, ⟨2, 0⟩, 1), (12, ⟨2, 0⟩, 3), (12, ⟨2, 0⟩, 5), (8, ⟨6, 0⟩, 0), (8, ⟨6, 0⟩, 2), (8, ⟨6, 0⟩, 4), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row25_pairing_45 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 4), (8, ⟨-4, 0⟩, 0), (8, ⟨-4, 0⟩, 2), (8, ⟨-4, 0⟩, 4), (8, ⟨4, 0⟩, 0), (8, ⟨4, 0⟩, 2), (8, ⟨4, 0⟩, 4), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row25_pairing_46 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row25_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 4), (8, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 2), (8, ⟨-2, 0⟩, 4), (8, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 2), (8, ⟨2, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row25_pairing_47 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row25_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row25_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 25 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨25, -1, [(12, 1), (21, 1), (26, 1), (40, 1), (41, 1), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row26_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (32, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (32, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5)]

theorem g32p_row26_pairing_0 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (24, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4)]

theorem g32p_row26_pairing_1 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (16, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (28, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (28, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (16, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row26_pairing_2 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (12, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (12, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (16, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row26_pairing_3 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (24, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4)]

theorem g32p_row26_pairing_4 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (10, ⟨-3, -6⟩, 4), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (32, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (16, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (36, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (10, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 4)]

theorem g32p_row26_pairing_5 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (16, ⟨-2, -4⟩, 0), (76, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 4), (96, ⟨-1, -2⟩, 5), (96, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (76, ⟨1, 2⟩, 4), (16, ⟨2, 4⟩, 0), (2, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (2, ⟨5, 10⟩, 4)]

theorem g32p_row26_pairing_6 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_6)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row26_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (28, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (32, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (16, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (28, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 4), (2, ⟨6, 12⟩, 4)]

theorem g32p_row26_pairing_7 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_7)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row26_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (16, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (16, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (16, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4)]

theorem g32p_row26_pairing_8 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (8, ⟨-5, -10⟩, 2), (16, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (64, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 4), (32, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 4), (64, ⟨1, 2⟩, 5), (16, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (18, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (16, ⟨3, 6⟩, 4), (8, ⟨5, 10⟩, 4), (2, ⟨10, 20⟩, 4)]

theorem g32p_row26_pairing_9 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row26_terms_9)
      [1, -1, 1] [-576, -672, -192, 288, 384, 192] = true := by
  decide +kernel

def g32p_row26_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (8, ⟨-5, -10⟩, 0), (16, ⟨-3, -6⟩, 4), (24, ⟨-2, -4⟩, 1), (26, ⟨-2, -4⟩, 2), (20, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (32, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 3), (16, ⟨1, 2⟩, 4), (8, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 2), (26, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (16, ⟨3, 6⟩, 2), (8, ⟨5, 10⟩, 0), (2, ⟨10, 20⟩, 4)]

theorem g32p_row26_pairing_10 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (2, ⟨-7, -14⟩, 2), (8, ⟨-3, -6⟩, 0), (20, ⟨-3, -6⟩, 2), (24, ⟨-3, -6⟩, 5), (24, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (16, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (8, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (20, ⟨3, 6⟩, 4), (2, ⟨7, 14⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row26_pairing_11 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_11)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row26_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 4), (16, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 5), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 1), (14, ⟨-1, -2⟩, 4), (14, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 4), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 2), (2, ⟨15, 30⟩, 4)]

theorem g32p_row26_pairing_12 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (16, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (16, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (16, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4)]

theorem g32p_row26_pairing_13 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 4), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 2), (8, ⟨6, 12⟩, 4)]

theorem g32p_row26_pairing_14 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-7, -14⟩, 0), (4, ⟨-7, -14⟩, 2), (4, ⟨-7, -14⟩, 4), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (8, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (8, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (8, ⟨7, 14⟩, 0), (4, ⟨7, 14⟩, 2), (4, ⟨7, 14⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row26_pairing_15 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 4), (8, ⟨-5, -10⟩, 0), (4, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (16, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (16, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (8, ⟨5, 10⟩, 0), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row26_pairing_16 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (4, ⟨-8, -16⟩, 2), (4, ⟨-8, -16⟩, 4), (8, ⟨-5, -10⟩, 0), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (8, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (8, ⟨5, 10⟩, 0), (4, ⟨8, 16⟩, 2), (4, ⟨8, 16⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row26_pairing_17 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 4), (4, ⟨-5, -10⟩, 2), (4, ⟨-5, -10⟩, 4), (4, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (12, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (12, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨5, 10⟩, 2), (4, ⟨5, 10⟩, 4), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row26_pairing_18 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-8, -16⟩, 0), (4, ⟨-5, -10⟩, 2), (4, ⟨-5, -10⟩, 4), (12, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (12, ⟨3, 6⟩, 2), (12, ⟨3, 6⟩, 4), (4, ⟨5, 10⟩, 2), (4, ⟨5, 10⟩, 4), (8, ⟨8, 16⟩, 0), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row26_pairing_19 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 2), (14, ⟨-4, -8⟩, 2), (24, ⟨-4, -8⟩, 5), (16, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (16, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (24, ⟨4, 8⟩, 1), (14, ⟨4, 8⟩, 4), (2, ⟨20, 40⟩, 4)]

theorem g32p_row26_pairing_20 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_20)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row26_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 2), (2, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 4), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 4), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 2), (2, ⟨8, 16⟩, 4), (2, ⟨24, 48⟩, 4)]

theorem g32p_row26_pairing_21 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (24, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4)]

theorem g32p_row26_pairing_22 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (8, ⟨-9, -18⟩, 2), (10, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (36, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (32, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (10, ⟨6, 12⟩, 4), (8, ⟨9, 18⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row26_pairing_23 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row26_terms_23)
      [1, -1, 1] [-576, -480, -192, 480, 384, -192] = true := by
  decide +kernel

def g32p_row26_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (8, ⟨-9, -18⟩, 4), (8, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 4), (8, ⟨-2, -4⟩, 0), (28, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 5), (64, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (40, ⟨-1, -2⟩, 4), (40, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 4), (64, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (28, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 4), (8, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 4)]

theorem g32p_row26_pairing_24 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_24)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (2, ⟨-10, -20⟩, 4), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 4), (8, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (16, ⟨-1, -2⟩, 4), (24, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (8, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (24, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (2, ⟨10, 20⟩, 2), (2, ⟨30, 60⟩, 4)]

theorem g32p_row26_pairing_25 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (16, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (16, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (16, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4)]

theorem g32p_row26_pairing_26 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 4), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (8, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (8, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row26_pairing_27 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row26_pairing_28 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 4), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 2), (8, ⟨6, 12⟩, 4)]

theorem g32p_row26_pairing_29 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (8, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 4), (8, ⟨-6, -12⟩, 4), (8, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 4), (16, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (8, ⟨6, 12⟩, 2), (8, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 4)]

theorem g32p_row26_pairing_30 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (8, ⟨-8, -16⟩, 2), (2, ⟨-8, -16⟩, 4), (8, ⟨-6, -12⟩, 2), (16, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 2), (16, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 4), (8, ⟨6, 12⟩, 4), (2, ⟨8, 16⟩, 2), (8, ⟨8, 16⟩, 4), (2, ⟨40, 80⟩, 4)]

theorem g32p_row26_pairing_31 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row26_terms_31)
      [1, -1, 1] [-576, -576, -192, 384, 384] = true := by
  decide +kernel

def g32p_row26_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (16, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (16, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (16, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4)]

theorem g32p_row26_pairing_32 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 1), (22, ⟨-3, -6⟩, 4), (16, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (16, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (16, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (8, ⟨3, 6⟩, 0), (22, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 5), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 4), (2, ⟨45, 90⟩, 4)]

theorem g32p_row26_pairing_33 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row26_terms_33)
      [1, -1, 1] [-576, -672, -192, 288, 384, 192] = true := by
  decide +kernel

def g32p_row26_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (16, ⟨-9, -18⟩, 4), (24, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (14, ⟨-3, -6⟩, 4), (48, ⟨-1, -2⟩, 2), (72, ⟨-1, -2⟩, 5), (72, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 4), (14, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4), (24, ⟨3, 6⟩, 5), (16, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 4)]

theorem g32p_row26_pairing_34 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (24, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4)]

theorem g32p_row26_pairing_35 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 4), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 4), (8, ⟨-3, -6⟩, 0), (4, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (12, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (12, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (8, ⟨3, 6⟩, 0), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 4), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row26_pairing_36 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (16, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 3), (8, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (16, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row26_pairing_37 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 4), (8, ⟨-6, -12⟩, 0), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (8, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (8, ⟨6, 12⟩, 0), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row26_pairing_38 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 2), (8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 4), (12, ⟨-4, -8⟩, 2), (2, ⟨-4, -8⟩, 4), (24, ⟨-4, -8⟩, 5), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 4), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (24, ⟨4, 8⟩, 1), (2, ⟨4, 8⟩, 2), (12, ⟨4, 8⟩, 4), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 2), (2, ⟨60, 120⟩, 4)]

theorem g32p_row26_pairing_39 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_39)
      [1, -1, 1] [0, 96, 0, 96, 0, -192] = true := by
  decide +kernel

def g32p_row26_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 2), (8, ⟨-8, -16⟩, 0), (8, ⟨-8, -16⟩, 2), (8, ⟨8, 16⟩, 0), (8, ⟨8, 16⟩, 4), (2, ⟨64, 128⟩, 4)]

theorem g32p_row26_pairing_40 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row26_terms_40)
      [1, -1, 1] [-576, -576, -192, 384, 384] = true := by
  decide +kernel

def g32p_row26_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (8, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 2), (4, ⟨-8, -16⟩, 4), (8, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 2), (4, ⟨8, 16⟩, 4), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 4)]

theorem g32p_row26_pairing_41 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (8, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 2), (4, ⟨-8, -16⟩, 4), (8, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 2), (4, ⟨8, 16⟩, 4), (1, ⟨80, 160⟩, 2), (1, ⟨80, 160⟩, 4)]

theorem g32p_row26_pairing_42 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 2), (2, ⟨-9, -18⟩, 2), (32, ⟨-3, -6⟩, 1), (28, ⟨-3, -6⟩, 4), (28, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 5), (2, ⟨9, 18⟩, 4), (2, ⟨81, 162⟩, 4)]

theorem g32p_row26_pairing_43 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 6 g32p_row26_terms_43)
      [1, -1, 1] [-576, -672, -192, 288, 384, 192] = true := by
  decide +kernel

def g32p_row26_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 4), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 2), (8, ⟨-7, 0⟩, 4), (8, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 4), (8, ⟨-2, 0⟩, 0), (4, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (4, ⟨-2, 0⟩, 3), (8, ⟨-2, 0⟩, 4), (4, ⟨-2, 0⟩, 5), (16, ⟨-1, 0⟩, 0), (32, ⟨-1, 0⟩, 1), (16, ⟨-1, 0⟩, 2), (32, ⟨-1, 0⟩, 3), (16, ⟨-1, 0⟩, 4), (32, ⟨-1, 0⟩, 5), (16, ⟨1, 0⟩, 0), (32, ⟨1, 0⟩, 1), (16, ⟨1, 0⟩, 2), (32, ⟨1, 0⟩, 3), (16, ⟨1, 0⟩, 4), (32, ⟨1, 0⟩, 5), (8, ⟨2, 0⟩, 0), (4, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (4, ⟨2, 0⟩, 3), (8, ⟨2, 0⟩, 4), (4, ⟨2, 0⟩, 5), (8, ⟨3, 0⟩, 0), (8, ⟨3, 0⟩, 2), (8, ⟨3, 0⟩, 4), (8, ⟨7, 0⟩, 0), (8, ⟨7, 0⟩, 2), (8, ⟨7, 0⟩, 4), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row26_pairing_44 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 4), (16, ⟨-3, 0⟩, 0), (16, ⟨-3, 0⟩, 2), (16, ⟨-3, 0⟩, 4), (8, ⟨-2, 0⟩, 0), (4, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (4, ⟨-2, 0⟩, 3), (8, ⟨-2, 0⟩, 4), (4, ⟨-2, 0⟩, 5), (16, ⟨-1, 0⟩, 0), (32, ⟨-1, 0⟩, 1), (16, ⟨-1, 0⟩, 2), (32, ⟨-1, 0⟩, 3), (16, ⟨-1, 0⟩, 4), (32, ⟨-1, 0⟩, 5), (16, ⟨1, 0⟩, 0), (32, ⟨1, 0⟩, 1), (16, ⟨1, 0⟩, 2), (32, ⟨1, 0⟩, 3), (16, ⟨1, 0⟩, 4), (32, ⟨1, 0⟩, 5), (8, ⟨2, 0⟩, 0), (4, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (4, ⟨2, 0⟩, 3), (8, ⟨2, 0⟩, 4), (4, ⟨2, 0⟩, 5), (16, ⟨3, 0⟩, 0), (16, ⟨3, 0⟩, 2), (16, ⟨3, 0⟩, 4), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row26_pairing_45 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 4), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 2), (8, ⟨-8, 0⟩, 4), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 2), (8, ⟨8, 0⟩, 4), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row26_pairing_46 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row26_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 4), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 2), (8, ⟨-8, 0⟩, 4), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 2), (8, ⟨8, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row26_pairing_47 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 6 g32p_row26_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row26_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 26 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨26, -1, [(10, 1), (24, 1), (32, 1), (34, 1), (41, 1), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row27_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(54, ⟨-1, -2⟩, 0), (54, ⟨-1, -2⟩, 1), (54, ⟨-1, -2⟩, 2), (54, ⟨1, 2⟩, 0), (54, ⟨1, 2⟩, 1), (54, ⟨1, 2⟩, 2)]

theorem g32p_row27_pairing_0 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row27_pairing_1 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (7, ⟨-2, -4⟩, 1), (7, ⟨-2, -4⟩, 2), (66, ⟨-1, -2⟩, 0), (37, ⟨-1, -2⟩, 1), (37, ⟨-1, -2⟩, 2), (66, ⟨1, 2⟩, 0), (37, ⟨1, 2⟩, 1), (37, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (7, ⟨2, 4⟩, 1), (7, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row27_pairing_2 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (42, ⟨-1, -2⟩, 0), (49, ⟨-1, -2⟩, 1), (49, ⟨-1, -2⟩, 2), (42, ⟨1, 2⟩, 0), (49, ⟨1, 2⟩, 1), (49, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row27_pairing_3 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row27_pairing_4 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (2, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (30, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (30, ⟨-1, -2⟩, 1), (38, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (38, ⟨1, 2⟩, 1), (30, ⟨1, 2⟩, 2), (30, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 2)]

theorem g32p_row27_pairing_5 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (2, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 2), (24, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (30, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 0), (42, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (2, ⟨1, 2⟩, 1), (42, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (30, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (2, ⟨5, 10⟩, 2)]

theorem g32p_row27_pairing_6 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (12, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (12, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row27_pairing_7 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row27_pairing_8 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (6, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 2), (2, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 1), (2, ⟨10, 20⟩, 2)]

theorem g32p_row27_pairing_9 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (6, ⟨-5, -10⟩, 1), (2, ⟨-5, -10⟩, 2), (2, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 2), (66, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (66, ⟨-1, -2⟩, 2), (66, ⟨1, 2⟩, 0), (66, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (2, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 1), (6, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 2)]

theorem g32p_row27_pairing_10 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (30, ⟨-3, -6⟩, 0), (18, ⟨-3, -6⟩, 1), (28, ⟨-3, -6⟩, 2), (30, ⟨3, 6⟩, 0), (28, ⟨3, 6⟩, 1), (18, ⟨3, 6⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row27_pairing_11 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_11)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (6, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (6, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 2), (6, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row27_pairing_12 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row27_pairing_13 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2)]

theorem g32p_row27_pairing_14 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (6, ⟨-7, -14⟩, 0), (5, ⟨-7, -14⟩, 1), (5, ⟨-7, -14⟩, 2), (30, ⟨-2, -4⟩, 0), (21, ⟨-2, -4⟩, 1), (21, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (30, ⟨2, 4⟩, 0), (21, ⟨2, 4⟩, 1), (21, ⟨2, 4⟩, 2), (6, ⟨7, 14⟩, 0), (5, ⟨7, 14⟩, 1), (5, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row27_pairing_15 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (6, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (48, ⟨-1, -2⟩, 0), (46, ⟨-1, -2⟩, 1), (46, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (46, ⟨1, 2⟩, 1), (46, ⟨1, 2⟩, 2), (6, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row27_pairing_16 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (6, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (30, ⟨-2, -4⟩, 0), (21, ⟨-2, -4⟩, 1), (21, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (30, ⟨2, 4⟩, 0), (21, ⟨2, 4⟩, 1), (21, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (6, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row27_pairing_17 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (6, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (6, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (60, ⟨-1, -2⟩, 0), (40, ⟨-1, -2⟩, 1), (40, ⟨-1, -2⟩, 2), (60, ⟨1, 2⟩, 0), (40, ⟨1, 2⟩, 1), (40, ⟨1, 2⟩, 2), (6, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (6, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row27_pairing_18 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (6, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (30, ⟨-2, -4⟩, 0), (21, ⟨-2, -4⟩, 1), (21, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (30, ⟨2, 4⟩, 0), (21, ⟨2, 4⟩, 1), (21, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (6, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row27_pairing_19 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 1), (6, ⟨-5, -10⟩, 0), (6, ⟨-5, -10⟩, 2), (6, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (42, ⟨-1, -2⟩, 0), (42, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (42, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (42, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (6, ⟨5, 10⟩, 0), (6, ⟨5, 10⟩, 1), (2, ⟨20, 40⟩, 2)]

theorem g32p_row27_pairing_20 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_20)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 1), (6, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (6, ⟨-6, -12⟩, 2), (24, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (24, ⟨-3, -6⟩, 2), (24, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨24, 48⟩, 2)]

theorem g32p_row27_pairing_21 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_21)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row27_pairing_22 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_22)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 2), (6, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (6, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (2, ⟨9, 18⟩, 0), (6, ⟨9, 18⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row27_pairing_23 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_23)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (6, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (12, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (12, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 1), (6, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (6, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row27_pairing_24 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row27_terms_24)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row27_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (36, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (36, ⟨-3, -6⟩, 2), (36, ⟨3, 6⟩, 0), (36, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row27_pairing_25 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row27_pairing_26 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (2, ⟨-9, -18⟩, 0), (7, ⟨-9, -18⟩, 1), (7, ⟨-9, -18⟩, 2), (2, ⟨9, 18⟩, 0), (7, ⟨9, 18⟩, 1), (7, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row27_pairing_27 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row27_pairing_28 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2)]

theorem g32p_row27_pairing_29 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (6, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (2, ⟨-6, -12⟩, 0), (6, ⟨-6, -12⟩, 1), (12, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (42, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (42, ⟨-1, -2⟩, 2), (42, ⟨1, 2⟩, 0), (42, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 2), (2, ⟨8, 16⟩, 1), (6, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 2)]

theorem g32p_row27_pairing_30 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row27_terms_30)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row27_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (6, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 2), (2, ⟨-6, -12⟩, 0), (6, ⟨-6, -12⟩, 2), (6, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (60, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (60, ⟨-1, -2⟩, 2), (60, ⟨1, 2⟩, 0), (60, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 1), (6, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 2)]

theorem g32p_row27_pairing_31 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row27_pairing_32 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (2, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (12, ⟨-9, -18⟩, 2), (2, ⟨9, 18⟩, 0), (12, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row27_pairing_33 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row27_pairing_34 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row27_terms_34)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row27_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row27_pairing_35 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (6, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (24, ⟨-3, -6⟩, 0), (22, ⟨-3, -6⟩, 1), (22, ⟨-3, -6⟩, 2), (24, ⟨3, 6⟩, 0), (22, ⟨3, 6⟩, 1), (22, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row27_pairing_36 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (6, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (6, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row27_pairing_37 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (30, ⟨-3, -6⟩, 0), (19, ⟨-3, -6⟩, 1), (19, ⟨-3, -6⟩, 2), (30, ⟨3, 6⟩, 0), (19, ⟨3, 6⟩, 1), (19, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row27_pairing_38 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 1), (6, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (6, ⟨-6, -12⟩, 2), (30, ⟨-3, -6⟩, 0), (30, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (30, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (30, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨60, 120⟩, 2)]

theorem g32p_row27_pairing_39 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row27_terms_39)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row27_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 1), (6, ⟨-8, -16⟩, 0), (6, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (6, ⟨-4, -8⟩, 0), (6, ⟨-4, -8⟩, 2), (24, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (6, ⟨4, 8⟩, 0), (6, ⟨4, 8⟩, 1), (6, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 1), (6, ⟨8, 16⟩, 2), (2, ⟨64, 128⟩, 2)]

theorem g32p_row27_pairing_40 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row27_terms_40)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row27_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (6, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (6, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (24, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (6, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (6, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 2)]

theorem g32p_row27_pairing_41 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (6, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (24, ⟨-4, -8⟩, 0), (18, ⟨-4, -8⟩, 1), (18, ⟨-4, -8⟩, 2), (6, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (24, ⟨4, 8⟩, 0), (18, ⟨4, 8⟩, 1), (18, ⟨4, 8⟩, 2), (6, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 1), (1, ⟨80, 160⟩, 2)]

theorem g32p_row27_pairing_42 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 1), (2, ⟨81, 162⟩, 2)]

theorem g32p_row27_pairing_43 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row27_terms_43)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row27_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 2), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 1), (8, ⟨-7, 0⟩, 2), (36, ⟨-2, 0⟩, 0), (36, ⟨-2, 0⟩, 1), (36, ⟨-2, 0⟩, 2), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 2), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 2), (36, ⟨2, 0⟩, 0), (36, ⟨2, 0⟩, 1), (36, ⟨2, 0⟩, 2), (8, ⟨7, 0⟩, 0), (8, ⟨7, 0⟩, 1), (8, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 1), (1, ⟨20, 0⟩, 2)]

theorem g32p_row27_pairing_44 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 2), (6, ⟨-6, 0⟩, 0), (6, ⟨-6, 0⟩, 1), (6, ⟨-6, 0⟩, 2), (8, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 1), (8, ⟨-3, 0⟩, 2), (8, ⟨3, 0⟩, 0), (8, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 2), (6, ⟨6, 0⟩, 0), (6, ⟨6, 0⟩, 1), (6, ⟨6, 0⟩, 2), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 1), (1, ⟨60, 0⟩, 2)]

theorem g32p_row27_pairing_45 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 2), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 2), (6, ⟨-4, 0⟩, 0), (6, ⟨-4, 0⟩, 1), (6, ⟨-4, 0⟩, 2), (30, ⟨-2, 0⟩, 0), (30, ⟨-2, 0⟩, 1), (30, ⟨-2, 0⟩, 2), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 2), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 2), (30, ⟨2, 0⟩, 0), (30, ⟨2, 0⟩, 1), (30, ⟨2, 0⟩, 2), (6, ⟨4, 0⟩, 0), (6, ⟨4, 0⟩, 1), (6, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 1), (1, ⟨64, 0⟩, 2)]

theorem g32p_row27_pairing_46 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row27_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 2), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 2), (30, ⟨-4, 0⟩, 0), (30, ⟨-4, 0⟩, 1), (30, ⟨-4, 0⟩, 2), (6, ⟨-2, 0⟩, 0), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 2), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 2), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 2), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 1), (6, ⟨2, 0⟩, 2), (30, ⟨4, 0⟩, 0), (30, ⟨4, 0⟩, 1), (30, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 1), (1, ⟨80, 0⟩, 2)]

theorem g32p_row27_pairing_47 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row27_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row27_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 27 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨27, -1, [(25, 1), (31, 1), (35, 1), (40, 1), (41, 1), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row28_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (27, ⟨-1, -2⟩, 3), (27, ⟨-1, -2⟩, 4), (27, ⟨-1, -2⟩, 5), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (27, ⟨1, 2⟩, 3), (27, ⟨1, 2⟩, 4), (27, ⟨1, 2⟩, 5)]

theorem g32p_row28_pairing_0 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 3), (27, ⟨-1, -2⟩, 4), (27, ⟨-1, -2⟩, 5), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (27, ⟨1, 2⟩, 3), (3, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 4), (9, ⟨3, 6⟩, 5)]

theorem g32p_row28_pairing_1 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 0), (1, ⟨-4, -8⟩, 3), (1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (1, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (25, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (25, ⟨-1, -2⟩, 3), (21, ⟨-1, -2⟩, 4), (21, ⟨-1, -2⟩, 5), (25, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (25, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (1, ⟨4, 8⟩, 0), (1, ⟨4, 8⟩, 3)]

theorem g32p_row28_pairing_2 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 0), (1, ⟨-4, -8⟩, 3), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (1, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (25, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (25, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (25, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (25, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (1, ⟨4, 8⟩, 0), (1, ⟨4, 8⟩, 3)]

theorem g32p_row28_pairing_3 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 3), (9, ⟨-3, -6⟩, 4), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 2), (27, ⟨-1, -2⟩, 3), (27, ⟨-1, -2⟩, 5), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 3), (27, ⟨1, 2⟩, 4), (3, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 5)]

theorem g32p_row28_pairing_4 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 3), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (7, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (7, ⟨-2, -4⟩, 3), (12, ⟨-2, -4⟩, 4), (15, ⟨-2, -4⟩, 5), (19, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (19, ⟨-1, -2⟩, 3), (12, ⟨-1, -2⟩, 4), (15, ⟨-1, -2⟩, 5), (19, ⟨1, 2⟩, 0), (15, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (19, ⟨1, 2⟩, 3), (15, ⟨1, 2⟩, 4), (12, ⟨1, 2⟩, 5), (7, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (7, ⟨2, 4⟩, 3), (15, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (1, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 3)]

theorem g32p_row28_pairing_5 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 3), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 5), (7, ⟨-2, -4⟩, 0), (15, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (7, ⟨-2, -4⟩, 3), (15, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (19, ⟨-1, -2⟩, 0), (15, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (19, ⟨-1, -2⟩, 3), (15, ⟨-1, -2⟩, 4), (12, ⟨-1, -2⟩, 5), (19, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (15, ⟨1, 2⟩, 2), (19, ⟨1, 2⟩, 3), (12, ⟨1, 2⟩, 4), (15, ⟨1, 2⟩, 5), (7, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (7, ⟨2, 4⟩, 3), (12, ⟨2, 4⟩, 4), (15, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (1, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 3)]

theorem g32p_row28_pairing_6 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (2, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 3), (6, ⟨-3, -6⟩, 4), (6, ⟨-3, -6⟩, 5), (2, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 3), (6, ⟨3, 6⟩, 4), (6, ⟨3, 6⟩, 5), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3)]

theorem g32p_row28_pairing_7 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (9, ⟨-3, -6⟩, 5), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 3), (27, ⟨-1, -2⟩, 4), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 2), (27, ⟨1, 2⟩, 3), (27, ⟨1, 2⟩, 5), (3, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 4)]

theorem g32p_row28_pairing_8 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 0), (1, ⟨-10, -20⟩, 3), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 3), (3, ⟨-5, -10⟩, 4), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 5), (1, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 3), (3, ⟨5, 10⟩, 5), (1, ⟨10, 20⟩, 0), (1, ⟨10, 20⟩, 3)]

theorem g32p_row28_pairing_9 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 0), (1, ⟨-10, -20⟩, 3), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 3), (3, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (1, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 3), (3, ⟨5, 10⟩, 4), (1, ⟨10, 20⟩, 0), (1, ⟨10, 20⟩, 3)]

theorem g32p_row28_pairing_10 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 0), (1, ⟨-15, -30⟩, 3), (8, ⟨-3, -6⟩, 0), (15, ⟨-3, -6⟩, 1), (15, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 3), (15, ⟨-3, -6⟩, 4), (15, ⟨-3, -6⟩, 5), (8, ⟨3, 6⟩, 0), (15, ⟨3, 6⟩, 1), (15, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 3), (15, ⟨3, 6⟩, 4), (15, ⟨3, 6⟩, 5), (1, ⟨15, 30⟩, 0), (1, ⟨15, 30⟩, 3)]

theorem g32p_row28_pairing_11 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_11)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 0), (1, ⟨-15, -30⟩, 3), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (2, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨15, 30⟩, 0), (1, ⟨15, 30⟩, 3)]

theorem g32p_row28_pairing_12 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 3), (27, ⟨-1, -2⟩, 4), (27, ⟨-1, -2⟩, 5), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (27, ⟨1, 2⟩, 3), (3, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 4), (9, ⟨3, 6⟩, 5)]

theorem g32p_row28_pairing_13 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-6, -12⟩, 0), (9, ⟨-6, -12⟩, 1), (9, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (27, ⟨-1, -2⟩, 3), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 3), (27, ⟨1, 2⟩, 4), (27, ⟨1, 2⟩, 5), (3, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 3), (9, ⟨6, 12⟩, 4), (9, ⟨6, 12⟩, 5)]

theorem g32p_row28_pairing_14 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row28_terms_14)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row28_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-20, -40⟩, 3), (2, ⟨-7, -14⟩, 0), (3, ⟨-7, -14⟩, 1), (3, ⟨-7, -14⟩, 2), (2, ⟨-7, -14⟩, 3), (3, ⟨-7, -14⟩, 4), (3, ⟨-7, -14⟩, 5), (6, ⟨-2, -4⟩, 0), (15, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (15, ⟨-2, -4⟩, 4), (15, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (15, ⟨2, 4⟩, 4), (15, ⟨2, 4⟩, 5), (2, ⟨7, 14⟩, 0), (3, ⟨7, 14⟩, 1), (3, ⟨7, 14⟩, 2), (2, ⟨7, 14⟩, 3), (3, ⟨7, 14⟩, 4), (3, ⟨7, 14⟩, 5), (1, ⟨20, 40⟩, 0), (1, ⟨20, 40⟩, 3)]

theorem g32p_row28_pairing_15 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-20, -40⟩, 3), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (1, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 3), (3, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 4), (3, ⟨-4, -8⟩, 5), (25, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (25, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (25, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (25, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 3), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨20, 40⟩, 0), (1, ⟨20, 40⟩, 3)]

theorem g32p_row28_pairing_16 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-20, -40⟩, 3), (1, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 3), (1, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 3), (3, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (6, ⟨-2, -4⟩, 0), (15, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (15, ⟨-2, -4⟩, 4), (15, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (15, ⟨2, 4⟩, 4), (15, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 3), (1, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 4), (3, ⟨8, 16⟩, 5), (1, ⟨20, 40⟩, 0), (1, ⟨20, 40⟩, 3)]

theorem g32p_row28_pairing_17 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-20, -40⟩, 3), (1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 3), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 4), (3, ⟨-4, -8⟩, 5), (25, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (25, ⟨-1, -2⟩, 3), (21, ⟨-1, -2⟩, 4), (21, ⟨-1, -2⟩, 5), (25, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (25, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (1, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 3), (3, ⟨5, 10⟩, 4), (3, ⟨5, 10⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (1, ⟨20, 40⟩, 0), (1, ⟨20, 40⟩, 3)]

theorem g32p_row28_pairing_18 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-20, -40⟩, 3), (1, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 3), (3, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 3), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (6, ⟨-2, -4⟩, 0), (15, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (15, ⟨-2, -4⟩, 4), (15, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (15, ⟨2, 4⟩, 4), (15, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (1, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 3), (3, ⟨5, 10⟩, 4), (3, ⟨5, 10⟩, 5), (1, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨8, 16⟩, 3), (1, ⟨20, 40⟩, 0), (1, ⟨20, 40⟩, 3)]

theorem g32p_row28_pairing_19 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-20, -40⟩, 3), (3, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (2, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (21, ⟨-1, -2⟩, 4), (21, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (2, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (3, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (3, ⟨5, 10⟩, 4), (3, ⟨5, 10⟩, 5), (1, ⟨20, 40⟩, 0), (1, ⟨20, 40⟩, 3)]

theorem g32p_row28_pairing_20 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 0), (1, ⟨-24, -48⟩, 3), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (2, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (12, ⟨-3, -6⟩, 4), (12, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 3), (12, ⟨3, 6⟩, 4), (12, ⟨3, 6⟩, 5), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨24, 48⟩, 0), (1, ⟨24, 48⟩, 3)]

theorem g32p_row28_pairing_21 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 3), (9, ⟨-9, -18⟩, 4), (3, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 2), (3, ⟨9, 18⟩, 3), (9, ⟨9, 18⟩, 5)]

theorem g32p_row28_pairing_22 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_22)
      [1, -1, 1] [0, -81, 0, -81, 0, 162] = true := by
  decide +kernel

def g32p_row28_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (1, ⟨-30, -60⟩, 3), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 5), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (1, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (6, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (6, ⟨3, 6⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (1, ⟨30, 60⟩, 0), (1, ⟨30, 60⟩, 3)]

theorem g32p_row28_pairing_23 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_23)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (1, ⟨-30, -60⟩, 3), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (6, ⟨-3, -6⟩, 5), (1, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (6, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 5), (1, ⟨30, 60⟩, 0), (1, ⟨30, 60⟩, 3)]

theorem g32p_row28_pairing_24 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_24)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (1, ⟨-30, -60⟩, 3), (8, ⟨-3, -6⟩, 0), (18, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 3), (18, ⟨-3, -6⟩, 4), (18, ⟨-3, -6⟩, 5), (8, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (18, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 3), (18, ⟨3, 6⟩, 4), (18, ⟨3, 6⟩, 5), (1, ⟨30, 60⟩, 0), (1, ⟨30, 60⟩, 3)]

theorem g32p_row28_pairing_25 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 1), (9, ⟨-9, -18⟩, 2), (3, ⟨-9, -18⟩, 3), (3, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 3), (9, ⟨9, 18⟩, 4), (9, ⟨9, 18⟩, 5)]

theorem g32p_row28_pairing_26 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row28_terms_26)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row28_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 0), (1, ⟨-36, -72⟩, 3), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-9, -18⟩, 5), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (3, ⟨9, 18⟩, 5), (1, ⟨36, 72⟩, 0), (1, ⟨36, 72⟩, 3)]

theorem g32p_row28_pairing_27 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 0), (1, ⟨-36, -72⟩, 3), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-9, -18⟩, 5), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (3, ⟨9, 18⟩, 5), (1, ⟨36, 72⟩, 0), (1, ⟨36, 72⟩, 3)]

theorem g32p_row28_pairing_28 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-6, -12⟩, 0), (9, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 3), (9, ⟨-6, -12⟩, 4), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 3), (27, ⟨-1, -2⟩, 4), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 2), (27, ⟨1, 2⟩, 3), (27, ⟨1, 2⟩, 5), (3, ⟨6, 12⟩, 0), (9, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (9, ⟨6, 12⟩, 5)]

theorem g32p_row28_pairing_29 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_29)
      [1, -1, 1] [0, -81, 0, -81, 0, 162] = true := by
  decide +kernel

def g32p_row28_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 0), (1, ⟨-40, -80⟩, 3), (1, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 3), (3, ⟨-8, -16⟩, 5), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (1, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (21, ⟨-1, -2⟩, 4), (21, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 5), (1, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 4), (1, ⟨40, 80⟩, 0), (1, ⟨40, 80⟩, 3)]

theorem g32p_row28_pairing_30 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 0), (1, ⟨-40, -80⟩, 3), (1, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 3), (3, ⟨-8, -16⟩, 4), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 5), (1, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (21, ⟨-1, -2⟩, 4), (21, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (1, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 2), (1, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 5), (1, ⟨40, 80⟩, 0), (1, ⟨40, 80⟩, 3)]

theorem g32p_row28_pairing_31 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 3), (9, ⟨-9, -18⟩, 4), (3, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 2), (3, ⟨9, 18⟩, 3), (9, ⟨9, 18⟩, 5)]

theorem g32p_row28_pairing_32 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_32)
      [1, -1, 1] [0, -81, 0, -81, 0, 162] = true := by
  decide +kernel

def g32p_row28_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 0), (1, ⟨-45, -90⟩, 3), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-9, -18⟩, 5), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (3, ⟨9, 18⟩, 5), (1, ⟨45, 90⟩, 0), (1, ⟨45, 90⟩, 3)]

theorem g32p_row28_pairing_33 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 0), (1, ⟨-45, -90⟩, 3), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-9, -18⟩, 5), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (3, ⟨9, 18⟩, 5), (1, ⟨45, 90⟩, 0), (1, ⟨45, 90⟩, 3)]

theorem g32p_row28_pairing_34 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 3), (9, ⟨-9, -18⟩, 4), (9, ⟨-9, -18⟩, 5), (3, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 1), (9, ⟨9, 18⟩, 2), (3, ⟨9, 18⟩, 3)]

theorem g32p_row28_pairing_35 :
    g32p_cyclotomicPairingCheck 486 (-1)
      (g32p_pairingCoefficients 6 g32p_row28_terms_35)
      [1, -1, 1] [486, 567, 162, -243, -324, -162] = true := by
  decide +kernel

def g32p_row28_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (1, ⟨-60, -120⟩, 3), (1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-9, -18⟩, 5), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (7, ⟨-3, -6⟩, 0), (15, ⟨-3, -6⟩, 1), (15, ⟨-3, -6⟩, 2), (7, ⟨-3, -6⟩, 3), (12, ⟨-3, -6⟩, 4), (12, ⟨-3, -6⟩, 5), (7, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (7, ⟨3, 6⟩, 3), (15, ⟨3, 6⟩, 4), (15, ⟨3, 6⟩, 5), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (1, ⟨60, 120⟩, 0), (1, ⟨60, 120⟩, 3)]

theorem g32p_row28_pairing_36 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (1, ⟨-60, -120⟩, 3), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨60, 120⟩, 0), (1, ⟨60, 120⟩, 3)]

theorem g32p_row28_pairing_37 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (1, ⟨-60, -120⟩, 3), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (7, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (7, ⟨-3, -6⟩, 3), (15, ⟨-3, -6⟩, 4), (15, ⟨-3, -6⟩, 5), (7, ⟨3, 6⟩, 0), (15, ⟨3, 6⟩, 1), (15, ⟨3, 6⟩, 2), (7, ⟨3, 6⟩, 3), (12, ⟨3, 6⟩, 4), (12, ⟨3, 6⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (3, ⟨9, 18⟩, 5), (1, ⟨60, 120⟩, 0), (1, ⟨60, 120⟩, 3)]

theorem g32p_row28_pairing_38 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (1, ⟨-60, -120⟩, 3), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (2, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (15, ⟨-3, -6⟩, 1), (15, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (15, ⟨-3, -6⟩, 4), (15, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (15, ⟨3, 6⟩, 1), (15, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 3), (15, ⟨3, 6⟩, 4), (15, ⟨3, 6⟩, 5), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨60, 120⟩, 0), (1, ⟨60, 120⟩, 3)]

theorem g32p_row28_pairing_39 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 0), (1, ⟨-64, -128⟩, 3), (2, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (2, ⟨-8, -16⟩, 3), (3, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 4), (3, ⟨-4, -8⟩, 5), (6, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (12, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (12, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (2, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (2, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 4), (3, ⟨8, 16⟩, 5), (1, ⟨64, 128⟩, 0), (1, ⟨64, 128⟩, 3)]

theorem g32p_row28_pairing_40 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 0), (1, ⟨-64, -128⟩, 3), (2, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (2, ⟨-8, -16⟩, 3), (3, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 4), (3, ⟨-4, -8⟩, 5), (6, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (12, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (12, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (2, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (2, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 4), (3, ⟨8, 16⟩, 5), (1, ⟨64, 128⟩, 0), (1, ⟨64, 128⟩, 3)]

theorem g32p_row28_pairing_41 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 0), (1, ⟨-80, -160⟩, 3), (2, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (2, ⟨-8, -16⟩, 3), (3, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (6, ⟨-4, -8⟩, 0), (12, ⟨-4, -8⟩, 1), (12, ⟨-4, -8⟩, 2), (6, ⟨-4, -8⟩, 3), (12, ⟨-4, -8⟩, 4), (12, ⟨-4, -8⟩, 5), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (6, ⟨4, 8⟩, 0), (12, ⟨4, 8⟩, 1), (12, ⟨4, 8⟩, 2), (6, ⟨4, 8⟩, 3), (12, ⟨4, 8⟩, 4), (12, ⟨4, 8⟩, 5), (2, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (2, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 4), (3, ⟨8, 16⟩, 5), (1, ⟨80, 160⟩, 0), (1, ⟨80, 160⟩, 3)]

theorem g32p_row28_pairing_42 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 0), (1, ⟨-81, -162⟩, 3), (1, ⟨81, 162⟩, 0), (1, ⟨81, 162⟩, 3)]

theorem g32p_row28_pairing_43 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_43)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-20, 0⟩, 3), (6, ⟨-7, 0⟩, 0), (9, ⟨-7, 0⟩, 2), (9, ⟨-7, 0⟩, 4), (45, ⟨-2, 0⟩, 1), (18, ⟨-2, 0⟩, 3), (45, ⟨-2, 0⟩, 5), (54, ⟨-1, 0⟩, 0), (27, ⟨-1, 0⟩, 2), (27, ⟨-1, 0⟩, 4), (27, ⟨1, 0⟩, 1), (54, ⟨1, 0⟩, 3), (27, ⟨1, 0⟩, 5), (18, ⟨2, 0⟩, 0), (45, ⟨2, 0⟩, 2), (45, ⟨2, 0⟩, 4), (9, ⟨7, 0⟩, 1), (6, ⟨7, 0⟩, 3), (9, ⟨7, 0⟩, 5), (3, ⟨20, 0⟩, 0)]

theorem g32p_row28_pairing_44 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row28_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row28_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-60, 0⟩, 3), (9, ⟨-6, 0⟩, 2), (9, ⟨-6, 0⟩, 4), (6, ⟨-3, 0⟩, 0), (9, ⟨-3, 0⟩, 2), (9, ⟨-3, 0⟩, 4), (9, ⟨3, 0⟩, 1), (6, ⟨3, 0⟩, 3), (9, ⟨3, 0⟩, 5), (9, ⟨6, 0⟩, 1), (9, ⟨6, 0⟩, 5), (3, ⟨60, 0⟩, 0)]

theorem g32p_row28_pairing_45 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row28_terms_45)
      [1, -1, 1] [-324, -243, 0, 81] = true := by
  decide +kernel

def g32p_row28_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-64, 0⟩, 3), (6, ⟨-8, 0⟩, 0), (9, ⟨-8, 0⟩, 2), (9, ⟨-8, 0⟩, 4), (9, ⟨-4, 0⟩, 1), (9, ⟨-4, 0⟩, 5), (18, ⟨-2, 0⟩, 0), (36, ⟨-2, 0⟩, 2), (36, ⟨-2, 0⟩, 4), (27, ⟨-1, 0⟩, 1), (54, ⟨-1, 0⟩, 3), (27, ⟨-1, 0⟩, 5), (54, ⟨1, 0⟩, 0), (27, ⟨1, 0⟩, 2), (27, ⟨1, 0⟩, 4), (36, ⟨2, 0⟩, 1), (18, ⟨2, 0⟩, 3), (36, ⟨2, 0⟩, 5), (9, ⟨4, 0⟩, 2), (9, ⟨4, 0⟩, 4), (9, ⟨8, 0⟩, 1), (6, ⟨8, 0⟩, 3), (9, ⟨8, 0⟩, 5), (3, ⟨64, 0⟩, 0)]

theorem g32p_row28_pairing_46 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row28_terms_46)
      [1, -1, 1] [-324, -243, 0, 81] = true := by
  decide +kernel

def g32p_row28_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-80, 0⟩, 3), (9, ⟨-8, 0⟩, 1), (6, ⟨-8, 0⟩, 3), (9, ⟨-8, 0⟩, 5), (18, ⟨-4, 0⟩, 0), (36, ⟨-4, 0⟩, 2), (36, ⟨-4, 0⟩, 4), (9, ⟨-2, 0⟩, 1), (9, ⟨-2, 0⟩, 5), (54, ⟨-1, 0⟩, 0), (27, ⟨-1, 0⟩, 2), (27, ⟨-1, 0⟩, 4), (27, ⟨1, 0⟩, 1), (54, ⟨1, 0⟩, 3), (27, ⟨1, 0⟩, 5), (9, ⟨2, 0⟩, 2), (9, ⟨2, 0⟩, 4), (36, ⟨4, 0⟩, 1), (18, ⟨4, 0⟩, 3), (36, ⟨4, 0⟩, 5), (6, ⟨8, 0⟩, 0), (9, ⟨8, 0⟩, 2), (9, ⟨8, 0⟩, 4), (3, ⟨80, 0⟩, 0)]

theorem g32p_row28_pairing_47 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row28_terms_47)
      [1, -1, 1] [-324, -243, 0, 81] = true := by
  decide +kernel

theorem g32p_row28_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 28 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
         ![0, 1, 1, 1]) := by
  refine ⟨⟨28, -1, [(15, 1), (27, 1), (36, -1), (46, 1), (47, 1), (48, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row29_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(54, ⟨-1, -2⟩, 0), (54, ⟨-1, -2⟩, 1), (54, ⟨-1, -2⟩, 2), (54, ⟨1, 2⟩, 0), (54, ⟨1, 2⟩, 1), (54, ⟨1, 2⟩, 2)]

theorem g32p_row29_pairing_0 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row29_pairing_1 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (42, ⟨-1, -2⟩, 0), (49, ⟨-1, -2⟩, 1), (49, ⟨-1, -2⟩, 2), (42, ⟨1, 2⟩, 0), (49, ⟨1, 2⟩, 1), (49, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row29_pairing_2 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (7, ⟨-2, -4⟩, 1), (7, ⟨-2, -4⟩, 2), (66, ⟨-1, -2⟩, 0), (37, ⟨-1, -2⟩, 1), (37, ⟨-1, -2⟩, 2), (66, ⟨1, 2⟩, 0), (37, ⟨1, 2⟩, 1), (37, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (7, ⟨2, 4⟩, 1), (7, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row29_pairing_3 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row29_pairing_4 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (2, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 2), (24, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (30, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 0), (42, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (2, ⟨1, 2⟩, 1), (42, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (30, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (2, ⟨5, 10⟩, 2)]

theorem g32p_row29_pairing_5 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (2, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (30, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (30, ⟨-1, -2⟩, 1), (38, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (38, ⟨1, 2⟩, 1), (30, ⟨1, 2⟩, 2), (30, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 2)]

theorem g32p_row29_pairing_6 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (12, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (12, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row29_pairing_7 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row29_pairing_8 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (6, ⟨-5, -10⟩, 1), (2, ⟨-5, -10⟩, 2), (2, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 2), (66, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (66, ⟨-1, -2⟩, 2), (66, ⟨1, 2⟩, 0), (66, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (2, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 1), (6, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 2)]

theorem g32p_row29_pairing_9 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (6, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 2), (2, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 1), (2, ⟨10, 20⟩, 2)]

theorem g32p_row29_pairing_10 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (30, ⟨-3, -6⟩, 0), (18, ⟨-3, -6⟩, 1), (28, ⟨-3, -6⟩, 2), (30, ⟨3, 6⟩, 0), (28, ⟨3, 6⟩, 1), (18, ⟨3, 6⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row29_pairing_11 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_11)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (6, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (6, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 2), (6, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row29_pairing_12 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row29_pairing_13 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2)]

theorem g32p_row29_pairing_14 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (6, ⟨-7, -14⟩, 0), (5, ⟨-7, -14⟩, 1), (5, ⟨-7, -14⟩, 2), (30, ⟨-2, -4⟩, 0), (21, ⟨-2, -4⟩, 1), (21, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (30, ⟨2, 4⟩, 0), (21, ⟨2, 4⟩, 1), (21, ⟨2, 4⟩, 2), (6, ⟨7, 14⟩, 0), (5, ⟨7, 14⟩, 1), (5, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row29_pairing_15 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (6, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (6, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (60, ⟨-1, -2⟩, 0), (40, ⟨-1, -2⟩, 1), (40, ⟨-1, -2⟩, 2), (60, ⟨1, 2⟩, 0), (40, ⟨1, 2⟩, 1), (40, ⟨1, 2⟩, 2), (6, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (6, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row29_pairing_16 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (6, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (30, ⟨-2, -4⟩, 0), (21, ⟨-2, -4⟩, 1), (21, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (30, ⟨2, 4⟩, 0), (21, ⟨2, 4⟩, 1), (21, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (6, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row29_pairing_17 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (6, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (48, ⟨-1, -2⟩, 0), (46, ⟨-1, -2⟩, 1), (46, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (46, ⟨1, 2⟩, 1), (46, ⟨1, 2⟩, 2), (6, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row29_pairing_18 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (6, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (30, ⟨-2, -4⟩, 0), (21, ⟨-2, -4⟩, 1), (21, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (30, ⟨2, 4⟩, 0), (21, ⟨2, 4⟩, 1), (21, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (6, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row29_pairing_19 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 1), (6, ⟨-5, -10⟩, 0), (6, ⟨-5, -10⟩, 2), (6, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (42, ⟨-1, -2⟩, 0), (42, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (42, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (42, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (6, ⟨5, 10⟩, 0), (6, ⟨5, 10⟩, 1), (2, ⟨20, 40⟩, 2)]

theorem g32p_row29_pairing_20 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_20)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 1), (6, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (6, ⟨-6, -12⟩, 2), (24, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (24, ⟨-3, -6⟩, 2), (24, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨24, 48⟩, 2)]

theorem g32p_row29_pairing_21 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_21)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row29_pairing_22 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_22)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (6, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (12, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (12, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 1), (6, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (6, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row29_pairing_23 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row29_terms_23)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row29_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 2), (6, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (6, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (2, ⟨9, 18⟩, 0), (6, ⟨9, 18⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row29_pairing_24 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (36, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (36, ⟨-3, -6⟩, 2), (36, ⟨3, 6⟩, 0), (36, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row29_pairing_25 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row29_pairing_26 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row29_pairing_27 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (2, ⟨-9, -18⟩, 0), (7, ⟨-9, -18⟩, 1), (7, ⟨-9, -18⟩, 2), (2, ⟨9, 18⟩, 0), (7, ⟨9, 18⟩, 1), (7, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row29_pairing_28 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2)]

theorem g32p_row29_pairing_29 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (6, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 2), (2, ⟨-6, -12⟩, 0), (6, ⟨-6, -12⟩, 2), (6, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (60, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (60, ⟨-1, -2⟩, 2), (60, ⟨1, 2⟩, 0), (60, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 1), (6, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 2)]

theorem g32p_row29_pairing_30 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (6, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (2, ⟨-6, -12⟩, 0), (6, ⟨-6, -12⟩, 1), (12, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (42, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (42, ⟨-1, -2⟩, 2), (42, ⟨1, 2⟩, 0), (42, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 2), (2, ⟨8, 16⟩, 1), (6, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 2)]

theorem g32p_row29_pairing_31 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row29_terms_31)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row29_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row29_pairing_32 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row29_pairing_33 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row29_terms_33)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row29_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (2, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (12, ⟨-9, -18⟩, 2), (2, ⟨9, 18⟩, 0), (12, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row29_pairing_34 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row29_pairing_35 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (30, ⟨-3, -6⟩, 0), (19, ⟨-3, -6⟩, 1), (19, ⟨-3, -6⟩, 2), (30, ⟨3, 6⟩, 0), (19, ⟨3, 6⟩, 1), (19, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row29_pairing_36 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (6, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (6, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row29_pairing_37 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (6, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (24, ⟨-3, -6⟩, 0), (22, ⟨-3, -6⟩, 1), (22, ⟨-3, -6⟩, 2), (24, ⟨3, 6⟩, 0), (22, ⟨3, 6⟩, 1), (22, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row29_pairing_38 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 1), (6, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (6, ⟨-6, -12⟩, 2), (30, ⟨-3, -6⟩, 0), (30, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (30, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (30, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 0), (6, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨60, 120⟩, 2)]

theorem g32p_row29_pairing_39 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row29_terms_39)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row29_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 1), (6, ⟨-8, -16⟩, 0), (6, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (6, ⟨-4, -8⟩, 0), (6, ⟨-4, -8⟩, 2), (24, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (6, ⟨4, 8⟩, 0), (6, ⟨4, 8⟩, 1), (6, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 1), (6, ⟨8, 16⟩, 2), (2, ⟨64, 128⟩, 2)]

theorem g32p_row29_pairing_40 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row29_terms_40)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row29_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (6, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (6, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (24, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (6, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (6, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 2)]

theorem g32p_row29_pairing_41 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (6, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (24, ⟨-4, -8⟩, 0), (18, ⟨-4, -8⟩, 1), (18, ⟨-4, -8⟩, 2), (6, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (24, ⟨4, 8⟩, 0), (18, ⟨4, 8⟩, 1), (18, ⟨4, 8⟩, 2), (6, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 1), (1, ⟨80, 160⟩, 2)]

theorem g32p_row29_pairing_42 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 1), (2, ⟨81, 162⟩, 2)]

theorem g32p_row29_pairing_43 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row29_terms_43)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row29_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 2), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 1), (8, ⟨-7, 0⟩, 2), (36, ⟨-2, 0⟩, 0), (36, ⟨-2, 0⟩, 1), (36, ⟨-2, 0⟩, 2), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 2), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 2), (36, ⟨2, 0⟩, 0), (36, ⟨2, 0⟩, 1), (36, ⟨2, 0⟩, 2), (8, ⟨7, 0⟩, 0), (8, ⟨7, 0⟩, 1), (8, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 1), (1, ⟨20, 0⟩, 2)]

theorem g32p_row29_pairing_44 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 2), (6, ⟨-6, 0⟩, 0), (6, ⟨-6, 0⟩, 1), (6, ⟨-6, 0⟩, 2), (8, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 1), (8, ⟨-3, 0⟩, 2), (8, ⟨3, 0⟩, 0), (8, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 2), (6, ⟨6, 0⟩, 0), (6, ⟨6, 0⟩, 1), (6, ⟨6, 0⟩, 2), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 1), (1, ⟨60, 0⟩, 2)]

theorem g32p_row29_pairing_45 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 2), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 2), (6, ⟨-4, 0⟩, 0), (6, ⟨-4, 0⟩, 1), (6, ⟨-4, 0⟩, 2), (30, ⟨-2, 0⟩, 0), (30, ⟨-2, 0⟩, 1), (30, ⟨-2, 0⟩, 2), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 2), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 2), (30, ⟨2, 0⟩, 0), (30, ⟨2, 0⟩, 1), (30, ⟨2, 0⟩, 2), (6, ⟨4, 0⟩, 0), (6, ⟨4, 0⟩, 1), (6, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 1), (1, ⟨64, 0⟩, 2)]

theorem g32p_row29_pairing_46 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row29_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 2), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 2), (30, ⟨-4, 0⟩, 0), (30, ⟨-4, 0⟩, 1), (30, ⟨-4, 0⟩, 2), (6, ⟨-2, 0⟩, 0), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 2), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 2), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 2), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 1), (6, ⟨2, 0⟩, 2), (30, ⟨4, 0⟩, 0), (30, ⟨4, 0⟩, 1), (30, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 1), (1, ⟨80, 0⟩, 2)]

theorem g32p_row29_pairing_47 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row29_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row29_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 29 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨29, -1, [(24, 1), (32, 1), (34, 1), (40, 1), (41, 1), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row30_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_0 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (9, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 3), (27, ⟨1, 2⟩, 4), (27, ⟨1, 2⟩, 5), (9, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5)]

theorem g32p_row30_pairing_1 :
    g32p_cyclotomicPairingCheck 324 (1)
      (g32p_pairingCoefficients 6 g32p_row30_terms_1)
      [1, -1, 1] [-324, -378, -108, 162, 216, 108] = true := by
  decide +kernel

def g32p_row30_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (9, ⟨-2, -4⟩, 4), (9, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 3), (27, ⟨-1, -2⟩, 4), (27, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3)]

theorem g32p_row30_pairing_2 :
    g32p_cyclotomicPairingCheck 324 (-1)
      (g32p_pairingCoefficients 6 g32p_row30_terms_2)
      [1, -1, 1] [324, 378, 108, -162, -216, -108] = true := by
  decide +kernel

def g32p_row30_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (9, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 3), (27, ⟨1, 2⟩, 4), (27, ⟨1, 2⟩, 5), (9, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5)]

theorem g32p_row30_pairing_3 :
    g32p_cyclotomicPairingCheck 324 (1)
      (g32p_pairingCoefficients 6 g32p_row30_terms_3)
      [1, -1, 1] [-324, -378, -108, 162, 216, 108] = true := by
  decide +kernel

def g32p_row30_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (9, ⟨-2, -4⟩, 2), (9, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 4), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5)]

theorem g32p_row30_pairing_4 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (9, ⟨-2, -4⟩, 2), (9, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 4), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5)]

theorem g32p_row30_pairing_5 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 5), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 4), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (9, ⟨2, 4⟩, 2), (9, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4)]

theorem g32p_row30_pairing_6 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_7 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 2), (10, ⟨-3, -6⟩, 3), (12, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 4), (10, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 3), (12, ⟨3, 6⟩, 4)]

theorem g32p_row30_pairing_8 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_8)
      [1, -1, 1] [0, 54, 0, 54, 0, -108] = true := by
  decide +kernel

def g32p_row30_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 2), (10, ⟨-3, -6⟩, 3), (12, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 4), (10, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 3), (12, ⟨3, 6⟩, 4)]

theorem g32p_row30_pairing_9 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_9)
      [1, -1, 1] [0, 54, 0, 54, 0, -108] = true := by
  decide +kernel

def g32p_row30_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 3), (12, ⟨-3, -6⟩, 4), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 4), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 5), (10, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 2), (10, ⟨3, 6⟩, 3), (12, ⟨3, 6⟩, 5)]

theorem g32p_row30_pairing_10 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_10)
      [1, -1, 1] [0, -54, 0, -54, 0, 108] = true := by
  decide +kernel

def g32p_row30_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_11 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_11)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_12 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (10, ⟨-3, -6⟩, 3), (9, ⟨-3, -6⟩, 4), (9, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (10, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (10, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5)]

theorem g32p_row30_pairing_13 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (9, ⟨-2, -4⟩, 3), (9, ⟨-2, -4⟩, 4), (9, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (9, ⟨2, 4⟩, 3), (9, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5)]

theorem g32p_row30_pairing_14 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_15 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (9, ⟨-2, -4⟩, 3), (9, ⟨-2, -4⟩, 4), (9, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (9, ⟨2, 4⟩, 3), (9, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5)]

theorem g32p_row30_pairing_16 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (10, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (10, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (10, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 4), (9, ⟨3, 6⟩, 5)]

theorem g32p_row30_pairing_17 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (9, ⟨-2, -4⟩, 3), (9, ⟨-2, -4⟩, 4), (9, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (9, ⟨2, 4⟩, 3), (9, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3)]

theorem g32p_row30_pairing_18 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (10, ⟨-3, -6⟩, 3), (9, ⟨-3, -6⟩, 4), (9, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (10, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (10, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5)]

theorem g32p_row30_pairing_19 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_20 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_21 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 4), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 5), (9, ⟨2, 4⟩, 2), (9, ⟨2, 4⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 5)]

theorem g32p_row30_pairing_22 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_22)
      [1, -1, 1] [0, -54, 0, -54, 0, 108] = true := by
  decide +kernel

def g32p_row30_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 5), (9, ⟨-2, -4⟩, 2), (9, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 4), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4)]

theorem g32p_row30_pairing_23 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_23)
      [1, -1, 1] [0, 54, 0, 54, 0, -108] = true := by
  decide +kernel

def g32p_row30_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 4), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 5), (9, ⟨2, 4⟩, 2), (9, ⟨2, 4⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 5)]

theorem g32p_row30_pairing_24 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_24)
      [1, -1, 1] [0, -54, 0, -54, 0, 108] = true := by
  decide +kernel

def g32p_row30_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_25 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (9, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (9, ⟨-3, -6⟩, 3), (9, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 4), (9, ⟨3, 6⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (3, ⟨9, 18⟩, 5)]

theorem g32p_row30_pairing_26 :
    g32p_cyclotomicPairingCheck 324 (1)
      (g32p_pairingCoefficients 6 g32p_row30_terms_26)
      [1, -1, 1] [-324, -378, -108, 162, 216, 108] = true := by
  decide +kernel

def g32p_row30_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-9, -18⟩, 5), (9, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 3), (9, ⟨-3, -6⟩, 4), (9, ⟨-3, -6⟩, 5), (9, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (9, ⟨3, 6⟩, 3), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3)]

theorem g32p_row30_pairing_27 :
    g32p_cyclotomicPairingCheck 324 (-1)
      (g32p_pairingCoefficients 6 g32p_row30_terms_27)
      [1, -1, 1] [324, 378, 108, -162, -216, -108] = true := by
  decide +kernel

def g32p_row30_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (9, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (9, ⟨-3, -6⟩, 3), (9, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 4), (9, ⟨3, 6⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (3, ⟨9, 18⟩, 5)]

theorem g32p_row30_pairing_28 :
    g32p_cyclotomicPairingCheck 324 (1)
      (g32p_pairingCoefficients 6 g32p_row30_terms_28)
      [1, -1, 1] [-324, -378, -108, 162, 216, 108] = true := by
  decide +kernel

def g32p_row30_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (9, ⟨-2, -4⟩, 3), (9, ⟨-2, -4⟩, 4), (9, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 4), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (9, ⟨2, 4⟩, 3), (9, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 5)]

theorem g32p_row30_pairing_29 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (9, ⟨-2, -4⟩, 3), (9, ⟨-2, -4⟩, 4), (9, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 4), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (9, ⟨2, 4⟩, 3), (9, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 5)]

theorem g32p_row30_pairing_30 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 5), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (9, ⟨-2, -4⟩, 3), (9, ⟨-2, -4⟩, 4), (9, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 4), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 5), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (9, ⟨2, 4⟩, 3), (9, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4)]

theorem g32p_row30_pairing_31 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (9, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 2), (9, ⟨-3, -6⟩, 3), (9, ⟨-3, -6⟩, 5), (9, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 4), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 5)]

theorem g32p_row30_pairing_32 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 5), (9, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 3), (9, ⟨-3, -6⟩, 4), (9, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 2), (9, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4)]

theorem g32p_row30_pairing_33 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (9, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 2), (9, ⟨-3, -6⟩, 3), (9, ⟨-3, -6⟩, 5), (9, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 4), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 5)]

theorem g32p_row30_pairing_34 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-9, -18⟩, 5), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (9, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3)]

theorem g32p_row30_pairing_35 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-9, -18⟩, 5), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (9, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3)]

theorem g32p_row30_pairing_36 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_37 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (9, ⟨-2, -4⟩, 4), (9, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (3, ⟨9, 18⟩, 5)]

theorem g32p_row30_pairing_38 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_39 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_40 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_41 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_42 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row30_pairing_43 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_43)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 3), (2, ⟨-7, 0⟩, 0), (3, ⟨-7, 0⟩, 2), (3, ⟨-7, 0⟩, 4), (18, ⟨-3, 0⟩, 0), (9, ⟨-3, 0⟩, 1), (9, ⟨-3, 0⟩, 5), (6, ⟨-2, 0⟩, 1), (24, ⟨-2, 0⟩, 3), (6, ⟨-2, 0⟩, 5), (18, ⟨-1, 0⟩, 2), (18, ⟨-1, 0⟩, 4), (18, ⟨1, 0⟩, 1), (18, ⟨1, 0⟩, 5), (24, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 2), (6, ⟨2, 0⟩, 4), (9, ⟨3, 0⟩, 2), (18, ⟨3, 0⟩, 3), (9, ⟨3, 0⟩, 4), (3, ⟨7, 0⟩, 1), (2, ⟨7, 0⟩, 3), (3, ⟨7, 0⟩, 5), (1, ⟨20, 0⟩, 0)]

theorem g32p_row30_pairing_44 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 3), (3, ⟨-6, 0⟩, 2), (3, ⟨-6, 0⟩, 4), (20, ⟨-3, 0⟩, 0), (9, ⟨-3, 0⟩, 1), (3, ⟨-3, 0⟩, 2), (3, ⟨-3, 0⟩, 4), (9, ⟨-3, 0⟩, 5), (3, ⟨3, 0⟩, 1), (9, ⟨3, 0⟩, 2), (20, ⟨3, 0⟩, 3), (9, ⟨3, 0⟩, 4), (3, ⟨3, 0⟩, 5), (3, ⟨6, 0⟩, 1), (3, ⟨6, 0⟩, 5), (1, ⟨60, 0⟩, 0)]

theorem g32p_row30_pairing_45 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 3), (2, ⟨-8, 0⟩, 0), (3, ⟨-8, 0⟩, 2), (3, ⟨-8, 0⟩, 4), (3, ⟨-4, 0⟩, 1), (3, ⟨-4, 0⟩, 5), (24, ⟨-2, 0⟩, 0), (3, ⟨-2, 0⟩, 2), (3, ⟨-2, 0⟩, 4), (18, ⟨-1, 0⟩, 1), (18, ⟨-1, 0⟩, 5), (18, ⟨1, 0⟩, 2), (18, ⟨1, 0⟩, 4), (3, ⟨2, 0⟩, 1), (24, ⟨2, 0⟩, 3), (3, ⟨2, 0⟩, 5), (3, ⟨4, 0⟩, 2), (3, ⟨4, 0⟩, 4), (3, ⟨8, 0⟩, 1), (2, ⟨8, 0⟩, 3), (3, ⟨8, 0⟩, 5), (1, ⟨64, 0⟩, 0)]

theorem g32p_row30_pairing_46 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row30_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 3), (3, ⟨-8, 0⟩, 1), (2, ⟨-8, 0⟩, 3), (3, ⟨-8, 0⟩, 5), (24, ⟨-4, 0⟩, 0), (3, ⟨-4, 0⟩, 2), (3, ⟨-4, 0⟩, 4), (3, ⟨-2, 0⟩, 1), (3, ⟨-2, 0⟩, 5), (18, ⟨-1, 0⟩, 2), (18, ⟨-1, 0⟩, 4), (18, ⟨1, 0⟩, 1), (18, ⟨1, 0⟩, 5), (3, ⟨2, 0⟩, 2), (3, ⟨2, 0⟩, 4), (3, ⟨4, 0⟩, 1), (24, ⟨4, 0⟩, 3), (3, ⟨4, 0⟩, 5), (2, ⟨8, 0⟩, 0), (3, ⟨8, 0⟩, 2), (3, ⟨8, 0⟩, 4), (1, ⟨80, 0⟩, 0)]

theorem g32p_row30_pairing_47 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 6 g32p_row30_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row30_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 30 ∧ g32SparseVec v.coords =
        (![0, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨30, -1, [(2, 1), (3, -1), (4, 1), (27, 1), (28, -1), (29, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row31_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-1, -2⟩, 0), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 3), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (1, ⟨1, 2⟩, 0), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 3), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5)]

theorem g32p_row31_pairing_0 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row31_pairing_1 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 0), (1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨4, 8⟩, 0)]

theorem g32p_row31_pairing_2 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 0), (1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨4, 8⟩, 0)]

theorem g32p_row31_pairing_3 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-2, -4⟩, 5), (3, ⟨2, 4⟩, 1)]

theorem g32p_row31_pairing_4 :
    g32p_cyclotomicPairingCheck 18 (-1)
      (g32p_pairingCoefficients 6 g32p_row31_terms_4)
      [1, -1, 1] [18, 24, 6, -6, -12, -12] = true := by
  decide +kernel

def g32p_row31_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 0), (1, ⟨-3, -6⟩, 3), (1, ⟨-2, -4⟩, 5), (2, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 4), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (2, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 1), (1, ⟨3, 6⟩, 3), (1, ⟨5, 10⟩, 0)]

theorem g32p_row31_pairing_5 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 0), (1, ⟨-3, -6⟩, 3), (1, ⟨-2, -4⟩, 1), (1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 4), (2, ⟨-1, -2⟩, 5), (2, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 3), (1, ⟨5, 10⟩, 0)]

theorem g32p_row31_pairing_6 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-2, -4⟩, 3), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 3), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨6, 12⟩, 0)]

theorem g32p_row31_pairing_7 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row31_pairing_8 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 0), (1, ⟨-2, -4⟩, 3), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 3), (1, ⟨10, 20⟩, 0)]

theorem g32p_row31_pairing_9 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 0), (1, ⟨-2, -4⟩, 3), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 3), (1, ⟨10, 20⟩, 0)]

theorem g32p_row31_pairing_10 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 0), (1, ⟨-7, -14⟩, 3), (1, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 5), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 5), (1, ⟨7, 14⟩, 3), (1, ⟨15, 30⟩, 0)]

theorem g32p_row31_pairing_11 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_11)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 0), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 3), (1, ⟨-1, -2⟩, 5), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 3), (1, ⟨1, 2⟩, 5), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨15, 30⟩, 0)]

theorem g32p_row31_pairing_12 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row31_pairing_13 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row31_pairing_14 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 0)]

theorem g32p_row31_pairing_15 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4), (1, ⟨20, 40⟩, 0)]

theorem g32p_row31_pairing_16 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 0)]

theorem g32p_row31_pairing_17 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4), (1, ⟨20, 40⟩, 0)]

theorem g32p_row31_pairing_18 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 0)]

theorem g32p_row31_pairing_19 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 4), (1, ⟨-4, -8⟩, 3), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨4, 8⟩, 3), (1, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨20, 40⟩, 0)]

theorem g32p_row31_pairing_20 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 0), (1, ⟨-8, -16⟩, 3), (1, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 5), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 5), (1, ⟨8, 16⟩, 3), (1, ⟨24, 48⟩, 0)]

theorem g32p_row31_pairing_21 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-2, -4⟩, 1), (3, ⟨2, 4⟩, 5)]

theorem g32p_row31_pairing_22 :
    g32p_cyclotomicPairingCheck 18 (1)
      (g32p_pairingCoefficients 6 g32p_row31_terms_22)
      [1, -1, 1] [-18, -24, -6, 6, 12, 12] = true := by
  decide +kernel

def g32p_row31_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (1, ⟨-6, -12⟩, 3), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-2, -4⟩, 5), (2, ⟨-1, -2⟩, 1), (2, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 1), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨6, 12⟩, 3), (1, ⟨30, 60⟩, 0)]

theorem g32p_row31_pairing_23 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_23)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (1, ⟨-6, -12⟩, 3), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-2, -4⟩, 1), (2, ⟨-1, -2⟩, 5), (2, ⟨1, 2⟩, 1), (1, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨6, 12⟩, 3), (1, ⟨30, 60⟩, 0)]

theorem g32p_row31_pairing_24 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_24)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (1, ⟨-10, -20⟩, 3), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨10, 20⟩, 3), (1, ⟨30, 60⟩, 0)]

theorem g32p_row31_pairing_25 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row31_pairing_26 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 0), (1, ⟨36, 72⟩, 0)]

theorem g32p_row31_pairing_27 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 0), (1, ⟨36, 72⟩, 0)]

theorem g32p_row31_pairing_28 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-2, -4⟩, 5), (3, ⟨2, 4⟩, 1)]

theorem g32p_row31_pairing_29 :
    g32p_cyclotomicPairingCheck 18 (-1)
      (g32p_pairingCoefficients 6 g32p_row31_terms_29)
      [1, -1, 1] [18, 24, 6, -6, -12, -12] = true := by
  decide +kernel

def g32p_row31_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 0), (1, ⟨-8, -16⟩, 3), (1, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨8, 16⟩, 3), (1, ⟨40, 80⟩, 0)]

theorem g32p_row31_pairing_30 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 0), (1, ⟨-8, -16⟩, 3), (1, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨8, 16⟩, 3), (1, ⟨40, 80⟩, 0)]

theorem g32p_row31_pairing_31 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row31_pairing_32 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 0), (1, ⟨-3, -6⟩, 3), (1, ⟨3, 6⟩, 3), (1, ⟨45, 90⟩, 0)]

theorem g32p_row31_pairing_33 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 0), (1, ⟨-3, -6⟩, 3), (1, ⟨3, 6⟩, 3), (1, ⟨45, 90⟩, 0)]

theorem g32p_row31_pairing_34 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row31_pairing_35 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (1, ⟨60, 120⟩, 0)]

theorem g32p_row31_pairing_36 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 4), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 4), (1, ⟨60, 120⟩, 0)]

theorem g32p_row31_pairing_37 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (1, ⟨60, 120⟩, 0)]

theorem g32p_row31_pairing_38 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (1, ⟨-4, -8⟩, 3), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨4, 8⟩, 3), (1, ⟨60, 120⟩, 0)]

theorem g32p_row31_pairing_39 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 0), (1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4), (1, ⟨64, 128⟩, 0)]

theorem g32p_row31_pairing_40 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 0), (1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4), (1, ⟨64, 128⟩, 0)]

theorem g32p_row31_pairing_41 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 0), (1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨80, 160⟩, 0)]

theorem g32p_row31_pairing_42 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 0), (1, ⟨-9, -18⟩, 3), (1, ⟨9, 18⟩, 3), (1, ⟨81, 162⟩, 0)]

theorem g32p_row31_pairing_43 :
    g32p_cyclotomicPairingCheck 18 (0)
      (g32p_pairingCoefficients 6 g32p_row31_terms_43)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row31_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨2, 0⟩, 2), (3, ⟨2, 0⟩, 4), (3, ⟨20, 0⟩, 0)]

theorem g32p_row31_pairing_44 :
    g32p_cyclotomicPairingCheck 18 (3)
      (g32p_pairingCoefficients 6 g32p_row31_terms_44)
      [1, -1, 1] [6, 6, 6] = true := by
  decide +kernel

def g32p_row31_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-6, 0⟩, 2), (3, ⟨-6, 0⟩, 4), (3, ⟨60, 0⟩, 0)]

theorem g32p_row31_pairing_45 :
    g32p_cyclotomicPairingCheck 18 (11)
      (g32p_pairingCoefficients 6 g32p_row31_terms_45)
      [1, -1, 1] [-18, -18, -18] = true := by
  decide +kernel

def g32p_row31_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨4, 0⟩, 2), (3, ⟨4, 0⟩, 4), (3, ⟨64, 0⟩, 0)]

theorem g32p_row31_pairing_46 :
    g32p_cyclotomicPairingCheck 18 (10)
      (g32p_pairingCoefficients 6 g32p_row31_terms_46)
      [1, -1, 1] [12, 12, 12] = true := by
  decide +kernel

def g32p_row31_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨2, 0⟩, 2), (3, ⟨2, 0⟩, 4), (3, ⟨80, 0⟩, 0)]

theorem g32p_row31_pairing_47 :
    g32p_cyclotomicPairingCheck 18 (13)
      (g32p_pairingCoefficients 6 g32p_row31_terms_47)
      [1, -1, 1] [6, 6, 6] = true := by
  decide +kernel

theorem g32p_row31_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 31 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         ![3, 11, 10, 13]) := by
  refine ⟨⟨31, 1, [(5, -1), (23, 1), (30, -1), (45, 1), (46, 1), (48, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end
