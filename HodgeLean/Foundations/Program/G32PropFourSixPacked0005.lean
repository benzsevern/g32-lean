import HodgeLean.Foundations.Program.G32PropFourSixPacked0003
import HodgeLean.Papers.PapersG32CertificatesDefs

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row32_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(216, ⟨-1, -2⟩, 1), (216, ⟨1, 2⟩, 2)]

theorem g32p_row32_pairing_0 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 3 g32p_row32_terms_0)
      [1, 1, 1] [-648, 432] = true := by
  decide +kernel

def g32p_row32_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row32_pairing_1 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (8, ⟨-3, -6⟩, 0), (10, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 1), (10, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row32_pairing_2 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (8, ⟨-3, -6⟩, 0), (10, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 1), (10, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row32_pairing_3 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row32_pairing_4 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (8, ⟨-3, -6⟩, 0), (32, ⟨-2, -4⟩, 1), (54, ⟨-1, -2⟩, 1), (128, ⟨-1, -2⟩, 2), (128, ⟨1, 2⟩, 1), (54, ⟨1, 2⟩, 2), (32, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (2, ⟨5, 10⟩, 2)]

theorem g32p_row32_pairing_5 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (8, ⟨-3, -6⟩, 0), (32, ⟨-2, -4⟩, 1), (54, ⟨-1, -2⟩, 1), (128, ⟨-1, -2⟩, 2), (128, ⟨1, 2⟩, 1), (54, ⟨1, 2⟩, 2), (32, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (2, ⟨5, 10⟩, 2)]

theorem g32p_row32_pairing_6 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (12, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 1), (18, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row32_pairing_7 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row32_pairing_8 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (8, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (26, ⟨-2, -4⟩, 2), (72, ⟨-1, -2⟩, 1), (72, ⟨1, 2⟩, 2), (26, ⟨2, 4⟩, 1), (8, ⟨3, 6⟩, 0), (8, ⟨5, 10⟩, 1), (2, ⟨10, 20⟩, 2)]

theorem g32p_row32_pairing_9 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (8, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (26, ⟨-2, -4⟩, 2), (72, ⟨-1, -2⟩, 1), (72, ⟨1, 2⟩, 2), (26, ⟨2, 4⟩, 1), (8, ⟨3, 6⟩, 0), (8, ⟨5, 10⟩, 1), (2, ⟨10, 20⟩, 2)]

theorem g32p_row32_pairing_10 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (42, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (108, ⟨-1, -2⟩, 1), (108, ⟨1, 2⟩, 2), (16, ⟨3, 6⟩, 1), (42, ⟨3, 6⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row32_pairing_11 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 3 g32p_row32_terms_11)
      [1, 1, 1] [-648, 432] = true := by
  decide +kernel

def g32p_row32_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (16, ⟨-6, -12⟩, 1), (12, ⟨-3, -6⟩, 1), (162, ⟨-1, -2⟩, 2), (162, ⟨1, 2⟩, 1), (12, ⟨3, 6⟩, 2), (16, ⟨6, 12⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row32_pairing_12 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row32_pairing_13 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2)]

theorem g32p_row32_pairing_14 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-7, -14⟩, 1), (8, ⟨-7, -14⟩, 2), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (8, ⟨7, 14⟩, 1), (8, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row32_pairing_15 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-6, -12⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (6, ⟨-4, -8⟩, 1), (6, ⟨-4, -8⟩, 2), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (6, ⟨4, 8⟩, 1), (6, ⟨4, 8⟩, 2), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (8, ⟨6, 12⟩, 0), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row32_pairing_16 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row32_pairing_17 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-6, -12⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (6, ⟨-4, -8⟩, 1), (6, ⟨-4, -8⟩, 2), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (6, ⟨4, 8⟩, 1), (6, ⟨4, 8⟩, 2), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (8, ⟨6, 12⟩, 0), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row32_pairing_18 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row32_pairing_19 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 1), (12, ⟨-5, -10⟩, 1), (18, ⟨-4, -8⟩, 1), (16, ⟨-2, -4⟩, 1), (36, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 2), (18, ⟨4, 8⟩, 2), (12, ⟨5, 10⟩, 2), (2, ⟨20, 40⟩, 2)]

theorem g32p_row32_pairing_20 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 3 g32p_row32_terms_20)
      [1, 1, 1] [-648, 432] = true := by
  decide +kernel

def g32p_row32_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 1), (16, ⟨-6, -12⟩, 1), (24, ⟨-3, -6⟩, 1), (24, ⟨3, 6⟩, 2), (16, ⟨6, 12⟩, 2), (2, ⟨24, 48⟩, 2)]

theorem g32p_row32_pairing_21 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 3 g32p_row32_terms_21)
      [1, 1, 1] [-648, 432] = true := by
  decide +kernel

def g32p_row32_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row32_pairing_22 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_22)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 1), (18, ⟨2, 4⟩, 2), (12, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 1), (8, ⟨9, 18⟩, 0), (2, ⟨30, 60⟩, 2)]

theorem g32p_row32_pairing_23 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_23)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 1), (18, ⟨2, 4⟩, 2), (12, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 1), (8, ⟨9, 18⟩, 0), (2, ⟨30, 60⟩, 2)]

theorem g32p_row32_pairing_24 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (52, ⟨-3, -6⟩, 1), (18, ⟨-2, -4⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 1), (18, ⟨2, 4⟩, 2), (52, ⟨3, 6⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row32_pairing_25 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 3 g32p_row32_terms_25)
      [1, 1, 1] [-648, 432] = true := by
  decide +kernel

def g32p_row32_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row32_pairing_26 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row32_pairing_27 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row32_pairing_28 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2)]

theorem g32p_row32_pairing_29 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (8, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 0), (20, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 1), (24, ⟨1, 2⟩, 2), (20, ⟨2, 4⟩, 1), (8, ⟨6, 12⟩, 0), (8, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 2)]

theorem g32p_row32_pairing_30 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (8, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 0), (20, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 1), (24, ⟨1, 2⟩, 2), (20, ⟨2, 4⟩, 1), (8, ⟨6, 12⟩, 0), (8, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 2)]

theorem g32p_row32_pairing_31 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row32_pairing_32 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (18, ⟨-3, -6⟩, 2), (108, ⟨-1, -2⟩, 1), (108, ⟨1, 2⟩, 2), (18, ⟨3, 6⟩, 1), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row32_pairing_33 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 3 g32p_row32_terms_33)
      [1, 1, 1] [-648, 432] = true := by
  decide +kernel

def g32p_row32_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (18, ⟨-3, -6⟩, 2), (108, ⟨-1, -2⟩, 1), (108, ⟨1, 2⟩, 2), (18, ⟨3, 6⟩, 1), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row32_pairing_34 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 3 g32p_row32_terms_34)
      [1, 1, 1] [-648, 432] = true := by
  decide +kernel

def g32p_row32_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row32_pairing_35 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (16, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (16, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row32_pairing_36 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (6, ⟨-6, -12⟩, 1), (6, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 1), (6, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row32_pairing_37 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (16, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (16, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row32_pairing_38 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 1), (16, ⟨-6, -12⟩, 1), (18, ⟨-4, -8⟩, 1), (36, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 1), (36, ⟨1, 2⟩, 2), (36, ⟨3, 6⟩, 1), (18, ⟨4, 8⟩, 2), (16, ⟨6, 12⟩, 2), (2, ⟨60, 120⟩, 2)]

theorem g32p_row32_pairing_39 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 3 g32p_row32_terms_39)
      [1, 1, 1] [-648, 432] = true := by
  decide +kernel

def g32p_row32_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 1), (16, ⟨-8, -16⟩, 2), (12, ⟨-4, -8⟩, 1), (24, ⟨-2, -4⟩, 2), (24, ⟨2, 4⟩, 1), (12, ⟨4, 8⟩, 2), (16, ⟨8, 16⟩, 1), (2, ⟨64, 128⟩, 2)]

theorem g32p_row32_pairing_40 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_40)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (8, ⟨-8, -16⟩, 1), (8, ⟨-8, -16⟩, 2), (6, ⟨-4, -8⟩, 1), (6, ⟨-4, -8⟩, 2), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (6, ⟨4, 8⟩, 1), (6, ⟨4, 8⟩, 2), (8, ⟨8, 16⟩, 1), (8, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 2)]

theorem g32p_row32_pairing_41 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (8, ⟨-8, -16⟩, 1), (8, ⟨-8, -16⟩, 2), (12, ⟨-4, -8⟩, 1), (12, ⟨-4, -8⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (12, ⟨4, 8⟩, 1), (12, ⟨4, 8⟩, 2), (8, ⟨8, 16⟩, 1), (8, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 1), (1, ⟨80, 160⟩, 2)]

theorem g32p_row32_pairing_42 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 1), (18, ⟨-3, -6⟩, 2), (108, ⟨-1, -2⟩, 2), (108, ⟨1, 2⟩, 1), (18, ⟨3, 6⟩, 1), (2, ⟨81, 162⟩, 2)]

theorem g32p_row32_pairing_43 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_43)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 2), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 1), (8, ⟨-7, 0⟩, 2), (18, ⟨-2, 0⟩, 0), (18, ⟨-2, 0⟩, 1), (18, ⟨-2, 0⟩, 2), (18, ⟨2, 0⟩, 0), (18, ⟨2, 0⟩, 1), (18, ⟨2, 0⟩, 2), (8, ⟨7, 0⟩, 0), (8, ⟨7, 0⟩, 1), (8, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 1), (1, ⟨20, 0⟩, 2)]

theorem g32p_row32_pairing_44 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 2), (6, ⟨-6, 0⟩, 0), (6, ⟨-6, 0⟩, 1), (6, ⟨-6, 0⟩, 2), (8, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 1), (8, ⟨-3, 0⟩, 2), (8, ⟨3, 0⟩, 0), (8, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 2), (6, ⟨6, 0⟩, 0), (6, ⟨6, 0⟩, 1), (6, ⟨6, 0⟩, 2), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 1), (1, ⟨60, 0⟩, 2)]

theorem g32p_row32_pairing_45 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 2), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 2), (6, ⟨-4, 0⟩, 0), (6, ⟨-4, 0⟩, 1), (6, ⟨-4, 0⟩, 2), (12, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 1), (12, ⟨-2, 0⟩, 2), (12, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 1), (12, ⟨2, 0⟩, 2), (6, ⟨4, 0⟩, 0), (6, ⟨4, 0⟩, 1), (6, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 1), (1, ⟨64, 0⟩, 2)]

theorem g32p_row32_pairing_46 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row32_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 2), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 2), (12, ⟨-4, 0⟩, 0), (12, ⟨-4, 0⟩, 1), (12, ⟨-4, 0⟩, 2), (6, ⟨-2, 0⟩, 0), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 2), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 1), (6, ⟨2, 0⟩, 2), (12, ⟨4, 0⟩, 0), (12, ⟨4, 0⟩, 1), (12, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 1), (1, ⟨80, 0⟩, 2)]

theorem g32p_row32_pairing_47 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 3 g32p_row32_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row32_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 32 ∧ g32SparseVec v.coords =
        (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨32, -1, [(1, 1), (12, 1), (21, 1), (22, 1), (26, 1), (34, 1), (35, 1), (40, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row33_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(48, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2)]

theorem g32p_row33_pairing_0 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2)]

theorem g32p_row33_pairing_1 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (2, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (46, ⟨-1, -2⟩, 0), (20, ⟨-1, -2⟩, 1), (20, ⟨-1, -2⟩, 2), (46, ⟨1, 2⟩, 0), (20, ⟨1, 2⟩, 1), (20, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row33_pairing_2 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (2, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (24, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (28, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (28, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row33_pairing_3 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2)]

theorem g32p_row33_pairing_4 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (2, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (24, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 2)]

theorem g32p_row33_pairing_5 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (2, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (46, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (46, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (2, ⟨5, 10⟩, 2)]

theorem g32p_row33_pairing_6 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (16, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (20, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (40, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (40, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row33_pairing_7 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(20, ⟨-3, -6⟩, 0), (20, ⟨-3, -6⟩, 1), (20, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (20, ⟨3, 6⟩, 0), (20, ⟨3, 6⟩, 1), (20, ⟨3, 6⟩, 2)]

theorem g32p_row33_pairing_8 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (8, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 2), (4, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 2), (24, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (52, ⟨-1, -2⟩, 0), (28, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (52, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 1), (8, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 1), (2, ⟨10, 20⟩, 2)]

theorem g32p_row33_pairing_9 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (8, ⟨-5, -10⟩, 1), (2, ⟨-5, -10⟩, 2), (4, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (16, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (44, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (44, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 1), (8, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 2)]

theorem g32p_row33_pairing_10 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row33_terms_10)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row33_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (2, ⟨-7, -14⟩, 1), (16, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (16, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (52, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (52, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (2, ⟨7, 14⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row33_pairing_11 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_11)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (8, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (2, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row33_pairing_12 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(20, ⟨-3, -6⟩, 0), (20, ⟨-3, -6⟩, 1), (20, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (20, ⟨3, 6⟩, 0), (20, ⟨3, 6⟩, 1), (20, ⟨3, 6⟩, 2)]

theorem g32p_row33_pairing_13 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 1), (10, ⟨-6, -12⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (10, ⟨6, 12⟩, 2)]

theorem g32p_row33_pairing_14 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-7, -14⟩, 0), (6, ⟨-7, -14⟩, 1), (6, ⟨-7, -14⟩, 2), (8, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (14, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (8, ⟨7, 14⟩, 0), (6, ⟨7, 14⟩, 1), (6, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row33_pairing_15 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (2, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (5, ⟨-5, -10⟩, 1), (5, ⟨-5, -10⟩, 2), (8, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (2, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (32, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (32, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (14, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (5, ⟨5, 10⟩, 1), (5, ⟨5, 10⟩, 2), (2, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row33_pairing_16 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (5, ⟨-5, -10⟩, 1), (5, ⟨-5, -10⟩, 2), (4, ⟨-3, -6⟩, 0), (13, ⟨-3, -6⟩, 1), (13, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (14, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (13, ⟨3, 6⟩, 1), (13, ⟨3, 6⟩, 2), (5, ⟨5, 10⟩, 1), (5, ⟨5, 10⟩, 2), (8, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row33_pairing_17 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (2, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (8, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (8, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (2, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (31, ⟨-1, -2⟩, 1), (31, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (31, ⟨1, 2⟩, 1), (31, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (14, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (8, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (2, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row33_pairing_18 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (8, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (12, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (14, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (12, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (8, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row33_pairing_19 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 1), (8, ⟨-5, -10⟩, 0), (8, ⟨-5, -10⟩, 2), (2, ⟨-4, -8⟩, 1), (16, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (2, ⟨4, 8⟩, 2), (8, ⟨5, 10⟩, 0), (8, ⟨5, 10⟩, 1), (2, ⟨20, 40⟩, 2)]

theorem g32p_row33_pairing_20 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_20)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 1), (2, ⟨-8, -16⟩, 1), (8, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨8, 16⟩, 2), (2, ⟨24, 48⟩, 2)]

theorem g32p_row33_pairing_21 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_21)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row33_pairing_22 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_22)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (20, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (20, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row33_pairing_23 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_23)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (10, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (16, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (28, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (28, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (2, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 1), (28, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 1), (10, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row33_pairing_24 :
    g32p_cyclotomicPairingCheck 432 (2)
      (g32p_pairingCoefficients 3 g32p_row33_terms_24)
      [1, 1, 1] [-864, 576] = true := by
  decide +kernel

def g32p_row33_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-10, -20⟩, 2), (24, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (24, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (24, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (2, ⟨10, 20⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row33_pairing_25 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row33_pairing_26 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (2, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 1), (9, ⟨-9, -18⟩, 2), (2, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 1), (9, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row33_pairing_27 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (10, ⟨-9, -18⟩, 0), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (10, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (10, ⟨9, 18⟩, 0), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row33_pairing_28 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 1), (10, ⟨-6, -12⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (10, ⟨6, 12⟩, 2)]

theorem g32p_row33_pairing_29 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (8, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (2, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (26, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (26, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 2), (4, ⟨8, 16⟩, 1), (8, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 2)]

theorem g32p_row33_pairing_30 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row33_terms_30)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row33_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (8, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 2), (2, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 2), (18, ⟨-2, -4⟩, 0), (26, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (26, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 2)]

theorem g32p_row33_pairing_31 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row33_pairing_32 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (2, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (16, ⟨-9, -18⟩, 2), (2, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (2, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row33_pairing_33 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (10, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row33_pairing_34 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row33_terms_34)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row33_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row33_pairing_35 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (2, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (11, ⟨-2, -4⟩, 1), (11, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (19, ⟨-1, -2⟩, 1), (19, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (19, ⟨1, 2⟩, 1), (19, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (11, ⟨2, 4⟩, 1), (11, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row33_pairing_36 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (8, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (16, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row33_pairing_37 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (2, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 2), (16, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (15, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (15, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (15, ⟨1, 2⟩, 1), (15, ⟨1, 2⟩, 2), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row33_pairing_38 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 1), (8, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (2, ⟨-4, -8⟩, 2), (16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (8, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 1), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (2, ⟨4, 8⟩, 1), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (2, ⟨60, 120⟩, 2)]

theorem g32p_row33_pairing_39 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row33_terms_39)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row33_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 1), (8, ⟨-8, -16⟩, 0), (8, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (8, ⟨-4, -8⟩, 0), (8, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (8, ⟨4, 8⟩, 1), (8, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 1), (8, ⟨8, 16⟩, 2), (2, ⟨64, 128⟩, 2)]

theorem g32p_row33_pairing_40 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row33_terms_40)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row33_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (8, ⟨-8, -16⟩, 0), (6, ⟨-8, -16⟩, 1), (6, ⟨-8, -16⟩, 2), (8, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (8, ⟨8, 16⟩, 0), (6, ⟨8, 16⟩, 1), (6, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 2)]

theorem g32p_row33_pairing_41 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (8, ⟨-8, -16⟩, 0), (6, ⟨-8, -16⟩, 1), (6, ⟨-8, -16⟩, 2), (8, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (8, ⟨8, 16⟩, 0), (6, ⟨8, 16⟩, 1), (6, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 1), (1, ⟨80, 160⟩, 2)]

theorem g32p_row33_pairing_42 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 1), (2, ⟨-9, -18⟩, 1), (12, ⟨-3, -6⟩, 2), (12, ⟨3, 6⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨81, 162⟩, 2)]

theorem g32p_row33_pairing_43 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row33_terms_43)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row33_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 2), (10, ⟨-7, 0⟩, 0), (10, ⟨-7, 0⟩, 1), (10, ⟨-7, 0⟩, 2), (10, ⟨-3, 0⟩, 0), (10, ⟨-3, 0⟩, 1), (10, ⟨-3, 0⟩, 2), (22, ⟨-2, 0⟩, 0), (22, ⟨-2, 0⟩, 1), (22, ⟨-2, 0⟩, 2), (12, ⟨-1, 0⟩, 0), (12, ⟨-1, 0⟩, 1), (12, ⟨-1, 0⟩, 2), (12, ⟨1, 0⟩, 0), (12, ⟨1, 0⟩, 1), (12, ⟨1, 0⟩, 2), (22, ⟨2, 0⟩, 0), (22, ⟨2, 0⟩, 1), (22, ⟨2, 0⟩, 2), (10, ⟨3, 0⟩, 0), (10, ⟨3, 0⟩, 1), (10, ⟨3, 0⟩, 2), (10, ⟨7, 0⟩, 0), (10, ⟨7, 0⟩, 1), (10, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 1), (1, ⟨20, 0⟩, 2)]

theorem g32p_row33_pairing_44 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 2), (8, ⟨-6, 0⟩, 0), (8, ⟨-6, 0⟩, 1), (8, ⟨-6, 0⟩, 2), (20, ⟨-3, 0⟩, 0), (20, ⟨-3, 0⟩, 1), (20, ⟨-3, 0⟩, 2), (6, ⟨-2, 0⟩, 0), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 2), (12, ⟨-1, 0⟩, 0), (12, ⟨-1, 0⟩, 1), (12, ⟨-1, 0⟩, 2), (12, ⟨1, 0⟩, 0), (12, ⟨1, 0⟩, 1), (12, ⟨1, 0⟩, 2), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 1), (6, ⟨2, 0⟩, 2), (20, ⟨3, 0⟩, 0), (20, ⟨3, 0⟩, 1), (20, ⟨3, 0⟩, 2), (8, ⟨6, 0⟩, 0), (8, ⟨6, 0⟩, 1), (8, ⟨6, 0⟩, 2), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 1), (1, ⟨60, 0⟩, 2)]

theorem g32p_row33_pairing_45 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 2), (10, ⟨-8, 0⟩, 0), (10, ⟨-8, 0⟩, 1), (10, ⟨-8, 0⟩, 2), (8, ⟨-4, 0⟩, 0), (8, ⟨-4, 0⟩, 1), (8, ⟨-4, 0⟩, 2), (8, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (8, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (8, ⟨4, 0⟩, 0), (8, ⟨4, 0⟩, 1), (8, ⟨4, 0⟩, 2), (10, ⟨8, 0⟩, 0), (10, ⟨8, 0⟩, 1), (10, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 1), (1, ⟨64, 0⟩, 2)]

theorem g32p_row33_pairing_46 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row33_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 2), (10, ⟨-8, 0⟩, 0), (10, ⟨-8, 0⟩, 1), (10, ⟨-8, 0⟩, 2), (8, ⟨-4, 0⟩, 0), (8, ⟨-4, 0⟩, 1), (8, ⟨-4, 0⟩, 2), (8, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (8, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (8, ⟨4, 0⟩, 0), (8, ⟨4, 0⟩, 1), (8, ⟨4, 0⟩, 2), (10, ⟨8, 0⟩, 0), (10, ⟨8, 0⟩, 1), (10, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 1), (1, ⟨80, 0⟩, 2)]

theorem g32p_row33_pairing_47 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row33_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row33_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 33 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨33, -1, [(11, 1), (25, 2), (31, 1), (35, 1), (40, 1), (41, 1), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row34_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 5), (32, ⟨-1, -2⟩, 8), (32, ⟨-1, -2⟩, 11), (32, ⟨-1, -2⟩, 14), (32, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 7), (32, ⟨1, 2⟩, 10), (32, ⟨1, 2⟩, 13)]

theorem g32p_row34_pairing_0 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_0)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [0, 32, 0, 0, 0, 0, 32, 0, 0, 0, 0, -64] = true := by
  decide +kernel

def g32p_row34_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row34_pairing_1 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_1)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 5), (1, ⟨-4, -8⟩, 10), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 7), (16, ⟨-1, -2⟩, 8), (16, ⟨-1, -2⟩, 11), (16, ⟨-1, -2⟩, 13), (16, ⟨-1, -2⟩, 14), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 7), (16, ⟨1, 2⟩, 8), (16, ⟨1, 2⟩, 11), (16, ⟨1, 2⟩, 13), (16, ⟨1, 2⟩, 14), (1, ⟨4, 8⟩, 5), (1, ⟨4, 8⟩, 10)]

theorem g32p_row34_pairing_2 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_2)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 5), (1, ⟨-4, -8⟩, 10), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 7), (16, ⟨-1, -2⟩, 8), (16, ⟨-1, -2⟩, 11), (16, ⟨-1, -2⟩, 13), (16, ⟨-1, -2⟩, 14), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 7), (16, ⟨1, 2⟩, 8), (16, ⟨1, 2⟩, 11), (16, ⟨1, 2⟩, 13), (16, ⟨1, 2⟩, 14), (1, ⟨4, 8⟩, 5), (1, ⟨4, 8⟩, 10)]

theorem g32p_row34_pairing_3 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_3)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row34_pairing_4 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_4)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 5), (10, ⟨-3, -6⟩, 10), (20, ⟨-1, -2⟩, 5), (20, ⟨1, 2⟩, 10), (10, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 10)]

theorem g32p_row34_pairing_5 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_5)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 5), (10, ⟨-3, -6⟩, 10), (20, ⟨-1, -2⟩, 5), (20, ⟨1, 2⟩, 10), (10, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 10)]

theorem g32p_row34_pairing_6 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_6)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 5), (20, ⟨-2, -4⟩, 5), (10, ⟨-2, -4⟩, 10), (32, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 8), (32, ⟨-1, -2⟩, 11), (32, ⟨-1, -2⟩, 14), (32, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 7), (32, ⟨1, 2⟩, 13), (10, ⟨2, 4⟩, 5), (20, ⟨2, 4⟩, 10), (2, ⟨6, 12⟩, 10)]

theorem g32p_row34_pairing_7 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_7)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [0, 32, 0, 0, 0, 0, 32, 0, 0, 0, 0, -64] = true := by
  decide +kernel

def g32p_row34_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row34_pairing_8 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_8)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 5), (10, ⟨-2, -4⟩, 5), (20, ⟨-2, -4⟩, 10), (20, ⟨2, 4⟩, 5), (10, ⟨2, 4⟩, 10), (2, ⟨10, 20⟩, 10)]

theorem g32p_row34_pairing_9 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_9)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 5), (10, ⟨-2, -4⟩, 5), (20, ⟨-2, -4⟩, 10), (20, ⟨2, 4⟩, 5), (10, ⟨2, 4⟩, 10), (2, ⟨10, 20⟩, 10)]

theorem g32p_row34_pairing_10 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_10)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 5), (10, ⟨-7, -14⟩, 5), (20, ⟨-3, -6⟩, 5), (20, ⟨3, 6⟩, 10), (10, ⟨7, 14⟩, 10), (2, ⟨15, 30⟩, 10)]

theorem g32p_row34_pairing_11 :
    g32p_cyclotomicPairingCheck 480 (1)
      (g32p_pairingCoefficients 15 g32p_row34_terms_11)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-480, -480, -480, 0, 0, 320, 320, 320] = true := by
  decide +kernel

def g32p_row34_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 5), (30, ⟨-1, -2⟩, 10), (30, ⟨1, 2⟩, 5), (2, ⟨15, 30⟩, 10)]

theorem g32p_row34_pairing_12 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_12)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row34_pairing_13 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_13)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row34_pairing_14 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_14)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 5), (1, ⟨-20, -40⟩, 10), (1, ⟨20, 40⟩, 5), (1, ⟨20, 40⟩, 10)]

theorem g32p_row34_pairing_15 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_15)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 5), (1, ⟨-20, -40⟩, 10), (1, ⟨20, 40⟩, 5), (1, ⟨20, 40⟩, 10)]

theorem g32p_row34_pairing_16 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_16)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 5), (1, ⟨-20, -40⟩, 10), (1, ⟨20, 40⟩, 5), (1, ⟨20, 40⟩, 10)]

theorem g32p_row34_pairing_17 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_17)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 5), (1, ⟨-20, -40⟩, 10), (1, ⟨20, 40⟩, 5), (1, ⟨20, 40⟩, 10)]

theorem g32p_row34_pairing_18 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_18)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 5), (1, ⟨-20, -40⟩, 10), (1, ⟨20, 40⟩, 5), (1, ⟨20, 40⟩, 10)]

theorem g32p_row34_pairing_19 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_19)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 5), (30, ⟨-4, -8⟩, 5), (30, ⟨4, 8⟩, 10), (2, ⟨20, 40⟩, 10)]

theorem g32p_row34_pairing_20 :
    g32p_cyclotomicPairingCheck 480 (1)
      (g32p_pairingCoefficients 15 g32p_row34_terms_20)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-480, -480, -480, 0, 0, 320, 320, 320] = true := by
  decide +kernel

def g32p_row34_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 5), (10, ⟨-8, -16⟩, 5), (32, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 7), (32, ⟨-1, -2⟩, 13), (32, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 8), (32, ⟨1, 2⟩, 11), (32, ⟨1, 2⟩, 14), (10, ⟨8, 16⟩, 10), (2, ⟨24, 48⟩, 10)]

theorem g32p_row34_pairing_21 :
    g32p_cyclotomicPairingCheck 480 (1)
      (g32p_pairingCoefficients 15 g32p_row34_terms_21)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-480, -512, -480, 0, 0, 320, 288, 320, 0, 0, 0, 64] = true := by
  decide +kernel

def g32p_row34_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row34_pairing_22 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_22)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 5), (10, ⟨-6, -12⟩, 5), (20, ⟨-2, -4⟩, 5), (20, ⟨2, 4⟩, 10), (10, ⟨6, 12⟩, 10), (2, ⟨30, 60⟩, 10)]

theorem g32p_row34_pairing_23 :
    g32p_cyclotomicPairingCheck 480 (1)
      (g32p_pairingCoefficients 15 g32p_row34_terms_23)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-480, -480, -480, 0, 0, 320, 320, 320] = true := by
  decide +kernel

def g32p_row34_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 5), (10, ⟨-6, -12⟩, 5), (20, ⟨-2, -4⟩, 5), (20, ⟨2, 4⟩, 10), (10, ⟨6, 12⟩, 10), (2, ⟨30, 60⟩, 10)]

theorem g32p_row34_pairing_24 :
    g32p_cyclotomicPairingCheck 480 (1)
      (g32p_pairingCoefficients 15 g32p_row34_terms_24)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-480, -480, -480, 0, 0, 320, 320, 320] = true := by
  decide +kernel

def g32p_row34_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 5), (10, ⟨-10, -20⟩, 10), (20, ⟨-2, -4⟩, 5), (20, ⟨2, 4⟩, 10), (10, ⟨10, 20⟩, 5), (2, ⟨30, 60⟩, 10)]

theorem g32p_row34_pairing_25 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_25)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row34_pairing_26 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_26)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 5), (1, ⟨-36, -72⟩, 10), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 7), (16, ⟨-1, -2⟩, 8), (16, ⟨-1, -2⟩, 11), (16, ⟨-1, -2⟩, 13), (16, ⟨-1, -2⟩, 14), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 7), (16, ⟨1, 2⟩, 8), (16, ⟨1, 2⟩, 11), (16, ⟨1, 2⟩, 13), (16, ⟨1, 2⟩, 14), (1, ⟨36, 72⟩, 5), (1, ⟨36, 72⟩, 10)]

theorem g32p_row34_pairing_27 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_27)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 5), (1, ⟨-36, -72⟩, 10), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 7), (16, ⟨-1, -2⟩, 8), (16, ⟨-1, -2⟩, 11), (16, ⟨-1, -2⟩, 13), (16, ⟨-1, -2⟩, 14), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 7), (16, ⟨1, 2⟩, 8), (16, ⟨1, 2⟩, 11), (16, ⟨1, 2⟩, 13), (16, ⟨1, 2⟩, 14), (1, ⟨36, 72⟩, 5), (1, ⟨36, 72⟩, 10)]

theorem g32p_row34_pairing_28 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_28)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row34_pairing_29 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_29)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 5), (10, ⟨-8, -16⟩, 10), (10, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 10)]

theorem g32p_row34_pairing_30 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_30)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 5), (10, ⟨-8, -16⟩, 10), (10, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 10)]

theorem g32p_row34_pairing_31 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_31)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row34_pairing_32 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_32)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 5), (30, ⟨-3, -6⟩, 10), (30, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 10)]

theorem g32p_row34_pairing_33 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_33)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 5), (30, ⟨-3, -6⟩, 10), (30, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 10)]

theorem g32p_row34_pairing_34 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_34)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row34_pairing_35 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_35)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 5), (1, ⟨-60, -120⟩, 10), (1, ⟨60, 120⟩, 5), (1, ⟨60, 120⟩, 10)]

theorem g32p_row34_pairing_36 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_36)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 5), (1, ⟨-60, -120⟩, 10), (1, ⟨60, 120⟩, 5), (1, ⟨60, 120⟩, 10)]

theorem g32p_row34_pairing_37 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_37)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 5), (1, ⟨-60, -120⟩, 10), (1, ⟨60, 120⟩, 5), (1, ⟨60, 120⟩, 10)]

theorem g32p_row34_pairing_38 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_38)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 5), (20, ⟨-4, -8⟩, 5), (10, ⟨-4, -8⟩, 10), (10, ⟨4, 8⟩, 5), (20, ⟨4, 8⟩, 10), (2, ⟨60, 120⟩, 10)]

theorem g32p_row34_pairing_39 :
    g32p_cyclotomicPairingCheck 480 (1)
      (g32p_pairingCoefficients 15 g32p_row34_terms_39)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-480, -480, -480, 0, 0, 320, 320, 320] = true := by
  decide +kernel

def g32p_row34_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 5), (32, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 7), (32, ⟨-1, -2⟩, 13), (32, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 8), (32, ⟨1, 2⟩, 11), (32, ⟨1, 2⟩, 14), (2, ⟨64, 128⟩, 10)]

theorem g32p_row34_pairing_40 :
    g32p_cyclotomicPairingCheck 480 (1)
      (g32p_pairingCoefficients 15 g32p_row34_terms_40)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-480, -512, -480, 0, 0, 320, 288, 320, 0, 0, 0, 64] = true := by
  decide +kernel

def g32p_row34_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 5), (1, ⟨-64, -128⟩, 10), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 7), (16, ⟨-1, -2⟩, 8), (16, ⟨-1, -2⟩, 11), (16, ⟨-1, -2⟩, 13), (16, ⟨-1, -2⟩, 14), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 7), (16, ⟨1, 2⟩, 8), (16, ⟨1, 2⟩, 11), (16, ⟨1, 2⟩, 13), (16, ⟨1, 2⟩, 14), (1, ⟨64, 128⟩, 5), (1, ⟨64, 128⟩, 10)]

theorem g32p_row34_pairing_41 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_41)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 5), (1, ⟨-80, -160⟩, 10), (1, ⟨80, 160⟩, 5), (1, ⟨80, 160⟩, 10)]

theorem g32p_row34_pairing_42 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_42)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 5), (10, ⟨-9, -18⟩, 5), (20, ⟨-3, -6⟩, 10), (32, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 8), (32, ⟨-1, -2⟩, 11), (32, ⟨-1, -2⟩, 14), (32, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 7), (32, ⟨1, 2⟩, 13), (20, ⟨3, 6⟩, 5), (10, ⟨9, 18⟩, 10), (2, ⟨81, 162⟩, 10)]

theorem g32p_row34_pairing_43 :
    g32p_cyclotomicPairingCheck 480 (1)
      (g32p_pairingCoefficients 15 g32p_row34_terms_43)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-480, -448, -480, 0, 0, 320, 352, 320, 0, 0, 0, -64] = true := by
  decide +kernel

def g32p_row34_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 5), (1, ⟨-20, 0⟩, 10), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 5), (1, ⟨20, 0⟩, 10)]

theorem g32p_row34_pairing_44 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_44)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 5), (1, ⟨-60, 0⟩, 10), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 5), (1, ⟨60, 0⟩, 10)]

theorem g32p_row34_pairing_45 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_45)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 5), (1, ⟨-64, 0⟩, 10), (16, ⟨-1, 0⟩, 1), (16, ⟨-1, 0⟩, 2), (16, ⟨-1, 0⟩, 3), (16, ⟨-1, 0⟩, 4), (16, ⟨-1, 0⟩, 6), (16, ⟨-1, 0⟩, 7), (16, ⟨-1, 0⟩, 8), (16, ⟨-1, 0⟩, 9), (16, ⟨-1, 0⟩, 11), (16, ⟨-1, 0⟩, 12), (16, ⟨-1, 0⟩, 13), (16, ⟨-1, 0⟩, 14), (16, ⟨1, 0⟩, 1), (16, ⟨1, 0⟩, 2), (16, ⟨1, 0⟩, 3), (16, ⟨1, 0⟩, 4), (16, ⟨1, 0⟩, 6), (16, ⟨1, 0⟩, 7), (16, ⟨1, 0⟩, 8), (16, ⟨1, 0⟩, 9), (16, ⟨1, 0⟩, 11), (16, ⟨1, 0⟩, 12), (16, ⟨1, 0⟩, 13), (16, ⟨1, 0⟩, 14), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 5), (1, ⟨64, 0⟩, 10)]

theorem g32p_row34_pairing_46 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_46)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

def g32p_row34_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 5), (1, ⟨-80, 0⟩, 10), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 5), (1, ⟨80, 0⟩, 10)]

theorem g32p_row34_pairing_47 :
    g32p_cyclotomicPairingCheck 480 (0)
      (g32p_pairingCoefficients 15 g32p_row34_terms_47)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row34_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 34 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨34, -1, [(12, 1), (21, 1), (22, 1), (24, 1), (25, 1), (40, 1), (41, 1), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row35_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(48, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2)]

theorem g32p_row35_pairing_0 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2)]

theorem g32p_row35_pairing_1 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (8, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 0), (22, ⟨-2, -4⟩, 1), (22, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (31, ⟨-1, -2⟩, 1), (31, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (31, ⟨1, 2⟩, 1), (31, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 0), (22, ⟨2, 4⟩, 1), (22, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row35_pairing_2 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (8, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (40, ⟨-1, -2⟩, 0), (23, ⟨-1, -2⟩, 1), (23, ⟨-1, -2⟩, 2), (40, ⟨1, 2⟩, 0), (23, ⟨1, 2⟩, 1), (23, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row35_pairing_3 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2)]

theorem g32p_row35_pairing_4 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (40, ⟨-1, -2⟩, 0), (30, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (40, ⟨1, 2⟩, 0), (28, ⟨1, 2⟩, 1), (30, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (2, ⟨5, 10⟩, 2)]

theorem g32p_row35_pairing_5 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (26, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (26, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 2)]

theorem g32p_row35_pairing_6 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (10, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (24, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (20, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (28, ⟨-1, -2⟩, 1), (10, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (10, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row35_pairing_7 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(20, ⟨-3, -6⟩, 0), (20, ⟨-3, -6⟩, 1), (20, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (20, ⟨3, 6⟩, 0), (20, ⟨3, 6⟩, 1), (20, ⟨3, 6⟩, 2)]

theorem g32p_row35_pairing_8 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (2, ⟨-5, -10⟩, 1), (8, ⟨-5, -10⟩, 2), (16, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-2, -4⟩, 0), (22, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (32, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (32, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (22, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (8, ⟨5, 10⟩, 1), (2, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 2)]

theorem g32p_row35_pairing_9 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (2, ⟨-5, -10⟩, 0), (8, ⟨-5, -10⟩, 2), (16, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (24, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (46, ⟨-1, -2⟩, 0), (28, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (46, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (2, ⟨5, 10⟩, 0), (8, ⟨5, 10⟩, 1), (2, ⟨10, 20⟩, 2)]

theorem g32p_row35_pairing_10 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (2, ⟨-7, -14⟩, 1), (10, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (24, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (22, ⟨-1, -2⟩, 0), (28, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (2, ⟨7, 14⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row35_pairing_11 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_11)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (2, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (10, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (2, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (16, ⟨6, 12⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row35_pairing_12 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row35_terms_12)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row35_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(20, ⟨-3, -6⟩, 0), (20, ⟨-3, -6⟩, 1), (20, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (20, ⟨3, 6⟩, 0), (20, ⟨3, 6⟩, 1), (20, ⟨3, 6⟩, 2)]

theorem g32p_row35_pairing_13 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 1), (10, ⟨-6, -12⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (10, ⟨6, 12⟩, 2)]

theorem g32p_row35_pairing_14 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (2, ⟨-7, -14⟩, 0), (9, ⟨-7, -14⟩, 1), (9, ⟨-7, -14⟩, 2), (2, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (14, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (2, ⟨7, 14⟩, 0), (9, ⟨7, 14⟩, 1), (9, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row35_pairing_15 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (2, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (8, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (11, ⟨-2, -4⟩, 1), (11, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (28, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (28, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (11, ⟨2, 4⟩, 1), (11, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (2, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (8, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row35_pairing_16 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (2, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (18, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (14, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (18, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row35_pairing_17 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (5, ⟨-5, -10⟩, 1), (5, ⟨-5, -10⟩, 2), (8, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (11, ⟨-2, -4⟩, 1), (11, ⟨-2, -4⟩, 2), (32, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (32, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (11, ⟨2, 4⟩, 1), (11, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (5, ⟨5, 10⟩, 1), (5, ⟨5, 10⟩, 2), (8, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row35_pairing_18 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (2, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (5, ⟨-5, -10⟩, 1), (5, ⟨-5, -10⟩, 2), (16, ⟨-3, -6⟩, 0), (7, ⟨-3, -6⟩, 1), (7, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (14, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (7, ⟨3, 6⟩, 1), (7, ⟨3, 6⟩, 2), (5, ⟨5, 10⟩, 1), (5, ⟨5, 10⟩, 2), (2, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row35_pairing_19 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 1), (8, ⟨-5, -10⟩, 0), (8, ⟨-5, -10⟩, 2), (2, ⟨-4, -8⟩, 1), (4, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (2, ⟨4, 8⟩, 2), (8, ⟨5, 10⟩, 0), (8, ⟨5, 10⟩, 1), (2, ⟨20, 40⟩, 2)]

theorem g32p_row35_pairing_20 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_20)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 1), (2, ⟨-8, -16⟩, 1), (2, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (10, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (2, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (16, ⟨6, 12⟩, 2), (2, ⟨8, 16⟩, 2), (2, ⟨24, 48⟩, 2)]

theorem g32p_row35_pairing_21 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row35_terms_21)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row35_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row35_pairing_22 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_22)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (8, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (4, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (10, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (22, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 1), (22, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row35_pairing_23 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row35_terms_23)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row35_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (8, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 2), (2, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (2, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (2, ⟨-1, -2⟩, 1), (42, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (42, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row35_pairing_24 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-10, -20⟩, 2), (18, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (28, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (18, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (2, ⟨10, 20⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row35_pairing_25 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row35_pairing_26 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (10, ⟨-9, -18⟩, 0), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (10, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (10, ⟨9, 18⟩, 0), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row35_pairing_27 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (8, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (6, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (6, ⟨9, 18⟩, 1), (6, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row35_pairing_28 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 1), (10, ⟨-6, -12⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (10, ⟨6, 12⟩, 2)]

theorem g32p_row35_pairing_29 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (2, ⟨-8, -16⟩, 0), (10, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 2), (24, ⟨-2, -4⟩, 0), (26, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (24, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (26, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (2, ⟨8, 16⟩, 0), (10, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 2)]

theorem g32p_row35_pairing_30 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (2, ⟨-8, -16⟩, 1), (10, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 1), (20, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (20, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 2), (10, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 2)]

theorem g32p_row35_pairing_31 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row35_pairing_32 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (10, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row35_pairing_33 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row35_terms_33)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row35_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row35_pairing_34 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row35_terms_34)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row35_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row35_pairing_35 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (8, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 2), (10, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (15, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (15, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (15, ⟨1, 2⟩, 1), (15, ⟨1, 2⟩, 2), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row35_pairing_36 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (8, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (4, ⟨-3, -6⟩, 0), (18, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (18, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row35_pairing_37 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (8, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (2, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (2, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (14, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row35_pairing_38 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 1), (2, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (2, ⟨-4, -8⟩, 2), (16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (2, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 1), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (2, ⟨4, 8⟩, 1), (2, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (16, ⟨6, 12⟩, 2), (2, ⟨60, 120⟩, 2)]

theorem g32p_row35_pairing_39 :
    g32p_cyclotomicPairingCheck 432 (2)
      (g32p_pairingCoefficients 3 g32p_row35_terms_39)
      [1, 1, 1] [-864, 576] = true := by
  decide +kernel

def g32p_row35_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 1), (2, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (16, ⟨-8, -16⟩, 2), (8, ⟨-4, -8⟩, 0), (8, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (8, ⟨4, 8⟩, 1), (2, ⟨8, 16⟩, 0), (16, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (2, ⟨64, 128⟩, 2)]

theorem g32p_row35_pairing_40 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_40)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (2, ⟨-8, -16⟩, 0), (9, ⟨-8, -16⟩, 1), (9, ⟨-8, -16⟩, 2), (8, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (2, ⟨8, 16⟩, 0), (9, ⟨8, 16⟩, 1), (9, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 2)]

theorem g32p_row35_pairing_41 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (2, ⟨-8, -16⟩, 0), (9, ⟨-8, -16⟩, 1), (9, ⟨-8, -16⟩, 2), (8, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (2, ⟨8, 16⟩, 0), (9, ⟨8, 16⟩, 1), (9, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 1), (1, ⟨80, 160⟩, 2)]

theorem g32p_row35_pairing_42 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 1), (2, ⟨-9, -18⟩, 1), (12, ⟨-3, -6⟩, 2), (12, ⟨3, 6⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨81, 162⟩, 2)]

theorem g32p_row35_pairing_43 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row35_terms_43)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row35_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 2), (10, ⟨-7, 0⟩, 0), (10, ⟨-7, 0⟩, 1), (10, ⟨-7, 0⟩, 2), (10, ⟨-3, 0⟩, 0), (10, ⟨-3, 0⟩, 1), (10, ⟨-3, 0⟩, 2), (22, ⟨-2, 0⟩, 0), (22, ⟨-2, 0⟩, 1), (22, ⟨-2, 0⟩, 2), (12, ⟨-1, 0⟩, 0), (12, ⟨-1, 0⟩, 1), (12, ⟨-1, 0⟩, 2), (12, ⟨1, 0⟩, 0), (12, ⟨1, 0⟩, 1), (12, ⟨1, 0⟩, 2), (22, ⟨2, 0⟩, 0), (22, ⟨2, 0⟩, 1), (22, ⟨2, 0⟩, 2), (10, ⟨3, 0⟩, 0), (10, ⟨3, 0⟩, 1), (10, ⟨3, 0⟩, 2), (10, ⟨7, 0⟩, 0), (10, ⟨7, 0⟩, 1), (10, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 1), (1, ⟨20, 0⟩, 2)]

theorem g32p_row35_pairing_44 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 2), (8, ⟨-6, 0⟩, 0), (8, ⟨-6, 0⟩, 1), (8, ⟨-6, 0⟩, 2), (20, ⟨-3, 0⟩, 0), (20, ⟨-3, 0⟩, 1), (20, ⟨-3, 0⟩, 2), (6, ⟨-2, 0⟩, 0), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 2), (12, ⟨-1, 0⟩, 0), (12, ⟨-1, 0⟩, 1), (12, ⟨-1, 0⟩, 2), (12, ⟨1, 0⟩, 0), (12, ⟨1, 0⟩, 1), (12, ⟨1, 0⟩, 2), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 1), (6, ⟨2, 0⟩, 2), (20, ⟨3, 0⟩, 0), (20, ⟨3, 0⟩, 1), (20, ⟨3, 0⟩, 2), (8, ⟨6, 0⟩, 0), (8, ⟨6, 0⟩, 1), (8, ⟨6, 0⟩, 2), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 1), (1, ⟨60, 0⟩, 2)]

theorem g32p_row35_pairing_45 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 2), (10, ⟨-8, 0⟩, 0), (10, ⟨-8, 0⟩, 1), (10, ⟨-8, 0⟩, 2), (8, ⟨-4, 0⟩, 0), (8, ⟨-4, 0⟩, 1), (8, ⟨-4, 0⟩, 2), (8, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (8, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (8, ⟨4, 0⟩, 0), (8, ⟨4, 0⟩, 1), (8, ⟨4, 0⟩, 2), (10, ⟨8, 0⟩, 0), (10, ⟨8, 0⟩, 1), (10, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 1), (1, ⟨64, 0⟩, 2)]

theorem g32p_row35_pairing_46 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row35_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 2), (10, ⟨-8, 0⟩, 0), (10, ⟨-8, 0⟩, 1), (10, ⟨-8, 0⟩, 2), (8, ⟨-4, 0⟩, 0), (8, ⟨-4, 0⟩, 1), (8, ⟨-4, 0⟩, 2), (8, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (8, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (8, ⟨4, 0⟩, 0), (8, ⟨4, 0⟩, 1), (8, ⟨4, 0⟩, 2), (10, ⟨8, 0⟩, 0), (10, ⟨8, 0⟩, 1), (10, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 1), (1, ⟨80, 0⟩, 2)]

theorem g32p_row35_pairing_47 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row35_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row35_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 35 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨35, -1, [(13, 1), (22, 1), (24, 1), (34, 1), (35, 1), (40, 2), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row36_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(64, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 5), (64, ⟨1, 2⟩, 1), (64, ⟨1, 2⟩, 4)]

theorem g32p_row36_pairing_0 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_0)
      [1, -1, 1] [0, 64, 0, 64, 0, -128] = true := by
  decide +kernel

def g32p_row36_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row36_pairing_1 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row36_pairing_2 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row36_pairing_3 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row36_pairing_4 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 4), (16, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 4), (40, ⟨-1, -2⟩, 5), (40, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (28, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 5), (2, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row36_pairing_5 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 4), (16, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 4), (40, ⟨-1, -2⟩, 5), (40, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (28, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 5), (2, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row36_pairing_6 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 2), (8, ⟨-2, -4⟩, 1), (28, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (40, ⟨-2, -4⟩, 5), (40, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (28, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (2, ⟨6, 12⟩, 4)]

theorem g32p_row36_pairing_7 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_7)
      [1, -1, 1] [0, 64, 0, 64, 0, -128] = true := by
  decide +kernel

def g32p_row36_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row36_pairing_8 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (24, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (20, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (24, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 2), (10, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row36_pairing_9 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (24, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (20, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (24, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 2), (10, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row36_pairing_10 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (2, ⟨-7, -14⟩, 2), (8, ⟨-7, -14⟩, 5), (20, ⟨-3, -6⟩, 2), (24, ⟨-3, -6⟩, 5), (16, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 5), (24, ⟨3, 6⟩, 1), (20, ⟨3, 6⟩, 4), (8, ⟨7, 14⟩, 1), (2, ⟨7, 14⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row36_pairing_11 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_11)
      [1, -1, 1] [0, 128, 0, 128, 0, -256] = true := by
  decide +kernel

def g32p_row36_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (8, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 5), (48, ⟨-1, -2⟩, 1), (54, ⟨-1, -2⟩, 4), (54, ⟨1, 2⟩, 2), (48, ⟨1, 2⟩, 5), (16, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row36_pairing_12 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row36_pairing_13 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row36_pairing_14 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row36_pairing_15 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row36_pairing_16 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row36_pairing_17 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row36_pairing_18 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row36_pairing_19 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 2), (22, ⟨-4, -8⟩, 2), (32, ⟨-4, -8⟩, 5), (32, ⟨4, 8⟩, 1), (22, ⟨4, 8⟩, 4), (2, ⟨20, 40⟩, 4)]

theorem g32p_row36_pairing_20 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_20)
      [1, -1, 1] [0, 128, 0, 128, 0, -256] = true := by
  decide +kernel

def g32p_row36_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 2), (2, ⟨-8, -16⟩, 2), (8, ⟨-8, -16⟩, 5), (8, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 4), (2, ⟨24, 48⟩, 4)]

theorem g32p_row36_pairing_21 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_21)
      [1, -1, 1] [0, 64, 0, 64, 0, -128] = true := by
  decide +kernel

def g32p_row36_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row36_pairing_22 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (2, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 5), (28, ⟨-2, -4⟩, 2), (40, ⟨-2, -4⟩, 5), (40, ⟨2, 4⟩, 1), (28, ⟨2, 4⟩, 4), (8, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row36_pairing_23 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_23)
      [1, -1, 1] [0, 128, 0, 128, 0, -256] = true := by
  decide +kernel

def g32p_row36_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (2, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 5), (28, ⟨-2, -4⟩, 2), (40, ⟨-2, -4⟩, 5), (40, ⟨2, 4⟩, 1), (28, ⟨2, 4⟩, 4), (8, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row36_pairing_24 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_24)
      [1, -1, 1] [0, 128, 0, 128, 0, -256] = true := by
  decide +kernel

def g32p_row36_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (8, ⟨-10, -20⟩, 1), (2, ⟨-10, -20⟩, 4), (16, ⟨-2, -4⟩, 1), (20, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (24, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (20, ⟨2, 4⟩, 4), (16, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 2), (8, ⟨10, 20⟩, 5), (2, ⟨30, 60⟩, 4)]

theorem g32p_row36_pairing_25 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row36_terms_25)
      [1, -1, 1] [-384, -448, -128, 192, 256, 128] = true := by
  decide +kernel

def g32p_row36_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row36_pairing_26 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row36_pairing_27 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row36_pairing_28 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row36_pairing_29 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (8, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 4), (2, ⟨8, 16⟩, 2), (8, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row36_pairing_30 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row36_terms_30)
      [1, -1, 1] [-384, -448, -128, 192, 256, 128] = true := by
  decide +kernel

def g32p_row36_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (8, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 4), (2, ⟨8, 16⟩, 2), (8, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row36_pairing_31 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row36_terms_31)
      [1, -1, 1] [-384, -448, -128, 192, 256, 128] = true := by
  decide +kernel

def g32p_row36_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row36_pairing_32 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (32, ⟨-3, -6⟩, 1), (22, ⟨-3, -6⟩, 4), (40, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 1), (40, ⟨1, 2⟩, 4), (22, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row36_pairing_33 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row36_terms_33)
      [1, -1, 1] [-384, -448, -128, 192, 256, 128] = true := by
  decide +kernel

def g32p_row36_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (32, ⟨-3, -6⟩, 1), (22, ⟨-3, -6⟩, 4), (40, ⟨-1, -2⟩, 2), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 1), (40, ⟨1, 2⟩, 4), (22, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row36_pairing_34 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row36_terms_34)
      [1, -1, 1] [-384, -448, -128, 192, 256, 128] = true := by
  decide +kernel

def g32p_row36_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row36_pairing_35 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row36_pairing_36 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row36_pairing_37 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row36_pairing_38 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 2), (8, ⟨-4, -8⟩, 1), (20, ⟨-4, -8⟩, 2), (2, ⟨-4, -8⟩, 4), (24, ⟨-4, -8⟩, 5), (24, ⟨4, 8⟩, 1), (2, ⟨4, 8⟩, 2), (20, ⟨4, 8⟩, 4), (8, ⟨4, 8⟩, 5), (2, ⟨60, 120⟩, 4)]

theorem g32p_row36_pairing_39 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row36_terms_39)
      [1, -1, 1] [-384, -320, -128, 320, 256, -128] = true := by
  decide +kernel

def g32p_row36_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 2), (2, ⟨64, 128⟩, 4)]

theorem g32p_row36_pairing_40 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row36_terms_40)
      [1, -1, 1] [-384, -384, -128, 256, 256] = true := by
  decide +kernel

def g32p_row36_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 4)]

theorem g32p_row36_pairing_41 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (1, ⟨80, 160⟩, 2), (1, ⟨80, 160⟩, 4)]

theorem g32p_row36_pairing_42 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 2), (2, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 5), (40, ⟨-3, -6⟩, 1), (28, ⟨-3, -6⟩, 4), (16, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 4), (32, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 5), (28, ⟨3, 6⟩, 2), (40, ⟨3, 6⟩, 5), (8, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 4), (2, ⟨81, 162⟩, 4)]

theorem g32p_row36_pairing_43 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row36_terms_43)
      [1, -1, 1] [-384, -448, -128, 192, 256, 128] = true := by
  decide +kernel

def g32p_row36_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 4), (4, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (4, ⟨-2, 0⟩, 2), (8, ⟨-2, 0⟩, 3), (4, ⟨-2, 0⟩, 4), (8, ⟨-2, 0⟩, 5), (4, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (4, ⟨2, 0⟩, 2), (8, ⟨2, 0⟩, 3), (4, ⟨2, 0⟩, 4), (8, ⟨2, 0⟩, 5), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row36_pairing_44 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 4), (4, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (4, ⟨-2, 0⟩, 2), (8, ⟨-2, 0⟩, 3), (4, ⟨-2, 0⟩, 4), (8, ⟨-2, 0⟩, 5), (4, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (4, ⟨2, 0⟩, 2), (8, ⟨2, 0⟩, 3), (4, ⟨2, 0⟩, 4), (8, ⟨2, 0⟩, 5), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row36_pairing_45 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 4), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row36_pairing_46 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row36_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row36_pairing_47 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row36_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row36_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 36 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨36, -1, [(26, 1), (31, 1), (32, 1), (34, 1), (35, 1), (40, 1), (41, 1), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row37_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (8, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5)]

theorem g32p_row37_pairing_0 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 5)]

theorem g32p_row37_pairing_1 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (8, ⟨-1, -2⟩, 0), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (14, ⟨-1, -2⟩, 4), (14, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 0), (14, ⟨1, 2⟩, 1), (14, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2)]

theorem g32p_row37_pairing_2 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 6 g32p_row37_terms_2)
      [1, -1, 1] [144, 168, 48, -72, -96, -48] = true := by
  decide +kernel

def g32p_row37_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (10, ⟨-1, -2⟩, 1), (10, ⟨-1, -2⟩, 2), (5, ⟨-1, -2⟩, 4), (5, ⟨-1, -2⟩, 5), (5, ⟨1, 2⟩, 1), (5, ⟨1, 2⟩, 2), (10, ⟨1, 2⟩, 4), (10, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 3), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 5)]

theorem g32p_row37_pairing_3 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (1, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (1, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 4), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 5)]

theorem g32p_row37_pairing_4 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 4), (8, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (14, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (14, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (1, ⟨1, 2⟩, 1), (14, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (14, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 5)]

theorem g32p_row37_pairing_5 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_5)
      [1, -1, 1] [0, -24, 0, -24, 0, 48] = true := by
  decide +kernel

def g32p_row37_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 0), (5, ⟨-1, -2⟩, 1), (10, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (5, ⟨-1, -2⟩, 4), (10, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 0), (10, ⟨1, 2⟩, 1), (5, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (10, ⟨1, 2⟩, 4), (5, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 4)]

theorem g32p_row37_pairing_6 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 4), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4)]

theorem g32p_row37_pairing_7 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_7)
      [1, -1, 1] [0, 24, 0, 24, 0, -48] = true := by
  decide +kernel

def g32p_row37_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 3), (2, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 4), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 5), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 3), (2, ⟨3, 6⟩, 4)]

theorem g32p_row37_pairing_8 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 3), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 5), (4, ⟨-1, -2⟩, 0), (14, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (14, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (14, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (8, ⟨1, 2⟩, 4), (14, ⟨1, 2⟩, 5), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 4), (4, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 3)]

theorem g32p_row37_pairing_9 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 4), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (8, ⟨-1, -2⟩, 1), (14, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 4), (14, ⟨-1, -2⟩, 5), (14, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (14, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 5)]

theorem g32p_row37_pairing_10 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 4), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 4), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 5)]

theorem g32p_row37_pairing_11 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_11)
      [1, -1, 1] [0, -24, 0, -24, 0, 48] = true := by
  decide +kernel

def g32p_row37_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 3), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 4), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 4), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3)]

theorem g32p_row37_pairing_12 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 3), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 3), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 5)]

theorem g32p_row37_pairing_13 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (4, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5)]

theorem g32p_row37_pairing_14 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-7, -14⟩, 0), (4, ⟨-7, -14⟩, 3), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 3), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 3), (4, ⟨7, 14⟩, 0), (4, ⟨7, 14⟩, 3)]

theorem g32p_row37_pairing_15 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (4, ⟨-4, -8⟩, 4), (4, ⟨-4, -8⟩, 5), (1, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 3), (8, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5)]

theorem g32p_row37_pairing_16 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 3), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (4, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 3)]

theorem g32p_row37_pairing_17 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 5), (4, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 3), (4, ⟨-4, -8⟩, 4), (4, ⟨-4, -8⟩, 5), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (4, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 3), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2)]

theorem g32p_row37_pairing_18 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 6 g32p_row37_terms_18)
      [1, -1, 1] [144, 168, 48, -72, -96, -48] = true := by
  decide +kernel

def g32p_row37_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 3), (4, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 3), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 5), (4, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 3)]

theorem g32p_row37_pairing_19 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-5, -10⟩, 2), (4, ⟨-5, -10⟩, 5), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (4, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 4)]

theorem g32p_row37_pairing_20 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_20)
      [1, -1, 1] [0, 24, 0, 24, 0, -48] = true := by
  decide +kernel

def g32p_row37_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 3), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 4), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3)]

theorem g32p_row37_pairing_21 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 4), (4, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 3), (7, ⟨-1, -2⟩, 4), (4, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (7, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 5), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 5)]

theorem g32p_row37_pairing_22 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_22)
      [1, -1, 1] [0, -24, 0, -24, 0, 48] = true := by
  decide +kernel

def g32p_row37_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 5), (4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 3), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 3), (4, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (7, ⟨-1, -2⟩, 5), (7, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (7, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 3), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 4)]

theorem g32p_row37_pairing_23 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_23)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 4), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (7, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (7, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 5), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 5)]

theorem g32p_row37_pairing_24 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_24)
      [1, -1, 1] [0, -24, 0, -24, 0, 48] = true := by
  decide +kernel

def g32p_row37_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row37_pairing_25 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4), (1, ⟨9, 18⟩, 5)]

theorem g32p_row37_pairing_26 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 5), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2)]

theorem g32p_row37_pairing_27 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4), (1, ⟨9, 18⟩, 5)]

theorem g32p_row37_pairing_28 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 3), (1, ⟨-6, -12⟩, 4), (4, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (4, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 5)]

theorem g32p_row37_pairing_29 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 4), (8, ⟨-2, -4⟩, 0), (5, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 3), (5, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 4), (8, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 3), (5, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 5)]

theorem g32p_row37_pairing_30 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_30)
      [1, -1, 1] [0, -24, 0, -24, 0, 48] = true := by
  decide +kernel

def g32p_row37_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 3), (1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 5), (4, ⟨-2, -4⟩, 1), (5, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (5, ⟨-2, -4⟩, 5), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 4), (8, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 5), (5, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (5, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 4), (4, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 3)]

theorem g32p_row37_pairing_31 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 4), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 5)]

theorem g32p_row37_pairing_32 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 5), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 4), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 4), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 5), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 5), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 4)]

theorem g32p_row37_pairing_33 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 4), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 5)]

theorem g32p_row37_pairing_34 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 3), (7, ⟨-1, -2⟩, 4), (7, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3)]

theorem g32p_row37_pairing_35 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 6 g32p_row37_terms_35)
      [1, -1, 1] [144, 168, 48, -72, -96, -48] = true := by
  decide +kernel

def g32p_row37_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 3), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (7, ⟨-1, -2⟩, 4), (7, ⟨-1, -2⟩, 5), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 3), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2)]

theorem g32p_row37_pairing_36 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 6 g32p_row37_terms_36)
      [1, -1, 1] [144, 168, 48, -72, -96, -48] = true := by
  decide +kernel

def g32p_row37_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 4), (4, ⟨-6, -12⟩, 5), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 3), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 3), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2)]

theorem g32p_row37_pairing_37 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 6 g32p_row37_terms_37)
      [1, -1, 1] [144, 168, 48, -72, -96, -48] = true := by
  decide +kernel

def g32p_row37_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (4, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (7, ⟨1, 2⟩, 4), (7, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (1, ⟨9, 18⟩, 4), (1, ⟨9, 18⟩, 5)]

theorem g32p_row37_pairing_38 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 3), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 3), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 3), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3)]

theorem g32p_row37_pairing_39 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 3), (4, ⟨-4, -8⟩, 2), (4, ⟨-4, -8⟩, 5), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 4), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 4), (4, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 3)]

theorem g32p_row37_pairing_40 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_40)
      [1, -1, 1] [0, 24, 0, 24, 0, -48] = true := by
  decide +kernel

def g32p_row37_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 3), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨4, 8⟩, 4), (4, ⟨4, 8⟩, 5), (4, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 3)]

theorem g32p_row37_pairing_41 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 6 g32p_row37_terms_41)
      [1, -1, 1] [-144, -168, -48, 72, 96, 48] = true := by
  decide +kernel

def g32p_row37_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 3), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨4, 8⟩, 4), (4, ⟨4, 8⟩, 5), (4, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 3)]

theorem g32p_row37_pairing_42 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 6 g32p_row37_terms_42)
      [1, -1, 1] [-144, -168, -48, 72, 96, 48] = true := by
  decide +kernel

def g32p_row37_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row37_pairing_43 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_43)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 3), (8, ⟨-7, 0⟩, 0), (1, ⟨-7, 0⟩, 2), (1, ⟨-7, 0⟩, 4), (1, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 3), (1, ⟨-3, 0⟩, 4), (8, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 3), (8, ⟨-2, 0⟩, 5), (6, ⟨-1, 0⟩, 2), (6, ⟨-1, 0⟩, 4), (6, ⟨1, 0⟩, 1), (6, ⟨1, 0⟩, 5), (6, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 2), (8, ⟨2, 0⟩, 4), (8, ⟨3, 0⟩, 0), (1, ⟨3, 0⟩, 1), (1, ⟨3, 0⟩, 5), (1, ⟨7, 0⟩, 1), (8, ⟨7, 0⟩, 3), (1, ⟨7, 0⟩, 5), (1, ⟨20, 0⟩, 0)]

theorem g32p_row37_pairing_44 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 3), (4, ⟨-6, 0⟩, 2), (4, ⟨-6, 0⟩, 4), (8, ⟨-3, 0⟩, 0), (2, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 3), (2, ⟨-3, 0⟩, 4), (6, ⟨-2, 0⟩, 0), (6, ⟨-1, 0⟩, 1), (6, ⟨-1, 0⟩, 5), (6, ⟨1, 0⟩, 2), (6, ⟨1, 0⟩, 4), (6, ⟨2, 0⟩, 3), (8, ⟨3, 0⟩, 0), (2, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 3), (2, ⟨3, 0⟩, 5), (4, ⟨6, 0⟩, 1), (4, ⟨6, 0⟩, 5), (1, ⟨60, 0⟩, 0)]

theorem g32p_row37_pairing_45 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 6 g32p_row37_terms_45)
      [1, -1, 1] [-96, -72, 0, 24] = true := by
  decide +kernel

def g32p_row37_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 3), (8, ⟨-8, 0⟩, 0), (1, ⟨-8, 0⟩, 2), (1, ⟨-8, 0⟩, 4), (4, ⟨-4, 0⟩, 1), (4, ⟨-4, 0⟩, 5), (4, ⟨-2, 0⟩, 2), (4, ⟨-2, 0⟩, 4), (4, ⟨2, 0⟩, 1), (4, ⟨2, 0⟩, 5), (4, ⟨4, 0⟩, 2), (4, ⟨4, 0⟩, 4), (1, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 3), (1, ⟨8, 0⟩, 5), (1, ⟨64, 0⟩, 0)]

theorem g32p_row37_pairing_46 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row37_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row37_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 3), (1, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 3), (1, ⟨-8, 0⟩, 5), (4, ⟨-4, 0⟩, 2), (4, ⟨-4, 0⟩, 4), (4, ⟨-2, 0⟩, 1), (4, ⟨-2, 0⟩, 5), (4, ⟨2, 0⟩, 2), (4, ⟨2, 0⟩, 4), (4, ⟨4, 0⟩, 1), (4, ⟨4, 0⟩, 5), (8, ⟨8, 0⟩, 0), (1, ⟨8, 0⟩, 2), (1, ⟨8, 0⟩, 4), (1, ⟨80, 0⟩, 0)]

theorem g32p_row37_pairing_47 :
    g32p_cyclotomicPairingCheck 144 (2)
      (g32p_pairingCoefficients 6 g32p_row37_terms_47)
      [1, -1, 1] [-144, -144] = true := by
  decide +kernel

theorem g32p_row37_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 37 ∧ g32SparseVec v.coords =
        (![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 0, 0, 0, 1, 1, 0],
         ![0, 1, 0, 2]) := by
  refine ⟨⟨37, -1, [(3, -1), (19, -1), (36, -1), (37, -1), (38, -1), (42, 1), (43, 1), (46, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row38_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2)]

theorem g32p_row38_pairing_0 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2)]

theorem g32p_row38_pairing_1 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (15, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (15, ⟨1, 2⟩, 1), (15, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2)]

theorem g32p_row38_pairing_2 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (15, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (15, ⟨1, 2⟩, 1), (15, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2)]

theorem g32p_row38_pairing_3 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 1), (8, ⟨-1, -2⟩, 0), (2, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1)]

theorem g32p_row38_pairing_4 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 1), (16, ⟨-1, -2⟩, 0), (10, ⟨-1, -2⟩, 1), (20, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (20, ⟨1, 2⟩, 1), (10, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 1)]

theorem g32p_row38_pairing_5 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-3, -6⟩, 1), (16, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (28, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 2), (2, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 2)]

theorem g32p_row38_pairing_6 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 3 g32p_row38_terms_6)
      [1, 1, 1] [-144, 96] = true := by
  decide +kernel

def g32p_row38_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (8, ⟨2, 4⟩, 1), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1)]

theorem g32p_row38_pairing_7 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 3 g32p_row38_terms_7)
      [1, 1, 1] [144, -96] = true := by
  decide +kernel

def g32p_row38_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (16, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2)]

theorem g32p_row38_pairing_8 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 1), (16, ⟨-2, -4⟩, 0), (16, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (28, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (4, ⟨3, 6⟩, 2)]

theorem g32p_row38_pairing_9 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-5, -10⟩, 0), (4, ⟨-3, -6⟩, 2), (8, ⟨-1, -2⟩, 0), (28, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (4, ⟨3, 6⟩, 1), (8, ⟨5, 10⟩, 0)]

theorem g32p_row38_pairing_10 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-2, -4⟩, 1), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2)]

theorem g32p_row38_pairing_11 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 3 g32p_row38_terms_11)
      [1, 1, 1] [-144, 96] = true := by
  decide +kernel

def g32p_row38_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-1, -2⟩, 1), (8, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 1), (8, ⟨6, 12⟩, 0)]

theorem g32p_row38_pairing_12 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (16, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2)]

theorem g32p_row38_pairing_13 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (8, ⟨-2, -4⟩, 0), (5, ⟨-2, -4⟩, 1), (5, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 1), (5, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2)]

theorem g32p_row38_pairing_14 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-7, -14⟩, 0), (8, ⟨-3, -6⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨7, 14⟩, 0)]

theorem g32p_row38_pairing_15 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (8, ⟨-5, -10⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (1, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (8, ⟨5, 10⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2)]

theorem g32p_row38_pairing_16 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-5, -10⟩, 0), (8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (8, ⟨5, 10⟩, 0)]

theorem g32p_row38_pairing_17 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (1, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2)]

theorem g32p_row38_pairing_18 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-8, -16⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (8, ⟨8, 16⟩, 0)]

theorem g32p_row38_pairing_19 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-5, -10⟩, 2), (16, ⟨-2, -4⟩, 0), (8, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (8, ⟨5, 10⟩, 1)]

theorem g32p_row38_pairing_20 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 3 g32p_row38_terms_20)
      [1, 1, 1] [144, -96] = true := by
  decide +kernel

def g32p_row38_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 1), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0)]

theorem g32p_row38_pairing_21 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_21)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 2), (8, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (14, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (14, ⟨1, 2⟩, 1), (8, ⟨2, 4⟩, 1), (8, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 1)]

theorem g32p_row38_pairing_22 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 3 g32p_row38_terms_22)
      [1, 1, 1] [144, -96] = true := by
  decide +kernel

def g32p_row38_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-9, -18⟩, 1), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-1, -2⟩, 0), (14, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (14, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 2)]

theorem g32p_row38_pairing_23 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 3 g32p_row38_terms_23)
      [1, 1, 1] [-144, 96] = true := by
  decide +kernel

def g32p_row38_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-9, -18⟩, 2), (8, ⟨-6, -12⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-2, -4⟩, 0), (8, ⟨-1, -2⟩, 1), (14, ⟨-1, -2⟩, 2), (14, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (2, ⟨9, 18⟩, 1)]

theorem g32p_row38_pairing_24 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row38_pairing_25 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2)]

theorem g32p_row38_pairing_26 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2)]

theorem g32p_row38_pairing_27 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2)]

theorem g32p_row38_pairing_28 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1)]

theorem g32p_row38_pairing_29 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-8, -16⟩, 0), (2, ⟨-6, -12⟩, 2), (8, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 1), (16, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 1), (8, ⟨8, 16⟩, 0)]

theorem g32p_row38_pairing_30 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (16, ⟨-2, -4⟩, 0), (10, ⟨-2, -4⟩, 1), (16, ⟨-1, -2⟩, 1), (16, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row38_pairing_31 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 3 g32p_row38_terms_31)
      [1, 1, 1] [-144, 96] = true := by
  decide +kernel

def g32p_row38_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (12, ⟨-1, -2⟩, 1), (12, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 1)]

theorem g32p_row38_pairing_32 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (8, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 2)]

theorem g32p_row38_pairing_33 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-9, -18⟩, 2), (2, ⟨-3, -6⟩, 1), (12, ⟨-1, -2⟩, 1), (12, ⟨1, 2⟩, 2), (2, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 1)]

theorem g32p_row38_pairing_34 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2)]

theorem g32p_row38_pairing_35 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (8, ⟨-1, -2⟩, 0), (11, ⟨-1, -2⟩, 1), (11, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (11, ⟨1, 2⟩, 1), (11, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2)]

theorem g32p_row38_pairing_36 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (16, ⟨-3, -6⟩, 0), (16, ⟨3, 6⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2)]

theorem g32p_row38_pairing_37 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (8, ⟨-6, -12⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (11, ⟨-1, -2⟩, 1), (11, ⟨-1, -2⟩, 2), (11, ⟨1, 2⟩, 1), (11, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2)]

theorem g32p_row38_pairing_38 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0)]

theorem g32p_row38_pairing_39 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_39)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-8, -16⟩, 0), (8, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 1), (8, ⟨4, 8⟩, 1), (8, ⟨8, 16⟩, 0)]

theorem g32p_row38_pairing_40 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 3 g32p_row38_terms_40)
      [1, 1, 1] [144, -96] = true := by
  decide +kernel

def g32p_row38_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-8, -16⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (8, ⟨8, 16⟩, 0)]

theorem g32p_row38_pairing_41 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-8, -16⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (8, ⟨8, 16⟩, 0)]

theorem g32p_row38_pairing_42 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row38_pairing_43 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_43)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (8, ⟨-7, 0⟩, 0), (1, ⟨-7, 0⟩, 1), (1, ⟨-7, 0⟩, 2), (8, ⟨-3, 0⟩, 0), (1, ⟨-3, 0⟩, 1), (1, ⟨-3, 0⟩, 2), (6, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (6, ⟨-1, 0⟩, 1), (6, ⟨-1, 0⟩, 2), (6, ⟨1, 0⟩, 1), (6, ⟨1, 0⟩, 2), (6, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (8, ⟨3, 0⟩, 0), (1, ⟨3, 0⟩, 1), (1, ⟨3, 0⟩, 2), (8, ⟨7, 0⟩, 0), (1, ⟨7, 0⟩, 1), (1, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0)]

theorem g32p_row38_pairing_44 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (4, ⟨-6, 0⟩, 1), (4, ⟨-6, 0⟩, 2), (16, ⟨-3, 0⟩, 0), (2, ⟨-3, 0⟩, 1), (2, ⟨-3, 0⟩, 2), (6, ⟨-2, 0⟩, 0), (6, ⟨-1, 0⟩, 1), (6, ⟨-1, 0⟩, 2), (6, ⟨1, 0⟩, 1), (6, ⟨1, 0⟩, 2), (6, ⟨2, 0⟩, 0), (16, ⟨3, 0⟩, 0), (2, ⟨3, 0⟩, 1), (2, ⟨3, 0⟩, 2), (4, ⟨6, 0⟩, 1), (4, ⟨6, 0⟩, 2), (1, ⟨60, 0⟩, 0)]

theorem g32p_row38_pairing_45 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (8, ⟨-8, 0⟩, 0), (1, ⟨-8, 0⟩, 1), (1, ⟨-8, 0⟩, 2), (4, ⟨-4, 0⟩, 1), (4, ⟨-4, 0⟩, 2), (4, ⟨-2, 0⟩, 1), (4, ⟨-2, 0⟩, 2), (4, ⟨2, 0⟩, 1), (4, ⟨2, 0⟩, 2), (4, ⟨4, 0⟩, 1), (4, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (1, ⟨8, 0⟩, 1), (1, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0)]

theorem g32p_row38_pairing_46 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row38_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (8, ⟨-8, 0⟩, 0), (1, ⟨-8, 0⟩, 1), (1, ⟨-8, 0⟩, 2), (4, ⟨-4, 0⟩, 1), (4, ⟨-4, 0⟩, 2), (4, ⟨-2, 0⟩, 1), (4, ⟨-2, 0⟩, 2), (4, ⟨2, 0⟩, 1), (4, ⟨2, 0⟩, 2), (4, ⟨4, 0⟩, 1), (4, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (1, ⟨8, 0⟩, 1), (1, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0)]

theorem g32p_row38_pairing_47 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row38_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row38_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 38 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨38, -1, [(7, 1), (8, -1), (12, 1), (21, -1), (23, -1), (24, 1), (32, 1), (41, -1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row39_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (8, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5)]

theorem g32p_row39_pairing_0 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 5)]

theorem g32p_row39_pairing_1 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 5), (8, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 3), (5, ⟨-1, -2⟩, 1), (5, ⟨-1, -2⟩, 2), (10, ⟨-1, -2⟩, 4), (10, ⟨-1, -2⟩, 5), (10, ⟨1, 2⟩, 1), (10, ⟨1, 2⟩, 2), (5, ⟨1, 2⟩, 4), (5, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2)]

theorem g32p_row39_pairing_2 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (14, ⟨-1, -2⟩, 1), (14, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 0), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (14, ⟨1, 2⟩, 4), (14, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 5)]

theorem g32p_row39_pairing_3 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 6 g32p_row39_terms_3)
      [1, -1, 1] [-144, -168, -48, 72, 96, 48] = true := by
  decide +kernel

def g32p_row39_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (1, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (1, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 4), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 5)]

theorem g32p_row39_pairing_4 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 5), (8, ⟨-1, -2⟩, 0), (10, ⟨-1, -2⟩, 1), (5, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (10, ⟨-1, -2⟩, 4), (5, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 0), (5, ⟨1, 2⟩, 1), (10, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (5, ⟨1, 2⟩, 4), (10, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 4), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 5)]

theorem g32p_row39_pairing_5 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 5), (8, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 5), (1, ⟨-1, -2⟩, 1), (14, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 4), (14, ⟨-1, -2⟩, 5), (14, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (14, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 4)]

theorem g32p_row39_pairing_6 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_6)
      [1, -1, 1] [0, 24, 0, 24, 0, -48] = true := by
  decide +kernel

def g32p_row39_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 4), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 4), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 5)]

theorem g32p_row39_pairing_7 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_7)
      [1, -1, 1] [0, -24, 0, -24, 0, 48] = true := by
  decide +kernel

def g32p_row39_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 3), (2, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 4), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 5), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 3), (2, ⟨3, 6⟩, 4)]

theorem g32p_row39_pairing_8 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 5), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (14, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (14, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (14, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 4), (14, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 4)]

theorem g32p_row39_pairing_9 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 3), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 4), (4, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (14, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 4), (14, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (14, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (14, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 5), (4, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 3)]

theorem g32p_row39_pairing_10 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 4), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4)]

theorem g32p_row39_pairing_11 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_11)
      [1, -1, 1] [0, 24, 0, 24, 0, -48] = true := by
  decide +kernel

def g32p_row39_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 3), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 4), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3)]

theorem g32p_row39_pairing_12 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 3), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 3), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 5)]

theorem g32p_row39_pairing_13 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (4, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5)]

theorem g32p_row39_pairing_14 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-7, -14⟩, 0), (4, ⟨-7, -14⟩, 3), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 3), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 3), (4, ⟨7, 14⟩, 0), (4, ⟨7, 14⟩, 3)]

theorem g32p_row39_pairing_15 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (4, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 3), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (1, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 5), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (4, ⟨4, 8⟩, 4), (4, ⟨4, 8⟩, 5), (4, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 3), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5)]

theorem g32p_row39_pairing_16 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 6 g32p_row39_terms_16)
      [1, -1, 1] [-144, -168, -48, 72, 96, 48] = true := by
  decide +kernel

def g32p_row39_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 3), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 3), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 3)]

theorem g32p_row39_pairing_17 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 5), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (4, ⟨4, 8⟩, 4), (4, ⟨4, 8⟩, 5), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2)]

theorem g32p_row39_pairing_18 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 3), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 5), (4, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 3)]

theorem g32p_row39_pairing_19 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 4), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 3), (8, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 3), (4, ⟨5, 10⟩, 2), (4, ⟨5, 10⟩, 5)]

theorem g32p_row39_pairing_20 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_20)
      [1, -1, 1] [0, -24, 0, -24, 0, 48] = true := by
  decide +kernel

def g32p_row39_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 3), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 4), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 4), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3)]

theorem g32p_row39_pairing_21 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 4), (4, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 3), (7, ⟨-1, -2⟩, 4), (4, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (7, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 5), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 5)]

theorem g32p_row39_pairing_22 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_22)
      [1, -1, 1] [0, -24, 0, -24, 0, 48] = true := by
  decide +kernel

def g32p_row39_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 5), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 5), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 4), (7, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (7, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 4)]

theorem g32p_row39_pairing_23 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_23)
      [1, -1, 1] [0, 24, 0, 24, 0, -48] = true := by
  decide +kernel

def g32p_row39_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 4), (4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 3), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 3), (7, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (7, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (7, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 3), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 4), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 5)]

theorem g32p_row39_pairing_24 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_24)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row39_pairing_25 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4), (1, ⟨9, 18⟩, 5)]

theorem g32p_row39_pairing_26 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 5), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3)]

theorem g32p_row39_pairing_27 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (1, ⟨9, 18⟩, 4), (1, ⟨9, 18⟩, 5)]

theorem g32p_row39_pairing_28 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 3), (1, ⟨-6, -12⟩, 4), (4, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (4, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 5)]

theorem g32p_row39_pairing_29 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 3), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 4), (5, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (5, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (8, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 4), (4, ⟨2, 4⟩, 1), (5, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (5, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 5), (4, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 3)]

theorem g32p_row39_pairing_30 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 5), (8, ⟨-2, -4⟩, 0), (5, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 3), (5, ⟨-2, -4⟩, 5), (8, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 4), (8, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 3), (5, ⟨2, 4⟩, 4), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 4)]

theorem g32p_row39_pairing_31 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_31)
      [1, -1, 1] [0, 24, 0, 24, 0, -48] = true := by
  decide +kernel

def g32p_row39_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 4), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 5)]

theorem g32p_row39_pairing_32 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 5), (4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 4), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 4), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 5), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4)]

theorem g32p_row39_pairing_33 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 4), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 4), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 4), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 5)]

theorem g32p_row39_pairing_34 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 3), (7, ⟨-1, -2⟩, 4), (7, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3)]

theorem g32p_row39_pairing_35 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 6 g32p_row39_terms_35)
      [1, -1, 1] [144, 168, 48, -72, -96, -48] = true := by
  decide +kernel

def g32p_row39_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (7, ⟨-1, -2⟩, 4), (7, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2)]

theorem g32p_row39_pairing_36 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 3), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 3), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 5)]

theorem g32p_row39_pairing_37 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 6 g32p_row39_terms_37)
      [1, -1, 1] [-144, -168, -48, 72, 96, 48] = true := by
  decide +kernel

def g32p_row39_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 3), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 3), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (7, ⟨1, 2⟩, 4), (7, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3), (1, ⟨9, 18⟩, 4), (1, ⟨9, 18⟩, 5)]

theorem g32p_row39_pairing_38 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 6 g32p_row39_terms_38)
      [1, -1, 1] [-144, -168, -48, 72, 96, 48] = true := by
  decide +kernel

def g32p_row39_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 3), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 3), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 3), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3)]

theorem g32p_row39_pairing_39 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 3), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 4), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 4), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 5), (4, ⟨4, 8⟩, 2), (4, ⟨4, 8⟩, 5), (4, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 3)]

theorem g32p_row39_pairing_40 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_40)
      [1, -1, 1] [0, -24, 0, -24, 0, 48] = true := by
  decide +kernel

def g32p_row39_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 3), (4, ⟨-4, -8⟩, 4), (4, ⟨-4, -8⟩, 5), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (4, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 3)]

theorem g32p_row39_pairing_41 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 6 g32p_row39_terms_41)
      [1, -1, 1] [144, 168, 48, -72, -96, -48] = true := by
  decide +kernel

def g32p_row39_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 3), (4, ⟨-4, -8⟩, 4), (4, ⟨-4, -8⟩, 5), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (4, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 3)]

theorem g32p_row39_pairing_42 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 6 g32p_row39_terms_42)
      [1, -1, 1] [144, 168, 48, -72, -96, -48] = true := by
  decide +kernel

def g32p_row39_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row39_pairing_43 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_43)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 3), (8, ⟨-7, 0⟩, 0), (1, ⟨-7, 0⟩, 2), (1, ⟨-7, 0⟩, 4), (1, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 3), (1, ⟨-3, 0⟩, 4), (8, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 3), (8, ⟨-2, 0⟩, 5), (6, ⟨-1, 0⟩, 2), (6, ⟨-1, 0⟩, 4), (6, ⟨1, 0⟩, 1), (6, ⟨1, 0⟩, 5), (6, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 2), (8, ⟨2, 0⟩, 4), (8, ⟨3, 0⟩, 0), (1, ⟨3, 0⟩, 1), (1, ⟨3, 0⟩, 5), (1, ⟨7, 0⟩, 1), (8, ⟨7, 0⟩, 3), (1, ⟨7, 0⟩, 5), (1, ⟨20, 0⟩, 0)]

theorem g32p_row39_pairing_44 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 3), (4, ⟨-6, 0⟩, 2), (4, ⟨-6, 0⟩, 4), (8, ⟨-3, 0⟩, 0), (2, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 3), (2, ⟨-3, 0⟩, 4), (6, ⟨-2, 0⟩, 0), (6, ⟨-1, 0⟩, 1), (6, ⟨-1, 0⟩, 5), (6, ⟨1, 0⟩, 2), (6, ⟨1, 0⟩, 4), (6, ⟨2, 0⟩, 3), (8, ⟨3, 0⟩, 0), (2, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 3), (2, ⟨3, 0⟩, 5), (4, ⟨6, 0⟩, 1), (4, ⟨6, 0⟩, 5), (1, ⟨60, 0⟩, 0)]

theorem g32p_row39_pairing_45 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 6 g32p_row39_terms_45)
      [1, -1, 1] [-96, -72, 0, 24] = true := by
  decide +kernel

def g32p_row39_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 3), (8, ⟨-8, 0⟩, 0), (1, ⟨-8, 0⟩, 2), (1, ⟨-8, 0⟩, 4), (4, ⟨-4, 0⟩, 1), (4, ⟨-4, 0⟩, 5), (4, ⟨-2, 0⟩, 2), (4, ⟨-2, 0⟩, 4), (4, ⟨2, 0⟩, 1), (4, ⟨2, 0⟩, 5), (4, ⟨4, 0⟩, 2), (4, ⟨4, 0⟩, 4), (1, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 3), (1, ⟨8, 0⟩, 5), (1, ⟨64, 0⟩, 0)]

theorem g32p_row39_pairing_46 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row39_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row39_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 3), (1, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 3), (1, ⟨-8, 0⟩, 5), (4, ⟨-4, 0⟩, 2), (4, ⟨-4, 0⟩, 4), (4, ⟨-2, 0⟩, 1), (4, ⟨-2, 0⟩, 5), (4, ⟨2, 0⟩, 2), (4, ⟨2, 0⟩, 4), (4, ⟨4, 0⟩, 1), (4, ⟨4, 0⟩, 5), (8, ⟨8, 0⟩, 0), (1, ⟨8, 0⟩, 2), (1, ⟨8, 0⟩, 4), (1, ⟨80, 0⟩, 0)]

theorem g32p_row39_pairing_47 :
    g32p_cyclotomicPairingCheck 144 (2)
      (g32p_pairingCoefficients 6 g32p_row39_terms_47)
      [1, -1, 1] [-144, -144] = true := by
  decide +kernel

theorem g32p_row39_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 39 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 1, 0, 0, -1, -1, 0],
         ![0, 1, 0, 2]) := by
  refine ⟨⟨39, 1, [(4, 1), (17, 1), (36, -1), (38, 1), (39, 1), (42, -1), (43, -1), (46, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row40_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(48, ⟨-1, -2⟩, 1), (48, ⟨1, 2⟩, 2)]

theorem g32p_row40_pairing_0 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 3 g32p_row40_terms_0)
      [1, 1, 1] [-144, 96] = true := by
  decide +kernel

def g32p_row40_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2)]

theorem g32p_row40_pairing_1 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0)]

theorem g32p_row40_pairing_2 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0)]

theorem g32p_row40_pairing_3 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 1), (8, ⟨-1, -2⟩, 0), (2, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1)]

theorem g32p_row40_pairing_4 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (10, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (2, ⟨2, 4⟩, 1), (10, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0)]

theorem g32p_row40_pairing_5 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0)]

theorem g32p_row40_pairing_6 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 2), (10, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (10, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 1), (2, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row40_pairing_7 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (16, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2)]

theorem g32p_row40_pairing_8 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (16, ⟨-3, -6⟩, 0), (28, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (16, ⟨3, 6⟩, 0), (2, ⟨5, 10⟩, 1)]

theorem g32p_row40_pairing_9 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-3, -6⟩, 0), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0)]

theorem g32p_row40_pairing_10 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 2), (10, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (10, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 1), (2, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row40_pairing_11 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_11)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (8, ⟨-3, -6⟩, 1), (10, ⟨-2, -4⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 1), (10, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row40_pairing_12 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 3 g32p_row40_terms_12)
      [1, 1, 1] [-144, 96] = true := by
  decide +kernel

def g32p_row40_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (16, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2)]

theorem g32p_row40_pairing_13 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (8, ⟨-2, -4⟩, 0), (5, ⟨-2, -4⟩, 1), (5, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 1), (5, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2)]

theorem g32p_row40_pairing_14 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-7, -14⟩, 1), (1, ⟨-7, -14⟩, 2), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (1, ⟨7, 14⟩, 1), (1, ⟨7, 14⟩, 2)]

theorem g32p_row40_pairing_15 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (8, ⟨6, 12⟩, 0)]

theorem g32p_row40_pairing_16 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (16, ⟨-3, -6⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (1, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2)]

theorem g32p_row40_pairing_17 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (15, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (15, ⟨1, 2⟩, 1), (15, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (8, ⟨6, 12⟩, 0)]

theorem g32p_row40_pairing_18 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (16, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2)]

theorem g32p_row40_pairing_19 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-5, -10⟩, 1), (2, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (8, ⟨5, 10⟩, 2)]

theorem g32p_row40_pairing_20 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 3 g32p_row40_terms_20)
      [1, 1, 1] [-144, 96] = true := by
  decide +kernel

def g32p_row40_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (8, ⟨-3, -6⟩, 1), (10, ⟨-2, -4⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 1), (10, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row40_pairing_21 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 3 g32p_row40_terms_21)
      [1, 1, 1] [-144, 96] = true := by
  decide +kernel

def g32p_row40_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 2), (8, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (14, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (14, ⟨1, 2⟩, 1), (8, ⟨2, 4⟩, 1), (8, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 1)]

theorem g32p_row40_pairing_22 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 3 g32p_row40_terms_22)
      [1, 1, 1] [144, -96] = true := by
  decide +kernel

def g32p_row40_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (2, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 2), (2, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (2, ⟨2, 4⟩, 1), (8, ⟨3, 6⟩, 1), (2, ⟨6, 12⟩, 1), (8, ⟨9, 18⟩, 0)]

theorem g32p_row40_pairing_23 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 3 g32p_row40_terms_23)
      [1, 1, 1] [144, -96] = true := by
  decide +kernel

def g32p_row40_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (2, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨-1, -2⟩, 0), (20, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (2, ⟨1, 2⟩, 1), (20, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0)]

theorem g32p_row40_pairing_24 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(18, ⟨-3, -6⟩, 1), (12, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (18, ⟨3, 6⟩, 2)]

theorem g32p_row40_pairing_25 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 3 g32p_row40_terms_25)
      [1, 1, 1] [-144, 96] = true := by
  decide +kernel

def g32p_row40_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2)]

theorem g32p_row40_pairing_26 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-3, -6⟩, 0), (8, ⟨3, 6⟩, 0), (8, ⟨9, 18⟩, 0)]

theorem g32p_row40_pairing_27 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2)]

theorem g32p_row40_pairing_28 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1)]

theorem g32p_row40_pairing_29 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 1), (16, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0)]

theorem g32p_row40_pairing_30 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 0), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 1), (16, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (2, ⟨8, 16⟩, 1)]

theorem g32p_row40_pairing_31 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (12, ⟨-1, -2⟩, 1), (12, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 1)]

theorem g32p_row40_pairing_32 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-3, -6⟩, 0), (8, ⟨3, 6⟩, 0), (8, ⟨9, 18⟩, 0)]

theorem g32p_row40_pairing_33 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (8, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 2)]

theorem g32p_row40_pairing_34 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2)]

theorem g32p_row40_pairing_35 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (1, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0)]

theorem g32p_row40_pairing_36 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2)]

theorem g32p_row40_pairing_37 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (8, ⟨-1, -2⟩, 0), (11, ⟨-1, -2⟩, 1), (11, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (11, ⟨1, 2⟩, 1), (11, ⟨1, 2⟩, 2), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0)]

theorem g32p_row40_pairing_38 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (16, ⟨-3, -6⟩, 2), (2, ⟨-2, -4⟩, 1), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 1), (2, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 1), (2, ⟨6, 12⟩, 2)]

theorem g32p_row40_pairing_39 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 3 g32p_row40_terms_39)
      [1, 1, 1] [144, -96] = true := by
  decide +kernel

def g32p_row40_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-8, -16⟩, 2), (8, ⟨-4, -8⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 1), (8, ⟨4, 8⟩, 2), (2, ⟨8, 16⟩, 1)]

theorem g32p_row40_pairing_40 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_40)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (1, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2)]

theorem g32p_row40_pairing_41 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (1, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2)]

theorem g32p_row40_pairing_42 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row40_pairing_43 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_43)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (8, ⟨-7, 0⟩, 0), (1, ⟨-7, 0⟩, 1), (1, ⟨-7, 0⟩, 2), (8, ⟨-3, 0⟩, 0), (1, ⟨-3, 0⟩, 1), (1, ⟨-3, 0⟩, 2), (6, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (6, ⟨-1, 0⟩, 1), (6, ⟨-1, 0⟩, 2), (6, ⟨1, 0⟩, 1), (6, ⟨1, 0⟩, 2), (6, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (8, ⟨3, 0⟩, 0), (1, ⟨3, 0⟩, 1), (1, ⟨3, 0⟩, 2), (8, ⟨7, 0⟩, 0), (1, ⟨7, 0⟩, 1), (1, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0)]

theorem g32p_row40_pairing_44 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (4, ⟨-6, 0⟩, 1), (4, ⟨-6, 0⟩, 2), (16, ⟨-3, 0⟩, 0), (2, ⟨-3, 0⟩, 1), (2, ⟨-3, 0⟩, 2), (6, ⟨-2, 0⟩, 0), (6, ⟨-1, 0⟩, 1), (6, ⟨-1, 0⟩, 2), (6, ⟨1, 0⟩, 1), (6, ⟨1, 0⟩, 2), (6, ⟨2, 0⟩, 0), (16, ⟨3, 0⟩, 0), (2, ⟨3, 0⟩, 1), (2, ⟨3, 0⟩, 2), (4, ⟨6, 0⟩, 1), (4, ⟨6, 0⟩, 2), (1, ⟨60, 0⟩, 0)]

theorem g32p_row40_pairing_45 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (8, ⟨-8, 0⟩, 0), (1, ⟨-8, 0⟩, 1), (1, ⟨-8, 0⟩, 2), (4, ⟨-4, 0⟩, 1), (4, ⟨-4, 0⟩, 2), (4, ⟨-2, 0⟩, 1), (4, ⟨-2, 0⟩, 2), (4, ⟨2, 0⟩, 1), (4, ⟨2, 0⟩, 2), (4, ⟨4, 0⟩, 1), (4, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (1, ⟨8, 0⟩, 1), (1, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0)]

theorem g32p_row40_pairing_46 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row40_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (8, ⟨-8, 0⟩, 0), (1, ⟨-8, 0⟩, 1), (1, ⟨-8, 0⟩, 2), (4, ⟨-4, 0⟩, 1), (4, ⟨-4, 0⟩, 2), (4, ⟨-2, 0⟩, 1), (4, ⟨-2, 0⟩, 2), (4, ⟨2, 0⟩, 1), (4, ⟨2, 0⟩, 2), (4, ⟨4, 0⟩, 1), (4, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (1, ⟨8, 0⟩, 1), (1, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0)]

theorem g32p_row40_pairing_47 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 3 g32p_row40_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row40_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 40 ∧ g32SparseVec v.coords =
        (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨40, 1, [(1, 1), (13, 1), (21, 1), (22, 1), (23, -1), (24, -1), (26, 1), (40, -1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row41_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5)]

theorem g32p_row41_pairing_0 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3)]

theorem g32p_row41_pairing_1 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3)]

theorem g32p_row41_pairing_2 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3)]

theorem g32p_row41_pairing_3 :
    g32p_cyclotomicPairingCheck 54 (1)
      (g32p_pairingCoefficients 6 g32p_row41_terms_3)
      [1, -1, 1] [-54, -63, -18, 27, 36, 18] = true := by
  decide +kernel

def g32p_row41_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3)]

theorem g32p_row41_pairing_4 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 5), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 4), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 4), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3)]

theorem g32p_row41_pairing_5 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 5), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 4), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3)]

theorem g32p_row41_pairing_6 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_6)
      [1, -1, 1] [0, 9, 0, 9, 0, -18] = true := by
  decide +kernel

def g32p_row41_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row41_pairing_7 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3)]

theorem g32p_row41_pairing_8 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 4), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3)]

theorem g32p_row41_pairing_9 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_9)
      [1, -1, 1] [0, 9, 0, 9, 0, -18] = true := by
  decide +kernel

def g32p_row41_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3)]

theorem g32p_row41_pairing_10 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 4)]

theorem g32p_row41_pairing_11 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_11)
      [1, -1, 1] [0, 9, 0, 9, 0, -18] = true := by
  decide +kernel

def g32p_row41_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row41_pairing_12 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3)]

theorem g32p_row41_pairing_13 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3)]

theorem g32p_row41_pairing_14 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5)]

theorem g32p_row41_pairing_15 :
    g32p_cyclotomicPairingCheck 54 (1)
      (g32p_pairingCoefficients 6 g32p_row41_terms_15)
      [1, -1, 1] [-54, -63, -18, 27, 36, 18] = true := by
  decide +kernel

def g32p_row41_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (9, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3)]

theorem g32p_row41_pairing_16 :
    g32p_cyclotomicPairingCheck 54 (-1)
      (g32p_pairingCoefficients 6 g32p_row41_terms_16)
      [1, -1, 1] [54, 63, 18, -27, -36, -18] = true := by
  decide +kernel

def g32p_row41_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (3, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3)]

theorem g32p_row41_pairing_17 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3)]

theorem g32p_row41_pairing_18 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3)]

theorem g32p_row41_pairing_19 :
    g32p_cyclotomicPairingCheck 54 (1)
      (g32p_pairingCoefficients 6 g32p_row41_terms_19)
      [1, -1, 1] [-54, -63, -18, 27, 36, 18] = true := by
  decide +kernel

def g32p_row41_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5)]

theorem g32p_row41_pairing_20 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 4)]

theorem g32p_row41_pairing_21 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_21)
      [1, -1, 1] [0, 9, 0, 9, 0, -18] = true := by
  decide +kernel

def g32p_row41_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3)]

theorem g32p_row41_pairing_22 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3)]

theorem g32p_row41_pairing_23 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_23)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3)]

theorem g32p_row41_pairing_24 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_24)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 4)]

theorem g32p_row41_pairing_25 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_25)
      [1, -1, 1] [0, 9, 0, 9, 0, -18] = true := by
  decide +kernel

def g32p_row41_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3)]

theorem g32p_row41_pairing_26 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3)]

theorem g32p_row41_pairing_27 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3)]

theorem g32p_row41_pairing_28 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3)]

theorem g32p_row41_pairing_29 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 4), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3)]

theorem g32p_row41_pairing_30 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_30)
      [1, -1, 1] [0, 9, 0, 9, 0, -18] = true := by
  decide +kernel

def g32p_row41_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3)]

theorem g32p_row41_pairing_31 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3)]

theorem g32p_row41_pairing_32 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3)]

theorem g32p_row41_pairing_33 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3)]

theorem g32p_row41_pairing_34 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3)]

theorem g32p_row41_pairing_35 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3)]

theorem g32p_row41_pairing_36 :
    g32p_cyclotomicPairingCheck 54 (1)
      (g32p_pairingCoefficients 6 g32p_row41_terms_36)
      [1, -1, 1] [-54, -63, -18, 27, 36, 18] = true := by
  decide +kernel

def g32p_row41_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row41_pairing_37 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3)]

theorem g32p_row41_pairing_38 :
    g32p_cyclotomicPairingCheck 54 (1)
      (g32p_pairingCoefficients 6 g32p_row41_terms_38)
      [1, -1, 1] [-54, -63, -18, 27, 36, 18] = true := by
  decide +kernel

def g32p_row41_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 4), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 5)]

theorem g32p_row41_pairing_39 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_39)
      [1, -1, 1] [0, -9, 0, -9, 0, 18] = true := by
  decide +kernel

def g32p_row41_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 4), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 5)]

theorem g32p_row41_pairing_40 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_40)
      [1, -1, 1] [0, -9, 0, -9, 0, 18] = true := by
  decide +kernel

def g32p_row41_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2)]

theorem g32p_row41_pairing_41 :
    g32p_cyclotomicPairingCheck 54 (-1)
      (g32p_pairingCoefficients 6 g32p_row41_terms_41)
      [1, -1, 1] [54, 63, 18, -27, -36, -18] = true := by
  decide +kernel

def g32p_row41_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-4, -8⟩, 4), (3, ⟨-4, -8⟩, 5), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2)]

theorem g32p_row41_pairing_42 :
    g32p_cyclotomicPairingCheck 54 (-1)
      (g32p_pairingCoefficients 6 g32p_row41_terms_42)
      [1, -1, 1] [54, 63, 18, -27, -36, -18] = true := by
  decide +kernel

def g32p_row41_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row41_pairing_43 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_43)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 3), (2, ⟨-7, 0⟩, 0), (3, ⟨-2, 0⟩, 1), (3, ⟨-2, 0⟩, 5), (6, ⟨-1, 0⟩, 0), (6, ⟨-1, 0⟩, 2), (6, ⟨-1, 0⟩, 4), (6, ⟨1, 0⟩, 1), (6, ⟨1, 0⟩, 3), (6, ⟨1, 0⟩, 5), (3, ⟨2, 0⟩, 2), (3, ⟨2, 0⟩, 4), (2, ⟨7, 0⟩, 3), (1, ⟨20, 0⟩, 0)]

theorem g32p_row41_pairing_44 :
    g32p_cyclotomicPairingCheck 54 (0)
      (g32p_pairingCoefficients 6 g32p_row41_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row41_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 3), (2, ⟨-3, 0⟩, 0), (2, ⟨3, 0⟩, 3), (1, ⟨60, 0⟩, 0)]

theorem g32p_row41_pairing_45 :
    g32p_cyclotomicPairingCheck 54 (2)
      (g32p_pairingCoefficients 6 g32p_row41_terms_45)
      [1, -1, 1] [-54, -54] = true := by
  decide +kernel

def g32p_row41_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 3), (2, ⟨-8, 0⟩, 0), (3, ⟨-2, 0⟩, 2), (3, ⟨-2, 0⟩, 4), (6, ⟨-1, 0⟩, 1), (6, ⟨-1, 0⟩, 3), (6, ⟨-1, 0⟩, 5), (6, ⟨1, 0⟩, 0), (6, ⟨1, 0⟩, 2), (6, ⟨1, 0⟩, 4), (3, ⟨2, 0⟩, 1), (3, ⟨2, 0⟩, 5), (2, ⟨8, 0⟩, 3), (1, ⟨64, 0⟩, 0)]

theorem g32p_row41_pairing_46 :
    g32p_cyclotomicPairingCheck 54 (2)
      (g32p_pairingCoefficients 6 g32p_row41_terms_46)
      [1, -1, 1] [-54, -54] = true := by
  decide +kernel

def g32p_row41_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 3), (2, ⟨-8, 0⟩, 3), (3, ⟨-4, 0⟩, 2), (3, ⟨-4, 0⟩, 4), (6, ⟨-1, 0⟩, 0), (6, ⟨-1, 0⟩, 2), (6, ⟨-1, 0⟩, 4), (6, ⟨1, 0⟩, 1), (6, ⟨1, 0⟩, 3), (6, ⟨1, 0⟩, 5), (3, ⟨4, 0⟩, 1), (3, ⟨4, 0⟩, 5), (2, ⟨8, 0⟩, 0), (1, ⟨80, 0⟩, 0)]

theorem g32p_row41_pairing_47 :
    g32p_cyclotomicPairingCheck 54 (4)
      (g32p_pairingCoefficients 6 g32p_row41_terms_47)
      [1, -1, 1] [-126, -108, 0, 18] = true := by
  decide +kernel

theorem g32p_row41_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 41 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, -1, -1, 0],
         ![0, 2, 2, 4]) := by
  refine ⟨⟨41, 1, [(4, 1), (16, 1), (17, -1), (20, 1), (37, 1), (39, 1), (42, -1), (43, -1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row42_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(64, ⟨-1, -2⟩, 0), (64, ⟨-1, -2⟩, 1), (64, ⟨-1, -2⟩, 2), (64, ⟨1, 2⟩, 0), (64, ⟨1, 2⟩, 1), (64, ⟨1, 2⟩, 2)]

theorem g32p_row42_pairing_0 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (56, ⟨-1, -2⟩, 0), (56, ⟨-1, -2⟩, 1), (56, ⟨-1, -2⟩, 2), (56, ⟨1, 2⟩, 0), (56, ⟨1, 2⟩, 1), (56, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row42_pairing_1 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (60, ⟨-1, -2⟩, 1), (60, ⟨-1, -2⟩, 2), (60, ⟨1, 2⟩, 1), (60, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row42_pairing_2 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (20, ⟨-2, -4⟩, 1), (20, ⟨-2, -4⟩, 2), (64, ⟨-1, -2⟩, 0), (28, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (64, ⟨1, 2⟩, 0), (28, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (20, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row42_pairing_3 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (56, ⟨-1, -2⟩, 0), (56, ⟨-1, -2⟩, 1), (56, ⟨-1, -2⟩, 2), (56, ⟨1, 2⟩, 0), (56, ⟨1, 2⟩, 1), (56, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row42_pairing_4 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (10, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (64, ⟨-1, -2⟩, 0), (68, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (64, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (68, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 1), (2, ⟨5, 10⟩, 2)]

theorem g32p_row42_pairing_5 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (8, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (172, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 1), (172, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (2, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 2)]

theorem g32p_row42_pairing_6 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 3 g32p_row42_terms_6)
      [1, 1, 1] [-576, 384] = true := by
  decide +kernel

def g32p_row42_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (60, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (56, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (56, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 1), (60, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row42_pairing_7 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 3 g32p_row42_terms_7)
      [1, 1, 1] [-576, 384] = true := by
  decide +kernel

def g32p_row42_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (48, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2)]

theorem g32p_row42_pairing_8 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (8, ⟨-5, -10⟩, 1), (16, ⟨-3, -6⟩, 1), (16, ⟨-2, -4⟩, 0), (26, ⟨-2, -4⟩, 1), (36, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 1), (96, ⟨-1, -2⟩, 2), (96, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (36, ⟨2, 4⟩, 1), (26, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 2), (8, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 2)]

theorem g32p_row42_pairing_9 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (8, ⟨-5, -10⟩, 0), (16, ⟨-3, -6⟩, 2), (34, ⟨-2, -4⟩, 1), (44, ⟨-2, -4⟩, 2), (56, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (56, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 2), (44, ⟨2, 4⟩, 1), (34, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 1), (8, ⟨5, 10⟩, 0), (2, ⟨10, 20⟩, 2)]

theorem g32p_row42_pairing_10 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (2, ⟨-7, -14⟩, 1), (8, ⟨-3, -6⟩, 0), (44, ⟨-3, -6⟩, 1), (56, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (56, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (44, ⟨3, 6⟩, 2), (2, ⟨7, 14⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row42_pairing_11 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 3 g32p_row42_terms_11)
      [1, 1, 1] [-576, 384] = true := by
  decide +kernel

def g32p_row42_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 2), (24, ⟨-3, -6⟩, 1), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 2), (38, ⟨-1, -2⟩, 2), (38, ⟨1, 2⟩, 1), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (24, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (2, ⟨15, 30⟩, 2)]

theorem g32p_row42_pairing_12 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (48, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2)]

theorem g32p_row42_pairing_13 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2)]

theorem g32p_row42_pairing_14 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-7, -14⟩, 0), (4, ⟨-7, -14⟩, 1), (4, ⟨-7, -14⟩, 2), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (8, ⟨7, 14⟩, 0), (4, ⟨7, 14⟩, 1), (4, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row42_pairing_15 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (8, ⟨-5, -10⟩, 0), (16, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 2), (56, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (56, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (8, ⟨5, 10⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row42_pairing_16 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (8, ⟨-5, -10⟩, 0), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (8, ⟨5, 10⟩, 0), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row42_pairing_17 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (16, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 2), (64, ⟨-1, -2⟩, 0), (28, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (64, ⟨1, 2⟩, 0), (28, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row42_pairing_18 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-8, -16⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (12, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (12, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (8, ⟨8, 16⟩, 0), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row42_pairing_19 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 1), (38, ⟨-4, -8⟩, 1), (16, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (16, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (38, ⟨4, 8⟩, 2), (2, ⟨20, 40⟩, 2)]

theorem g32p_row42_pairing_20 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 3 g32p_row42_terms_20)
      [1, 1, 1] [-576, 384] = true := by
  decide +kernel

def g32p_row42_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 1), (2, ⟨-8, -16⟩, 1), (8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (2, ⟨8, 16⟩, 2), (2, ⟨24, 48⟩, 2)]

theorem g32p_row42_pairing_21 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_21)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (56, ⟨-1, -2⟩, 0), (56, ⟨-1, -2⟩, 1), (56, ⟨-1, -2⟩, 2), (56, ⟨1, 2⟩, 0), (56, ⟨1, 2⟩, 1), (56, ⟨1, 2⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row42_pairing_22 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_22)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (8, ⟨-9, -18⟩, 1), (10, ⟨-6, -12⟩, 1), (8, ⟨-3, -6⟩, 0), (68, ⟨-2, -4⟩, 1), (56, ⟨-1, -2⟩, 0), (56, ⟨-1, -2⟩, 1), (56, ⟨1, 2⟩, 0), (56, ⟨1, 2⟩, 2), (68, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (10, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row42_pairing_23 :
    g32p_cyclotomicPairingCheck 576 (2)
      (g32p_pairingCoefficients 3 g32p_row42_terms_23)
      [1, 1, 1] [-1152, 768] = true := by
  decide +kernel

def g32p_row42_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (60, ⟨-2, -4⟩, 1), (8, ⟨-1, -2⟩, 1), (104, ⟨-1, -2⟩, 2), (104, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (60, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 1), (8, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row42_pairing_24 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-10, -20⟩, 2), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (36, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (56, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (56, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (2, ⟨10, 20⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row42_pairing_25 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (48, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row42_pairing_26 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row42_pairing_27 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row42_pairing_28 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2)]

theorem g32p_row42_pairing_29 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (8, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 2), (8, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 2), (16, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 1), (8, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 2)]

theorem g32p_row42_pairing_30 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (8, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 1), (16, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (16, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 2), (2, ⟨8, 16⟩, 1), (8, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 2)]

theorem g32p_row42_pairing_31 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 3 g32p_row42_terms_31)
      [1, 1, 1] [-576, 384] = true := by
  decide +kernel

def g32p_row42_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (48, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row42_pairing_32 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-3, -6⟩, 0), (46, ⟨-3, -6⟩, 2), (48, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (46, ⟨3, 6⟩, 1), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row42_pairing_33 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (16, ⟨-9, -18⟩, 2), (16, ⟨-3, -6⟩, 1), (38, ⟨-3, -6⟩, 2), (120, ⟨-1, -2⟩, 1), (120, ⟨1, 2⟩, 2), (38, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (16, ⟨9, 18⟩, 1), (2, ⟨45, 90⟩, 2)]

theorem g32p_row42_pairing_34 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (56, ⟨-1, -2⟩, 0), (56, ⟨-1, -2⟩, 1), (56, ⟨-1, -2⟩, 2), (56, ⟨1, 2⟩, 0), (56, ⟨1, 2⟩, 1), (56, ⟨1, 2⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row42_pairing_35 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (16, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 2), (56, ⟨-1, -2⟩, 0), (28, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (56, ⟨1, 2⟩, 0), (28, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row42_pairing_36 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (16, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row42_pairing_37 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨-6, -12⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (56, ⟨-1, -2⟩, 1), (56, ⟨-1, -2⟩, 2), (56, ⟨1, 2⟩, 1), (56, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row42_pairing_38 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 1), (8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 2), (36, ⟨-4, -8⟩, 1), (2, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (2, ⟨4, 8⟩, 1), (36, ⟨4, 8⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (2, ⟨60, 120⟩, 2)]

theorem g32p_row42_pairing_39 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 3 g32p_row42_terms_39)
      [1, 1, 1] [-576, 384] = true := by
  decide +kernel

def g32p_row42_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 1), (8, ⟨-8, -16⟩, 0), (8, ⟨-8, -16⟩, 1), (8, ⟨8, 16⟩, 0), (8, ⟨8, 16⟩, 2), (2, ⟨64, 128⟩, 2)]

theorem g32p_row42_pairing_40 :
    g32p_cyclotomicPairingCheck 576 (1)
      (g32p_pairingCoefficients 3 g32p_row42_terms_40)
      [1, 1, 1] [-576, 384] = true := by
  decide +kernel

def g32p_row42_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (8, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (8, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 2)]

theorem g32p_row42_pairing_41 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (8, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (8, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 1), (1, ⟨80, 160⟩, 2)]

theorem g32p_row42_pairing_42 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 1), (2, ⟨-9, -18⟩, 1), (60, ⟨-3, -6⟩, 2), (60, ⟨3, 6⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨81, 162⟩, 2)]

theorem g32p_row42_pairing_43 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_43)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 2), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 1), (8, ⟨-7, 0⟩, 2), (8, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 1), (8, ⟨-3, 0⟩, 2), (12, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 1), (12, ⟨-2, 0⟩, 2), (48, ⟨-1, 0⟩, 0), (48, ⟨-1, 0⟩, 1), (48, ⟨-1, 0⟩, 2), (48, ⟨1, 0⟩, 0), (48, ⟨1, 0⟩, 1), (48, ⟨1, 0⟩, 2), (12, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 1), (12, ⟨2, 0⟩, 2), (8, ⟨3, 0⟩, 0), (8, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 2), (8, ⟨7, 0⟩, 0), (8, ⟨7, 0⟩, 1), (8, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 1), (1, ⟨20, 0⟩, 2)]

theorem g32p_row42_pairing_44 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 2), (16, ⟨-3, 0⟩, 0), (16, ⟨-3, 0⟩, 1), (16, ⟨-3, 0⟩, 2), (12, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 1), (12, ⟨-2, 0⟩, 2), (48, ⟨-1, 0⟩, 0), (48, ⟨-1, 0⟩, 1), (48, ⟨-1, 0⟩, 2), (48, ⟨1, 0⟩, 0), (48, ⟨1, 0⟩, 1), (48, ⟨1, 0⟩, 2), (12, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 1), (12, ⟨2, 0⟩, 2), (16, ⟨3, 0⟩, 0), (16, ⟨3, 0⟩, 1), (16, ⟨3, 0⟩, 2), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 1), (1, ⟨60, 0⟩, 2)]

theorem g32p_row42_pairing_45 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 2), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 2), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 1), (1, ⟨64, 0⟩, 2)]

theorem g32p_row42_pairing_46 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row42_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 2), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 2), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 1), (1, ⟨80, 0⟩, 2)]

theorem g32p_row42_pairing_47 :
    g32p_cyclotomicPairingCheck 576 (0)
      (g32p_pairingCoefficients 3 g32p_row42_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row42_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 42 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨42, 1, [(7, 1), (8, 1), (12, 1), (21, 1), (24, 2), (32, 1), (40, 1), (41, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row43_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5)]

theorem g32p_row43_pairing_0 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(5, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (5, ⟨-3, -6⟩, 3), (5, ⟨-3, -6⟩, 4), (5, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (11, ⟨-1, -2⟩, 0), (11, ⟨-1, -2⟩, 1), (11, ⟨-1, -2⟩, 2), (11, ⟨-1, -2⟩, 3), (11, ⟨-1, -2⟩, 4), (11, ⟨-1, -2⟩, 5), (11, ⟨1, 2⟩, 0), (11, ⟨1, 2⟩, 1), (11, ⟨1, 2⟩, 2), (11, ⟨1, 2⟩, 3), (11, ⟨1, 2⟩, 4), (11, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (5, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (5, ⟨3, 6⟩, 3), (5, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 5)]

theorem g32p_row43_pairing_1 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (19, ⟨-2, -4⟩, 1), (19, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (16, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 3), (5, ⟨-1, -2⟩, 4), (5, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 0), (5, ⟨1, 2⟩, 1), (5, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 3), (22, ⟨1, 2⟩, 4), (22, ⟨1, 2⟩, 5), (8, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 3), (19, ⟨2, 4⟩, 4), (19, ⟨2, 4⟩, 5), (5, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 5), (1, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 5)]

theorem g32p_row43_pairing_2 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 6 g32p_row43_terms_2)
      [1, -1, 1] [-432, -504, -144, 216, 288, 144] = true := by
  decide +kernel

def g32p_row43_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (5, ⟨-3, -6⟩, 4), (5, ⟨-3, -6⟩, 5), (18, ⟨-2, -4⟩, 0), (10, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (18, ⟨-2, -4⟩, 3), (17, ⟨-1, -2⟩, 1), (17, ⟨-1, -2⟩, 2), (26, ⟨-1, -2⟩, 4), (26, ⟨-1, -2⟩, 5), (26, ⟨1, 2⟩, 1), (26, ⟨1, 2⟩, 2), (17, ⟨1, 2⟩, 4), (17, ⟨1, 2⟩, 5), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 3), (10, ⟨2, 4⟩, 4), (10, ⟨2, 4⟩, 5), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 5)]

theorem g32p_row43_pairing_3 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(5, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (5, ⟨-3, -6⟩, 3), (5, ⟨-3, -6⟩, 4), (5, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (11, ⟨-1, -2⟩, 0), (11, ⟨-1, -2⟩, 1), (11, ⟨-1, -2⟩, 2), (11, ⟨-1, -2⟩, 3), (11, ⟨-1, -2⟩, 4), (11, ⟨-1, -2⟩, 5), (11, ⟨1, 2⟩, 0), (11, ⟨1, 2⟩, 1), (11, ⟨1, 2⟩, 2), (11, ⟨1, 2⟩, 3), (11, ⟨1, 2⟩, 4), (11, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (5, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (5, ⟨3, 6⟩, 3), (5, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 5)]

theorem g32p_row43_pairing_4 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (5, ⟨-3, -6⟩, 5), (10, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (10, ⟨-2, -4⟩, 3), (12, ⟨-2, -4⟩, 5), (8, ⟨-1, -2⟩, 0), (5, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (5, ⟨-1, -2⟩, 4), (36, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (5, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (36, ⟨1, 2⟩, 4), (5, ⟨1, 2⟩, 5), (10, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (10, ⟨2, 4⟩, 3), (12, ⟨2, 4⟩, 4), (5, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (5, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 5), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 4)]

theorem g32p_row43_pairing_5 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_5)
      [1, -1, 1] [0, 72, 0, 72, 0, -144] = true := by
  decide +kernel

def g32p_row43_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 5), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 4), (9, ⟨-2, -4⟩, 1), (13, ⟨-2, -4⟩, 2), (9, ⟨-2, -4⟩, 4), (13, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (10, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (10, ⟨-1, -2⟩, 4), (15, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (15, ⟨1, 2⟩, 1), (10, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (15, ⟨1, 2⟩, 4), (10, ⟨1, 2⟩, 5), (13, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (13, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (6, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 5), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 4)]

theorem g32p_row43_pairing_6 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 5), (9, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (9, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (5, ⟨-3, -6⟩, 5), (9, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (9, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (15, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (15, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (15, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (15, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (9, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (9, ⟨3, 6⟩, 3), (5, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 4)]

theorem g32p_row43_pairing_7 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (10, ⟨-3, -6⟩, 3), (10, ⟨-3, -6⟩, 4), (10, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (10, ⟨3, 6⟩, 3), (10, ⟨3, 6⟩, 4), (10, ⟨3, 6⟩, 5)]

theorem g32p_row43_pairing_8 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 2), (1, ⟨-10, -20⟩, 5), (5, ⟨-5, -10⟩, 0), (5, ⟨-5, -10⟩, 3), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 4), (5, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (5, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (19, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (19, ⟨-1, -2⟩, 3), (12, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (19, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (19, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (12, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 1), (5, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (5, ⟨2, 4⟩, 5), (10, ⟨3, 6⟩, 2), (10, ⟨3, 6⟩, 5), (5, ⟨5, 10⟩, 0), (5, ⟨5, 10⟩, 3), (1, ⟨10, 20⟩, 1), (1, ⟨10, 20⟩, 4)]

theorem g32p_row43_pairing_9 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 2), (1, ⟨-10, -20⟩, 5), (5, ⟨-5, -10⟩, 2), (5, ⟨-5, -10⟩, 5), (10, ⟨-3, -6⟩, 2), (10, ⟨-3, -6⟩, 5), (10, ⟨-2, -4⟩, 0), (7, ⟨-2, -4⟩, 2), (10, ⟨-2, -4⟩, 3), (7, ⟨-2, -4⟩, 5), (8, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (17, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (17, ⟨-1, -2⟩, 5), (8, ⟨1, 2⟩, 0), (17, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 3), (17, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (10, ⟨2, 4⟩, 0), (7, ⟨2, 4⟩, 1), (10, ⟨2, 4⟩, 3), (7, ⟨2, 4⟩, 4), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 4), (5, ⟨5, 10⟩, 1), (5, ⟨5, 10⟩, 4), (1, ⟨10, 20⟩, 1), (1, ⟨10, 20⟩, 4)]

theorem g32p_row43_pairing_10 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_10)
      [1, -1, 1] [0, 72, 0, 72, 0, -144] = true := by
  decide +kernel

def g32p_row43_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 2), (1, ⟨-15, -30⟩, 5), (1, ⟨-7, -14⟩, 2), (1, ⟨-7, -14⟩, 5), (5, ⟨-3, -6⟩, 0), (13, ⟨-3, -6⟩, 2), (5, ⟨-3, -6⟩, 3), (13, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 5), (11, ⟨-1, -2⟩, 0), (11, ⟨-1, -2⟩, 1), (14, ⟨-1, -2⟩, 2), (11, ⟨-1, -2⟩, 3), (11, ⟨-1, -2⟩, 4), (14, ⟨-1, -2⟩, 5), (11, ⟨1, 2⟩, 0), (14, ⟨1, 2⟩, 1), (11, ⟨1, 2⟩, 2), (11, ⟨1, 2⟩, 3), (14, ⟨1, 2⟩, 4), (11, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (5, ⟨3, 6⟩, 0), (13, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 3), (13, ⟨3, 6⟩, 4), (1, ⟨7, 14⟩, 1), (1, ⟨7, 14⟩, 4), (1, ⟨15, 30⟩, 1), (1, ⟨15, 30⟩, 4)]

theorem g32p_row43_pairing_11 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_11)
      [1, -1, 1] [0, 72, 0, 72, 0, -144] = true := by
  decide +kernel

def g32p_row43_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 2), (1, ⟨-15, -30⟩, 5), (5, ⟨-6, -12⟩, 0), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 3), (5, ⟨-6, -12⟩, 4), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (6, ⟨-3, -6⟩, 5), (5, ⟨-2, -4⟩, 0), (5, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (5, ⟨-2, -4⟩, 3), (5, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (1, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (1, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (5, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (5, ⟨2, 4⟩, 2), (5, ⟨2, 4⟩, 3), (8, ⟨2, 4⟩, 4), (5, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (6, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5), (5, ⟨6, 12⟩, 0), (5, ⟨6, 12⟩, 2), (5, ⟨6, 12⟩, 3), (5, ⟨6, 12⟩, 5), (1, ⟨15, 30⟩, 1), (1, ⟨15, 30⟩, 4)]

theorem g32p_row43_pairing_12 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (10, ⟨-3, -6⟩, 3), (10, ⟨-3, -6⟩, 4), (10, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (10, ⟨3, 6⟩, 3), (10, ⟨3, 6⟩, 4), (10, ⟨3, 6⟩, 5)]

theorem g32p_row43_pairing_13 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(5, ⟨-6, -12⟩, 0), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 2), (5, ⟨-6, -12⟩, 3), (5, ⟨-6, -12⟩, 4), (5, ⟨-6, -12⟩, 5), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (9, ⟨-2, -4⟩, 3), (9, ⟨-2, -4⟩, 4), (9, ⟨-2, -4⟩, 5), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (9, ⟨2, 4⟩, 3), (9, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (5, ⟨6, 12⟩, 0), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 2), (5, ⟨6, 12⟩, 3), (5, ⟨6, 12⟩, 4), (5, ⟨6, 12⟩, 5)]

theorem g32p_row43_pairing_14 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (5, ⟨-7, -14⟩, 0), (5, ⟨-7, -14⟩, 1), (5, ⟨-7, -14⟩, 2), (5, ⟨-7, -14⟩, 3), (5, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (5, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (14, ⟨2, 4⟩, 4), (14, ⟨2, 4⟩, 5), (5, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (5, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 5), (5, ⟨7, 14⟩, 0), (5, ⟨7, 14⟩, 3), (5, ⟨7, 14⟩, 4), (5, ⟨7, 14⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row43_pairing_15 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 6 g32p_row43_terms_15)
      [1, -1, 1] [-432, -504, -144, 216, 288, 144] = true := by
  decide +kernel

def g32p_row43_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (5, ⟨-6, -12⟩, 4), (5, ⟨-6, -12⟩, 5), (5, ⟨-5, -10⟩, 4), (5, ⟨-5, -10⟩, 5), (4, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (4, ⟨-4, -8⟩, 3), (4, ⟨-2, -4⟩, 0), (10, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (16, ⟨-1, -2⟩, 0), (14, ⟨-1, -2⟩, 1), (14, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 3), (13, ⟨-1, -2⟩, 4), (13, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 0), (13, ⟨1, 2⟩, 1), (13, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 3), (14, ⟨1, 2⟩, 4), (14, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (10, ⟨2, 4⟩, 4), (10, ⟨2, 4⟩, 5), (4, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 3), (4, ⟨4, 8⟩, 4), (4, ⟨4, 8⟩, 5), (5, ⟨5, 10⟩, 1), (5, ⟨5, 10⟩, 2), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row43_pairing_16 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (5, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 3), (5, ⟨-5, -10⟩, 4), (5, ⟨-5, -10⟩, 5), (7, ⟨-3, -6⟩, 1), (7, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (8, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (12, ⟨-1, -2⟩, 4), (12, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (14, ⟨2, 4⟩, 4), (14, ⟨2, 4⟩, 5), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (7, ⟨3, 6⟩, 4), (7, ⟨3, 6⟩, 5), (5, ⟨5, 10⟩, 1), (5, ⟨5, 10⟩, 2), (5, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 3), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row43_pairing_17 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 2), (5, ⟨-5, -10⟩, 0), (5, ⟨-5, -10⟩, 3), (4, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (4, ⟨-4, -8⟩, 3), (4, ⟨-2, -4⟩, 0), (7, ⟨-2, -4⟩, 1), (7, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (11, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (11, ⟨-1, -2⟩, 3), (16, ⟨-1, -2⟩, 4), (16, ⟨-1, -2⟩, 5), (11, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (11, ⟨1, 2⟩, 3), (16, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (7, ⟨2, 4⟩, 4), (7, ⟨2, 4⟩, 5), (4, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 3), (4, ⟨4, 8⟩, 4), (4, ⟨4, 8⟩, 5), (5, ⟨5, 10⟩, 0), (5, ⟨5, 10⟩, 3), (5, ⟨6, 12⟩, 4), (5, ⟨6, 12⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row43_pairing_18 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 6 g32p_row43_terms_18)
      [1, -1, 1] [-432, -504, -144, 216, 288, 144] = true := by
  decide +kernel

def g32p_row43_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (5, ⟨-8, -16⟩, 4), (5, ⟨-8, -16⟩, 5), (5, ⟨-5, -10⟩, 0), (5, ⟨-5, -10⟩, 3), (5, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (5, ⟨-3, -6⟩, 3), (6, ⟨-3, -6⟩, 4), (6, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (14, ⟨2, 4⟩, 4), (14, ⟨2, 4⟩, 5), (5, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (5, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5), (5, ⟨5, 10⟩, 0), (5, ⟨5, 10⟩, 3), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row43_pairing_19 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 5), (4, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 3), (4, ⟨-5, -10⟩, 4), (1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 5), (10, ⟨-2, -4⟩, 0), (5, ⟨-2, -4⟩, 1), (5, ⟨-2, -4⟩, 2), (10, ⟨-2, -4⟩, 3), (5, ⟨-2, -4⟩, 4), (5, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (12, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (8, ⟨1, 2⟩, 4), (12, ⟨1, 2⟩, 5), (10, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 1), (5, ⟨2, 4⟩, 2), (10, ⟨2, 4⟩, 3), (5, ⟨2, 4⟩, 4), (5, ⟨2, 4⟩, 5), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 4), (4, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 2), (4, ⟨5, 10⟩, 3), (4, ⟨5, 10⟩, 5), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 4)]

theorem g32p_row43_pairing_20 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 2), (1, ⟨-24, -48⟩, 5), (1, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 5), (5, ⟨-6, -12⟩, 0), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 3), (5, ⟨-6, -12⟩, 4), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 5), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 3), (9, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 4), (8, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 5), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 2), (9, ⟨2, 4⟩, 3), (9, ⟨2, 4⟩, 5), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 4), (5, ⟨6, 12⟩, 0), (5, ⟨6, 12⟩, 2), (5, ⟨6, 12⟩, 3), (5, ⟨6, 12⟩, 5), (1, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 4), (1, ⟨24, 48⟩, 1), (1, ⟨24, 48⟩, 4)]

theorem g32p_row43_pairing_21 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(5, ⟨-9, -18⟩, 0), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (5, ⟨-9, -18⟩, 3), (5, ⟨-9, -18⟩, 4), (5, ⟨-9, -18⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (11, ⟨-1, -2⟩, 0), (11, ⟨-1, -2⟩, 1), (11, ⟨-1, -2⟩, 2), (11, ⟨-1, -2⟩, 3), (11, ⟨-1, -2⟩, 4), (11, ⟨-1, -2⟩, 5), (11, ⟨1, 2⟩, 0), (11, ⟨1, 2⟩, 1), (11, ⟨1, 2⟩, 2), (11, ⟨1, 2⟩, 3), (11, ⟨1, 2⟩, 4), (11, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (5, ⟨9, 18⟩, 0), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (5, ⟨9, 18⟩, 3), (5, ⟨9, 18⟩, 4), (5, ⟨9, 18⟩, 5)]

theorem g32p_row43_pairing_22 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 4), (5, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 2), (5, ⟨-6, -12⟩, 3), (1, ⟨-6, -12⟩, 5), (4, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (5, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (5, ⟨-2, -4⟩, 0), (10, ⟨-2, -4⟩, 2), (5, ⟨-2, -4⟩, 3), (10, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (17, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (17, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (17, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (17, ⟨1, 2⟩, 5), (5, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (5, ⟨2, 4⟩, 3), (10, ⟨2, 4⟩, 4), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 5), (5, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 4), (5, ⟨9, 18⟩, 2), (5, ⟨9, 18⟩, 5), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row43_pairing_23 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_23)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (5, ⟨-9, -18⟩, 2), (5, ⟨-9, -18⟩, 5), (6, ⟨-6, -12⟩, 2), (6, ⟨-6, -12⟩, 5), (9, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (9, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 1), (11, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (11, ⟨-2, -4⟩, 5), (15, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (11, ⟨-1, -2⟩, 2), (15, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 4), (11, ⟨-1, -2⟩, 5), (15, ⟨1, 2⟩, 0), (11, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (15, ⟨1, 2⟩, 3), (11, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 5), (11, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (11, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (9, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (6, ⟨6, 12⟩, 1), (6, ⟨6, 12⟩, 4), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 4), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row43_pairing_24 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_24)
      [1, -1, 1] [0, 144, 0, 144, 0, -288] = true := by
  decide +kernel

def g32p_row43_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (1, ⟨-10, -20⟩, 1), (1, ⟨-10, -20⟩, 4), (9, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (9, ⟨-3, -6⟩, 3), (9, ⟨-3, -6⟩, 4), (8, ⟨-3, -6⟩, 5), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 4), (15, ⟨-1, -2⟩, 0), (14, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (15, ⟨-1, -2⟩, 3), (14, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (15, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (14, ⟨1, 2⟩, 2), (15, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (14, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 5), (9, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (9, ⟨3, 6⟩, 3), (8, ⟨3, 6⟩, 4), (9, ⟨3, 6⟩, 5), (1, ⟨10, 20⟩, 2), (1, ⟨10, 20⟩, 5), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row43_pairing_25 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(5, ⟨-9, -18⟩, 0), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (5, ⟨-9, -18⟩, 3), (5, ⟨-9, -18⟩, 4), (5, ⟨-9, -18⟩, 5), (5, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (5, ⟨-3, -6⟩, 3), (5, ⟨-3, -6⟩, 4), (5, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (5, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (5, ⟨3, 6⟩, 3), (5, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 5), (5, ⟨9, 18⟩, 0), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (5, ⟨9, 18⟩, 3), (5, ⟨9, 18⟩, 4), (5, ⟨9, 18⟩, 5)]

theorem g32p_row43_pairing_26 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 5), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 4), (12, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (8, ⟨3, 6⟩, 5), (10, ⟨9, 18⟩, 4), (10, ⟨9, 18⟩, 5), (1, ⟨36, 72⟩, 4), (1, ⟨36, 72⟩, 5)]

theorem g32p_row43_pairing_27 :
    g32p_cyclotomicPairingCheck 432 (2)
      (g32p_pairingCoefficients 6 g32p_row43_terms_27)
      [1, -1, 1] [-864, -1008, -288, 432, 576, 288] = true := by
  decide +kernel

def g32p_row43_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (5, ⟨-9, -18⟩, 0), (5, ⟨-9, -18⟩, 3), (5, ⟨-9, -18⟩, 4), (5, ⟨-9, -18⟩, 5), (5, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (5, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (5, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (5, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 5), (5, ⟨9, 18⟩, 0), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (5, ⟨9, 18⟩, 3), (1, ⟨36, 72⟩, 4), (1, ⟨36, 72⟩, 5)]

theorem g32p_row43_pairing_28 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(5, ⟨-6, -12⟩, 0), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 2), (5, ⟨-6, -12⟩, 3), (5, ⟨-6, -12⟩, 4), (5, ⟨-6, -12⟩, 5), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (9, ⟨-2, -4⟩, 3), (9, ⟨-2, -4⟩, 4), (9, ⟨-2, -4⟩, 5), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (9, ⟨2, 4⟩, 3), (9, ⟨2, 4⟩, 4), (9, ⟨2, 4⟩, 5), (5, ⟨6, 12⟩, 0), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 2), (5, ⟨6, 12⟩, 3), (5, ⟨6, 12⟩, 4), (5, ⟨6, 12⟩, 5)]

theorem g32p_row43_pairing_29 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 2), (1, ⟨-40, -80⟩, 5), (1, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 4), (5, ⟨-8, -16⟩, 5), (5, ⟨-6, -12⟩, 2), (5, ⟨-6, -12⟩, 5), (18, ⟨-2, -4⟩, 0), (13, ⟨-2, -4⟩, 2), (18, ⟨-2, -4⟩, 3), (13, ⟨-2, -4⟩, 5), (16, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 4), (18, ⟨2, 4⟩, 0), (13, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 3), (13, ⟨2, 4⟩, 4), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 4), (5, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (5, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 5), (1, ⟨40, 80⟩, 1), (1, ⟨40, 80⟩, 4)]

theorem g32p_row43_pairing_30 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_30)
      [1, -1, 1] [0, 144, 0, 144, 0, -288] = true := by
  decide +kernel

def g32p_row43_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 2), (1, ⟨-40, -80⟩, 5), (5, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 3), (1, ⟨-8, -16⟩, 4), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 4), (4, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (18, ⟨-2, -4⟩, 4), (9, ⟨-2, -4⟩, 5), (16, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 5), (16, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 4), (4, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (9, ⟨2, 4⟩, 4), (18, ⟨2, 4⟩, 5), (5, ⟨6, 12⟩, 2), (5, ⟨6, 12⟩, 5), (5, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 2), (5, ⟨8, 16⟩, 3), (1, ⟨8, 16⟩, 5), (1, ⟨40, 80⟩, 1), (1, ⟨40, 80⟩, 4)]

theorem g32p_row43_pairing_31 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(5, ⟨-9, -18⟩, 0), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (5, ⟨-9, -18⟩, 3), (5, ⟨-9, -18⟩, 4), (5, ⟨-9, -18⟩, 5), (5, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (5, ⟨-3, -6⟩, 3), (5, ⟨-3, -6⟩, 4), (5, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (5, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (5, ⟨3, 6⟩, 3), (5, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 5), (5, ⟨9, 18⟩, 0), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (5, ⟨9, 18⟩, 3), (5, ⟨9, 18⟩, 4), (5, ⟨9, 18⟩, 5)]

theorem g32p_row43_pairing_32 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 2), (1, ⟨-45, -90⟩, 5), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 4), (1, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (10, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 4), (10, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (10, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 5), (10, ⟨9, 18⟩, 2), (10, ⟨9, 18⟩, 5), (1, ⟨45, 90⟩, 1), (1, ⟨45, 90⟩, 4)]

theorem g32p_row43_pairing_33 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 2), (1, ⟨-45, -90⟩, 5), (5, ⟨-9, -18⟩, 0), (5, ⟨-9, -18⟩, 2), (5, ⟨-9, -18⟩, 3), (5, ⟨-9, -18⟩, 5), (5, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 3), (6, ⟨-3, -6⟩, 4), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (5, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 2), (5, ⟨3, 6⟩, 3), (6, ⟨3, 6⟩, 5), (5, ⟨9, 18⟩, 0), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 3), (5, ⟨9, 18⟩, 4), (1, ⟨45, 90⟩, 1), (1, ⟨45, 90⟩, 4)]

theorem g32p_row43_pairing_34 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_34)
      [1, -1, 1] [0, 72, 0, 72, 0, -144] = true := by
  decide +kernel

def g32p_row43_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(5, ⟨-9, -18⟩, 0), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (5, ⟨-9, -18⟩, 3), (5, ⟨-9, -18⟩, 4), (5, ⟨-9, -18⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (11, ⟨-1, -2⟩, 0), (11, ⟨-1, -2⟩, 1), (11, ⟨-1, -2⟩, 2), (11, ⟨-1, -2⟩, 3), (11, ⟨-1, -2⟩, 4), (11, ⟨-1, -2⟩, 5), (11, ⟨1, 2⟩, 0), (11, ⟨1, 2⟩, 1), (11, ⟨1, 2⟩, 2), (11, ⟨1, 2⟩, 3), (11, ⟨1, 2⟩, 4), (11, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (5, ⟨9, 18⟩, 0), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (5, ⟨9, 18⟩, 3), (5, ⟨9, 18⟩, 4), (5, ⟨9, 18⟩, 5)]

theorem g32p_row43_pairing_35 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (5, ⟨-6, -12⟩, 0), (5, ⟨-6, -12⟩, 3), (13, ⟨-3, -6⟩, 1), (13, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (9, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (9, ⟨2, 4⟩, 3), (13, ⟨3, 6⟩, 4), (13, ⟨3, 6⟩, 5), (5, ⟨6, 12⟩, 0), (5, ⟨6, 12⟩, 3), (5, ⟨9, 18⟩, 4), (5, ⟨9, 18⟩, 5), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row43_pairing_36 :
    g32p_cyclotomicPairingCheck 432 (2)
      (g32p_pairingCoefficients 6 g32p_row43_terms_36)
      [1, -1, 1] [-864, -1008, -288, 432, 576, 288] = true := by
  decide +kernel

def g32p_row43_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (10, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (10, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (6, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 3), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (10, ⟨3, 6⟩, 3), (6, ⟨3, 6⟩, 4), (6, ⟨3, 6⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 5), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row43_pairing_37 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 6 g32p_row43_terms_37)
      [1, -1, 1] [-432, -504, -144, 216, 288, 144] = true := by
  decide +kernel

def g32p_row43_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (5, ⟨-9, -18⟩, 4), (5, ⟨-9, -18⟩, 5), (5, ⟨-6, -12⟩, 4), (5, ⟨-6, -12⟩, 5), (5, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (5, ⟨-3, -6⟩, 3), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (7, ⟨-2, -4⟩, 4), (7, ⟨-2, -4⟩, 5), (11, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (11, ⟨-1, -2⟩, 3), (11, ⟨-1, -2⟩, 4), (11, ⟨-1, -2⟩, 5), (11, ⟨1, 2⟩, 0), (11, ⟨1, 2⟩, 1), (11, ⟨1, 2⟩, 2), (11, ⟨1, 2⟩, 3), (8, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 0), (7, ⟨2, 4⟩, 1), (7, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (5, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 3), (8, ⟨3, 6⟩, 4), (8, ⟨3, 6⟩, 5), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 2), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row43_pairing_38 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 5), (5, ⟨-6, -12⟩, 0), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 3), (5, ⟨-6, -12⟩, 4), (1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 4), (4, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (8, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (5, ⟨-2, -4⟩, 0), (5, ⟨-2, -4⟩, 1), (5, ⟨-2, -4⟩, 3), (5, ⟨-2, -4⟩, 4), (4, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (8, ⟨1, 2⟩, 5), (5, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 2), (5, ⟨2, 4⟩, 3), (5, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (8, ⟨3, 6⟩, 5), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 5), (5, ⟨6, 12⟩, 0), (5, ⟨6, 12⟩, 2), (5, ⟨6, 12⟩, 3), (5, ⟨6, 12⟩, 5), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 4)]

theorem g32p_row43_pairing_39 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 5), (5, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 2), (5, ⟨-8, -16⟩, 3), (5, ⟨-8, -16⟩, 5), (4, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 3), (4, ⟨-4, -8⟩, 4), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 4), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 5), (4, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 2), (4, ⟨4, 8⟩, 3), (4, ⟨4, 8⟩, 5), (5, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 3), (5, ⟨8, 16⟩, 4), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 4)]

theorem g32p_row43_pairing_40 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_40)
      [1, -1, 1] [0, 72, 0, 72, 0, -144] = true := by
  decide +kernel

def g32p_row43_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (5, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (5, ⟨-8, -16⟩, 3), (4, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 3), (4, ⟨-4, -8⟩, 4), (4, ⟨-4, -8⟩, 5), (8, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (4, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (4, ⟨4, 8⟩, 3), (5, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 3), (5, ⟨8, 16⟩, 4), (5, ⟨8, 16⟩, 5), (1, ⟨64, 128⟩, 4), (1, ⟨64, 128⟩, 5)]

theorem g32p_row43_pairing_41 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 6 g32p_row43_terms_41)
      [1, -1, 1] [-432, -504, -144, 216, 288, 144] = true := by
  decide +kernel

def g32p_row43_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (5, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 3), (5, ⟨-8, -16⟩, 4), (5, ⟨-8, -16⟩, 5), (8, ⟨-4, -8⟩, 4), (8, ⟨-4, -8⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (8, ⟨4, 8⟩, 1), (8, ⟨4, 8⟩, 2), (5, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (5, ⟨8, 16⟩, 3), (1, ⟨80, 160⟩, 4), (1, ⟨80, 160⟩, 5)]

theorem g32p_row43_pairing_42 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 2), (1, ⟨-81, -162⟩, 5), (1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 5), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 4), (6, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 5), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 4), (1, ⟨81, 162⟩, 1), (1, ⟨81, 162⟩, 4)]

theorem g32p_row43_pairing_43 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_43)
      [1, -1, 1] [0, 72, 0, 72, 0, -144] = true := by
  decide +kernel

def g32p_row43_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 3), (1, ⟨-20, 0⟩, 5), (10, ⟨-7, 0⟩, 0), (10, ⟨-7, 0⟩, 2), (10, ⟨-7, 0⟩, 4), (2, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 1), (2, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 3), (2, ⟨-3, 0⟩, 4), (8, ⟨-3, 0⟩, 5), (22, ⟨-2, 0⟩, 1), (22, ⟨-2, 0⟩, 3), (22, ⟨-2, 0⟩, 5), (12, ⟨-1, 0⟩, 0), (12, ⟨-1, 0⟩, 2), (12, ⟨-1, 0⟩, 4), (12, ⟨1, 0⟩, 1), (12, ⟨1, 0⟩, 3), (12, ⟨1, 0⟩, 5), (22, ⟨2, 0⟩, 0), (22, ⟨2, 0⟩, 2), (22, ⟨2, 0⟩, 4), (8, ⟨3, 0⟩, 0), (2, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 2), (2, ⟨3, 0⟩, 3), (8, ⟨3, 0⟩, 4), (2, ⟨3, 0⟩, 5), (10, ⟨7, 0⟩, 1), (10, ⟨7, 0⟩, 3), (10, ⟨7, 0⟩, 5), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row43_pairing_44 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 3), (1, ⟨-60, 0⟩, 5), (8, ⟨-6, 0⟩, 0), (8, ⟨-6, 0⟩, 2), (8, ⟨-6, 0⟩, 4), (12, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 1), (12, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 3), (12, ⟨-3, 0⟩, 4), (8, ⟨-3, 0⟩, 5), (6, ⟨-2, 0⟩, 0), (6, ⟨-2, 0⟩, 2), (6, ⟨-2, 0⟩, 4), (12, ⟨-1, 0⟩, 1), (12, ⟨-1, 0⟩, 3), (12, ⟨-1, 0⟩, 5), (12, ⟨1, 0⟩, 0), (12, ⟨1, 0⟩, 2), (12, ⟨1, 0⟩, 4), (6, ⟨2, 0⟩, 1), (6, ⟨2, 0⟩, 3), (6, ⟨2, 0⟩, 5), (8, ⟨3, 0⟩, 0), (12, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 2), (12, ⟨3, 0⟩, 3), (8, ⟨3, 0⟩, 4), (12, ⟨3, 0⟩, 5), (8, ⟨6, 0⟩, 1), (8, ⟨6, 0⟩, 3), (8, ⟨6, 0⟩, 5), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row43_pairing_45 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 3), (1, ⟨-64, 0⟩, 5), (10, ⟨-8, 0⟩, 0), (10, ⟨-8, 0⟩, 2), (10, ⟨-8, 0⟩, 4), (8, ⟨-4, 0⟩, 1), (8, ⟨-4, 0⟩, 3), (8, ⟨-4, 0⟩, 5), (8, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 2), (8, ⟨-2, 0⟩, 4), (8, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 3), (8, ⟨2, 0⟩, 5), (8, ⟨4, 0⟩, 0), (8, ⟨4, 0⟩, 2), (8, ⟨4, 0⟩, 4), (10, ⟨8, 0⟩, 1), (10, ⟨8, 0⟩, 3), (10, ⟨8, 0⟩, 5), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row43_pairing_46 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row43_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 3), (1, ⟨-80, 0⟩, 5), (10, ⟨-8, 0⟩, 1), (10, ⟨-8, 0⟩, 3), (10, ⟨-8, 0⟩, 5), (8, ⟨-4, 0⟩, 0), (8, ⟨-4, 0⟩, 2), (8, ⟨-4, 0⟩, 4), (8, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 3), (8, ⟨-2, 0⟩, 5), (8, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 2), (8, ⟨2, 0⟩, 4), (8, ⟨4, 0⟩, 1), (8, ⟨4, 0⟩, 3), (8, ⟨4, 0⟩, 5), (10, ⟨8, 0⟩, 0), (10, ⟨8, 0⟩, 2), (10, ⟨8, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row43_pairing_47 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row43_terms_47)
      [1, -1, 1] [144, 0, 0, -144] = true := by
  decide +kernel

theorem g32p_row43_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 43 ∧ g32SparseVec v.coords =
        (![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨43, -1, [(3, 1), (16, 1), (19, 1), (28, 2), (37, 2), (38, 1), (42, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row44_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(48, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2)]

theorem g32p_row44_pairing_0 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2)]

theorem g32p_row44_pairing_1 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (26, ⟨-2, -4⟩, 1), (26, ⟨-2, -4⟩, 2), (32, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (32, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (26, ⟨2, 4⟩, 1), (26, ⟨2, 4⟩, 2), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row44_pairing_2 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (20, ⟨-2, -4⟩, 1), (20, ⟨-2, -4⟩, 2), (32, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (32, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (20, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 2), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row44_pairing_3 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2)]

theorem g32p_row44_pairing_4 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (8, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (32, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (38, ⟨-1, -2⟩, 1), (44, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (44, ⟨1, 2⟩, 1), (38, ⟨1, 2⟩, 2), (32, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 2)]

theorem g32p_row44_pairing_5 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (2, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (20, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (56, ⟨-1, -2⟩, 1), (26, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (26, ⟨1, 2⟩, 1), (56, ⟨1, 2⟩, 2), (20, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 2)]

theorem g32p_row44_pairing_6 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (10, ⟨-3, -6⟩, 0), (26, ⟨-3, -6⟩, 1), (8, ⟨-2, -4⟩, 0), (20, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (28, ⟨-1, -2⟩, 1), (10, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (10, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (26, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row44_pairing_7 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row44_terms_7)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row44_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(20, ⟨-3, -6⟩, 0), (20, ⟨-3, -6⟩, 1), (20, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (20, ⟨3, 6⟩, 0), (20, ⟨3, 6⟩, 1), (20, ⟨3, 6⟩, 2)]

theorem g32p_row44_pairing_8 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (8, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 1), (4, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (22, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (26, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (26, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (22, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (8, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 2)]

theorem g32p_row44_pairing_9 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (2, ⟨-5, -10⟩, 0), (8, ⟨-5, -10⟩, 1), (16, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (44, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (44, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 0), (8, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 2)]

theorem g32p_row44_pairing_10 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row44_terms_10)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row44_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (2, ⟨-7, -14⟩, 1), (18, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (30, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (30, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 1), (18, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (2, ⟨7, 14⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row44_pairing_11 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_11)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 2), (28, ⟨-3, -6⟩, 1), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 1), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (28, ⟨3, 6⟩, 2), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (2, ⟨15, 30⟩, 2)]

theorem g32p_row44_pairing_12 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(20, ⟨-3, -6⟩, 0), (20, ⟨-3, -6⟩, 1), (20, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (20, ⟨3, 6⟩, 0), (20, ⟨3, 6⟩, 1), (20, ⟨3, 6⟩, 2)]

theorem g32p_row44_pairing_13 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 1), (10, ⟨-6, -12⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (10, ⟨6, 12⟩, 2)]

theorem g32p_row44_pairing_14 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (10, ⟨-7, -14⟩, 0), (5, ⟨-7, -14⟩, 1), (5, ⟨-7, -14⟩, 2), (10, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (10, ⟨7, 14⟩, 0), (5, ⟨7, 14⟩, 1), (5, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row44_pairing_15 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 2), (2, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (8, ⟨-4, -8⟩, 1), (8, ⟨-4, -8⟩, 2), (15, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (46, ⟨-1, -2⟩, 0), (20, ⟨-1, -2⟩, 1), (20, ⟨-1, -2⟩, 2), (46, ⟨1, 2⟩, 0), (20, ⟨1, 2⟩, 1), (20, ⟨1, 2⟩, 2), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 1), (8, ⟨4, 8⟩, 2), (2, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row44_pairing_16 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (2, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (2, ⟨-3, -6⟩, 0), (14, ⟨-3, -6⟩, 1), (14, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (14, ⟨3, 6⟩, 1), (14, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (8, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row44_pairing_17 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 2), (8, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (8, ⟨-4, -8⟩, 1), (8, ⟨-4, -8⟩, 2), (15, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (40, ⟨-1, -2⟩, 0), (23, ⟨-1, -2⟩, 1), (23, ⟨-1, -2⟩, 2), (40, ⟨1, 2⟩, 0), (23, ⟨1, 2⟩, 1), (23, ⟨1, 2⟩, 2), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 1), (8, ⟨4, 8⟩, 2), (8, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row44_pairing_18 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (2, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (8, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (11, ⟨-3, -6⟩, 1), (11, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (11, ⟨3, 6⟩, 1), (11, ⟨3, 6⟩, 2), (8, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (2, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row44_pairing_19 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 1), (16, ⟨-5, -10⟩, 1), (2, ⟨-4, -8⟩, 1), (20, ⟨-2, -4⟩, 0), (10, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (20, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (10, ⟨2, 4⟩, 2), (2, ⟨4, 8⟩, 2), (16, ⟨5, 10⟩, 2), (2, ⟨20, 40⟩, 2)]

theorem g32p_row44_pairing_20 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row44_terms_20)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row44_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 1), (2, ⟨-8, -16⟩, 1), (10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (10, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (2, ⟨8, 16⟩, 2), (2, ⟨24, 48⟩, 2)]

theorem g32p_row44_pairing_21 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_21)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row44_pairing_22 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_22)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (2, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-1, -2⟩, 0), (30, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (14, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (30, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (14, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (8, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row44_pairing_23 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_23)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (8, ⟨-9, -18⟩, 1), (2, ⟨-9, -18⟩, 2), (2, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 1), (8, ⟨-3, -6⟩, 0), (18, ⟨-3, -6⟩, 2), (10, ⟨-2, -4⟩, 0), (20, ⟨-2, -4⟩, 1), (8, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (34, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (34, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 0), (20, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (2, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row44_pairing_24 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row44_terms_24)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row44_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-10, -20⟩, 2), (18, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (28, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (18, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (2, ⟨10, 20⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row44_pairing_25 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row44_pairing_26 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (2, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 1), (9, ⟨-9, -18⟩, 2), (2, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 1), (9, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row44_pairing_27 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (8, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (6, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (6, ⟨9, 18⟩, 1), (6, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row44_pairing_28 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 1), (10, ⟨-6, -12⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (10, ⟨6, 12⟩, 2)]

theorem g32p_row44_pairing_29 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (2, ⟨-8, -16⟩, 0), (8, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (24, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (20, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (24, ⟨2, 4⟩, 0), (20, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2), (2, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (8, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 2)]

theorem g32p_row44_pairing_30 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row44_terms_30)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row44_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (8, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (2, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (12, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (12, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 2), (8, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 2)]

theorem g32p_row44_pairing_31 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row44_pairing_32 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (2, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (16, ⟨-9, -18⟩, 2), (2, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (2, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row44_pairing_33 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row44_pairing_34 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row44_terms_34)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row44_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row44_pairing_35 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (8, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (10, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (11, ⟨-2, -4⟩, 1), (11, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (19, ⟨-1, -2⟩, 1), (19, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (19, ⟨1, 2⟩, 1), (19, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (11, ⟨2, 4⟩, 1), (11, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row44_pairing_36 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (20, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (20, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row44_pairing_37 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (2, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (16, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (2, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (14, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row44_pairing_38 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 1), (10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 2), (2, ⟨-4, -8⟩, 2), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (10, ⟨-2, -4⟩, 0), (10, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (8, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (2, ⟨4, 8⟩, 1), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (2, ⟨60, 120⟩, 2)]

theorem g32p_row44_pairing_39 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_39)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 1), (10, ⟨-8, -16⟩, 0), (10, ⟨-8, -16⟩, 1), (16, ⟨-4, -8⟩, 1), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (16, ⟨4, 8⟩, 2), (10, ⟨8, 16⟩, 0), (10, ⟨8, 16⟩, 2), (2, ⟨64, 128⟩, 2)]

theorem g32p_row44_pairing_40 :
    g32p_cyclotomicPairingCheck 432 (2)
      (g32p_pairingCoefficients 3 g32p_row44_terms_40)
      [1, 1, 1] [-864, 576] = true := by
  decide +kernel

def g32p_row44_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (10, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (8, ⟨-4, -8⟩, 1), (8, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 1), (8, ⟨4, 8⟩, 2), (10, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 2)]

theorem g32p_row44_pairing_41 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (10, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (8, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (10, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 1), (1, ⟨80, 160⟩, 2)]

theorem g32p_row44_pairing_42 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 1), (2, ⟨-9, -18⟩, 1), (12, ⟨-3, -6⟩, 2), (12, ⟨3, 6⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨81, 162⟩, 2)]

theorem g32p_row44_pairing_43 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row44_terms_43)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row44_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 2), (10, ⟨-7, 0⟩, 0), (10, ⟨-7, 0⟩, 1), (10, ⟨-7, 0⟩, 2), (10, ⟨-3, 0⟩, 0), (10, ⟨-3, 0⟩, 1), (10, ⟨-3, 0⟩, 2), (22, ⟨-2, 0⟩, 0), (22, ⟨-2, 0⟩, 1), (22, ⟨-2, 0⟩, 2), (12, ⟨-1, 0⟩, 0), (12, ⟨-1, 0⟩, 1), (12, ⟨-1, 0⟩, 2), (12, ⟨1, 0⟩, 0), (12, ⟨1, 0⟩, 1), (12, ⟨1, 0⟩, 2), (22, ⟨2, 0⟩, 0), (22, ⟨2, 0⟩, 1), (22, ⟨2, 0⟩, 2), (10, ⟨3, 0⟩, 0), (10, ⟨3, 0⟩, 1), (10, ⟨3, 0⟩, 2), (10, ⟨7, 0⟩, 0), (10, ⟨7, 0⟩, 1), (10, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 1), (1, ⟨20, 0⟩, 2)]

theorem g32p_row44_pairing_44 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 2), (8, ⟨-6, 0⟩, 0), (8, ⟨-6, 0⟩, 1), (8, ⟨-6, 0⟩, 2), (20, ⟨-3, 0⟩, 0), (20, ⟨-3, 0⟩, 1), (20, ⟨-3, 0⟩, 2), (6, ⟨-2, 0⟩, 0), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 2), (12, ⟨-1, 0⟩, 0), (12, ⟨-1, 0⟩, 1), (12, ⟨-1, 0⟩, 2), (12, ⟨1, 0⟩, 0), (12, ⟨1, 0⟩, 1), (12, ⟨1, 0⟩, 2), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 1), (6, ⟨2, 0⟩, 2), (20, ⟨3, 0⟩, 0), (20, ⟨3, 0⟩, 1), (20, ⟨3, 0⟩, 2), (8, ⟨6, 0⟩, 0), (8, ⟨6, 0⟩, 1), (8, ⟨6, 0⟩, 2), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 1), (1, ⟨60, 0⟩, 2)]

theorem g32p_row44_pairing_45 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 2), (10, ⟨-8, 0⟩, 0), (10, ⟨-8, 0⟩, 1), (10, ⟨-8, 0⟩, 2), (8, ⟨-4, 0⟩, 0), (8, ⟨-4, 0⟩, 1), (8, ⟨-4, 0⟩, 2), (8, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (8, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (8, ⟨4, 0⟩, 0), (8, ⟨4, 0⟩, 1), (8, ⟨4, 0⟩, 2), (10, ⟨8, 0⟩, 0), (10, ⟨8, 0⟩, 1), (10, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 1), (1, ⟨64, 0⟩, 2)]

theorem g32p_row44_pairing_46 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row44_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 2), (10, ⟨-8, 0⟩, 0), (10, ⟨-8, 0⟩, 1), (10, ⟨-8, 0⟩, 2), (8, ⟨-4, 0⟩, 0), (8, ⟨-4, 0⟩, 1), (8, ⟨-4, 0⟩, 2), (8, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (8, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (8, ⟨4, 0⟩, 0), (8, ⟨4, 0⟩, 1), (8, ⟨4, 0⟩, 2), (10, ⟨8, 0⟩, 0), (10, ⟨8, 0⟩, 1), (10, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 1), (1, ⟨80, 0⟩, 2)]

theorem g32p_row44_pairing_47 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row44_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row44_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 44 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨44, -1, [(8, 1), (11, 1), (21, 1), (25, 1), (31, 1), (35, 1), (41, 2), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row45_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(54, ⟨-1, -2⟩, 0), (54, ⟨-1, -2⟩, 1), (54, ⟨-1, -2⟩, 2), (54, ⟨1, 2⟩, 0), (54, ⟨1, 2⟩, 1), (54, ⟨1, 2⟩, 2)]

theorem g32p_row45_pairing_0 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2)]

theorem g32p_row45_pairing_1 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (15, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (39, ⟨-1, -2⟩, 0), (43, ⟨-1, -2⟩, 1), (42, ⟨-1, -2⟩, 2), (39, ⟨1, 2⟩, 0), (42, ⟨1, 2⟩, 1), (43, ⟨1, 2⟩, 2), (15, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row45_pairing_2 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-2, -4⟩, 0), (33, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (33, ⟨-1, -2⟩, 0), (88, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (33, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (88, ⟨1, 2⟩, 2), (3, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (33, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 2)]

theorem g32p_row45_pairing_3 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row45_terms_3)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row45_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 0), (36, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 0), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2)]

theorem g32p_row45_pairing_4 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 1), (1, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 2), (3, ⟨-2, -4⟩, 0), (43, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (33, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (46, ⟨-1, -2⟩, 2), (33, ⟨1, 2⟩, 0), (46, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (3, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (43, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (1, ⟨5, 10⟩, 2)]

theorem g32p_row45_pairing_5 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 1), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (15, ⟨-2, -4⟩, 0), (25, ⟨-2, -4⟩, 1), (21, ⟨-2, -4⟩, 2), (39, ⟨-1, -2⟩, 0), (33, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (39, ⟨1, 2⟩, 0), (28, ⟨1, 2⟩, 1), (33, ⟨1, 2⟩, 2), (15, ⟨2, 4⟩, 0), (21, ⟨2, 4⟩, 1), (25, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 2)]

theorem g32p_row45_pairing_6 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 1), (6, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (6, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 2)]

theorem g32p_row45_pairing_7 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(22, ⟨-3, -6⟩, 0), (22, ⟨-3, -6⟩, 1), (22, ⟨-3, -6⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (22, ⟨3, 6⟩, 0), (22, ⟨3, 6⟩, 1), (22, ⟨3, 6⟩, 2)]

theorem g32p_row45_pairing_8 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 1), (3, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (10, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (12, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (87, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (15, ⟨1, 2⟩, 1), (87, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (1, ⟨10, 20⟩, 2)]

theorem g32p_row45_pairing_9 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row45_terms_9)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row45_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 1), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 2), (10, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 2), (21, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (51, ⟨-1, -2⟩, 0), (42, ⟨-1, -2⟩, 1), (33, ⟨-1, -2⟩, 2), (51, ⟨1, 2⟩, 0), (33, ⟨1, 2⟩, 1), (42, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 1), (21, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (3, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨10, 20⟩, 2)]

theorem g32p_row45_pairing_10 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 1), (9, ⟨-7, -14⟩, 1), (6, ⟨-3, -6⟩, 0), (27, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 2), (6, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (27, ⟨3, 6⟩, 2), (9, ⟨7, 14⟩, 2), (1, ⟨15, 30⟩, 2)]

theorem g32p_row45_pairing_11 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row45_terms_11)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row45_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 1), (3, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (3, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 2), (1, ⟨15, 30⟩, 2)]

theorem g32p_row45_pairing_12 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(22, ⟨-3, -6⟩, 0), (22, ⟨-3, -6⟩, 1), (22, ⟨-3, -6⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (22, ⟨3, 6⟩, 0), (22, ⟨3, 6⟩, 1), (22, ⟨3, 6⟩, 2)]

theorem g32p_row45_pairing_13 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (27, ⟨-2, -4⟩, 0), (27, ⟨-2, -4⟩, 1), (27, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (27, ⟨2, 4⟩, 0), (27, ⟨2, 4⟩, 1), (27, ⟨2, 4⟩, 2), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2)]

theorem g32p_row45_pairing_14 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (3, ⟨-7, -14⟩, 0), (3, ⟨-7, -14⟩, 1), (2, ⟨-7, -14⟩, 2), (9, ⟨-3, -6⟩, 0), (27, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (9, ⟨3, 6⟩, 0), (27, ⟨3, 6⟩, 1), (3, ⟨7, 14⟩, 0), (2, ⟨7, 14⟩, 1), (3, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 2)]

theorem g32p_row45_pairing_15 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (21, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (79, ⟨-1, -2⟩, 2), (21, ⟨1, 2⟩, 0), (79, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 2), (3, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 2)]

theorem g32p_row45_pairing_16 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (19, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 1), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (19, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (3, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 2), (3, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 2)]

theorem g32p_row45_pairing_17 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (1, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 2), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (42, ⟨-1, -2⟩, 0), (39, ⟨-1, -2⟩, 1), (43, ⟨-1, -2⟩, 2), (42, ⟨1, 2⟩, 0), (43, ⟨1, 2⟩, 1), (39, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 2), (3, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row45_pairing_18 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (3, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (1, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 2), (10, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (27, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (27, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (3, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (3, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 2)]

theorem g32p_row45_pairing_19 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (3, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 2), (9, ⟨-4, -8⟩, 1), (12, ⟨-2, -4⟩, 0), (11, ⟨-2, -4⟩, 1), (21, ⟨-2, -4⟩, 2), (39, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (42, ⟨-1, -2⟩, 2), (39, ⟨1, 2⟩, 0), (42, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 0), (21, ⟨2, 4⟩, 1), (11, ⟨2, 4⟩, 2), (9, ⟨4, 8⟩, 2), (3, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row45_pairing_20 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_20)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 1), (9, ⟨-8, -16⟩, 1), (3, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (3, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (3, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (24, ⟨3, 6⟩, 2), (3, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 2), (9, ⟨8, 16⟩, 2), (1, ⟨24, 48⟩, 2)]

theorem g32p_row45_pairing_21 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row45_terms_21)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row45_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2)]

theorem g32p_row45_pairing_22 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_22)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 1), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (12, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (18, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (27, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (27, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (6, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 1), (12, ⟨6, 12⟩, 2), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨30, 60⟩, 2)]

theorem g32p_row45_pairing_23 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row45_terms_23)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row45_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 1), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 2), (3, ⟨-6, -12⟩, 0), (9, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (3, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (3, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (3, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (9, ⟨6, 12⟩, 2), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (1, ⟨30, 60⟩, 2)]

theorem g32p_row45_pairing_24 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 1), (9, ⟨-10, -20⟩, 2), (9, ⟨-3, -6⟩, 0), (26, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (27, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (9, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (26, ⟨3, 6⟩, 2), (9, ⟨10, 20⟩, 1), (1, ⟨30, 60⟩, 2)]

theorem g32p_row45_pairing_25 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (18, ⟨-3, -6⟩, 0), (18, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 2), (18, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (18, ⟨3, 6⟩, 2), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2)]

theorem g32p_row45_pairing_26 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (18, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (18, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row45_pairing_27 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (9, ⟨-3, -6⟩, 0), (27, ⟨-3, -6⟩, 1), (9, ⟨3, 6⟩, 0), (27, ⟨3, 6⟩, 2), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (6, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 2)]

theorem g32p_row45_pairing_28 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row45_terms_28)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row45_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (27, ⟨-2, -4⟩, 0), (27, ⟨-2, -4⟩, 1), (27, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (27, ⟨2, 4⟩, 0), (27, ⟨2, 4⟩, 1), (27, ⟨2, 4⟩, 2), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2)]

theorem g32p_row45_pairing_29 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 1), (3, ⟨-8, -16⟩, 0), (10, ⟨-8, -16⟩, 2), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (21, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (19, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (60, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (60, ⟨1, 2⟩, 2), (21, ⟨2, 4⟩, 0), (19, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨8, 16⟩, 0), (10, ⟨8, 16⟩, 1), (1, ⟨40, 80⟩, 2)]

theorem g32p_row45_pairing_30 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 1), (3, ⟨-8, -16⟩, 1), (10, ⟨-8, -16⟩, 2), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (24, ⟨-2, -4⟩, 0), (21, ⟨-2, -4⟩, 1), (19, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (30, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (30, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (19, ⟨2, 4⟩, 1), (21, ⟨2, 4⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (10, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨40, 80⟩, 2)]

theorem g32p_row45_pairing_31 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (18, ⟨-3, -6⟩, 0), (18, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 2), (18, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (18, ⟨3, 6⟩, 2), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2)]

theorem g32p_row45_pairing_32 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 1), (4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (18, ⟨-3, -6⟩, 0), (27, ⟨-3, -6⟩, 2), (18, ⟨3, 6⟩, 0), (27, ⟨3, 6⟩, 1), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 2), (1, ⟨45, 90⟩, 2)]

theorem g32p_row45_pairing_33 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 1), (1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (6, ⟨-9, -18⟩, 2), (9, ⟨-3, -6⟩, 0), (18, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 2), (9, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (18, ⟨3, 6⟩, 2), (1, ⟨9, 18⟩, 0), (6, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (1, ⟨45, 90⟩, 2)]

theorem g32p_row45_pairing_34 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2)]

theorem g32p_row45_pairing_35 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 2), (1, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (27, ⟨-2, -4⟩, 1), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 2), (27, ⟨2, 4⟩, 2), (6, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (24, ⟨3, 6⟩, 2), (3, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row45_pairing_36 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row45_terms_36)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row45_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (12, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (29, ⟨-3, -6⟩, 2), (12, ⟨3, 6⟩, 0), (29, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (3, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 2)]

theorem g32p_row45_pairing_37 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (3, ⟨-3, -6⟩, 0), (27, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (3, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (27, ⟨3, 6⟩, 2), (3, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 2), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 2)]

theorem g32p_row45_pairing_38 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row45_terms_38)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row45_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (3, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (9, ⟨-4, -8⟩, 2), (6, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (24, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (6, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (9, ⟨4, 8⟩, 1), (3, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 2)]

theorem g32p_row45_pairing_39 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_39)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (3, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 2), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (3, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 2)]

theorem g32p_row45_pairing_40 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_40)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (3, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 2), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (3, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 2)]

theorem g32p_row45_pairing_41 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (3, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (24, ⟨-4, -8⟩, 2), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 2), (3, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (3, ⟨4, 8⟩, 0), (24, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (3, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 2)]

theorem g32p_row45_pairing_42 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 1), (9, ⟨-9, -18⟩, 1), (9, ⟨9, 18⟩, 2), (1, ⟨81, 162⟩, 2)]

theorem g32p_row45_pairing_43 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row45_terms_43)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row45_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 1), (8, ⟨-7, 0⟩, 2), (18, ⟨-3, 0⟩, 0), (18, ⟨-3, 0⟩, 1), (18, ⟨-3, 0⟩, 2), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 2), (36, ⟨2, 0⟩, 0), (36, ⟨2, 0⟩, 1), (36, ⟨2, 0⟩, 2), (18, ⟨3, 0⟩, 0), (18, ⟨3, 0⟩, 1), (18, ⟨3, 0⟩, 2), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 1), (1, ⟨20, 0⟩, 2)]

theorem g32p_row45_pairing_44 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-6, 0⟩, 0), (6, ⟨-6, 0⟩, 1), (6, ⟨-6, 0⟩, 2), (26, ⟨-3, 0⟩, 0), (26, ⟨-3, 0⟩, 1), (26, ⟨-3, 0⟩, 2), (18, ⟨3, 0⟩, 0), (18, ⟨3, 0⟩, 1), (18, ⟨3, 0⟩, 2), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 1), (1, ⟨60, 0⟩, 2)]

theorem g32p_row45_pairing_45 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 2), (30, ⟨-2, 0⟩, 0), (30, ⟨-2, 0⟩, 1), (30, ⟨-2, 0⟩, 2), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 2), (6, ⟨4, 0⟩, 0), (6, ⟨4, 0⟩, 1), (6, ⟨4, 0⟩, 2), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 1), (1, ⟨64, 0⟩, 2)]

theorem g32p_row45_pairing_46 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row45_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(30, ⟨-4, 0⟩, 0), (30, ⟨-4, 0⟩, 1), (30, ⟨-4, 0⟩, 2), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 2), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 1), (6, ⟨2, 0⟩, 2), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 1), (1, ⟨80, 0⟩, 2)]

theorem g32p_row45_pairing_47 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row45_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row45_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 45 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨45, -1, [(4, 1), (10, 1), (12, 1), (22, 1), (24, 1), (29, 1), (37, 1), (39, 1), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row46_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(72, ⟨-1, -2⟩, 2), (72, ⟨-1, -2⟩, 5), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 4)]

theorem g32p_row46_pairing_0 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_0)
      [1, -1, 1] [0, 72, 0, 72, 0, -144] = true := by
  decide +kernel

def g32p_row46_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 3), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 3), (12, ⟨2, 4⟩, 5)]

theorem g32p_row46_pairing_1 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (4, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (12, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (12, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (12, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row46_pairing_2 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (4, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (12, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (12, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (12, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row46_pairing_3 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row46_pairing_4 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (12, ⟨-3, -6⟩, 1), (8, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 2), (44, ⟨-1, -2⟩, 4), (36, ⟨-1, -2⟩, 5), (36, ⟨1, 2⟩, 1), (44, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 4), (8, ⟨2, 4⟩, 4), (12, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row46_pairing_5 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (12, ⟨-3, -6⟩, 1), (8, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 2), (44, ⟨-1, -2⟩, 4), (36, ⟨-1, -2⟩, 5), (36, ⟨1, 2⟩, 1), (44, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 4), (8, ⟨2, 4⟩, 4), (12, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row46_pairing_6 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 2), (36, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 1), (24, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 4), (36, ⟨2, 4⟩, 5), (8, ⟨3, 6⟩, 4), (2, ⟨6, 12⟩, 4)]

theorem g32p_row46_pairing_7 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 6 g32p_row46_terms_7)
      [1, -1, 1] [-432, -504, -144, 216, 288, 144] = true := by
  decide +kernel

def g32p_row46_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row46_pairing_8 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (12, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row46_pairing_9 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (12, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row46_pairing_10 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (12, ⟨-7, -14⟩, 5), (26, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 5), (36, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 4), (12, ⟨3, 6⟩, 1), (26, ⟨3, 6⟩, 4), (12, ⟨7, 14⟩, 1), (2, ⟨15, 30⟩, 4)]

theorem g32p_row46_pairing_11 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_11)
      [1, -1, 1] [0, 144, 0, 144, 0, -288] = true := by
  decide +kernel

def g32p_row46_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (8, ⟨-3, -6⟩, 2), (24, ⟨-2, -4⟩, 5), (48, ⟨-1, -2⟩, 1), (54, ⟨-1, -2⟩, 4), (54, ⟨1, 2⟩, 2), (48, ⟨1, 2⟩, 5), (24, ⟨2, 4⟩, 1), (8, ⟨3, 6⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row46_pairing_12 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row46_pairing_13 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 3), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 3), (12, ⟨2, 4⟩, 5)]

theorem g32p_row46_pairing_14 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row46_pairing_15 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (4, ⟨-4, -8⟩, 2), (4, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 3), (12, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (12, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (12, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 3), (4, ⟨4, 8⟩, 2), (4, ⟨4, 8⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row46_pairing_16 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row46_pairing_17 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (4, ⟨-4, -8⟩, 2), (4, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 3), (12, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (12, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (12, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 3), (4, ⟨4, 8⟩, 2), (4, ⟨4, 8⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row46_pairing_18 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (8, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row46_pairing_19 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 2), (8, ⟨-5, -10⟩, 2), (18, ⟨-4, -8⟩, 2), (24, ⟨-4, -8⟩, 5), (8, ⟨-1, -2⟩, 4), (48, ⟨-1, -2⟩, 5), (48, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (24, ⟨4, 8⟩, 1), (18, ⟨4, 8⟩, 4), (8, ⟨5, 10⟩, 4), (2, ⟨20, 40⟩, 4)]

theorem g32p_row46_pairing_20 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_20)
      [1, -1, 1] [0, 144, 0, 144, 0, -288] = true := by
  decide +kernel

def g32p_row46_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 2), (12, ⟨-8, -16⟩, 5), (8, ⟨-3, -6⟩, 2), (24, ⟨-1, -2⟩, 1), (24, ⟨1, 2⟩, 5), (8, ⟨3, 6⟩, 4), (12, ⟨8, 16⟩, 1), (2, ⟨24, 48⟩, 4)]

theorem g32p_row46_pairing_21 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_21)
      [1, -1, 1] [0, 72, 0, 72, 0, -144] = true := by
  decide +kernel

def g32p_row46_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row46_pairing_22 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (12, ⟨-6, -12⟩, 5), (8, ⟨-3, -6⟩, 4), (18, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 1), (24, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 2), (12, ⟨6, 12⟩, 1), (2, ⟨30, 60⟩, 4)]

theorem g32p_row46_pairing_23 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_23)
      [1, -1, 1] [0, 72, 0, 72, 0, -144] = true := by
  decide +kernel

def g32p_row46_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (12, ⟨-6, -12⟩, 5), (8, ⟨-3, -6⟩, 4), (18, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 1), (24, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 2), (12, ⟨6, 12⟩, 1), (2, ⟨30, 60⟩, 4)]

theorem g32p_row46_pairing_24 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_24)
      [1, -1, 1] [0, 72, 0, 72, 0, -144] = true := by
  decide +kernel

def g32p_row46_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (12, ⟨-10, -20⟩, 1), (16, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 5), (48, ⟨-1, -2⟩, 1), (48, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 4), (12, ⟨10, 20⟩, 5), (2, ⟨30, 60⟩, 4)]

theorem g32p_row46_pairing_25 :
    g32p_cyclotomicPairingCheck 432 (2)
      (g32p_pairingCoefficients 6 g32p_row46_terms_25)
      [1, -1, 1] [-864, -1008, -288, 432, 576, 288] = true := by
  decide +kernel

def g32p_row46_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row46_pairing_26 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row46_pairing_27 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row46_pairing_28 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row46_pairing_29 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (12, ⟨-8, -16⟩, 1), (8, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 4), (8, ⟨2, 4⟩, 2), (12, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row46_pairing_30 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 6 g32p_row46_terms_30)
      [1, -1, 1] [-432, -504, -144, 216, 288, 144] = true := by
  decide +kernel

def g32p_row46_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (12, ⟨-8, -16⟩, 1), (8, ⟨-2, -4⟩, 4), (8, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 4), (8, ⟨2, 4⟩, 2), (12, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row46_pairing_31 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 6 g32p_row46_terms_31)
      [1, -1, 1] [-432, -504, -144, 216, 288, 144] = true := by
  decide +kernel

def g32p_row46_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row46_pairing_32 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (24, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 4), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 4), (18, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row46_pairing_33 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 6 g32p_row46_terms_33)
      [1, -1, 1] [-432, -504, -144, 216, 288, 144] = true := by
  decide +kernel

def g32p_row46_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (24, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 4), (36, ⟨-1, -2⟩, 2), (36, ⟨1, 2⟩, 4), (18, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row46_pairing_34 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 6 g32p_row46_terms_34)
      [1, -1, 1] [-432, -504, -144, 216, 288, 144] = true := by
  decide +kernel

def g32p_row46_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 3), (12, ⟨-2, -4⟩, 5), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 3), (12, ⟨2, 4⟩, 5)]

theorem g32p_row46_pairing_35 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 3), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 3), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row46_pairing_36 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 4), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row46_pairing_37 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 3), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 3), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row46_pairing_38 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 2), (12, ⟨-4, -8⟩, 1), (18, ⟨-4, -8⟩, 2), (12, ⟨-4, -8⟩, 5), (16, ⟨-3, -6⟩, 4), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 5), (16, ⟨3, 6⟩, 2), (12, ⟨4, 8⟩, 1), (18, ⟨4, 8⟩, 4), (12, ⟨4, 8⟩, 5), (2, ⟨60, 120⟩, 4)]

theorem g32p_row46_pairing_39 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 6 g32p_row46_terms_39)
      [1, -1, 1] [-432, -432, -144, 288, 288] = true := by
  decide +kernel

def g32p_row46_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 2), (8, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 4), (8, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 4), (2, ⟨64, 128⟩, 4)]

theorem g32p_row46_pairing_40 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 6 g32p_row46_terms_40)
      [1, -1, 1] [-432, -432, -144, 288, 288] = true := by
  decide +kernel

def g32p_row46_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (4, ⟨-4, -8⟩, 2), (4, ⟨-4, -8⟩, 4), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (4, ⟨4, 8⟩, 2), (4, ⟨4, 8⟩, 4), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 4)]

theorem g32p_row46_pairing_41 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (4, ⟨-4, -8⟩, 2), (4, ⟨-4, -8⟩, 4), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (4, ⟨4, 8⟩, 2), (4, ⟨4, 8⟩, 4), (1, ⟨80, 160⟩, 2), (1, ⟨80, 160⟩, 4)]

theorem g32p_row46_pairing_42 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 2), (12, ⟨-9, -18⟩, 5), (12, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 4), (36, ⟨-1, -2⟩, 4), (36, ⟨1, 2⟩, 2), (18, ⟨3, 6⟩, 2), (12, ⟨3, 6⟩, 5), (12, ⟨9, 18⟩, 1), (2, ⟨81, 162⟩, 4)]

theorem g32p_row46_pairing_43 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_43)
      [1, -1, 1] [0, 72, 0, 72, 0, -144] = true := by
  decide +kernel

def g32p_row46_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 4), (8, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 2), (8, ⟨-2, 0⟩, 4), (8, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 2), (8, ⟨2, 0⟩, 4), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row46_pairing_44 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 4), (4, ⟨-6, 0⟩, 0), (4, ⟨-6, 0⟩, 2), (4, ⟨-6, 0⟩, 4), (4, ⟨6, 0⟩, 0), (4, ⟨6, 0⟩, 2), (4, ⟨6, 0⟩, 4), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row46_pairing_45 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 4), (4, ⟨-4, 0⟩, 0), (4, ⟨-4, 0⟩, 2), (4, ⟨-4, 0⟩, 4), (4, ⟨-2, 0⟩, 0), (4, ⟨-2, 0⟩, 2), (4, ⟨-2, 0⟩, 4), (4, ⟨2, 0⟩, 0), (4, ⟨2, 0⟩, 2), (4, ⟨2, 0⟩, 4), (4, ⟨4, 0⟩, 0), (4, ⟨4, 0⟩, 2), (4, ⟨4, 0⟩, 4), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row46_pairing_46 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row46_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 4), (4, ⟨-4, 0⟩, 0), (4, ⟨-4, 0⟩, 2), (4, ⟨-4, 0⟩, 4), (4, ⟨-2, 0⟩, 0), (4, ⟨-2, 0⟩, 2), (4, ⟨-2, 0⟩, 4), (4, ⟨2, 0⟩, 0), (4, ⟨2, 0⟩, 2), (4, ⟨2, 0⟩, 4), (4, ⟨4, 0⟩, 0), (4, ⟨4, 0⟩, 2), (4, ⟨4, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row46_pairing_47 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 6 g32p_row46_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row46_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 46 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨46, -2, [(8, 1), (26, 2), (31, 1), (32, 1), (34, 1), (35, 1), (40, 1), (41, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row47_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(48, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2)]

theorem g32p_row47_pairing_0 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2)]

theorem g32p_row47_pairing_1 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (20, ⟨-2, -4⟩, 1), (20, ⟨-2, -4⟩, 2), (32, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (32, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (20, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 2), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row47_pairing_2 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (26, ⟨-2, -4⟩, 1), (26, ⟨-2, -4⟩, 2), (32, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (32, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (26, ⟨2, 4⟩, 1), (26, ⟨2, 4⟩, 2), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row47_pairing_3 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2)]

theorem g32p_row47_pairing_4 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (2, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (20, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (56, ⟨-1, -2⟩, 1), (26, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (26, ⟨1, 2⟩, 1), (56, ⟨1, 2⟩, 2), (20, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 2)]

theorem g32p_row47_pairing_5 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (8, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (32, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (38, ⟨-1, -2⟩, 1), (44, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (44, ⟨1, 2⟩, 1), (38, ⟨1, 2⟩, 2), (32, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 2)]

theorem g32p_row47_pairing_6 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (10, ⟨-3, -6⟩, 0), (26, ⟨-3, -6⟩, 1), (8, ⟨-2, -4⟩, 0), (20, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (28, ⟨-1, -2⟩, 1), (10, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (10, ⟨1, 2⟩, 1), (28, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (20, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (26, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row47_pairing_7 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row47_terms_7)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row47_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(20, ⟨-3, -6⟩, 0), (20, ⟨-3, -6⟩, 1), (20, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (20, ⟨3, 6⟩, 0), (20, ⟨3, 6⟩, 1), (20, ⟨3, 6⟩, 2)]

theorem g32p_row47_pairing_8 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (2, ⟨-5, -10⟩, 0), (8, ⟨-5, -10⟩, 1), (16, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (44, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (44, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 0), (8, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 2)]

theorem g32p_row47_pairing_9 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row47_terms_9)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row47_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (8, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 1), (4, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (22, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (26, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (26, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (22, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (8, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 2)]

theorem g32p_row47_pairing_10 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (2, ⟨-7, -14⟩, 1), (18, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (30, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (30, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 1), (18, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (2, ⟨7, 14⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row47_pairing_11 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_11)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 2), (28, ⟨-3, -6⟩, 1), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 1), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (28, ⟨3, 6⟩, 2), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (2, ⟨15, 30⟩, 2)]

theorem g32p_row47_pairing_12 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(20, ⟨-3, -6⟩, 0), (20, ⟨-3, -6⟩, 1), (20, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (20, ⟨3, 6⟩, 0), (20, ⟨3, 6⟩, 1), (20, ⟨3, 6⟩, 2)]

theorem g32p_row47_pairing_13 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 1), (10, ⟨-6, -12⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (10, ⟨6, 12⟩, 2)]

theorem g32p_row47_pairing_14 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (10, ⟨-7, -14⟩, 0), (5, ⟨-7, -14⟩, 1), (5, ⟨-7, -14⟩, 2), (10, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (10, ⟨7, 14⟩, 0), (5, ⟨7, 14⟩, 1), (5, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row47_pairing_15 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 2), (8, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (8, ⟨-4, -8⟩, 1), (8, ⟨-4, -8⟩, 2), (15, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (40, ⟨-1, -2⟩, 0), (23, ⟨-1, -2⟩, 1), (23, ⟨-1, -2⟩, 2), (40, ⟨1, 2⟩, 0), (23, ⟨1, 2⟩, 1), (23, ⟨1, 2⟩, 2), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 1), (8, ⟨4, 8⟩, 2), (8, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row47_pairing_16 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (2, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (8, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (11, ⟨-3, -6⟩, 1), (11, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (11, ⟨3, 6⟩, 1), (11, ⟨3, 6⟩, 2), (8, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (2, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row47_pairing_17 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 2), (2, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (8, ⟨-4, -8⟩, 1), (8, ⟨-4, -8⟩, 2), (15, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (46, ⟨-1, -2⟩, 0), (20, ⟨-1, -2⟩, 1), (20, ⟨-1, -2⟩, 2), (46, ⟨1, 2⟩, 0), (20, ⟨1, 2⟩, 1), (20, ⟨1, 2⟩, 2), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 1), (8, ⟨4, 8⟩, 2), (2, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row47_pairing_18 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (2, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (2, ⟨-3, -6⟩, 0), (14, ⟨-3, -6⟩, 1), (14, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (14, ⟨3, 6⟩, 1), (14, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (8, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row47_pairing_19 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 1), (16, ⟨-5, -10⟩, 1), (2, ⟨-4, -8⟩, 1), (20, ⟨-2, -4⟩, 0), (10, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (20, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (10, ⟨2, 4⟩, 2), (2, ⟨4, 8⟩, 2), (16, ⟨5, 10⟩, 2), (2, ⟨20, 40⟩, 2)]

theorem g32p_row47_pairing_20 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row47_terms_20)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row47_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 1), (2, ⟨-8, -16⟩, 1), (10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (10, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (2, ⟨8, 16⟩, 2), (2, ⟨24, 48⟩, 2)]

theorem g32p_row47_pairing_21 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_21)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row47_pairing_22 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_22)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (8, ⟨-9, -18⟩, 1), (2, ⟨-9, -18⟩, 2), (2, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 1), (8, ⟨-3, -6⟩, 0), (18, ⟨-3, -6⟩, 2), (10, ⟨-2, -4⟩, 0), (20, ⟨-2, -4⟩, 1), (8, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (34, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (34, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 0), (20, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (2, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 2), (2, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row47_pairing_23 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row47_terms_23)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row47_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (2, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 2), (16, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-1, -2⟩, 0), (30, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (14, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (30, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (14, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (8, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row47_pairing_24 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-10, -20⟩, 2), (18, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 2), (30, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (28, ⟨-1, -2⟩, 2), (30, ⟨1, 2⟩, 0), (28, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (18, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (2, ⟨10, 20⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row47_pairing_25 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row47_pairing_26 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (8, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (6, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (6, ⟨9, 18⟩, 1), (6, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row47_pairing_27 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (2, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 1), (9, ⟨-9, -18⟩, 2), (2, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 1), (9, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row47_pairing_28 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 1), (10, ⟨-6, -12⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (10, ⟨6, 12⟩, 2)]

theorem g32p_row47_pairing_29 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (8, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (2, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (12, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (12, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 2), (8, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 2)]

theorem g32p_row47_pairing_30 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (2, ⟨-8, -16⟩, 0), (8, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (24, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (20, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (16, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (24, ⟨2, 4⟩, 0), (20, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (2, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2), (2, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (8, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 2)]

theorem g32p_row47_pairing_31 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row47_terms_31)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row47_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (10, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (10, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row47_pairing_32 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (36, ⟨-1, -2⟩, 1), (36, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row47_pairing_33 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row47_terms_33)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row47_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (2, ⟨-9, -18⟩, 0), (2, ⟨-9, -18⟩, 1), (16, ⟨-9, -18⟩, 2), (2, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (12, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (2, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row47_pairing_34 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(10, ⟨-9, -18⟩, 0), (10, ⟨-9, -18⟩, 1), (10, ⟨-9, -18⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (10, ⟨9, 18⟩, 0), (10, ⟨9, 18⟩, 1), (10, ⟨9, 18⟩, 2)]

theorem g32p_row47_pairing_35 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (2, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (16, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (2, ⟨-2, -4⟩, 0), (14, ⟨-2, -4⟩, 1), (14, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (22, ⟨-1, -2⟩, 1), (22, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (22, ⟨1, 2⟩, 1), (22, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (14, ⟨2, 4⟩, 1), (14, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row47_pairing_36 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (20, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (12, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (20, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row47_pairing_37 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (8, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (10, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (11, ⟨-2, -4⟩, 1), (11, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (19, ⟨-1, -2⟩, 1), (19, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (19, ⟨1, 2⟩, 1), (19, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (11, ⟨2, 4⟩, 1), (11, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row47_pairing_38 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 1), (10, ⟨-6, -12⟩, 0), (10, ⟨-6, -12⟩, 2), (2, ⟨-4, -8⟩, 2), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (10, ⟨-2, -4⟩, 0), (10, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (16, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 0), (10, ⟨2, 4⟩, 1), (8, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (2, ⟨4, 8⟩, 1), (10, ⟨6, 12⟩, 0), (10, ⟨6, 12⟩, 1), (2, ⟨60, 120⟩, 2)]

theorem g32p_row47_pairing_39 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_39)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 1), (10, ⟨-8, -16⟩, 0), (10, ⟨-8, -16⟩, 1), (16, ⟨-4, -8⟩, 1), (8, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 2), (16, ⟨4, 8⟩, 2), (10, ⟨8, 16⟩, 0), (10, ⟨8, 16⟩, 2), (2, ⟨64, 128⟩, 2)]

theorem g32p_row47_pairing_40 :
    g32p_cyclotomicPairingCheck 432 (2)
      (g32p_pairingCoefficients 3 g32p_row47_terms_40)
      [1, 1, 1] [-864, 576] = true := by
  decide +kernel

def g32p_row47_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (10, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (8, ⟨-4, -8⟩, 1), (8, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 1), (8, ⟨4, 8⟩, 2), (10, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 2)]

theorem g32p_row47_pairing_41 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (10, ⟨-8, -16⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (8, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (8, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (10, ⟨8, 16⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 1), (1, ⟨80, 160⟩, 2)]

theorem g32p_row47_pairing_42 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 1), (2, ⟨-9, -18⟩, 1), (12, ⟨-3, -6⟩, 2), (12, ⟨3, 6⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨81, 162⟩, 2)]

theorem g32p_row47_pairing_43 :
    g32p_cyclotomicPairingCheck 432 (1)
      (g32p_pairingCoefficients 3 g32p_row47_terms_43)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row47_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 2), (10, ⟨-7, 0⟩, 0), (10, ⟨-7, 0⟩, 1), (10, ⟨-7, 0⟩, 2), (10, ⟨-3, 0⟩, 0), (10, ⟨-3, 0⟩, 1), (10, ⟨-3, 0⟩, 2), (22, ⟨-2, 0⟩, 0), (22, ⟨-2, 0⟩, 1), (22, ⟨-2, 0⟩, 2), (12, ⟨-1, 0⟩, 0), (12, ⟨-1, 0⟩, 1), (12, ⟨-1, 0⟩, 2), (12, ⟨1, 0⟩, 0), (12, ⟨1, 0⟩, 1), (12, ⟨1, 0⟩, 2), (22, ⟨2, 0⟩, 0), (22, ⟨2, 0⟩, 1), (22, ⟨2, 0⟩, 2), (10, ⟨3, 0⟩, 0), (10, ⟨3, 0⟩, 1), (10, ⟨3, 0⟩, 2), (10, ⟨7, 0⟩, 0), (10, ⟨7, 0⟩, 1), (10, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 1), (1, ⟨20, 0⟩, 2)]

theorem g32p_row47_pairing_44 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 2), (8, ⟨-6, 0⟩, 0), (8, ⟨-6, 0⟩, 1), (8, ⟨-6, 0⟩, 2), (20, ⟨-3, 0⟩, 0), (20, ⟨-3, 0⟩, 1), (20, ⟨-3, 0⟩, 2), (6, ⟨-2, 0⟩, 0), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 2), (12, ⟨-1, 0⟩, 0), (12, ⟨-1, 0⟩, 1), (12, ⟨-1, 0⟩, 2), (12, ⟨1, 0⟩, 0), (12, ⟨1, 0⟩, 1), (12, ⟨1, 0⟩, 2), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 1), (6, ⟨2, 0⟩, 2), (20, ⟨3, 0⟩, 0), (20, ⟨3, 0⟩, 1), (20, ⟨3, 0⟩, 2), (8, ⟨6, 0⟩, 0), (8, ⟨6, 0⟩, 1), (8, ⟨6, 0⟩, 2), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 1), (1, ⟨60, 0⟩, 2)]

theorem g32p_row47_pairing_45 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 2), (10, ⟨-8, 0⟩, 0), (10, ⟨-8, 0⟩, 1), (10, ⟨-8, 0⟩, 2), (8, ⟨-4, 0⟩, 0), (8, ⟨-4, 0⟩, 1), (8, ⟨-4, 0⟩, 2), (8, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (8, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (8, ⟨4, 0⟩, 0), (8, ⟨4, 0⟩, 1), (8, ⟨4, 0⟩, 2), (10, ⟨8, 0⟩, 0), (10, ⟨8, 0⟩, 1), (10, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 1), (1, ⟨64, 0⟩, 2)]

theorem g32p_row47_pairing_46 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row47_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 2), (10, ⟨-8, 0⟩, 0), (10, ⟨-8, 0⟩, 1), (10, ⟨-8, 0⟩, 2), (8, ⟨-4, 0⟩, 0), (8, ⟨-4, 0⟩, 1), (8, ⟨-4, 0⟩, 2), (8, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (8, ⟨-2, 0⟩, 2), (8, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (8, ⟨2, 0⟩, 2), (8, ⟨4, 0⟩, 0), (8, ⟨4, 0⟩, 1), (8, ⟨4, 0⟩, 2), (10, ⟨8, 0⟩, 0), (10, ⟨8, 0⟩, 1), (10, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 1), (1, ⟨80, 0⟩, 2)]

theorem g32p_row47_pairing_47 :
    g32p_cyclotomicPairingCheck 432 (0)
      (g32p_pairingCoefficients 3 g32p_row47_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row47_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 47 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨47, -1, [(8, 1), (10, 1), (21, 1), (24, 1), (32, 1), (34, 1), (41, 2), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end
