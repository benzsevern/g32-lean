import HodgeLean.Foundations.Program.G32PropFourSixPacked0003
import HodgeLean.Papers.PapersG32CertificatesDefs

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row48_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(64, ⟨-1, -2⟩, 2), (64, ⟨-1, -2⟩, 5), (64, ⟨1, 2⟩, 1), (64, ⟨1, 2⟩, 4)]

theorem g32p_row48_pairing_0 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_0)
      [1, -1, 1] [0, 64, 0, 64, 0, -128] = true := by
  decide +kernel

def g32p_row48_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row48_pairing_1 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row48_pairing_2 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row48_pairing_3 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row48_pairing_4 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (10, ⟨-3, -6⟩, 4), (32, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (36, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (10, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 4)]

theorem g32p_row48_pairing_5 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (10, ⟨-3, -6⟩, 4), (32, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (36, ⟨1, 2⟩, 4), (32, ⟨1, 2⟩, 5), (10, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 4)]

theorem g32p_row48_pairing_6 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 2), (36, ⟨-2, -4⟩, 2), (10, ⟨-2, -4⟩, 4), (32, ⟨-2, -4⟩, 5), (32, ⟨2, 4⟩, 1), (10, ⟨2, 4⟩, 2), (36, ⟨2, 4⟩, 4), (2, ⟨6, 12⟩, 4)]

theorem g32p_row48_pairing_7 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_7)
      [1, -1, 1] [0, 64, 0, 64, 0, -128] = true := by
  decide +kernel

def g32p_row48_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row48_pairing_8 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (16, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (28, ⟨-2, -4⟩, 4), (16, ⟨-2, -4⟩, 5), (16, ⟨2, 4⟩, 1), (28, ⟨2, 4⟩, 2), (18, ⟨2, 4⟩, 4), (16, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row48_pairing_9 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (16, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (28, ⟨-2, -4⟩, 4), (16, ⟨-2, -4⟩, 5), (16, ⟨2, 4⟩, 1), (28, ⟨2, 4⟩, 2), (18, ⟨2, 4⟩, 4), (16, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row48_pairing_10 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (10, ⟨-7, -14⟩, 2), (28, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 5), (16, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 2), (8, ⟨-1, -2⟩, 4), (32, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (16, ⟨1, 2⟩, 5), (16, ⟨3, 6⟩, 1), (28, ⟨3, 6⟩, 4), (10, ⟨7, 14⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row48_pairing_11 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row48_terms_11)
      [1, -1, 1] [-384, -320, -128, 320, 256, -128] = true := by
  decide +kernel

def g32p_row48_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (8, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 5), (48, ⟨-1, -2⟩, 1), (54, ⟨-1, -2⟩, 4), (54, ⟨1, 2⟩, 2), (48, ⟨1, 2⟩, 5), (16, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row48_pairing_12 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row48_pairing_13 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row48_pairing_14 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row48_pairing_15 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row48_pairing_16 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row48_pairing_17 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row48_pairing_18 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row48_pairing_19 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 2), (38, ⟨-4, -8⟩, 2), (16, ⟨-4, -8⟩, 5), (16, ⟨4, 8⟩, 1), (38, ⟨4, 8⟩, 4), (2, ⟨20, 40⟩, 4)]

theorem g32p_row48_pairing_20 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row48_terms_20)
      [1, -1, 1] [-384, -320, -128, 320, 256, -128] = true := by
  decide +kernel

def g32p_row48_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 2), (10, ⟨-8, -16⟩, 2), (10, ⟨8, 16⟩, 4), (2, ⟨24, 48⟩, 4)]

theorem g32p_row48_pairing_21 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row48_terms_21)
      [1, -1, 1] [-384, -384, -128, 256, 256] = true := by
  decide +kernel

def g32p_row48_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row48_pairing_22 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (10, ⟨-6, -12⟩, 2), (36, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 5), (32, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 4), (10, ⟨6, 12⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row48_pairing_23 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row48_terms_23)
      [1, -1, 1] [-384, -320, -128, 320, 256, -128] = true := by
  decide +kernel

def g32p_row48_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (10, ⟨-6, -12⟩, 2), (36, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 5), (32, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 4), (10, ⟨6, 12⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row48_pairing_24 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row48_terms_24)
      [1, -1, 1] [-384, -320, -128, 320, 256, -128] = true := by
  decide +kernel

def g32p_row48_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (10, ⟨-10, -20⟩, 4), (16, ⟨-2, -4⟩, 1), (28, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (16, ⟨-2, -4⟩, 5), (16, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (28, ⟨2, 4⟩, 4), (16, ⟨2, 4⟩, 5), (10, ⟨10, 20⟩, 2), (2, ⟨30, 60⟩, 4)]

theorem g32p_row48_pairing_25 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row48_pairing_26 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row48_pairing_27 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row48_pairing_28 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row48_pairing_29 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (10, ⟨-8, -16⟩, 4), (10, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 4)]

theorem g32p_row48_pairing_30 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (10, ⟨-8, -16⟩, 4), (10, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 4)]

theorem g32p_row48_pairing_31 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row48_pairing_32 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (16, ⟨-3, -6⟩, 1), (38, ⟨-3, -6⟩, 4), (24, ⟨-1, -2⟩, 2), (48, ⟨-1, -2⟩, 5), (48, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 4), (38, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row48_pairing_33 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (16, ⟨-3, -6⟩, 1), (38, ⟨-3, -6⟩, 4), (24, ⟨-1, -2⟩, 2), (48, ⟨-1, -2⟩, 5), (48, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 4), (38, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row48_pairing_34 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row48_pairing_35 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row48_pairing_36 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row48_pairing_37 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 5), (8, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row48_pairing_38 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 2), (28, ⟨-4, -8⟩, 2), (10, ⟨-4, -8⟩, 4), (16, ⟨-4, -8⟩, 5), (16, ⟨4, 8⟩, 1), (10, ⟨4, 8⟩, 2), (28, ⟨4, 8⟩, 4), (2, ⟨60, 120⟩, 4)]

theorem g32p_row48_pairing_39 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row48_terms_39)
      [1, -1, 1] [-384, -320, -128, 320, 256, -128] = true := by
  decide +kernel

def g32p_row48_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 2), (2, ⟨64, 128⟩, 4)]

theorem g32p_row48_pairing_40 :
    g32p_cyclotomicPairingCheck 384 (1)
      (g32p_pairingCoefficients 6 g32p_row48_terms_40)
      [1, -1, 1] [-384, -384, -128, 256, 256] = true := by
  decide +kernel

def g32p_row48_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 4)]

theorem g32p_row48_pairing_41 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (1, ⟨80, 160⟩, 2), (1, ⟨80, 160⟩, 4)]

theorem g32p_row48_pairing_42 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 2), (10, ⟨-9, -18⟩, 2), (32, ⟨-3, -6⟩, 1), (36, ⟨-3, -6⟩, 4), (32, ⟨-1, -2⟩, 1), (16, ⟨-1, -2⟩, 4), (16, ⟨1, 2⟩, 2), (32, ⟨1, 2⟩, 5), (36, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 5), (10, ⟨9, 18⟩, 4), (2, ⟨81, 162⟩, 4)]

theorem g32p_row48_pairing_43 :
    g32p_cyclotomicPairingCheck 384 (2)
      (g32p_pairingCoefficients 6 g32p_row48_terms_43)
      [1, -1, 1] [-768, -896, -256, 384, 512, 256] = true := by
  decide +kernel

def g32p_row48_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 4), (4, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (4, ⟨-2, 0⟩, 2), (8, ⟨-2, 0⟩, 3), (4, ⟨-2, 0⟩, 4), (8, ⟨-2, 0⟩, 5), (4, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (4, ⟨2, 0⟩, 2), (8, ⟨2, 0⟩, 3), (4, ⟨2, 0⟩, 4), (8, ⟨2, 0⟩, 5), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row48_pairing_44 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 4), (4, ⟨-2, 0⟩, 0), (8, ⟨-2, 0⟩, 1), (4, ⟨-2, 0⟩, 2), (8, ⟨-2, 0⟩, 3), (4, ⟨-2, 0⟩, 4), (8, ⟨-2, 0⟩, 5), (4, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 1), (4, ⟨2, 0⟩, 2), (8, ⟨2, 0⟩, 3), (4, ⟨2, 0⟩, 4), (8, ⟨2, 0⟩, 5), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row48_pairing_45 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 4), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row48_pairing_46 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row48_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row48_pairing_47 :
    g32p_cyclotomicPairingCheck 384 (0)
      (g32p_pairingCoefficients 6 g32p_row48_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row48_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 48 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨48, -1, [(12, 1), (21, 1), (22, 1), (24, 1), (25, 1), (40, 1), (41, 1), (44, 2)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row49_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (9, ⟨-1, -2⟩, 6), (9, ⟨-1, -2⟩, 7), (9, ⟨-1, -2⟩, 8), (9, ⟨-1, -2⟩, 9), (9, ⟨-1, -2⟩, 10), (9, ⟨-1, -2⟩, 11), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (9, ⟨1, 2⟩, 6), (9, ⟨1, 2⟩, 7), (9, ⟨1, 2⟩, 8), (9, ⟨1, 2⟩, 9), (9, ⟨1, 2⟩, 10), (9, ⟨1, 2⟩, 11)]

theorem g32p_row49_pairing_0 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_0)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 6), (4, ⟨-3, -6⟩, 8), (4, ⟨-3, -6⟩, 10), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 6), (4, ⟨3, 6⟩, 8), (4, ⟨3, 6⟩, 10)]

theorem g32p_row49_pairing_1 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_1)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 8), (2, ⟨-3, -6⟩, 10), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 6), (4, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (6, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 6), (6, ⟨-1, -2⟩, 8), (6, ⟨-1, -2⟩, 10), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 6), (4, ⟨1, 2⟩, 8), (4, ⟨1, 2⟩, 10), (3, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 6), (3, ⟨2, 4⟩, 8), (3, ⟨2, 4⟩, 10), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 8), (2, ⟨3, 6⟩, 10), (1, ⟨4, 8⟩, 8), (1, ⟨4, 8⟩, 10)]

theorem g32p_row49_pairing_2 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_2)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 8), (2, ⟨-3, -6⟩, 10), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 6), (4, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (6, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 6), (6, ⟨-1, -2⟩, 8), (6, ⟨-1, -2⟩, 10), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 6), (4, ⟨1, 2⟩, 8), (4, ⟨1, 2⟩, 10), (3, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 6), (3, ⟨2, 4⟩, 8), (3, ⟨2, 4⟩, 10), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 8), (2, ⟨3, 6⟩, 10), (1, ⟨4, 8⟩, 8), (1, ⟨4, 8⟩, 10)]

theorem g32p_row49_pairing_3 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_3)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 6), (4, ⟨-3, -6⟩, 8), (4, ⟨-3, -6⟩, 10), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 6), (4, ⟨3, 6⟩, 8), (4, ⟨3, 6⟩, 10)]

theorem g32p_row49_pairing_4 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_4)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 4), (1, ⟨-5, -10⟩, 10), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 8), (2, ⟨-3, -6⟩, 10), (6, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 6), (6, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (3, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (3, ⟨-1, -2⟩, 6), (9, ⟨-1, -2⟩, 7), (4, ⟨-1, -2⟩, 8), (9, ⟨-1, -2⟩, 9), (3, ⟨-1, -2⟩, 10), (9, ⟨-1, -2⟩, 11), (3, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (3, ⟨1, 2⟩, 6), (9, ⟨1, 2⟩, 7), (3, ⟨1, 2⟩, 8), (9, ⟨1, 2⟩, 9), (4, ⟨1, 2⟩, 10), (9, ⟨1, 2⟩, 11), (6, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 6), (4, ⟨2, 4⟩, 8), (6, ⟨2, 4⟩, 10), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 8), (2, ⟨3, 6⟩, 10), (1, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 8)]

theorem g32p_row49_pairing_5 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_5)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 4), (1, ⟨-5, -10⟩, 10), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 8), (2, ⟨-3, -6⟩, 10), (6, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 6), (6, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (3, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (3, ⟨-1, -2⟩, 6), (9, ⟨-1, -2⟩, 7), (4, ⟨-1, -2⟩, 8), (9, ⟨-1, -2⟩, 9), (3, ⟨-1, -2⟩, 10), (9, ⟨-1, -2⟩, 11), (3, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (3, ⟨1, 2⟩, 6), (9, ⟨1, 2⟩, 7), (3, ⟨1, 2⟩, 8), (9, ⟨1, 2⟩, 9), (4, ⟨1, 2⟩, 10), (9, ⟨1, 2⟩, 11), (6, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 6), (4, ⟨2, 4⟩, 8), (6, ⟨2, 4⟩, 10), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 8), (2, ⟨3, 6⟩, 10), (1, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 8)]

theorem g32p_row49_pairing_6 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_6)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 10), (5, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (5, ⟨-3, -6⟩, 6), (1, ⟨-3, -6⟩, 8), (8, ⟨-3, -6⟩, 10), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 7), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 7), (9, ⟨-1, -2⟩, 9), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 5), (9, ⟨1, 2⟩, 9), (9, ⟨1, 2⟩, 11), (9, ⟨2, 4⟩, 5), (9, ⟨2, 4⟩, 11), (5, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 6), (8, ⟨3, 6⟩, 8), (1, ⟨3, 6⟩, 10), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 8)]

theorem g32p_row49_pairing_7 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_7)
      [1, 0, -1, 0, 1] [0, -27, 27, -27, 0, -27, 27, -27, 0, 54, -54, 54] = true := by
  decide +kernel

def g32p_row49_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 6), (4, ⟨-3, -6⟩, 8), (4, ⟨-3, -6⟩, 10), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 6), (4, ⟨3, 6⟩, 8), (4, ⟨3, 6⟩, 10)]

theorem g32p_row49_pairing_8 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_8)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 4), (1, ⟨-10, -20⟩, 10), (2, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 4), (2, ⟨-5, -10⟩, 6), (2, ⟨-5, -10⟩, 10), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 8), (2, ⟨-3, -6⟩, 10), (2, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 4), (9, ⟨-2, -4⟩, 5), (2, ⟨-2, -4⟩, 6), (2, ⟨-2, -4⟩, 10), (9, ⟨-2, -4⟩, 11), (5, ⟨-1, -2⟩, 0), (5, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (5, ⟨-1, -2⟩, 6), (5, ⟨-1, -2⟩, 8), (9, ⟨-1, -2⟩, 9), (8, ⟨-1, -2⟩, 10), (9, ⟨-1, -2⟩, 11), (5, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (5, ⟨1, 2⟩, 4), (5, ⟨1, 2⟩, 6), (9, ⟨1, 2⟩, 7), (8, ⟨1, 2⟩, 8), (9, ⟨1, 2⟩, 9), (5, ⟨1, 2⟩, 10), (2, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 6), (9, ⟨2, 4⟩, 7), (2, ⟨2, 4⟩, 8), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 8), (2, ⟨3, 6⟩, 10), (2, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 2), (2, ⟨5, 10⟩, 6), (2, ⟨5, 10⟩, 8), (1, ⟨10, 20⟩, 2), (1, ⟨10, 20⟩, 8)]

theorem g32p_row49_pairing_9 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_9)
      [1, 0, -1, 0, 1] [0, 27, 27, 27, 0, 27, 27, 27, 0, -54, -54, -54] = true := by
  decide +kernel

def g32p_row49_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 4), (1, ⟨-10, -20⟩, 10), (2, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 4), (2, ⟨-5, -10⟩, 6), (2, ⟨-5, -10⟩, 10), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 8), (2, ⟨-3, -6⟩, 10), (2, ⟨-2, -4⟩, 0), (2, ⟨-2, -4⟩, 4), (9, ⟨-2, -4⟩, 5), (2, ⟨-2, -4⟩, 6), (2, ⟨-2, -4⟩, 10), (9, ⟨-2, -4⟩, 11), (5, ⟨-1, -2⟩, 0), (5, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (8, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (5, ⟨-1, -2⟩, 6), (5, ⟨-1, -2⟩, 8), (9, ⟨-1, -2⟩, 9), (8, ⟨-1, -2⟩, 10), (9, ⟨-1, -2⟩, 11), (5, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (5, ⟨1, 2⟩, 4), (5, ⟨1, 2⟩, 6), (9, ⟨1, 2⟩, 7), (8, ⟨1, 2⟩, 8), (9, ⟨1, 2⟩, 9), (5, ⟨1, 2⟩, 10), (2, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 6), (9, ⟨2, 4⟩, 7), (2, ⟨2, 4⟩, 8), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 8), (2, ⟨3, 6⟩, 10), (2, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 2), (2, ⟨5, 10⟩, 6), (2, ⟨5, 10⟩, 8), (1, ⟨10, 20⟩, 2), (1, ⟨10, 20⟩, 8)]

theorem g32p_row49_pairing_10 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_10)
      [1, 0, -1, 0, 1] [0, 27, 27, 27, 0, 27, 27, 27, 0, -54, -54, -54] = true := by
  decide +kernel

def g32p_row49_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 4), (1, ⟨-15, -30⟩, 10), (8, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (8, ⟨-3, -6⟩, 6), (9, ⟨-3, -6⟩, 7), (4, ⟨-3, -6⟩, 8), (8, ⟨-3, -6⟩, 10), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (9, ⟨3, 6⟩, 5), (8, ⟨3, 6⟩, 6), (8, ⟨3, 6⟩, 8), (4, ⟨3, 6⟩, 10), (9, ⟨3, 6⟩, 11), (1, ⟨15, 30⟩, 2), (1, ⟨15, 30⟩, 8)]

theorem g32p_row49_pairing_11 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_11)
      [1, 0, -1, 0, 1] [0, -27, 27, -27, 0, -27, 27, -27, 0, 54, -54, 54] = true := by
  decide +kernel

def g32p_row49_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 4), (1, ⟨-15, -30⟩, 10), (4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 6), (4, ⟨-6, -12⟩, 8), (1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 6), (1, ⟨-3, -6⟩, 8), (4, ⟨-3, -6⟩, 10), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 5), (9, ⟨-1, -2⟩, 7), (9, ⟨-1, -2⟩, 9), (9, ⟨-1, -2⟩, 11), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 5), (9, ⟨1, 2⟩, 7), (9, ⟨1, 2⟩, 9), (9, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 6), (4, ⟨3, 6⟩, 8), (1, ⟨3, 6⟩, 10), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 6), (4, ⟨6, 12⟩, 10), (1, ⟨15, 30⟩, 2), (1, ⟨15, 30⟩, 8)]

theorem g32p_row49_pairing_12 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_12)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 6), (4, ⟨-3, -6⟩, 8), (4, ⟨-3, -6⟩, 10), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 6), (4, ⟨3, 6⟩, 8), (4, ⟨3, 6⟩, 10)]

theorem g32p_row49_pairing_13 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_13)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 4), (4, ⟨-6, -12⟩, 6), (4, ⟨-6, -12⟩, 8), (4, ⟨-6, -12⟩, 10), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 6), (4, ⟨6, 12⟩, 8), (4, ⟨6, 12⟩, 10)]

theorem g32p_row49_pairing_14 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_14)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (4, ⟨-7, -14⟩, 0), (4, ⟨-7, -14⟩, 2), (4, ⟨-7, -14⟩, 4), (4, ⟨-7, -14⟩, 6), (5, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (5, ⟨-2, -4⟩, 6), (5, ⟨-2, -4⟩, 8), (5, ⟨-2, -4⟩, 10), (5, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 2), (5, ⟨2, 4⟩, 4), (5, ⟨2, 4⟩, 6), (8, ⟨2, 4⟩, 8), (8, ⟨2, 4⟩, 10), (4, ⟨7, 14⟩, 0), (4, ⟨7, 14⟩, 6), (4, ⟨7, 14⟩, 8), (4, ⟨7, 14⟩, 10), (1, ⟨20, 40⟩, 8), (1, ⟨20, 40⟩, 10)]

theorem g32p_row49_pairing_15 :
    g32p_cyclotomicPairingCheck 324 (1)
      (g32p_pairingCoefficients 12 g32p_row49_terms_15)
      [1, 0, -1, 0, 1] [-324, 0, -378, 0, -108, 0, 162, 0, 216, 0, 108] = true := by
  decide +kernel

def g32p_row49_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (2, ⟨-6, -12⟩, 2), (2, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 8), (2, ⟨-6, -12⟩, 10), (2, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 6), (2, ⟨-5, -10⟩, 8), (2, ⟨-5, -10⟩, 10), (1, ⟨-4, -8⟩, 0), (1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (1, ⟨-4, -8⟩, 6), (4, ⟨-4, -8⟩, 8), (4, ⟨-4, -8⟩, 10), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 6), (4, ⟨-1, -2⟩, 8), (4, ⟨-1, -2⟩, 10), (6, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 6), (6, ⟨1, 2⟩, 8), (6, ⟨1, 2⟩, 10), (1, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 2), (4, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 6), (1, ⟨4, 8⟩, 8), (1, ⟨4, 8⟩, 10), (2, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 2), (2, ⟨5, 10⟩, 4), (2, ⟨5, 10⟩, 6), (2, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 4), (2, ⟨6, 12⟩, 8), (2, ⟨6, 12⟩, 10), (1, ⟨20, 40⟩, 8), (1, ⟨20, 40⟩, 10)]

theorem g32p_row49_pairing_16 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_16)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (2, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 6), (2, ⟨-8, -16⟩, 8), (2, ⟨-8, -16⟩, 10), (2, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 6), (2, ⟨-5, -10⟩, 8), (2, ⟨-5, -10⟩, 10), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 8), (2, ⟨-3, -6⟩, 10), (5, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (5, ⟨-2, -4⟩, 6), (5, ⟨-2, -4⟩, 8), (5, ⟨-2, -4⟩, 10), (5, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 2), (5, ⟨2, 4⟩, 4), (5, ⟨2, 4⟩, 6), (8, ⟨2, 4⟩, 8), (8, ⟨2, 4⟩, 10), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 8), (2, ⟨3, 6⟩, 10), (2, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 2), (2, ⟨5, 10⟩, 4), (2, ⟨5, 10⟩, 6), (2, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 2), (2, ⟨8, 16⟩, 4), (2, ⟨8, 16⟩, 6), (1, ⟨20, 40⟩, 8), (1, ⟨20, 40⟩, 10)]

theorem g32p_row49_pairing_17 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_17)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (2, ⟨-6, -12⟩, 2), (2, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 8), (2, ⟨-6, -12⟩, 10), (2, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 6), (2, ⟨-5, -10⟩, 8), (2, ⟨-5, -10⟩, 10), (1, ⟨-4, -8⟩, 0), (1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (1, ⟨-4, -8⟩, 6), (4, ⟨-4, -8⟩, 8), (4, ⟨-4, -8⟩, 10), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 6), (4, ⟨-1, -2⟩, 8), (4, ⟨-1, -2⟩, 10), (6, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 6), (6, ⟨1, 2⟩, 8), (6, ⟨1, 2⟩, 10), (1, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 2), (4, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 6), (1, ⟨4, 8⟩, 8), (1, ⟨4, 8⟩, 10), (2, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 2), (2, ⟨5, 10⟩, 4), (2, ⟨5, 10⟩, 6), (2, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 4), (2, ⟨6, 12⟩, 8), (2, ⟨6, 12⟩, 10), (1, ⟨20, 40⟩, 8), (1, ⟨20, 40⟩, 10)]

theorem g32p_row49_pairing_18 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_18)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (2, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 6), (2, ⟨-8, -16⟩, 8), (2, ⟨-8, -16⟩, 10), (2, ⟨-5, -10⟩, 0), (2, ⟨-5, -10⟩, 6), (2, ⟨-5, -10⟩, 8), (2, ⟨-5, -10⟩, 10), (2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 8), (2, ⟨-3, -6⟩, 10), (5, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 2), (8, ⟨-2, -4⟩, 4), (5, ⟨-2, -4⟩, 6), (5, ⟨-2, -4⟩, 8), (5, ⟨-2, -4⟩, 10), (5, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 2), (5, ⟨2, 4⟩, 4), (5, ⟨2, 4⟩, 6), (8, ⟨2, 4⟩, 8), (8, ⟨2, 4⟩, 10), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 8), (2, ⟨3, 6⟩, 10), (2, ⟨5, 10⟩, 0), (2, ⟨5, 10⟩, 2), (2, ⟨5, 10⟩, 4), (2, ⟨5, 10⟩, 6), (2, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 2), (2, ⟨8, 16⟩, 4), (2, ⟨8, 16⟩, 6), (1, ⟨20, 40⟩, 8), (1, ⟨20, 40⟩, 10)]

theorem g32p_row49_pairing_19 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_19)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 4), (1, ⟨-20, -40⟩, 10), (1, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 2), (4, ⟨-5, -10⟩, 4), (1, ⟨-5, -10⟩, 6), (1, ⟨-5, -10⟩, 8), (4, ⟨-5, -10⟩, 10), (9, ⟨-4, -8⟩, 1), (9, ⟨-4, -8⟩, 7), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 6), (4, ⟨-2, -4⟩, 8), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (4, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (4, ⟨-1, -2⟩, 6), (4, ⟨-1, -2⟩, 8), (9, ⟨-1, -2⟩, 9), (4, ⟨-1, -2⟩, 10), (9, ⟨-1, -2⟩, 11), (4, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (4, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 6), (9, ⟨1, 2⟩, 7), (4, ⟨1, 2⟩, 8), (9, ⟨1, 2⟩, 9), (4, ⟨1, 2⟩, 10), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 6), (4, ⟨2, 4⟩, 10), (9, ⟨4, 8⟩, 5), (9, ⟨4, 8⟩, 11), (1, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 6), (4, ⟨5, 10⟩, 8), (1, ⟨5, 10⟩, 10), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 8)]

theorem g32p_row49_pairing_20 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_20)
      [1, 0, -1, 0, 1] [0, -27, 27, -27, 0, -27, 27, -27, 0, 54, -54, 54] = true := by
  decide +kernel

def g32p_row49_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 4), (1, ⟨-24, -48⟩, 10), (4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 6), (4, ⟨-6, -12⟩, 8), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 6), (4, ⟨-3, -6⟩, 8), (4, ⟨-3, -6⟩, 10), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 6), (4, ⟨3, 6⟩, 8), (4, ⟨3, 6⟩, 10), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 6), (4, ⟨6, 12⟩, 10), (1, ⟨24, 48⟩, 2), (1, ⟨24, 48⟩, 8)]

theorem g32p_row49_pairing_21 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_21)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 6), (4, ⟨-9, -18⟩, 8), (4, ⟨-9, -18⟩, 10), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 6), (4, ⟨9, 18⟩, 8), (4, ⟨9, 18⟩, 10)]

theorem g32p_row49_pairing_22 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_22)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 4), (1, ⟨-30, -60⟩, 10), (2, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 4), (2, ⟨-9, -18⟩, 8), (2, ⟨-9, -18⟩, 10), (2, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 6), (2, ⟨-6, -12⟩, 10), (3, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 6), (6, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 7), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 7), (9, ⟨-1, -2⟩, 9), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 5), (9, ⟨1, 2⟩, 9), (9, ⟨1, 2⟩, 11), (9, ⟨2, 4⟩, 5), (9, ⟨2, 4⟩, 11), (3, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 6), (1, ⟨3, 6⟩, 8), (6, ⟨3, 6⟩, 10), (2, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 6), (2, ⟨6, 12⟩, 8), (2, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 4), (2, ⟨9, 18⟩, 8), (2, ⟨9, 18⟩, 10), (1, ⟨30, 60⟩, 2), (1, ⟨30, 60⟩, 8)]

theorem g32p_row49_pairing_23 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_23)
      [1, 0, -1, 0, 1] [0, -27, 27, -27, 0, -27, 27, -27, 0, 54, -54, 54] = true := by
  decide +kernel

def g32p_row49_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 4), (1, ⟨-30, -60⟩, 10), (2, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 4), (2, ⟨-9, -18⟩, 8), (2, ⟨-9, -18⟩, 10), (2, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 6), (2, ⟨-6, -12⟩, 10), (3, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 6), (6, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 7), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 7), (9, ⟨-1, -2⟩, 9), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 5), (9, ⟨1, 2⟩, 9), (9, ⟨1, 2⟩, 11), (9, ⟨2, 4⟩, 5), (9, ⟨2, 4⟩, 11), (3, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 6), (1, ⟨3, 6⟩, 8), (6, ⟨3, 6⟩, 10), (2, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 6), (2, ⟨6, 12⟩, 8), (2, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 4), (2, ⟨9, 18⟩, 8), (2, ⟨9, 18⟩, 10), (1, ⟨30, 60⟩, 2), (1, ⟨30, 60⟩, 8)]

theorem g32p_row49_pairing_24 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_24)
      [1, 0, -1, 0, 1] [0, -27, 27, -27, 0, -27, 27, -27, 0, 54, -54, 54] = true := by
  decide +kernel

def g32p_row49_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 4), (1, ⟨-30, -60⟩, 10), (9, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (9, ⟨-3, -6⟩, 6), (9, ⟨-3, -6⟩, 8), (8, ⟨-3, -6⟩, 10), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 7), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 7), (9, ⟨-1, -2⟩, 9), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 5), (9, ⟨1, 2⟩, 9), (9, ⟨1, 2⟩, 11), (9, ⟨2, 4⟩, 5), (9, ⟨2, 4⟩, 11), (9, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (9, ⟨3, 6⟩, 4), (9, ⟨3, 6⟩, 6), (8, ⟨3, 6⟩, 8), (9, ⟨3, 6⟩, 10), (1, ⟨30, 60⟩, 2), (1, ⟨30, 60⟩, 8)]

theorem g32p_row49_pairing_25 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_25)
      [1, 0, -1, 0, 1] [0, -27, 27, -27, 0, -27, 27, -27, 0, 54, -54, 54] = true := by
  decide +kernel

def g32p_row49_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 6), (4, ⟨-9, -18⟩, 8), (4, ⟨-9, -18⟩, 10), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 6), (4, ⟨9, 18⟩, 8), (4, ⟨9, 18⟩, 10)]

theorem g32p_row49_pairing_26 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_26)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (2, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 4), (2, ⟨-9, -18⟩, 6), (2, ⟨-9, -18⟩, 8), (2, ⟨-9, -18⟩, 10), (2, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 4), (2, ⟨9, 18⟩, 6), (4, ⟨9, 18⟩, 8), (4, ⟨9, 18⟩, 10), (1, ⟨36, 72⟩, 8), (1, ⟨36, 72⟩, 10)]

theorem g32p_row49_pairing_27 :
    g32p_cyclotomicPairingCheck 324 (1)
      (g32p_pairingCoefficients 12 g32p_row49_terms_27)
      [1, 0, -1, 0, 1] [-324, 0, -378, 0, -108, 0, 162, 0, 216, 0, 108] = true := by
  decide +kernel

def g32p_row49_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (2, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 4), (2, ⟨-9, -18⟩, 6), (2, ⟨-9, -18⟩, 8), (2, ⟨-9, -18⟩, 10), (2, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 4), (2, ⟨9, 18⟩, 6), (4, ⟨9, 18⟩, 8), (4, ⟨9, 18⟩, 10), (1, ⟨36, 72⟩, 8), (1, ⟨36, 72⟩, 10)]

theorem g32p_row49_pairing_28 :
    g32p_cyclotomicPairingCheck 324 (1)
      (g32p_pairingCoefficients 12 g32p_row49_terms_28)
      [1, 0, -1, 0, 1] [-324, 0, -378, 0, -108, 0, 162, 0, 216, 0, 108] = true := by
  decide +kernel

def g32p_row49_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 4), (4, ⟨-6, -12⟩, 6), (4, ⟨-6, -12⟩, 8), (4, ⟨-6, -12⟩, 10), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 6), (4, ⟨6, 12⟩, 8), (4, ⟨6, 12⟩, 10)]

theorem g32p_row49_pairing_29 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_29)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 4), (1, ⟨-40, -80⟩, 10), (2, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 4), (2, ⟨-8, -16⟩, 6), (2, ⟨-8, -16⟩, 10), (2, ⟨-6, -12⟩, 2), (2, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 8), (2, ⟨-6, -12⟩, 10), (3, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 6), (4, ⟨-2, -4⟩, 8), (3, ⟨-2, -4⟩, 10), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 6), (4, ⟨-1, -2⟩, 8), (4, ⟨-1, -2⟩, 10), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 6), (4, ⟨1, 2⟩, 8), (4, ⟨1, 2⟩, 10), (3, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 6), (3, ⟨2, 4⟩, 8), (4, ⟨2, 4⟩, 10), (2, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 4), (2, ⟨6, 12⟩, 8), (2, ⟨6, 12⟩, 10), (2, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 2), (2, ⟨8, 16⟩, 6), (2, ⟨8, 16⟩, 8), (1, ⟨40, 80⟩, 2), (1, ⟨40, 80⟩, 8)]

theorem g32p_row49_pairing_30 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_30)
      [1, 0, -1, 0, 1] [0, 0, 54, 0, 0, 0, 54, 0, 0, 0, -108] = true := by
  decide +kernel

def g32p_row49_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 4), (1, ⟨-40, -80⟩, 10), (2, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 4), (2, ⟨-8, -16⟩, 6), (2, ⟨-8, -16⟩, 10), (2, ⟨-6, -12⟩, 2), (2, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 8), (2, ⟨-6, -12⟩, 10), (3, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 6), (4, ⟨-2, -4⟩, 8), (3, ⟨-2, -4⟩, 10), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 4), (4, ⟨-1, -2⟩, 6), (4, ⟨-1, -2⟩, 8), (4, ⟨-1, -2⟩, 10), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 4), (4, ⟨1, 2⟩, 6), (4, ⟨1, 2⟩, 8), (4, ⟨1, 2⟩, 10), (3, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 6), (3, ⟨2, 4⟩, 8), (4, ⟨2, 4⟩, 10), (2, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 4), (2, ⟨6, 12⟩, 8), (2, ⟨6, 12⟩, 10), (2, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 2), (2, ⟨8, 16⟩, 6), (2, ⟨8, 16⟩, 8), (1, ⟨40, 80⟩, 2), (1, ⟨40, 80⟩, 8)]

theorem g32p_row49_pairing_31 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_31)
      [1, 0, -1, 0, 1] [0, 0, 54, 0, 0, 0, 54, 0, 0, 0, -108] = true := by
  decide +kernel

def g32p_row49_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 6), (4, ⟨-9, -18⟩, 8), (4, ⟨-9, -18⟩, 10), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 6), (4, ⟨9, 18⟩, 8), (4, ⟨9, 18⟩, 10)]

theorem g32p_row49_pairing_32 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_32)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 4), (1, ⟨-45, -90⟩, 10), (2, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 4), (2, ⟨-9, -18⟩, 6), (4, ⟨-9, -18⟩, 8), (2, ⟨-9, -18⟩, 10), (9, ⟨-3, -6⟩, 5), (9, ⟨-3, -6⟩, 11), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 7), (2, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 4), (2, ⟨9, 18⟩, 6), (2, ⟨9, 18⟩, 8), (4, ⟨9, 18⟩, 10), (1, ⟨45, 90⟩, 2), (1, ⟨45, 90⟩, 8)]

theorem g32p_row49_pairing_33 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_33)
      [1, 0, -1, 0, 1] [0, 27, 27, 27, 0, 27, 27, 27, 0, -54, -54, -54] = true := by
  decide +kernel

def g32p_row49_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 4), (1, ⟨-45, -90⟩, 10), (2, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 4), (2, ⟨-9, -18⟩, 6), (4, ⟨-9, -18⟩, 8), (2, ⟨-9, -18⟩, 10), (9, ⟨-3, -6⟩, 5), (9, ⟨-3, -6⟩, 11), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 7), (2, ⟨9, 18⟩, 0), (2, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 4), (2, ⟨9, 18⟩, 6), (2, ⟨9, 18⟩, 8), (4, ⟨9, 18⟩, 10), (1, ⟨45, 90⟩, 2), (1, ⟨45, 90⟩, 8)]

theorem g32p_row49_pairing_34 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_34)
      [1, 0, -1, 0, 1] [0, 27, 27, 27, 0, 27, 27, 27, 0, -54, -54, -54] = true := by
  decide +kernel

def g32p_row49_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 6), (4, ⟨-9, -18⟩, 8), (4, ⟨-9, -18⟩, 10), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 6), (4, ⟨9, 18⟩, 8), (4, ⟨9, 18⟩, 10)]

theorem g32p_row49_pairing_35 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_35)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (2, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 4), (2, ⟨-9, -18⟩, 8), (2, ⟨-9, -18⟩, 10), (2, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 6), (2, ⟨-6, -12⟩, 8), (2, ⟨-6, -12⟩, 10), (6, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 4), (6, ⟨-3, -6⟩, 6), (4, ⟨-3, -6⟩, 8), (4, ⟨-3, -6⟩, 10), (6, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (6, ⟨3, 6⟩, 6), (6, ⟨3, 6⟩, 8), (6, ⟨3, 6⟩, 10), (2, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 4), (2, ⟨6, 12⟩, 6), (2, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 4), (2, ⟨9, 18⟩, 8), (2, ⟨9, 18⟩, 10), (1, ⟨60, 120⟩, 8), (1, ⟨60, 120⟩, 10)]

theorem g32p_row49_pairing_36 :
    g32p_cyclotomicPairingCheck 324 (1)
      (g32p_pairingCoefficients 12 g32p_row49_terms_36)
      [1, 0, -1, 0, 1] [-324, 0, -378, 0, -108, 0, 162, 0, 216, 0, 108] = true := by
  decide +kernel

def g32p_row49_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 6), (4, ⟨-6, -12⟩, 8), (4, ⟨-6, -12⟩, 10), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 6), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 6), (4, ⟨3, 6⟩, 8), (4, ⟨3, 6⟩, 10), (1, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 6), (1, ⟨6, 12⟩, 8), (1, ⟨6, 12⟩, 10), (1, ⟨60, 120⟩, 8), (1, ⟨60, 120⟩, 10)]

theorem g32p_row49_pairing_37 :
    g32p_cyclotomicPairingCheck 324 (1)
      (g32p_pairingCoefficients 12 g32p_row49_terms_37)
      [1, 0, -1, 0, 1] [-324, 0, -378, 0, -108, 0, 162, 0, 216, 0, 108] = true := by
  decide +kernel

def g32p_row49_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (2, ⟨-9, -18⟩, 2), (2, ⟨-9, -18⟩, 4), (2, ⟨-9, -18⟩, 8), (2, ⟨-9, -18⟩, 10), (2, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 6), (2, ⟨-6, -12⟩, 8), (2, ⟨-6, -12⟩, 10), (6, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 4), (6, ⟨-3, -6⟩, 6), (4, ⟨-3, -6⟩, 8), (4, ⟨-3, -6⟩, 10), (6, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 4), (6, ⟨3, 6⟩, 6), (6, ⟨3, 6⟩, 8), (6, ⟨3, 6⟩, 10), (2, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 2), (2, ⟨6, 12⟩, 4), (2, ⟨6, 12⟩, 6), (2, ⟨9, 18⟩, 2), (2, ⟨9, 18⟩, 4), (2, ⟨9, 18⟩, 8), (2, ⟨9, 18⟩, 10), (1, ⟨60, 120⟩, 8), (1, ⟨60, 120⟩, 10)]

theorem g32p_row49_pairing_38 :
    g32p_cyclotomicPairingCheck 324 (1)
      (g32p_pairingCoefficients 12 g32p_row49_terms_38)
      [1, 0, -1, 0, 1] [-324, 0, -378, 0, -108, 0, 162, 0, 216, 0, 108] = true := by
  decide +kernel

def g32p_row49_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 4), (1, ⟨-60, -120⟩, 10), (4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 6), (4, ⟨-6, -12⟩, 8), (9, ⟨-4, -8⟩, 1), (9, ⟨-4, -8⟩, 7), (5, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (5, ⟨-3, -6⟩, 4), (5, ⟨-3, -6⟩, 6), (8, ⟨-3, -6⟩, 8), (5, ⟨-3, -6⟩, 10), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 5), (9, ⟨-1, -2⟩, 9), (9, ⟨-1, -2⟩, 11), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 7), (9, ⟨1, 2⟩, 9), (5, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 6), (5, ⟨3, 6⟩, 8), (8, ⟨3, 6⟩, 10), (9, ⟨4, 8⟩, 5), (9, ⟨4, 8⟩, 11), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 6), (4, ⟨6, 12⟩, 10), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 8)]

theorem g32p_row49_pairing_39 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_39)
      [1, 0, -1, 0, 1] [0, -27, 27, -27, 0, -27, 27, -27, 0, 54, -54, 54] = true := by
  decide +kernel

def g32p_row49_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 4), (1, ⟨-64, -128⟩, 10), (4, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 4), (4, ⟨-8, -16⟩, 6), (4, ⟨-8, -16⟩, 10), (1, ⟨-4, -8⟩, 0), (1, ⟨-4, -8⟩, 2), (4, ⟨-4, -8⟩, 4), (1, ⟨-4, -8⟩, 6), (1, ⟨-4, -8⟩, 8), (4, ⟨-4, -8⟩, 10), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 6), (4, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 6), (4, ⟨2, 4⟩, 8), (4, ⟨2, 4⟩, 10), (1, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 6), (4, ⟨4, 8⟩, 8), (1, ⟨4, 8⟩, 10), (4, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 2), (4, ⟨8, 16⟩, 6), (4, ⟨8, 16⟩, 8), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 8)]

theorem g32p_row49_pairing_40 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_40)
      [1, 0, -1, 0, 1] [0, 0, 108, 0, 0, 0, 108, 0, 0, 0, -216] = true := by
  decide +kernel

def g32p_row49_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (4, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 2), (4, ⟨-8, -16⟩, 4), (4, ⟨-8, -16⟩, 6), (1, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 2), (4, ⟨-4, -8⟩, 4), (1, ⟨-4, -8⟩, 6), (1, ⟨-4, -8⟩, 8), (1, ⟨-4, -8⟩, 10), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 6), (4, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 6), (4, ⟨2, 4⟩, 8), (4, ⟨2, 4⟩, 10), (1, ⟨4, 8⟩, 0), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 6), (4, ⟨4, 8⟩, 8), (4, ⟨4, 8⟩, 10), (4, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 6), (4, ⟨8, 16⟩, 8), (4, ⟨8, 16⟩, 10), (1, ⟨64, 128⟩, 8), (1, ⟨64, 128⟩, 10)]

theorem g32p_row49_pairing_41 :
    g32p_cyclotomicPairingCheck 324 (2)
      (g32p_pairingCoefficients 12 g32p_row49_terms_41)
      [1, 0, -1, 0, 1] [-648, 0, -756, 0, -216, 0, 324, 0, 432, 0, 216] = true := by
  decide +kernel

def g32p_row49_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (4, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 6), (4, ⟨-8, -16⟩, 8), (4, ⟨-8, -16⟩, 10), (4, ⟨-4, -8⟩, 0), (4, ⟨-4, -8⟩, 2), (4, ⟨-4, -8⟩, 4), (4, ⟨-4, -8⟩, 6), (4, ⟨-4, -8⟩, 8), (4, ⟨-4, -8⟩, 10), (1, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 6), (1, ⟨-2, -4⟩, 8), (1, ⟨-2, -4⟩, 10), (1, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 6), (4, ⟨2, 4⟩, 8), (4, ⟨2, 4⟩, 10), (4, ⟨4, 8⟩, 0), (4, ⟨4, 8⟩, 2), (4, ⟨4, 8⟩, 4), (4, ⟨4, 8⟩, 6), (4, ⟨4, 8⟩, 8), (4, ⟨4, 8⟩, 10), (4, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 2), (4, ⟨8, 16⟩, 4), (4, ⟨8, 16⟩, 6), (1, ⟨80, 160⟩, 8), (1, ⟨80, 160⟩, 10)]

theorem g32p_row49_pairing_42 :
    g32p_cyclotomicPairingCheck 324 (1)
      (g32p_pairingCoefficients 12 g32p_row49_terms_42)
      [1, 0, -1, 0, 1] [-324, 0, -378, 0, -108, 0, 162, 0, 216, 0, 108] = true := by
  decide +kernel

def g32p_row49_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 4), (1, ⟨-81, -162⟩, 10), (9, ⟨-3, -6⟩, 5), (9, ⟨-3, -6⟩, 11), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 7), (1, ⟨81, 162⟩, 2), (1, ⟨81, 162⟩, 8)]

theorem g32p_row49_pairing_43 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_43)
      [1, 0, -1, 0, 1] [0, 27, 81, 27, 0, 27, 81, 27, 0, -54, -162, -54] = true := by
  decide +kernel

def g32p_row49_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 6), (1, ⟨-20, 0⟩, 10), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 4), (8, ⟨-7, 0⟩, 8), (18, ⟨-2, 0⟩, 2), (18, ⟨-2, 0⟩, 6), (18, ⟨-2, 0⟩, 10), (18, ⟨2, 0⟩, 0), (18, ⟨2, 0⟩, 4), (18, ⟨2, 0⟩, 8), (8, ⟨7, 0⟩, 2), (8, ⟨7, 0⟩, 6), (8, ⟨7, 0⟩, 10), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 4), (1, ⟨20, 0⟩, 8)]

theorem g32p_row49_pairing_44 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_44)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 6), (1, ⟨-60, 0⟩, 10), (6, ⟨-6, 0⟩, 0), (6, ⟨-6, 0⟩, 4), (6, ⟨-6, 0⟩, 8), (8, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 4), (8, ⟨-3, 0⟩, 8), (8, ⟨3, 0⟩, 2), (8, ⟨3, 0⟩, 6), (8, ⟨3, 0⟩, 10), (6, ⟨6, 0⟩, 2), (6, ⟨6, 0⟩, 6), (6, ⟨6, 0⟩, 10), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 4), (1, ⟨60, 0⟩, 8)]

theorem g32p_row49_pairing_45 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_45)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 6), (1, ⟨-64, 0⟩, 10), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 4), (8, ⟨-8, 0⟩, 8), (6, ⟨-4, 0⟩, 2), (6, ⟨-4, 0⟩, 6), (6, ⟨-4, 0⟩, 10), (12, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 4), (12, ⟨-2, 0⟩, 8), (12, ⟨2, 0⟩, 2), (12, ⟨2, 0⟩, 6), (12, ⟨2, 0⟩, 10), (6, ⟨4, 0⟩, 0), (6, ⟨4, 0⟩, 4), (6, ⟨4, 0⟩, 8), (8, ⟨8, 0⟩, 2), (8, ⟨8, 0⟩, 6), (8, ⟨8, 0⟩, 10), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 4), (1, ⟨64, 0⟩, 8)]

theorem g32p_row49_pairing_46 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_46)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row49_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 6), (1, ⟨-80, 0⟩, 10), (8, ⟨-8, 0⟩, 2), (8, ⟨-8, 0⟩, 6), (8, ⟨-8, 0⟩, 10), (12, ⟨-4, 0⟩, 0), (12, ⟨-4, 0⟩, 4), (12, ⟨-4, 0⟩, 8), (6, ⟨-2, 0⟩, 2), (6, ⟨-2, 0⟩, 6), (6, ⟨-2, 0⟩, 10), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 4), (6, ⟨2, 0⟩, 8), (12, ⟨4, 0⟩, 2), (12, ⟨4, 0⟩, 6), (12, ⟨4, 0⟩, 10), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 4), (8, ⟨8, 0⟩, 8), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 4), (1, ⟨80, 0⟩, 8)]

theorem g32p_row49_pairing_47 :
    g32p_cyclotomicPairingCheck 324 (0)
      (g32p_pairingCoefficients 12 g32p_row49_terms_47)
      [1, 0, -1, 0, 1] [108, 0, 0, 0, 0, 0, -108] = true := by
  decide +kernel

theorem g32p_row49_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 49 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 2, 1, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨49, -1, [(16, 1), (28, 1), (29, 1), (37, 1), (38, 1), (39, 1), (42, 2), (43, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row50_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2)]

theorem g32p_row50_pairing_0 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 2), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 2), (3, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1)]

theorem g32p_row50_pairing_1 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 0), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (25, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (25, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (1, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 0)]

theorem g32p_row50_pairing_2 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 0), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (1, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (25, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (25, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (1, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨4, 8⟩, 0)]

theorem g32p_row50_pairing_3 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 2), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (3, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 2)]

theorem g32p_row50_pairing_4 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 0), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (7, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (19, ⟨-1, -2⟩, 0), (12, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (19, ⟨1, 2⟩, 0), (15, ⟨1, 2⟩, 1), (12, ⟨1, 2⟩, 2), (7, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 0)]

theorem g32p_row50_pairing_5 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 0), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (7, ⟨-2, -4⟩, 0), (15, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (19, ⟨-1, -2⟩, 0), (15, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (19, ⟨1, 2⟩, 0), (12, ⟨1, 2⟩, 1), (15, ⟨1, 2⟩, 2), (7, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨5, 10⟩, 0)]

theorem g32p_row50_pairing_6 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (2, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (2, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 0)]

theorem g32p_row50_pairing_7 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 2), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 2), (3, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1)]

theorem g32p_row50_pairing_8 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 0), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 1), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (1, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (1, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 2), (1, ⟨10, 20⟩, 0)]

theorem g32p_row50_pairing_9 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 0), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 2), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (1, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 1), (1, ⟨10, 20⟩, 0)]

theorem g32p_row50_pairing_10 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 0), (8, ⟨-3, -6⟩, 0), (15, ⟨-3, -6⟩, 1), (15, ⟨-3, -6⟩, 2), (8, ⟨3, 6⟩, 0), (15, ⟨3, 6⟩, 1), (15, ⟨3, 6⟩, 2), (1, ⟨15, 30⟩, 0)]

theorem g32p_row50_pairing_11 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_11)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 0), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨15, 30⟩, 0)]

theorem g32p_row50_pairing_12 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 2), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 2), (3, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1)]

theorem g32p_row50_pairing_13 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-6, -12⟩, 0), (9, ⟨-6, -12⟩, 2), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 2), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (3, ⟨6, 12⟩, 0), (9, ⟨6, 12⟩, 1)]

theorem g32p_row50_pairing_14 :
    g32p_cyclotomicPairingCheck 243 (-1)
      (g32p_pairingCoefficients 3 g32p_row50_terms_14)
      [1, 1, 1] [243, -162] = true := by
  decide +kernel

def g32p_row50_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (2, ⟨-7, -14⟩, 0), (3, ⟨-7, -14⟩, 1), (3, ⟨-7, -14⟩, 2), (6, ⟨-2, -4⟩, 0), (15, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (2, ⟨7, 14⟩, 0), (3, ⟨7, 14⟩, 1), (3, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 0)]

theorem g32p_row50_pairing_15 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 1), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (25, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (25, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨20, 40⟩, 0)]

theorem g32p_row50_pairing_16 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 2), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 1), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (6, ⟨-2, -4⟩, 0), (15, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 2), (1, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (1, ⟨20, 40⟩, 0)]

theorem g32p_row50_pairing_17 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 2), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (25, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (25, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 1), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 0)]

theorem g32p_row50_pairing_18 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 2), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (15, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 1), (1, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 0)]

theorem g32p_row50_pairing_19 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (3, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 2), (2, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (2, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (1, ⟨20, 40⟩, 0)]

theorem g32p_row50_pairing_20 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_20)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 0), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (6, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨24, 48⟩, 0)]

theorem g32p_row50_pairing_21 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_21)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 1), (3, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 2)]

theorem g32p_row50_pairing_22 :
    g32p_cyclotomicPairingCheck 243 (1)
      (g32p_pairingCoefficients 3 g32p_row50_terms_22)
      [1, 1, 1] [-243, 162] = true := by
  decide +kernel

def g32p_row50_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 2), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (1, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (1, ⟨30, 60⟩, 0)]

theorem g32p_row50_pairing_23 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_23)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (1, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨30, 60⟩, 0)]

theorem g32p_row50_pairing_24 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (8, ⟨-3, -6⟩, 0), (18, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 2), (8, ⟨3, 6⟩, 0), (18, ⟨3, 6⟩, 1), (18, ⟨3, 6⟩, 2), (1, ⟨30, 60⟩, 0)]

theorem g32p_row50_pairing_25 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 2), (3, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 1)]

theorem g32p_row50_pairing_26 :
    g32p_cyclotomicPairingCheck 243 (-1)
      (g32p_pairingCoefficients 3 g32p_row50_terms_26)
      [1, 1, 1] [243, -162] = true := by
  decide +kernel

def g32p_row50_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 0), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 0)]

theorem g32p_row50_pairing_27 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 0), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 0)]

theorem g32p_row50_pairing_28 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-6, -12⟩, 0), (9, ⟨-6, -12⟩, 1), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 2), (3, ⟨6, 12⟩, 0), (9, ⟨6, 12⟩, 2)]

theorem g32p_row50_pairing_29 :
    g32p_cyclotomicPairingCheck 243 (1)
      (g32p_pairingCoefficients 3 g32p_row50_terms_29)
      [1, 1, 1] [-243, 162] = true := by
  decide +kernel

def g32p_row50_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 0), (1, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 2), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (1, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (1, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (1, ⟨40, 80⟩, 0)]

theorem g32p_row50_pairing_30 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 0), (1, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (1, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (1, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 2), (1, ⟨40, 80⟩, 0)]

theorem g32p_row50_pairing_31 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 1), (3, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 2)]

theorem g32p_row50_pairing_32 :
    g32p_cyclotomicPairingCheck 243 (1)
      (g32p_pairingCoefficients 3 g32p_row50_terms_32)
      [1, 1, 1] [-243, 162] = true := by
  decide +kernel

def g32p_row50_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 0), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨45, 90⟩, 0)]

theorem g32p_row50_pairing_33 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 0), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨45, 90⟩, 0)]

theorem g32p_row50_pairing_34 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 1), (3, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 2)]

theorem g32p_row50_pairing_35 :
    g32p_cyclotomicPairingCheck 243 (1)
      (g32p_pairingCoefficients 3 g32p_row50_terms_35)
      [1, 1, 1] [-243, 162] = true := by
  decide +kernel

def g32p_row50_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (7, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (15, ⟨-3, -6⟩, 2), (7, ⟨3, 6⟩, 0), (15, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 0)]

theorem g32p_row50_pairing_36 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (2, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (2, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 0)]

theorem g32p_row50_pairing_37 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 2), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (7, ⟨-3, -6⟩, 0), (15, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (7, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (15, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (1, ⟨60, 120⟩, 0)]

theorem g32p_row50_pairing_38 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (6, ⟨-3, -6⟩, 0), (15, ⟨-3, -6⟩, 1), (15, ⟨-3, -6⟩, 2), (6, ⟨3, 6⟩, 0), (15, ⟨3, 6⟩, 1), (15, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 0)]

theorem g32p_row50_pairing_39 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_39)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 0), (2, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (6, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (2, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 0)]

theorem g32p_row50_pairing_40 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_40)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 0), (2, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (6, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (2, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 0)]

theorem g32p_row50_pairing_41 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 0), (2, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (6, ⟨-4, -8⟩, 0), (12, ⟨-4, -8⟩, 1), (12, ⟨-4, -8⟩, 2), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (6, ⟨4, 8⟩, 0), (12, ⟨4, 8⟩, 1), (12, ⟨4, 8⟩, 2), (2, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 0)]

theorem g32p_row50_pairing_42 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 0), (1, ⟨81, 162⟩, 0)]

theorem g32p_row50_pairing_43 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_43)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-7, 0⟩, 0), (9, ⟨-7, 0⟩, 1), (9, ⟨-7, 0⟩, 2), (54, ⟨-1, 0⟩, 0), (27, ⟨-1, 0⟩, 1), (27, ⟨-1, 0⟩, 2), (18, ⟨2, 0⟩, 0), (45, ⟨2, 0⟩, 1), (45, ⟨2, 0⟩, 2), (3, ⟨20, 0⟩, 0)]

theorem g32p_row50_pairing_44 :
    g32p_cyclotomicPairingCheck 243 (0)
      (g32p_pairingCoefficients 3 g32p_row50_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row50_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(9, ⟨-6, 0⟩, 1), (9, ⟨-6, 0⟩, 2), (6, ⟨-3, 0⟩, 0), (9, ⟨-3, 0⟩, 1), (9, ⟨-3, 0⟩, 2), (3, ⟨60, 0⟩, 0)]

theorem g32p_row50_pairing_45 :
    g32p_cyclotomicPairingCheck 243 (1)
      (g32p_pairingCoefficients 3 g32p_row50_terms_45)
      [1, 1, 1] [-81] = true := by
  decide +kernel

def g32p_row50_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-8, 0⟩, 0), (9, ⟨-8, 0⟩, 1), (9, ⟨-8, 0⟩, 2), (18, ⟨-2, 0⟩, 0), (36, ⟨-2, 0⟩, 1), (36, ⟨-2, 0⟩, 2), (54, ⟨1, 0⟩, 0), (27, ⟨1, 0⟩, 1), (27, ⟨1, 0⟩, 2), (9, ⟨4, 0⟩, 1), (9, ⟨4, 0⟩, 2), (3, ⟨64, 0⟩, 0)]

theorem g32p_row50_pairing_46 :
    g32p_cyclotomicPairingCheck 243 (1)
      (g32p_pairingCoefficients 3 g32p_row50_terms_46)
      [1, 1, 1] [-81] = true := by
  decide +kernel

def g32p_row50_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(18, ⟨-4, 0⟩, 0), (36, ⟨-4, 0⟩, 1), (36, ⟨-4, 0⟩, 2), (54, ⟨-1, 0⟩, 0), (27, ⟨-1, 0⟩, 1), (27, ⟨-1, 0⟩, 2), (9, ⟨2, 0⟩, 1), (9, ⟨2, 0⟩, 2), (6, ⟨8, 0⟩, 0), (9, ⟨8, 0⟩, 1), (9, ⟨8, 0⟩, 2), (3, ⟨80, 0⟩, 0)]

theorem g32p_row50_pairing_47 :
    g32p_cyclotomicPairingCheck 243 (1)
      (g32p_pairingCoefficients 3 g32p_row50_terms_47)
      [1, 1, 1] [-81] = true := by
  decide +kernel

theorem g32p_row50_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 50 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
         ![0, 1, 1, 1]) := by
  refine ⟨⟨50, 1, [(15, -1), (23, 1), (27, -1), (30, 1), (33, 1), (36, 1), (46, 1), (47, 1), (48, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row51_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2)]

theorem g32p_row51_pairing_0 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(12, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 2), (15, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 1), (15, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (3, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2)]

theorem g32p_row51_pairing_1 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 0), (1, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (14, ⟨-2, -4⟩, 0), (13, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (14, ⟨-1, -2⟩, 1), (29, ⟨-1, -2⟩, 2), (29, ⟨1, 2⟩, 1), (14, ⟨1, 2⟩, 2), (14, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (13, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 0)]

theorem g32p_row51_pairing_2 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 0), (4, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (14, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (13, ⟨-2, -4⟩, 2), (29, ⟨-1, -2⟩, 1), (14, ⟨-1, -2⟩, 2), (14, ⟨1, 2⟩, 1), (29, ⟨1, 2⟩, 2), (14, ⟨2, 4⟩, 0), (13, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 0)]

theorem g32p_row51_pairing_3 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 0), (30, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (3, ⟨1, 2⟩, 1), (30, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 0), (12, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2)]

theorem g32p_row51_pairing_4 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 0), (1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 0)]

theorem g32p_row51_pairing_5 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 0), (1, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (4, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (22, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (22, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (4, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 0)]

theorem g32p_row51_pairing_6 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (8, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (7, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (11, ⟨-1, -2⟩, 1), (11, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (11, ⟨1, 2⟩, 1), (11, ⟨1, 2⟩, 2), (7, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 0)]

theorem g32p_row51_pairing_7 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(24, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (18, ⟨-1, -2⟩, 1), (18, ⟨1, 2⟩, 2), (6, ⟨3, 6⟩, 1), (24, ⟨3, 6⟩, 2)]

theorem g32p_row51_pairing_8 :
    g32p_cyclotomicPairingCheck 216 (1)
      (g32p_pairingCoefficients 3 g32p_row51_terms_8)
      [1, 1, 1] [-216, 144] = true := by
  decide +kernel

def g32p_row51_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 0), (1, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (7, ⟨-2, -4⟩, 0), (5, ⟨-2, -4⟩, 1), (5, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (15, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (15, ⟨1, 2⟩, 2), (7, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 1), (5, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (4, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (1, ⟨10, 20⟩, 0)]

theorem g32p_row51_pairing_9 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 0), (4, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (2, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (7, ⟨-2, -4⟩, 0), (5, ⟨-2, -4⟩, 1), (5, ⟨-2, -4⟩, 2), (16, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (16, ⟨1, 2⟩, 0), (15, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (7, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 1), (5, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (1, ⟨10, 20⟩, 0)]

theorem g32p_row51_pairing_10 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 0), (1, ⟨-7, -14⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (6, ⟨-1, -2⟩, 0), (15, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 0), (15, ⟨1, 2⟩, 1), (15, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (1, ⟨7, 14⟩, 0), (1, ⟨15, 30⟩, 0)]

theorem g32p_row51_pairing_11 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_11)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 0), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 2), (14, ⟨-3, -6⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (9, ⟨-1, -2⟩, 0), (9, ⟨1, 2⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (14, ⟨3, 6⟩, 0), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 2), (1, ⟨15, 30⟩, 0)]

theorem g32p_row51_pairing_12 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(12, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 2), (18, ⟨-1, -2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2)]

theorem g32p_row51_pairing_13 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(12, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (27, ⟨-2, -4⟩, 2), (27, ⟨2, 4⟩, 1), (3, ⟨6, 12⟩, 1), (12, ⟨6, 12⟩, 2)]

theorem g32p_row51_pairing_14 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (5, ⟨-7, -14⟩, 1), (5, ⟨-7, -14⟩, 2), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (14, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (14, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (5, ⟨7, 14⟩, 1), (5, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 0)]

theorem g32p_row51_pairing_15 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (4, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (1, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (8, ⟨-4, -8⟩, 0), (6, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 2), (29, ⟨-1, -2⟩, 1), (14, ⟨-1, -2⟩, 2), (14, ⟨1, 2⟩, 1), (29, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (8, ⟨4, 8⟩, 0), (4, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (1, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 0)]

theorem g32p_row51_pairing_16 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (4, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (1, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (6, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (14, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (14, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (9, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (4, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (1, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 0)]

theorem g32p_row51_pairing_17 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (4, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (8, ⟨-4, -8⟩, 0), (6, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (14, ⟨-1, -2⟩, 1), (29, ⟨-1, -2⟩, 2), (29, ⟨1, 2⟩, 1), (14, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (1, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (4, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 0)]

theorem g32p_row51_pairing_18 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (4, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (9, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (14, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (14, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (6, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (4, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 0)]

theorem g32p_row51_pairing_19 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (8, ⟨-5, -10⟩, 0), (1, ⟨-4, -8⟩, 0), (10, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 1), (10, ⟨2, 4⟩, 2), (1, ⟨4, 8⟩, 0), (8, ⟨5, 10⟩, 0), (1, ⟨20, 40⟩, 0)]

theorem g32p_row51_pairing_20 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_20)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 0), (1, ⟨-8, -16⟩, 0), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 2), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (5, ⟨-2, -4⟩, 1), (5, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (5, ⟨2, 4⟩, 1), (5, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 2), (1, ⟨8, 16⟩, 0), (1, ⟨24, 48⟩, 0)]

theorem g32p_row51_pairing_21 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_21)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 1), (12, ⟨-9, -18⟩, 2), (12, ⟨-2, -4⟩, 0), (21, ⟨-1, -2⟩, 1), (12, ⟨-1, -2⟩, 2), (12, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 0), (12, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2)]

theorem g32p_row51_pairing_22 :
    g32p_cyclotomicPairingCheck 216 (-1)
      (g32p_pairingCoefficients 3 g32p_row51_terms_22)
      [1, 1, 1] [216, -144] = true := by
  decide +kernel

def g32p_row51_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (4, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (10, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (14, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (14, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (1, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨30, 60⟩, 0)]

theorem g32p_row51_pairing_23 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_23)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (1, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (1, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (10, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (8, ⟨-1, -2⟩, 1), (14, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (14, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (4, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (1, ⟨30, 60⟩, 0)]

theorem g32p_row51_pairing_24 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (1, ⟨-10, -20⟩, 0), (8, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (8, ⟨-1, -2⟩, 0), (15, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (15, ⟨1, 2⟩, 1), (15, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (8, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (1, ⟨10, 20⟩, 0), (1, ⟨30, 60⟩, 0)]

theorem g32p_row51_pairing_25 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(12, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (15, ⟨-3, -6⟩, 1), (18, ⟨-1, -2⟩, 1), (18, ⟨1, 2⟩, 2), (15, ⟨3, 6⟩, 2), (3, ⟨9, 18⟩, 1), (12, ⟨9, 18⟩, 2)]

theorem g32p_row51_pairing_26 :
    g32p_cyclotomicPairingCheck 216 (2)
      (g32p_pairingCoefficients 3 g32p_row51_terms_26)
      [1, 1, 1] [-432, 288] = true := by
  decide +kernel

def g32p_row51_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 0), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 0)]

theorem g32p_row51_pairing_27 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 0), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 0)]

theorem g32p_row51_pairing_28 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-6, -12⟩, 1), (12, ⟨-6, -12⟩, 2), (12, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (12, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (12, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2)]

theorem g32p_row51_pairing_29 :
    g32p_cyclotomicPairingCheck 216 (-1)
      (g32p_pairingCoefficients 3 g32p_row51_terms_29)
      [1, 1, 1] [216, -144] = true := by
  decide +kernel

def g32p_row51_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 0), (1, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (1, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (16, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (4, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (1, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨40, 80⟩, 0)]

theorem g32p_row51_pairing_30 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 0), (1, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (4, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (16, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 1), (8, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (1, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (1, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (1, ⟨40, 80⟩, 0)]

theorem g32p_row51_pairing_31 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 1), (12, ⟨-9, -18⟩, 2), (12, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 1), (3, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (12, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2)]

theorem g32p_row51_pairing_32 :
    g32p_cyclotomicPairingCheck 216 (-1)
      (g32p_pairingCoefficients 3 g32p_row51_terms_32)
      [1, 1, 1] [216, -144] = true := by
  decide +kernel

def g32p_row51_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 0), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (1, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (1, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (1, ⟨45, 90⟩, 0)]

theorem g32p_row51_pairing_33 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 0), (5, ⟨-9, -18⟩, 1), (5, ⟨-9, -18⟩, 2), (1, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (1, ⟨3, 6⟩, 0), (5, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (5, ⟨9, 18⟩, 1), (5, ⟨9, 18⟩, 2), (1, ⟨45, 90⟩, 0)]

theorem g32p_row51_pairing_34 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 1), (12, ⟨-9, -18⟩, 2), (12, ⟨-2, -4⟩, 2), (33, ⟨-1, -2⟩, 1), (33, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (12, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2)]

theorem g32p_row51_pairing_35 :
    g32p_cyclotomicPairingCheck 216 (-1)
      (g32p_pairingCoefficients 3 g32p_row51_terms_35)
      [1, 1, 1] [216, -144] = true := by
  decide +kernel

def g32p_row51_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (1, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 1), (5, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (5, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (4, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 0)]

theorem g32p_row51_pairing_36 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (8, ⟨-6, -12⟩, 0), (10, ⟨-3, -6⟩, 1), (10, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (10, ⟨3, 6⟩, 1), (10, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (1, ⟨60, 120⟩, 0)]

theorem g32p_row51_pairing_37 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (4, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (1, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (5, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (6, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (6, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (1, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 0)]

theorem g32p_row51_pairing_38 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (5, ⟨-6, -12⟩, 1), (5, ⟨-6, -12⟩, 2), (1, ⟨-4, -8⟩, 0), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (5, ⟨-2, -4⟩, 1), (5, ⟨-2, -4⟩, 2), (8, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 2), (8, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 2), (5, ⟨2, 4⟩, 1), (5, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 0), (5, ⟨6, 12⟩, 1), (5, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 0)]

theorem g32p_row51_pairing_39 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_39)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (8, ⟨-4, -8⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 0)]

theorem g32p_row51_pairing_40 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_40)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (8, ⟨-4, -8⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (8, ⟨4, 8⟩, 0), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 0)]

theorem g32p_row51_pairing_41 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 0), (5, ⟨-8, -16⟩, 1), (5, ⟨-8, -16⟩, 2), (4, ⟨-4, -8⟩, 1), (4, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (8, ⟨2, 4⟩, 0), (4, ⟨4, 8⟩, 1), (4, ⟨4, 8⟩, 2), (5, ⟨8, 16⟩, 1), (5, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 0)]

theorem g32p_row51_pairing_42 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 0), (1, ⟨-9, -18⟩, 0), (6, ⟨-3, -6⟩, 0), (6, ⟨3, 6⟩, 0), (1, ⟨9, 18⟩, 0), (1, ⟨81, 162⟩, 0)]

theorem g32p_row51_pairing_43 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_43)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(15, ⟨-7, 0⟩, 1), (15, ⟨-7, 0⟩, 2), (3, ⟨-3, 0⟩, 1), (3, ⟨-3, 0⟩, 2), (18, ⟨-1, 0⟩, 1), (18, ⟨-1, 0⟩, 2), (42, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 1), (12, ⟨2, 0⟩, 2), (12, ⟨3, 0⟩, 1), (12, ⟨3, 0⟩, 2), (3, ⟨20, 0⟩, 0)]

theorem g32p_row51_pairing_44 :
    g32p_cyclotomicPairingCheck 216 (1)
      (g32p_pairingCoefficients 3 g32p_row51_terms_44)
      [1, 1, 1] [-72] = true := by
  decide +kernel

def g32p_row51_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(24, ⟨-6, 0⟩, 0), (18, ⟨-3, 0⟩, 1), (18, ⟨-3, 0⟩, 2), (18, ⟨-2, 0⟩, 0), (18, ⟨1, 0⟩, 1), (18, ⟨1, 0⟩, 2), (12, ⟨3, 0⟩, 1), (12, ⟨3, 0⟩, 2), (3, ⟨60, 0⟩, 0)]

theorem g32p_row51_pairing_45 :
    g32p_cyclotomicPairingCheck 216 (0)
      (g32p_pairingCoefficients 3 g32p_row51_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row51_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(15, ⟨-8, 0⟩, 1), (15, ⟨-8, 0⟩, 2), (12, ⟨-2, 0⟩, 1), (12, ⟨-2, 0⟩, 2), (24, ⟨4, 0⟩, 0), (3, ⟨64, 0⟩, 0)]

theorem g32p_row51_pairing_46 :
    g32p_cyclotomicPairingCheck 216 (2)
      (g32p_pairingCoefficients 3 g32p_row51_terms_46)
      [1, 1, 1] [-144] = true := by
  decide +kernel

def g32p_row51_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(12, ⟨-4, 0⟩, 1), (12, ⟨-4, 0⟩, 2), (24, ⟨2, 0⟩, 0), (15, ⟨8, 0⟩, 1), (15, ⟨8, 0⟩, 2), (3, ⟨80, 0⟩, 0)]

theorem g32p_row51_pairing_47 :
    g32p_cyclotomicPairingCheck 216 (1)
      (g32p_pairingCoefficients 3 g32p_row51_terms_47)
      [1, 1, 1] [72] = true := by
  decide +kernel

theorem g32p_row51_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 51 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
         ![1, 0, 2, 1]) := by
  refine ⟨⟨51, -1, [(9, 1), (23, -1), (27, 2), (30, -1), (33, -1), (36, -1), (45, 1), (48, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end
