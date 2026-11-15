import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core
import HodgeLean.Papers.PapersG32CertificatesDefs

section

namespace HodgeLean.Foundations.Program

-- Coefficients are stored in increasing degree, including trailing zeroes.
def g32p_coeffAdd : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: g32p_coeffAdd xs ys

def g32p_coeffMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | x :: xs, ys => g32p_coeffAdd (ys.map (x * ·)) (0 :: g32p_coeffMul xs ys)

def g32p_coeffTrim (xs : List ℤ) : List ℤ := (xs.reverse.dropWhile (· == 0)).reverse

noncomputable def g32p_coeffEval (z : ℂ) : List ℤ → ℂ
  | [] => 0
  | x :: xs => x + z * g32p_coeffEval z xs

theorem g32p_coeffEval_add (z : ℂ) (xs ys : List ℤ) :
    g32p_coeffEval z (g32p_coeffAdd xs ys) =
      g32p_coeffEval z xs + g32p_coeffEval z ys := by
  induction xs generalizing ys with
  | nil => simp [g32p_coeffAdd, g32p_coeffEval]
  | cons x xs ih =>
    cases ys with
    | nil => simp [g32p_coeffAdd, g32p_coeffEval]
    | cons y ys => simp only [g32p_coeffAdd, g32p_coeffEval, Int.cast_add, ih]; ring

theorem g32p_coeffEval_scale (z : ℂ) (x : ℤ) (xs : List ℤ) :
    g32p_coeffEval z (xs.map (x * ·)) = x * g32p_coeffEval z xs := by
  induction xs with
  | nil => simp [g32p_coeffEval]
  | cons y ys ih => simp only [List.map_cons, g32p_coeffEval, Int.cast_mul, ih]; ring

theorem g32p_coeffEval_mul (z : ℂ) (xs ys : List ℤ) :
    g32p_coeffEval z (g32p_coeffMul xs ys) =
      g32p_coeffEval z xs * g32p_coeffEval z ys := by
  induction xs with
  | nil => simp [g32p_coeffMul, g32p_coeffEval]
  | cons x xs ih =>
    rw [g32p_coeffMul, g32p_coeffEval_add, g32p_coeffEval_scale]
    simp only [g32p_coeffEval, Int.cast_zero, zero_add, ih]
    ring

theorem g32p_coeffEval_append (z : ℂ) (xs ys : List ℤ) :
    g32p_coeffEval z (xs ++ ys) =
      g32p_coeffEval z xs + z ^ xs.length * g32p_coeffEval z ys := by
  induction xs with
  | nil => simp [g32p_coeffEval]
  | cons x xs ih =>
    simp only [List.cons_append, g32p_coeffEval, ih, List.length_cons, pow_succ]
    ring

theorem g32p_coeffEval_zeroes (z : ℂ) (n : ℕ) :
    g32p_coeffEval z (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, g32p_coeffEval, ih]

theorem g32p_coeffEval_trim (z : ℂ) (xs : List ℤ) :
    g32p_coeffEval z (g32p_coeffTrim xs) = g32p_coeffEval z xs := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    by_cases hx : x = 0
    · subst x
      simpa [g32p_coeffTrim, List.reverse_append, g32p_coeffEval_append,
        g32p_coeffEval] using ih
    · simp [g32p_coeffTrim, List.reverse_append, hx]

def g32p_coeffMonomial (degree : ℕ) (a : ℤ) : List ℤ :=
  List.replicate degree 0 ++ [a]

theorem g32p_coeffEval_monomial (z : ℂ) (degree : ℕ) (a : ℤ) :
    g32p_coeffEval z (g32p_coeffMonomial degree a) = a * z ^ degree := by
  simp [g32p_coeffMonomial, g32p_coeffEval_append, g32p_coeffEval_zeroes,
    g32p_coeffEval, mul_comm]

-- A term records its count, its trace in the Eisenstein basis, and the exponent
-- of the inverse supplier character. The common root has order divisible by 3.
def g32p_pairingCoefficients (m : ℕ) :
    List (ℕ × HurwitzPrymRex_Zw × ℕ) → List ℤ
  | [] => []
  | (n, a, e) :: xs => g32p_coeffAdd
      (g32p_coeffAdd (g32p_coeffMonomial e (n * a.re))
        (g32p_coeffMonomial (m / 3 + e) (n * a.om)))
      (g32p_pairingCoefficients m xs)

theorem g32p_pairingCoefficients_eval (m : ℕ) (z : ℂ)
    (xs : List (ℕ × HurwitzPrymRex_Zw × ℕ)) :
    g32p_coeffEval z (g32p_pairingCoefficients m xs) =
      (xs.map (fun x => (x.1 : ℂ) *
        HurwitzPrymRex_ev (z ^ (m / 3)) x.2.1 * z ^ x.2.2)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨n, a, e⟩
    simp only [g32p_pairingCoefficients, g32p_coeffEval_add,
      g32p_coeffEval_monomial, ih, List.map_cons, List.sum_cons,
      Int.cast_mul, Int.cast_natCast, pow_add, HurwitzPrymRex_ev]
    ring

-- Checks a polynomial identity with an explicit quotient, using only integer lists.
def g32p_cyclotomicPairingCheck (order : ℕ) (multiplicity : ℤ)
    (coefficients modulus quotient : List ℤ) : Bool :=
  decide (g32p_coeffTrim coefficients =
    g32p_coeffTrim (g32p_coeffAdd [(order : ℤ) * multiplicity] (g32p_coeffMul modulus quotient)))

theorem g32p_cyclotomicPairingCheck_sound (order : ℕ) (multiplicity : ℤ)
    (coefficients modulus quotient : List ℤ) (z : ℂ)
    (hroot : g32p_coeffEval z modulus = 0)
    (h : g32p_cyclotomicPairingCheck order multiplicity coefficients modulus quotient = true) :
    g32p_coeffEval z coefficients = (order : ℂ) * multiplicity := by
  have he := congrArg (g32p_coeffEval z) (of_decide_eq_true h)
  rw [g32p_coeffEval_trim, g32p_coeffEval_trim, g32p_coeffEval_add,
    g32p_coeffEval_mul, hroot] at he
  simpa [g32p_coeffEval] using he

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row01_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(51840, ⟨-1, -2⟩, 1), (51840, ⟨1, 2⟩, 2)]

theorem g32p_row01_pairing_0 :
    g32p_cyclotomicPairingCheck 155520 (1)
      (g32p_pairingCoefficients 3 g32p_row01_terms_0)
      [1, 1, 1] [-155520, 103680] = true := by
  decide +kernel

def g32p_row01_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(80, ⟨-3, -6⟩, 0), (80, ⟨-3, -6⟩, 1), (80, ⟨-3, -6⟩, 2), (1440, ⟨-2, -4⟩, 0), (1440, ⟨-2, -4⟩, 1), (1440, ⟨-2, -4⟩, 2), (10800, ⟨-1, -2⟩, 0), (10800, ⟨-1, -2⟩, 1), (10800, ⟨-1, -2⟩, 2), (10800, ⟨1, 2⟩, 0), (10800, ⟨1, 2⟩, 1), (10800, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 0), (1440, ⟨2, 4⟩, 1), (1440, ⟨2, 4⟩, 2), (80, ⟨3, 6⟩, 0), (80, ⟨3, 6⟩, 1), (80, ⟨3, 6⟩, 2)]

theorem g32p_row01_pairing_1 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (80, ⟨-3, -6⟩, 0), (1440, ⟨-2, -4⟩, 0), (1180, ⟨-2, -4⟩, 1), (1180, ⟨-2, -4⟩, 2), (10800, ⟨-1, -2⟩, 0), (12544, ⟨-1, -2⟩, 1), (12544, ⟨-1, -2⟩, 2), (10800, ⟨1, 2⟩, 0), (12544, ⟨1, 2⟩, 1), (12544, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 0), (1180, ⟨2, 4⟩, 1), (1180, ⟨2, 4⟩, 2), (80, ⟨3, 6⟩, 0), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row01_pairing_2 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (80, ⟨-3, -6⟩, 0), (1440, ⟨-2, -4⟩, 0), (1180, ⟨-2, -4⟩, 1), (1180, ⟨-2, -4⟩, 2), (10800, ⟨-1, -2⟩, 0), (12544, ⟨-1, -2⟩, 1), (12544, ⟨-1, -2⟩, 2), (10800, ⟨1, 2⟩, 0), (12544, ⟨1, 2⟩, 1), (12544, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 0), (1180, ⟨2, 4⟩, 1), (1180, ⟨2, 4⟩, 2), (80, ⟨3, 6⟩, 0), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row01_pairing_3 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(80, ⟨-3, -6⟩, 0), (80, ⟨-3, -6⟩, 1), (80, ⟨-3, -6⟩, 2), (1440, ⟨-2, -4⟩, 0), (1440, ⟨-2, -4⟩, 1), (1440, ⟨-2, -4⟩, 2), (10800, ⟨-1, -2⟩, 0), (10800, ⟨-1, -2⟩, 1), (10800, ⟨-1, -2⟩, 2), (10800, ⟨1, 2⟩, 0), (10800, ⟨1, 2⟩, 1), (10800, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 0), (1440, ⟨2, 4⟩, 1), (1440, ⟨2, 4⟩, 2), (80, ⟨3, 6⟩, 0), (80, ⟨3, 6⟩, 1), (80, ⟨3, 6⟩, 2)]

theorem g32p_row01_pairing_4 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (80, ⟨-3, -6⟩, 0), (90, ⟨-3, -6⟩, 2), (1440, ⟨-2, -4⟩, 0), (1040, ⟨-2, -4⟩, 1), (720, ⟨-2, -4⟩, 2), (10800, ⟨-1, -2⟩, 0), (13140, ⟨-1, -2⟩, 1), (13520, ⟨-1, -2⟩, 2), (10800, ⟨1, 2⟩, 0), (13520, ⟨1, 2⟩, 1), (13140, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 0), (720, ⟨2, 4⟩, 1), (1040, ⟨2, 4⟩, 2), (80, ⟨3, 6⟩, 0), (90, ⟨3, 6⟩, 1), (2, ⟨5, 10⟩, 2)]

theorem g32p_row01_pairing_5 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (80, ⟨-3, -6⟩, 0), (90, ⟨-3, -6⟩, 2), (1440, ⟨-2, -4⟩, 0), (1040, ⟨-2, -4⟩, 1), (720, ⟨-2, -4⟩, 2), (10800, ⟨-1, -2⟩, 0), (13140, ⟨-1, -2⟩, 1), (13520, ⟨-1, -2⟩, 2), (10800, ⟨1, 2⟩, 0), (13520, ⟨1, 2⟩, 1), (13140, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 0), (720, ⟨2, 4⟩, 1), (1040, ⟨2, 4⟩, 2), (80, ⟨3, 6⟩, 0), (90, ⟨3, 6⟩, 1), (2, ⟨5, 10⟩, 2)]

theorem g32p_row01_pairing_6 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (480, ⟨-3, -6⟩, 1), (160, ⟨-3, -6⟩, 2), (1620, ⟨-2, -4⟩, 1), (2970, ⟨-2, -4⟩, 2), (14688, ⟨-1, -2⟩, 1), (12960, ⟨-1, -2⟩, 2), (12960, ⟨1, 2⟩, 1), (14688, ⟨1, 2⟩, 2), (2970, ⟨2, 4⟩, 1), (1620, ⟨2, 4⟩, 2), (160, ⟨3, 6⟩, 1), (480, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row01_pairing_7 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(800, ⟨-3, -6⟩, 0), (800, ⟨-3, -6⟩, 1), (800, ⟨-3, -6⟩, 2), (10080, ⟨-1, -2⟩, 0), (10080, ⟨-1, -2⟩, 1), (10080, ⟨-1, -2⟩, 2), (10080, ⟨1, 2⟩, 0), (10080, ⟨1, 2⟩, 1), (10080, ⟨1, 2⟩, 2), (800, ⟨3, 6⟩, 0), (800, ⟨3, 6⟩, 1), (800, ⟨3, 6⟩, 2)]

theorem g32p_row01_pairing_8 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (80, ⟨-5, -10⟩, 2), (800, ⟨-3, -6⟩, 0), (1890, ⟨-2, -4⟩, 1), (620, ⟨-2, -4⟩, 2), (10080, ⟨-1, -2⟩, 0), (10080, ⟨-1, -2⟩, 1), (12240, ⟨-1, -2⟩, 2), (10080, ⟨1, 2⟩, 0), (12240, ⟨1, 2⟩, 1), (10080, ⟨1, 2⟩, 2), (620, ⟨2, 4⟩, 1), (1890, ⟨2, 4⟩, 2), (800, ⟨3, 6⟩, 0), (80, ⟨5, 10⟩, 1), (2, ⟨10, 20⟩, 2)]

theorem g32p_row01_pairing_9 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (80, ⟨-5, -10⟩, 2), (800, ⟨-3, -6⟩, 0), (1890, ⟨-2, -4⟩, 1), (620, ⟨-2, -4⟩, 2), (10080, ⟨-1, -2⟩, 0), (10080, ⟨-1, -2⟩, 1), (12240, ⟨-1, -2⟩, 2), (10080, ⟨1, 2⟩, 0), (12240, ⟨1, 2⟩, 1), (10080, ⟨1, 2⟩, 2), (620, ⟨2, 4⟩, 1), (1890, ⟨2, 4⟩, 2), (800, ⟨3, 6⟩, 0), (80, ⟨5, 10⟩, 1), (2, ⟨10, 20⟩, 2)]

theorem g32p_row01_pairing_10 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (90, ⟨-7, -14⟩, 1), (1500, ⟨-3, -6⟩, 1), (160, ⟨-3, -6⟩, 2), (2880, ⟨-2, -4⟩, 2), (10800, ⟨-1, -2⟩, 1), (9720, ⟨-1, -2⟩, 2), (9720, ⟨1, 2⟩, 1), (10800, ⟨1, 2⟩, 2), (2880, ⟨2, 4⟩, 1), (160, ⟨3, 6⟩, 1), (1500, ⟨3, 6⟩, 2), (90, ⟨7, 14⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row01_pairing_11 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_11)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (160, ⟨-6, -12⟩, 1), (1560, ⟨-3, -6⟩, 1), (4320, ⟨-2, -4⟩, 1), (14310, ⟨-1, -2⟩, 2), (14310, ⟨1, 2⟩, 1), (4320, ⟨2, 4⟩, 2), (1560, ⟨3, 6⟩, 2), (160, ⟨6, 12⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row01_pairing_12 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(800, ⟨-3, -6⟩, 0), (800, ⟨-3, -6⟩, 1), (800, ⟨-3, -6⟩, 2), (10080, ⟨-1, -2⟩, 0), (10080, ⟨-1, -2⟩, 1), (10080, ⟨-1, -2⟩, 2), (10080, ⟨1, 2⟩, 0), (10080, ⟨1, 2⟩, 1), (10080, ⟨1, 2⟩, 2), (800, ⟨3, 6⟩, 0), (800, ⟨3, 6⟩, 1), (800, ⟨3, 6⟩, 2)]

theorem g32p_row01_pairing_13 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(80, ⟨-6, -12⟩, 0), (80, ⟨-6, -12⟩, 1), (80, ⟨-6, -12⟩, 2), (2160, ⟨-2, -4⟩, 0), (2160, ⟨-2, -4⟩, 1), (2160, ⟨-2, -4⟩, 2), (5760, ⟨-1, -2⟩, 0), (5760, ⟨-1, -2⟩, 1), (5760, ⟨-1, -2⟩, 2), (5760, ⟨1, 2⟩, 0), (5760, ⟨1, 2⟩, 1), (5760, ⟨1, 2⟩, 2), (2160, ⟨2, 4⟩, 0), (2160, ⟨2, 4⟩, 1), (2160, ⟨2, 4⟩, 2), (80, ⟨6, 12⟩, 0), (80, ⟨6, 12⟩, 1), (80, ⟨6, 12⟩, 2)]

theorem g32p_row01_pairing_14 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (80, ⟨-7, -14⟩, 1), (80, ⟨-7, -14⟩, 2), (720, ⟨-3, -6⟩, 1), (720, ⟨-3, -6⟩, 2), (1260, ⟨-2, -4⟩, 1), (1260, ⟨-2, -4⟩, 2), (10080, ⟨-1, -2⟩, 1), (10080, ⟨-1, -2⟩, 2), (10080, ⟨1, 2⟩, 1), (10080, ⟨1, 2⟩, 2), (1260, ⟨2, 4⟩, 1), (1260, ⟨2, 4⟩, 2), (720, ⟨3, 6⟩, 1), (720, ⟨3, 6⟩, 2), (80, ⟨7, 14⟩, 1), (80, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row01_pairing_15 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (80, ⟨-6, -12⟩, 0), (40, ⟨-5, -10⟩, 1), (40, ⟨-5, -10⟩, 2), (240, ⟨-4, -8⟩, 1), (240, ⟨-4, -8⟩, 2), (2160, ⟨-2, -4⟩, 0), (540, ⟨-2, -4⟩, 1), (540, ⟨-2, -4⟩, 2), (5760, ⟨-1, -2⟩, 0), (9880, ⟨-1, -2⟩, 1), (9880, ⟨-1, -2⟩, 2), (5760, ⟨1, 2⟩, 0), (9880, ⟨1, 2⟩, 1), (9880, ⟨1, 2⟩, 2), (2160, ⟨2, 4⟩, 0), (540, ⟨2, 4⟩, 1), (540, ⟨2, 4⟩, 2), (240, ⟨4, 8⟩, 1), (240, ⟨4, 8⟩, 2), (40, ⟨5, 10⟩, 1), (40, ⟨5, 10⟩, 2), (80, ⟨6, 12⟩, 0), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row01_pairing_16 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (40, ⟨-8, -16⟩, 1), (40, ⟨-8, -16⟩, 2), (40, ⟨-5, -10⟩, 1), (40, ⟨-5, -10⟩, 2), (800, ⟨-3, -6⟩, 0), (360, ⟨-3, -6⟩, 1), (360, ⟨-3, -6⟩, 2), (1260, ⟨-2, -4⟩, 1), (1260, ⟨-2, -4⟩, 2), (10080, ⟨-1, -2⟩, 0), (5040, ⟨-1, -2⟩, 1), (5040, ⟨-1, -2⟩, 2), (10080, ⟨1, 2⟩, 0), (5040, ⟨1, 2⟩, 1), (5040, ⟨1, 2⟩, 2), (1260, ⟨2, 4⟩, 1), (1260, ⟨2, 4⟩, 2), (800, ⟨3, 6⟩, 0), (360, ⟨3, 6⟩, 1), (360, ⟨3, 6⟩, 2), (40, ⟨5, 10⟩, 1), (40, ⟨5, 10⟩, 2), (40, ⟨8, 16⟩, 1), (40, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row01_pairing_17 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (80, ⟨-6, -12⟩, 0), (40, ⟨-5, -10⟩, 1), (40, ⟨-5, -10⟩, 2), (240, ⟨-4, -8⟩, 1), (240, ⟨-4, -8⟩, 2), (2160, ⟨-2, -4⟩, 0), (540, ⟨-2, -4⟩, 1), (540, ⟨-2, -4⟩, 2), (5760, ⟨-1, -2⟩, 0), (9880, ⟨-1, -2⟩, 1), (9880, ⟨-1, -2⟩, 2), (5760, ⟨1, 2⟩, 0), (9880, ⟨1, 2⟩, 1), (9880, ⟨1, 2⟩, 2), (2160, ⟨2, 4⟩, 0), (540, ⟨2, 4⟩, 1), (540, ⟨2, 4⟩, 2), (240, ⟨4, 8⟩, 1), (240, ⟨4, 8⟩, 2), (40, ⟨5, 10⟩, 1), (40, ⟨5, 10⟩, 2), (80, ⟨6, 12⟩, 0), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row01_pairing_18 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (40, ⟨-8, -16⟩, 1), (40, ⟨-8, -16⟩, 2), (40, ⟨-5, -10⟩, 1), (40, ⟨-5, -10⟩, 2), (800, ⟨-3, -6⟩, 0), (360, ⟨-3, -6⟩, 1), (360, ⟨-3, -6⟩, 2), (1260, ⟨-2, -4⟩, 1), (1260, ⟨-2, -4⟩, 2), (10080, ⟨-1, -2⟩, 0), (5040, ⟨-1, -2⟩, 1), (5040, ⟨-1, -2⟩, 2), (10080, ⟨1, 2⟩, 0), (5040, ⟨1, 2⟩, 1), (5040, ⟨1, 2⟩, 2), (1260, ⟨2, 4⟩, 1), (1260, ⟨2, 4⟩, 2), (800, ⟨3, 6⟩, 0), (360, ⟨3, 6⟩, 1), (360, ⟨3, 6⟩, 2), (40, ⟨5, 10⟩, 1), (40, ⟨5, 10⟩, 2), (40, ⟨8, 16⟩, 1), (40, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row01_pairing_19 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 1), (480, ⟨-5, -10⟩, 1), (630, ⟨-4, -8⟩, 1), (160, ⟨-2, -4⟩, 1), (1440, ⟨-2, -4⟩, 2), (10080, ⟨-1, -2⟩, 1), (12480, ⟨-1, -2⟩, 2), (12480, ⟨1, 2⟩, 1), (10080, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 1), (160, ⟨2, 4⟩, 2), (630, ⟨4, 8⟩, 2), (480, ⟨5, 10⟩, 2), (2, ⟨20, 40⟩, 2)]

theorem g32p_row01_pairing_20 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_20)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 1), (90, ⟨-8, -16⟩, 1), (160, ⟨-6, -12⟩, 1), (960, ⟨-3, -6⟩, 1), (4320, ⟨-2, -4⟩, 1), (13248, ⟨-1, -2⟩, 2), (13248, ⟨1, 2⟩, 1), (4320, ⟨2, 4⟩, 2), (960, ⟨3, 6⟩, 2), (160, ⟨6, 12⟩, 2), (90, ⟨8, 16⟩, 2), (2, ⟨24, 48⟩, 2)]

theorem g32p_row01_pairing_21 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_21)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(80, ⟨-9, -18⟩, 0), (80, ⟨-9, -18⟩, 1), (80, ⟨-9, -18⟩, 2), (1440, ⟨-2, -4⟩, 0), (1440, ⟨-2, -4⟩, 1), (1440, ⟨-2, -4⟩, 2), (5040, ⟨-1, -2⟩, 0), (5040, ⟨-1, -2⟩, 1), (5040, ⟨-1, -2⟩, 2), (5040, ⟨1, 2⟩, 0), (5040, ⟨1, 2⟩, 1), (5040, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 0), (1440, ⟨2, 4⟩, 1), (1440, ⟨2, 4⟩, 2), (80, ⟨9, 18⟩, 0), (80, ⟨9, 18⟩, 1), (80, ⟨9, 18⟩, 2)]

theorem g32p_row01_pairing_22 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_22)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (80, ⟨-9, -18⟩, 0), (90, ⟨-6, -12⟩, 1), (80, ⟨-6, -12⟩, 2), (80, ⟨-3, -6⟩, 1), (480, ⟨-3, -6⟩, 2), (1440, ⟨-2, -4⟩, 0), (1620, ⟨-2, -4⟩, 1), (720, ⟨-2, -4⟩, 2), (5040, ⟨-1, -2⟩, 0), (5760, ⟨-1, -2⟩, 1), (6480, ⟨-1, -2⟩, 2), (5040, ⟨1, 2⟩, 0), (6480, ⟨1, 2⟩, 1), (5760, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 0), (720, ⟨2, 4⟩, 1), (1620, ⟨2, 4⟩, 2), (480, ⟨3, 6⟩, 1), (80, ⟨3, 6⟩, 2), (80, ⟨6, 12⟩, 1), (90, ⟨6, 12⟩, 2), (80, ⟨9, 18⟩, 0), (2, ⟨30, 60⟩, 2)]

theorem g32p_row01_pairing_23 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_23)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (80, ⟨-9, -18⟩, 0), (90, ⟨-6, -12⟩, 1), (80, ⟨-6, -12⟩, 2), (80, ⟨-3, -6⟩, 1), (480, ⟨-3, -6⟩, 2), (1440, ⟨-2, -4⟩, 0), (1620, ⟨-2, -4⟩, 1), (720, ⟨-2, -4⟩, 2), (5040, ⟨-1, -2⟩, 0), (5760, ⟨-1, -2⟩, 1), (6480, ⟨-1, -2⟩, 2), (5040, ⟨1, 2⟩, 0), (6480, ⟨1, 2⟩, 1), (5760, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 0), (720, ⟨2, 4⟩, 1), (1620, ⟨2, 4⟩, 2), (480, ⟨3, 6⟩, 1), (80, ⟨3, 6⟩, 2), (80, ⟨6, 12⟩, 1), (90, ⟨6, 12⟩, 2), (80, ⟨9, 18⟩, 0), (2, ⟨30, 60⟩, 2)]

theorem g32p_row01_pairing_24 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (90, ⟨-10, -20⟩, 2), (1600, ⟨-3, -6⟩, 1), (540, ⟨-2, -4⟩, 1), (1080, ⟨-2, -4⟩, 2), (8640, ⟨-1, -2⟩, 1), (11520, ⟨-1, -2⟩, 2), (11520, ⟨1, 2⟩, 1), (8640, ⟨1, 2⟩, 2), (1080, ⟨2, 4⟩, 1), (540, ⟨2, 4⟩, 2), (1600, ⟨3, 6⟩, 2), (90, ⟨10, 20⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row01_pairing_25 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(80, ⟨-9, -18⟩, 0), (80, ⟨-9, -18⟩, 1), (80, ⟨-9, -18⟩, 2), (720, ⟨-3, -6⟩, 0), (720, ⟨-3, -6⟩, 1), (720, ⟨-3, -6⟩, 2), (4320, ⟨-1, -2⟩, 0), (4320, ⟨-1, -2⟩, 1), (4320, ⟨-1, -2⟩, 2), (4320, ⟨1, 2⟩, 0), (4320, ⟨1, 2⟩, 1), (4320, ⟨1, 2⟩, 2), (720, ⟨3, 6⟩, 0), (720, ⟨3, 6⟩, 1), (720, ⟨3, 6⟩, 2), (80, ⟨9, 18⟩, 0), (80, ⟨9, 18⟩, 1), (80, ⟨9, 18⟩, 2)]

theorem g32p_row01_pairing_26 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (80, ⟨-9, -18⟩, 0), (40, ⟨-9, -18⟩, 1), (40, ⟨-9, -18⟩, 2), (720, ⟨-3, -6⟩, 0), (360, ⟨-3, -6⟩, 1), (360, ⟨-3, -6⟩, 2), (540, ⟨-2, -4⟩, 1), (540, ⟨-2, -4⟩, 2), (4320, ⟨-1, -2⟩, 0), (7344, ⟨-1, -2⟩, 1), (7344, ⟨-1, -2⟩, 2), (4320, ⟨1, 2⟩, 0), (7344, ⟨1, 2⟩, 1), (7344, ⟨1, 2⟩, 2), (540, ⟨2, 4⟩, 1), (540, ⟨2, 4⟩, 2), (720, ⟨3, 6⟩, 0), (360, ⟨3, 6⟩, 1), (360, ⟨3, 6⟩, 2), (80, ⟨9, 18⟩, 0), (40, ⟨9, 18⟩, 1), (40, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row01_pairing_27 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (80, ⟨-9, -18⟩, 0), (40, ⟨-9, -18⟩, 1), (40, ⟨-9, -18⟩, 2), (720, ⟨-3, -6⟩, 0), (360, ⟨-3, -6⟩, 1), (360, ⟨-3, -6⟩, 2), (540, ⟨-2, -4⟩, 1), (540, ⟨-2, -4⟩, 2), (4320, ⟨-1, -2⟩, 0), (7344, ⟨-1, -2⟩, 1), (7344, ⟨-1, -2⟩, 2), (4320, ⟨1, 2⟩, 0), (7344, ⟨1, 2⟩, 1), (7344, ⟨1, 2⟩, 2), (540, ⟨2, 4⟩, 1), (540, ⟨2, 4⟩, 2), (720, ⟨3, 6⟩, 0), (360, ⟨3, 6⟩, 1), (360, ⟨3, 6⟩, 2), (80, ⟨9, 18⟩, 0), (40, ⟨9, 18⟩, 1), (40, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row01_pairing_28 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(80, ⟨-6, -12⟩, 0), (80, ⟨-6, -12⟩, 1), (80, ⟨-6, -12⟩, 2), (2160, ⟨-2, -4⟩, 0), (2160, ⟨-2, -4⟩, 1), (2160, ⟨-2, -4⟩, 2), (5760, ⟨-1, -2⟩, 0), (5760, ⟨-1, -2⟩, 1), (5760, ⟨-1, -2⟩, 2), (5760, ⟨1, 2⟩, 0), (5760, ⟨1, 2⟩, 1), (5760, ⟨1, 2⟩, 2), (2160, ⟨2, 4⟩, 0), (2160, ⟨2, 4⟩, 1), (2160, ⟨2, 4⟩, 2), (80, ⟨6, 12⟩, 0), (80, ⟨6, 12⟩, 1), (80, ⟨6, 12⟩, 2)]

theorem g32p_row01_pairing_29 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (170, ⟨-8, -16⟩, 2), (80, ⟨-6, -12⟩, 0), (2160, ⟨-2, -4⟩, 0), (2160, ⟨-2, -4⟩, 1), (560, ⟨-2, -4⟩, 2), (5760, ⟨-1, -2⟩, 0), (3840, ⟨-1, -2⟩, 1), (5760, ⟨-1, -2⟩, 2), (5760, ⟨1, 2⟩, 0), (5760, ⟨1, 2⟩, 1), (3840, ⟨1, 2⟩, 2), (2160, ⟨2, 4⟩, 0), (560, ⟨2, 4⟩, 1), (2160, ⟨2, 4⟩, 2), (80, ⟨6, 12⟩, 0), (170, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 2)]

theorem g32p_row01_pairing_30 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (170, ⟨-8, -16⟩, 2), (80, ⟨-6, -12⟩, 0), (2160, ⟨-2, -4⟩, 0), (2160, ⟨-2, -4⟩, 1), (560, ⟨-2, -4⟩, 2), (5760, ⟨-1, -2⟩, 0), (3840, ⟨-1, -2⟩, 1), (5760, ⟨-1, -2⟩, 2), (5760, ⟨1, 2⟩, 0), (5760, ⟨1, 2⟩, 1), (3840, ⟨1, 2⟩, 2), (2160, ⟨2, 4⟩, 0), (560, ⟨2, 4⟩, 1), (2160, ⟨2, 4⟩, 2), (80, ⟨6, 12⟩, 0), (170, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 2)]

theorem g32p_row01_pairing_31 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(80, ⟨-9, -18⟩, 0), (80, ⟨-9, -18⟩, 1), (80, ⟨-9, -18⟩, 2), (720, ⟨-3, -6⟩, 0), (720, ⟨-3, -6⟩, 1), (720, ⟨-3, -6⟩, 2), (4320, ⟨-1, -2⟩, 0), (4320, ⟨-1, -2⟩, 1), (4320, ⟨-1, -2⟩, 2), (4320, ⟨1, 2⟩, 0), (4320, ⟨1, 2⟩, 1), (4320, ⟨1, 2⟩, 2), (720, ⟨3, 6⟩, 0), (720, ⟨3, 6⟩, 1), (720, ⟨3, 6⟩, 2), (80, ⟨9, 18⟩, 0), (80, ⟨9, 18⟩, 1), (80, ⟨9, 18⟩, 2)]

theorem g32p_row01_pairing_32 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (80, ⟨-9, -18⟩, 0), (80, ⟨-9, -18⟩, 1), (720, ⟨-3, -6⟩, 0), (1350, ⟨-3, -6⟩, 2), (4320, ⟨-1, -2⟩, 0), (7560, ⟨-1, -2⟩, 1), (4320, ⟨-1, -2⟩, 2), (4320, ⟨1, 2⟩, 0), (4320, ⟨1, 2⟩, 1), (7560, ⟨1, 2⟩, 2), (720, ⟨3, 6⟩, 0), (1350, ⟨3, 6⟩, 1), (80, ⟨9, 18⟩, 0), (80, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row01_pairing_33 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (80, ⟨-9, -18⟩, 0), (80, ⟨-9, -18⟩, 1), (720, ⟨-3, -6⟩, 0), (1350, ⟨-3, -6⟩, 2), (4320, ⟨-1, -2⟩, 0), (7560, ⟨-1, -2⟩, 1), (4320, ⟨-1, -2⟩, 2), (4320, ⟨1, 2⟩, 0), (4320, ⟨1, 2⟩, 1), (7560, ⟨1, 2⟩, 2), (720, ⟨3, 6⟩, 0), (1350, ⟨3, 6⟩, 1), (80, ⟨9, 18⟩, 0), (80, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row01_pairing_34 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(80, ⟨-9, -18⟩, 0), (80, ⟨-9, -18⟩, 1), (80, ⟨-9, -18⟩, 2), (1440, ⟨-2, -4⟩, 0), (1440, ⟨-2, -4⟩, 1), (1440, ⟨-2, -4⟩, 2), (5040, ⟨-1, -2⟩, 0), (5040, ⟨-1, -2⟩, 1), (5040, ⟨-1, -2⟩, 2), (5040, ⟨1, 2⟩, 0), (5040, ⟨1, 2⟩, 1), (5040, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 0), (1440, ⟨2, 4⟩, 1), (1440, ⟨2, 4⟩, 2), (80, ⟨9, 18⟩, 0), (80, ⟨9, 18⟩, 1), (80, ⟨9, 18⟩, 2)]

theorem g32p_row01_pairing_35 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (80, ⟨-9, -18⟩, 0), (40, ⟨-6, -12⟩, 1), (40, ⟨-6, -12⟩, 2), (520, ⟨-3, -6⟩, 1), (520, ⟨-3, -6⟩, 2), (1440, ⟨-2, -4⟩, 0), (900, ⟨-2, -4⟩, 1), (900, ⟨-2, -4⟩, 2), (5040, ⟨-1, -2⟩, 0), (3960, ⟨-1, -2⟩, 1), (3960, ⟨-1, -2⟩, 2), (5040, ⟨1, 2⟩, 0), (3960, ⟨1, 2⟩, 1), (3960, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 0), (900, ⟨2, 4⟩, 1), (900, ⟨2, 4⟩, 2), (520, ⟨3, 6⟩, 1), (520, ⟨3, 6⟩, 2), (40, ⟨6, 12⟩, 1), (40, ⟨6, 12⟩, 2), (80, ⟨9, 18⟩, 0), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row01_pairing_36 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (240, ⟨-6, -12⟩, 1), (240, ⟨-6, -12⟩, 2), (800, ⟨-3, -6⟩, 1), (800, ⟨-3, -6⟩, 2), (540, ⟨-2, -4⟩, 1), (540, ⟨-2, -4⟩, 2), (4320, ⟨-1, -2⟩, 1), (4320, ⟨-1, -2⟩, 2), (4320, ⟨1, 2⟩, 1), (4320, ⟨1, 2⟩, 2), (540, ⟨2, 4⟩, 1), (540, ⟨2, 4⟩, 2), (800, ⟨3, 6⟩, 1), (800, ⟨3, 6⟩, 2), (240, ⟨6, 12⟩, 1), (240, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row01_pairing_37 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (80, ⟨-9, -18⟩, 0), (40, ⟨-6, -12⟩, 1), (40, ⟨-6, -12⟩, 2), (520, ⟨-3, -6⟩, 1), (520, ⟨-3, -6⟩, 2), (1440, ⟨-2, -4⟩, 0), (900, ⟨-2, -4⟩, 1), (900, ⟨-2, -4⟩, 2), (5040, ⟨-1, -2⟩, 0), (3960, ⟨-1, -2⟩, 1), (3960, ⟨-1, -2⟩, 2), (5040, ⟨1, 2⟩, 0), (3960, ⟨1, 2⟩, 1), (3960, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 0), (900, ⟨2, 4⟩, 1), (900, ⟨2, 4⟩, 2), (520, ⟨3, 6⟩, 1), (520, ⟨3, 6⟩, 2), (40, ⟨6, 12⟩, 1), (40, ⟨6, 12⟩, 2), (80, ⟨9, 18⟩, 0), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row01_pairing_38 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 1), (160, ⟨-6, -12⟩, 1), (540, ⟨-4, -8⟩, 1), (90, ⟨-4, -8⟩, 2), (1440, ⟨-3, -6⟩, 2), (1440, ⟨-2, -4⟩, 1), (4320, ⟨-1, -2⟩, 1), (5760, ⟨-1, -2⟩, 2), (5760, ⟨1, 2⟩, 1), (4320, ⟨1, 2⟩, 2), (1440, ⟨2, 4⟩, 2), (1440, ⟨3, 6⟩, 1), (90, ⟨4, 8⟩, 1), (540, ⟨4, 8⟩, 2), (160, ⟨6, 12⟩, 2), (2, ⟨60, 120⟩, 2)]

theorem g32p_row01_pairing_39 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_39)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 1), (160, ⟨-8, -16⟩, 2), (480, ⟨-4, -8⟩, 1), (960, ⟨-2, -4⟩, 2), (11520, ⟨-1, -2⟩, 1), (10368, ⟨-1, -2⟩, 2), (10368, ⟨1, 2⟩, 1), (11520, ⟨1, 2⟩, 2), (960, ⟨2, 4⟩, 1), (480, ⟨4, 8⟩, 2), (160, ⟨8, 16⟩, 1), (2, ⟨64, 128⟩, 2)]

theorem g32p_row01_pairing_40 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_40)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (80, ⟨-8, -16⟩, 1), (80, ⟨-8, -16⟩, 2), (240, ⟨-4, -8⟩, 1), (240, ⟨-4, -8⟩, 2), (480, ⟨-2, -4⟩, 1), (480, ⟨-2, -4⟩, 2), (10944, ⟨-1, -2⟩, 1), (10944, ⟨-1, -2⟩, 2), (10944, ⟨1, 2⟩, 1), (10944, ⟨1, 2⟩, 2), (480, ⟨2, 4⟩, 1), (480, ⟨2, 4⟩, 2), (240, ⟨4, 8⟩, 1), (240, ⟨4, 8⟩, 2), (80, ⟨8, 16⟩, 1), (80, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 2)]

theorem g32p_row01_pairing_41 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (80, ⟨-8, -16⟩, 1), (80, ⟨-8, -16⟩, 2), (480, ⟨-4, -8⟩, 1), (480, ⟨-4, -8⟩, 2), (240, ⟨-2, -4⟩, 1), (240, ⟨-2, -4⟩, 2), (5760, ⟨-1, -2⟩, 1), (5760, ⟨-1, -2⟩, 2), (5760, ⟨1, 2⟩, 1), (5760, ⟨1, 2⟩, 2), (240, ⟨2, 4⟩, 1), (240, ⟨2, 4⟩, 2), (480, ⟨4, 8⟩, 1), (480, ⟨4, 8⟩, 2), (80, ⟨8, 16⟩, 1), (80, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 1), (1, ⟨80, 160⟩, 2)]

theorem g32p_row01_pairing_42 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 1), (90, ⟨-9, -18⟩, 1), (1620, ⟨-3, -6⟩, 2), (10368, ⟨-1, -2⟩, 1), (6480, ⟨-1, -2⟩, 2), (6480, ⟨1, 2⟩, 1), (10368, ⟨1, 2⟩, 2), (1620, ⟨3, 6⟩, 1), (90, ⟨9, 18⟩, 2), (2, ⟨81, 162⟩, 2)]

theorem g32p_row01_pairing_43 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_43)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 2), (80, ⟨-7, 0⟩, 0), (80, ⟨-7, 0⟩, 1), (80, ⟨-7, 0⟩, 2), (720, ⟨-3, 0⟩, 0), (720, ⟨-3, 0⟩, 1), (720, ⟨-3, 0⟩, 2), (1260, ⟨-2, 0⟩, 0), (1260, ⟨-2, 0⟩, 1), (1260, ⟨-2, 0⟩, 2), (10080, ⟨-1, 0⟩, 0), (10080, ⟨-1, 0⟩, 1), (10080, ⟨-1, 0⟩, 2), (10080, ⟨1, 0⟩, 0), (10080, ⟨1, 0⟩, 1), (10080, ⟨1, 0⟩, 2), (1260, ⟨2, 0⟩, 0), (1260, ⟨2, 0⟩, 1), (1260, ⟨2, 0⟩, 2), (720, ⟨3, 0⟩, 0), (720, ⟨3, 0⟩, 1), (720, ⟨3, 0⟩, 2), (80, ⟨7, 0⟩, 0), (80, ⟨7, 0⟩, 1), (80, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 1), (1, ⟨20, 0⟩, 2)]

theorem g32p_row01_pairing_44 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 2), (240, ⟨-6, 0⟩, 0), (240, ⟨-6, 0⟩, 1), (240, ⟨-6, 0⟩, 2), (800, ⟨-3, 0⟩, 0), (800, ⟨-3, 0⟩, 1), (800, ⟨-3, 0⟩, 2), (540, ⟨-2, 0⟩, 0), (540, ⟨-2, 0⟩, 1), (540, ⟨-2, 0⟩, 2), (4320, ⟨-1, 0⟩, 0), (4320, ⟨-1, 0⟩, 1), (4320, ⟨-1, 0⟩, 2), (4320, ⟨1, 0⟩, 0), (4320, ⟨1, 0⟩, 1), (4320, ⟨1, 0⟩, 2), (540, ⟨2, 0⟩, 0), (540, ⟨2, 0⟩, 1), (540, ⟨2, 0⟩, 2), (800, ⟨3, 0⟩, 0), (800, ⟨3, 0⟩, 1), (800, ⟨3, 0⟩, 2), (240, ⟨6, 0⟩, 0), (240, ⟨6, 0⟩, 1), (240, ⟨6, 0⟩, 2), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 1), (1, ⟨60, 0⟩, 2)]

theorem g32p_row01_pairing_45 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 2), (80, ⟨-8, 0⟩, 0), (80, ⟨-8, 0⟩, 1), (80, ⟨-8, 0⟩, 2), (240, ⟨-4, 0⟩, 0), (240, ⟨-4, 0⟩, 1), (240, ⟨-4, 0⟩, 2), (480, ⟨-2, 0⟩, 0), (480, ⟨-2, 0⟩, 1), (480, ⟨-2, 0⟩, 2), (10944, ⟨-1, 0⟩, 0), (10944, ⟨-1, 0⟩, 1), (10944, ⟨-1, 0⟩, 2), (10944, ⟨1, 0⟩, 0), (10944, ⟨1, 0⟩, 1), (10944, ⟨1, 0⟩, 2), (480, ⟨2, 0⟩, 0), (480, ⟨2, 0⟩, 1), (480, ⟨2, 0⟩, 2), (240, ⟨4, 0⟩, 0), (240, ⟨4, 0⟩, 1), (240, ⟨4, 0⟩, 2), (80, ⟨8, 0⟩, 0), (80, ⟨8, 0⟩, 1), (80, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 1), (1, ⟨64, 0⟩, 2)]

theorem g32p_row01_pairing_46 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row01_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 2), (80, ⟨-8, 0⟩, 0), (80, ⟨-8, 0⟩, 1), (80, ⟨-8, 0⟩, 2), (480, ⟨-4, 0⟩, 0), (480, ⟨-4, 0⟩, 1), (480, ⟨-4, 0⟩, 2), (240, ⟨-2, 0⟩, 0), (240, ⟨-2, 0⟩, 1), (240, ⟨-2, 0⟩, 2), (5760, ⟨-1, 0⟩, 0), (5760, ⟨-1, 0⟩, 1), (5760, ⟨-1, 0⟩, 2), (5760, ⟨1, 0⟩, 0), (5760, ⟨1, 0⟩, 1), (5760, ⟨1, 0⟩, 2), (240, ⟨2, 0⟩, 0), (240, ⟨2, 0⟩, 1), (240, ⟨2, 0⟩, 2), (480, ⟨4, 0⟩, 0), (480, ⟨4, 0⟩, 1), (480, ⟨4, 0⟩, 2), (80, ⟨8, 0⟩, 0), (80, ⟨8, 0⟩, 1), (80, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 1), (1, ⟨80, 0⟩, 2)]

theorem g32p_row01_pairing_47 :
    g32p_cyclotomicPairingCheck 155520 (0)
      (g32p_pairingCoefficients 3 g32p_row01_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row01_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 1 ∧ g32SparseVec v.coords =
        (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨1, -1, [(1, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row02_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(192, ⟨-1, -2⟩, 0), (192, ⟨-1, -2⟩, 1), (192, ⟨-1, -2⟩, 2), (192, ⟨-1, -2⟩, 3), (192, ⟨-1, -2⟩, 4), (192, ⟨-1, -2⟩, 5), (192, ⟨1, 2⟩, 0), (192, ⟨1, 2⟩, 1), (192, ⟨1, 2⟩, 2), (192, ⟨1, 2⟩, 3), (192, ⟨1, 2⟩, 4), (192, ⟨1, 2⟩, 5)]

theorem g32p_row02_pairing_0 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 4), (112, ⟨-1, -2⟩, 0), (112, ⟨-1, -2⟩, 2), (112, ⟨-1, -2⟩, 4), (112, ⟨1, 2⟩, 0), (112, ⟨1, 2⟩, 2), (112, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4)]

theorem g32p_row02_pairing_1 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (64, ⟨-2, -4⟩, 0), (44, ⟨-2, -4⟩, 2), (44, ⟨-2, -4⟩, 4), (128, ⟨-1, -2⟩, 0), (120, ⟨-1, -2⟩, 2), (120, ⟨-1, -2⟩, 4), (128, ⟨1, 2⟩, 0), (120, ⟨1, 2⟩, 2), (120, ⟨1, 2⟩, 4), (64, ⟨2, 4⟩, 0), (44, ⟨2, 4⟩, 2), (44, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row02_pairing_2 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (96, ⟨-2, -4⟩, 0), (28, ⟨-2, -4⟩, 2), (28, ⟨-2, -4⟩, 4), (184, ⟨-1, -2⟩, 2), (184, ⟨-1, -2⟩, 4), (184, ⟨1, 2⟩, 2), (184, ⟨1, 2⟩, 4), (96, ⟨2, 4⟩, 0), (28, ⟨2, 4⟩, 2), (28, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row02_pairing_3 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (32, ⟨-2, -4⟩, 0), (96, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (96, ⟨-2, -4⟩, 3), (32, ⟨-2, -4⟩, 4), (96, ⟨-2, -4⟩, 5), (112, ⟨-1, -2⟩, 0), (112, ⟨-1, -2⟩, 2), (112, ⟨-1, -2⟩, 4), (112, ⟨1, 2⟩, 0), (112, ⟨1, 2⟩, 2), (112, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (96, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (96, ⟨2, 4⟩, 3), (32, ⟨2, 4⟩, 4), (96, ⟨2, 4⟩, 5), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4)]

theorem g32p_row02_pairing_4 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (24, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 4), (32, ⟨-2, -4⟩, 0), (96, ⟨-2, -4⟩, 1), (96, ⟨-2, -4⟩, 2), (64, ⟨-1, -2⟩, 0), (336, ⟨-1, -2⟩, 1), (348, ⟨-1, -2⟩, 2), (192, ⟨-1, -2⟩, 3), (16, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (64, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (16, ⟨1, 2⟩, 2), (192, ⟨1, 2⟩, 3), (348, ⟨1, 2⟩, 4), (336, ⟨1, 2⟩, 5), (32, ⟨2, 4⟩, 0), (96, ⟨2, 4⟩, 4), (96, ⟨2, 4⟩, 5), (2, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4), (24, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row02_pairing_5 :
    g32p_cyclotomicPairingCheck 3456 (1)
      (g32p_pairingCoefficients 6 g32p_row02_terms_5)
      [1, -1, 1] [-3456, -4032, -1152, 1728, 2304, 1152] = true := by
  decide +kernel

def g32p_row02_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (24, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 4), (80, ⟨-2, -4⟩, 2), (48, ⟨-2, -4⟩, 4), (96, ⟨-2, -4⟩, 5), (192, ⟨-1, -2⟩, 0), (240, ⟨-1, -2⟩, 1), (108, ⟨-1, -2⟩, 2), (192, ⟨-1, -2⟩, 3), (128, ⟨-1, -2⟩, 4), (120, ⟨-1, -2⟩, 5), (192, ⟨1, 2⟩, 0), (120, ⟨1, 2⟩, 1), (128, ⟨1, 2⟩, 2), (192, ⟨1, 2⟩, 3), (108, ⟨1, 2⟩, 4), (240, ⟨1, 2⟩, 5), (96, ⟨2, 4⟩, 1), (48, ⟨2, 4⟩, 2), (80, ⟨2, 4⟩, 4), (18, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row02_pairing_6 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 2), (48, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 2), (32, ⟨-3, -6⟩, 4), (24, ⟨-2, -4⟩, 1), (60, ⟨-2, -4⟩, 2), (66, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (144, ⟨-1, -2⟩, 0), (96, ⟨-1, -2⟩, 1), (96, ⟨-1, -2⟩, 2), (192, ⟨-1, -2⟩, 3), (48, ⟨-1, -2⟩, 4), (96, ⟨-1, -2⟩, 5), (144, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (192, ⟨1, 2⟩, 3), (96, ⟨1, 2⟩, 4), (96, ⟨1, 2⟩, 5), (24, ⟨2, 4⟩, 1), (66, ⟨2, 4⟩, 2), (60, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (48, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4), (2, ⟨6, 12⟩, 4)]

theorem g32p_row02_pairing_7 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 2), (32, ⟨-3, -6⟩, 4), (96, ⟨-1, -2⟩, 0), (96, ⟨-1, -2⟩, 2), (96, ⟨-1, -2⟩, 4), (96, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 2), (96, ⟨1, 2⟩, 4), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 4)]

theorem g32p_row02_pairing_8 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (16, ⟨-5, -10⟩, 0), (32, ⟨-3, -6⟩, 4), (24, ⟨-2, -4⟩, 1), (42, ⟨-2, -4⟩, 2), (52, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (176, ⟨-1, -2⟩, 0), (96, ⟨-1, -2⟩, 1), (192, ⟨-1, -2⟩, 2), (192, ⟨-1, -2⟩, 3), (96, ⟨-1, -2⟩, 4), (96, ⟨-1, -2⟩, 5), (176, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 1), (96, ⟨1, 2⟩, 2), (192, ⟨1, 2⟩, 3), (192, ⟨1, 2⟩, 4), (96, ⟨1, 2⟩, 5), (24, ⟨2, 4⟩, 1), (52, ⟨2, 4⟩, 2), (42, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (32, ⟨3, 6⟩, 2), (16, ⟨5, 10⟩, 0), (2, ⟨10, 20⟩, 4)]

theorem g32p_row02_pairing_9 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (16, ⟨-5, -10⟩, 2), (32, ⟨-3, -6⟩, 2), (32, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (26, ⟨-2, -4⟩, 2), (36, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (64, ⟨-1, -2⟩, 0), (96, ⟨-1, -2⟩, 1), (112, ⟨-1, -2⟩, 2), (192, ⟨-1, -2⟩, 3), (288, ⟨-1, -2⟩, 4), (96, ⟨-1, -2⟩, 5), (64, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 1), (288, ⟨1, 2⟩, 2), (192, ⟨1, 2⟩, 3), (112, ⟨1, 2⟩, 4), (96, ⟨1, 2⟩, 5), (32, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (26, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (32, ⟨3, 6⟩, 4), (16, ⟨5, 10⟩, 4), (2, ⟨10, 20⟩, 4)]

theorem g32p_row02_pairing_10 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (2, ⟨-7, -14⟩, 2), (24, ⟨-7, -14⟩, 5), (16, ⟨-3, -6⟩, 0), (116, ⟨-3, -6⟩, 2), (24, ⟨-3, -6⟩, 5), (32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 2), (96, ⟨-2, -4⟩, 3), (96, ⟨-2, -4⟩, 5), (112, ⟨-1, -2⟩, 0), (160, ⟨-1, -2⟩, 2), (40, ⟨-1, -2⟩, 4), (144, ⟨-1, -2⟩, 5), (112, ⟨1, 2⟩, 0), (144, ⟨1, 2⟩, 1), (40, ⟨1, 2⟩, 2), (160, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (96, ⟨2, 4⟩, 1), (96, ⟨2, 4⟩, 3), (32, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (116, ⟨3, 6⟩, 4), (24, ⟨7, 14⟩, 1), (2, ⟨7, 14⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row02_pairing_11 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_11)
      [1, -1, 1] [0, 576, 0, 576, 0, -1152] = true := by
  decide +kernel

def g32p_row02_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (16, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 4), (32, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 2), (32, ⟨-3, -6⟩, 4), (16, ⟨-2, -4⟩, 0), (64, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 4), (32, ⟨-1, -2⟩, 0), (192, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (192, ⟨-1, -2⟩, 3), (38, ⟨-1, -2⟩, 4), (192, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 0), (192, ⟨1, 2⟩, 1), (38, ⟨1, 2⟩, 2), (192, ⟨1, 2⟩, 3), (32, ⟨1, 2⟩, 4), (192, ⟨1, 2⟩, 5), (16, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 2), (64, ⟨2, 4⟩, 4), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 4), (16, ⟨6, 12⟩, 0), (16, ⟨6, 12⟩, 2), (2, ⟨15, 30⟩, 4)]

theorem g32p_row02_pairing_12 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 2), (32, ⟨-3, -6⟩, 4), (96, ⟨-1, -2⟩, 0), (96, ⟨-1, -2⟩, 2), (96, ⟨-1, -2⟩, 4), (96, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 2), (96, ⟨1, 2⟩, 4), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 4)]

theorem g32p_row02_pairing_13 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 2), (16, ⟨-6, -12⟩, 4), (48, ⟨-2, -4⟩, 0), (48, ⟨-2, -4⟩, 2), (48, ⟨-2, -4⟩, 4), (48, ⟨2, 4⟩, 0), (48, ⟨2, 4⟩, 2), (48, ⟨2, 4⟩, 4), (16, ⟨6, 12⟩, 0), (16, ⟨6, 12⟩, 2), (16, ⟨6, 12⟩, 4)]

theorem g32p_row02_pairing_14 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (16, ⟨-7, -14⟩, 0), (8, ⟨-7, -14⟩, 2), (8, ⟨-7, -14⟩, 4), (16, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (32, ⟨-2, -4⟩, 0), (60, ⟨-2, -4⟩, 2), (60, ⟨-2, -4⟩, 4), (96, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 2), (48, ⟨-1, -2⟩, 4), (96, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 2), (48, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (60, ⟨2, 4⟩, 2), (60, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (16, ⟨7, 14⟩, 0), (8, ⟨7, 14⟩, 2), (8, ⟨7, 14⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row02_pairing_15 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 4), (8, ⟨-5, -10⟩, 2), (8, ⟨-5, -10⟩, 4), (32, ⟨-4, -8⟩, 0), (16, ⟨-4, -8⟩, 2), (16, ⟨-4, -8⟩, 4), (32, ⟨-2, -4⟩, 0), (20, ⟨-2, -4⟩, 2), (20, ⟨-2, -4⟩, 4), (128, ⟨-1, -2⟩, 0), (120, ⟨-1, -2⟩, 2), (120, ⟨-1, -2⟩, 4), (128, ⟨1, 2⟩, 0), (120, ⟨1, 2⟩, 2), (120, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (20, ⟨2, 4⟩, 2), (20, ⟨2, 4⟩, 4), (32, ⟨4, 8⟩, 0), (16, ⟨4, 8⟩, 2), (16, ⟨4, 8⟩, 4), (8, ⟨5, 10⟩, 2), (8, ⟨5, 10⟩, 4), (8, ⟨6, 12⟩, 2), (8, ⟨6, 12⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row02_pairing_16 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (16, ⟨-8, -16⟩, 0), (8, ⟨-5, -10⟩, 2), (8, ⟨-5, -10⟩, 4), (24, ⟨-3, -6⟩, 2), (24, ⟨-3, -6⟩, 4), (32, ⟨-2, -4⟩, 0), (60, ⟨-2, -4⟩, 2), (60, ⟨-2, -4⟩, 4), (96, ⟨-1, -2⟩, 2), (96, ⟨-1, -2⟩, 4), (96, ⟨1, 2⟩, 2), (96, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (60, ⟨2, 4⟩, 2), (60, ⟨2, 4⟩, 4), (24, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 4), (8, ⟨5, 10⟩, 2), (8, ⟨5, 10⟩, 4), (16, ⟨8, 16⟩, 0), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row02_pairing_17 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 4), (16, ⟨-5, -10⟩, 0), (32, ⟨-4, -8⟩, 0), (16, ⟨-4, -8⟩, 2), (16, ⟨-4, -8⟩, 4), (32, ⟨-2, -4⟩, 0), (20, ⟨-2, -4⟩, 2), (20, ⟨-2, -4⟩, 4), (112, ⟨-1, -2⟩, 0), (128, ⟨-1, -2⟩, 2), (128, ⟨-1, -2⟩, 4), (112, ⟨1, 2⟩, 0), (128, ⟨1, 2⟩, 2), (128, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (20, ⟨2, 4⟩, 2), (20, ⟨2, 4⟩, 4), (32, ⟨4, 8⟩, 0), (16, ⟨4, 8⟩, 2), (16, ⟨4, 8⟩, 4), (16, ⟨5, 10⟩, 0), (8, ⟨6, 12⟩, 2), (8, ⟨6, 12⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row02_pairing_18 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-8, -16⟩, 2), (8, ⟨-8, -16⟩, 4), (16, ⟨-5, -10⟩, 0), (16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (32, ⟨-2, -4⟩, 0), (60, ⟨-2, -4⟩, 2), (60, ⟨-2, -4⟩, 4), (96, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 2), (48, ⟨-1, -2⟩, 4), (96, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 2), (48, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (60, ⟨2, 4⟩, 2), (60, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4), (16, ⟨5, 10⟩, 0), (8, ⟨8, 16⟩, 2), (8, ⟨8, 16⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row02_pairing_19 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 2), (32, ⟨-5, -10⟩, 0), (32, ⟨-5, -10⟩, 4), (38, ⟨-4, -8⟩, 2), (48, ⟨-4, -8⟩, 5), (32, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 4), (32, ⟨-1, -2⟩, 0), (192, ⟨-1, -2⟩, 1), (64, ⟨-1, -2⟩, 2), (192, ⟨-1, -2⟩, 3), (96, ⟨-1, -2⟩, 4), (32, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 2), (192, ⟨1, 2⟩, 3), (64, ⟨1, 2⟩, 4), (192, ⟨1, 2⟩, 5), (32, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 2), (16, ⟨2, 4⟩, 4), (48, ⟨4, 8⟩, 1), (38, ⟨4, 8⟩, 4), (32, ⟨5, 10⟩, 0), (32, ⟨5, 10⟩, 2), (2, ⟨20, 40⟩, 4)]

theorem g32p_row02_pairing_20 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 2), (2, ⟨-8, -16⟩, 2), (24, ⟨-8, -16⟩, 5), (16, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 4), (64, ⟨-3, -6⟩, 2), (48, ⟨-2, -4⟩, 0), (96, ⟨-2, -4⟩, 1), (96, ⟨-2, -4⟩, 3), (48, ⟨-2, -4⟩, 4), (64, ⟨-1, -2⟩, 4), (64, ⟨1, 2⟩, 2), (48, ⟨2, 4⟩, 0), (48, ⟨2, 4⟩, 2), (96, ⟨2, 4⟩, 3), (96, ⟨2, 4⟩, 5), (64, ⟨3, 6⟩, 4), (16, ⟨6, 12⟩, 0), (16, ⟨6, 12⟩, 2), (24, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 4), (2, ⟨24, 48⟩, 4)]

theorem g32p_row02_pairing_21 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-9, -18⟩, 0), (16, ⟨-9, -18⟩, 2), (16, ⟨-9, -18⟩, 4), (32, ⟨-2, -4⟩, 0), (96, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (96, ⟨-2, -4⟩, 3), (32, ⟨-2, -4⟩, 4), (96, ⟨-2, -4⟩, 5), (112, ⟨-1, -2⟩, 0), (112, ⟨-1, -2⟩, 2), (112, ⟨-1, -2⟩, 4), (112, ⟨1, 2⟩, 0), (112, ⟨1, 2⟩, 2), (112, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (96, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (96, ⟨2, 4⟩, 3), (32, ⟨2, 4⟩, 4), (96, ⟨2, 4⟩, 5), (16, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 2), (16, ⟨9, 18⟩, 4)]

theorem g32p_row02_pairing_22 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (16, ⟨-9, -18⟩, 4), (16, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 2), (24, ⟨-6, -12⟩, 5), (32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (16, ⟨-2, -4⟩, 0), (96, ⟨-2, -4⟩, 1), (92, ⟨-2, -4⟩, 2), (24, ⟨-2, -4⟩, 5), (32, ⟨-1, -2⟩, 0), (96, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (192, ⟨-1, -2⟩, 3), (208, ⟨-1, -2⟩, 4), (96, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 1), (208, ⟨1, 2⟩, 2), (192, ⟨1, 2⟩, 3), (48, ⟨1, 2⟩, 4), (96, ⟨1, 2⟩, 5), (16, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (92, ⟨2, 4⟩, 4), (96, ⟨2, 4⟩, 5), (32, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 4), (16, ⟨6, 12⟩, 0), (24, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 4), (16, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 4)]

theorem g32p_row02_pairing_23 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_23)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (16, ⟨-9, -18⟩, 2), (18, ⟨-6, -12⟩, 2), (24, ⟨-6, -12⟩, 5), (48, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 2), (76, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 4), (120, ⟨-2, -4⟩, 5), (144, ⟨-1, -2⟩, 0), (112, ⟨-1, -2⟩, 2), (192, ⟨-1, -2⟩, 3), (32, ⟨-1, -2⟩, 4), (192, ⟨-1, -2⟩, 5), (144, ⟨1, 2⟩, 0), (192, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (192, ⟨1, 2⟩, 3), (112, ⟨1, 2⟩, 4), (120, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (76, ⟨2, 4⟩, 4), (48, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 4), (24, ⟨6, 12⟩, 1), (18, ⟨6, 12⟩, 4), (16, ⟨9, 18⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row02_pairing_24 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_24)
      [1, -1, 1] [0, 576, 0, 576, 0, -1152] = true := by
  decide +kernel

def g32p_row02_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (24, ⟨-10, -20⟩, 1), (2, ⟨-10, -20⟩, 4), (48, ⟨-3, -6⟩, 0), (64, ⟨-3, -6⟩, 2), (48, ⟨-3, -6⟩, 4), (36, ⟨-2, -4⟩, 2), (24, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (144, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 2), (192, ⟨-1, -2⟩, 3), (160, ⟨-1, -2⟩, 4), (192, ⟨-1, -2⟩, 5), (144, ⟨1, 2⟩, 0), (192, ⟨1, 2⟩, 1), (160, ⟨1, 2⟩, 2), (192, ⟨1, 2⟩, 3), (48, ⟨1, 2⟩, 4), (24, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (36, ⟨2, 4⟩, 4), (48, ⟨3, 6⟩, 0), (48, ⟨3, 6⟩, 2), (64, ⟨3, 6⟩, 4), (2, ⟨10, 20⟩, 2), (24, ⟨10, 20⟩, 5), (2, ⟨30, 60⟩, 4)]

theorem g32p_row02_pairing_25 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-9, -18⟩, 0), (16, ⟨-9, -18⟩, 2), (16, ⟨-9, -18⟩, 4), (16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (96, ⟨-1, -2⟩, 0), (96, ⟨-1, -2⟩, 2), (96, ⟨-1, -2⟩, 4), (96, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 2), (96, ⟨1, 2⟩, 4), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4), (16, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 2), (16, ⟨9, 18⟩, 4)]

theorem g32p_row02_pairing_26 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (16, ⟨-9, -18⟩, 2), (16, ⟨-9, -18⟩, 4), (16, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (96, ⟨-1, -2⟩, 2), (96, ⟨-1, -2⟩, 4), (96, ⟨1, 2⟩, 2), (96, ⟨1, 2⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4), (16, ⟨9, 18⟩, 2), (16, ⟨9, 18⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row02_pairing_27 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (16, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (16, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (96, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 2), (48, ⟨-1, -2⟩, 4), (96, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 2), (48, ⟨1, 2⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (16, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row02_pairing_28 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 2), (16, ⟨-6, -12⟩, 4), (48, ⟨-2, -4⟩, 0), (96, ⟨-2, -4⟩, 1), (48, ⟨-2, -4⟩, 2), (96, ⟨-2, -4⟩, 3), (48, ⟨-2, -4⟩, 4), (96, ⟨-2, -4⟩, 5), (48, ⟨2, 4⟩, 0), (96, ⟨2, 4⟩, 1), (48, ⟨2, 4⟩, 2), (96, ⟨2, 4⟩, 3), (48, ⟨2, 4⟩, 4), (96, ⟨2, 4⟩, 5), (16, ⟨6, 12⟩, 0), (16, ⟨6, 12⟩, 2), (16, ⟨6, 12⟩, 4)]

theorem g32p_row02_pairing_29 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (24, ⟨-8, -16⟩, 1), (16, ⟨-8, -16⟩, 2), (2, ⟨-8, -16⟩, 4), (16, ⟨-6, -12⟩, 2), (96, ⟨-2, -4⟩, 0), (192, ⟨-2, -4⟩, 1), (80, ⟨-2, -4⟩, 2), (128, ⟨-1, -2⟩, 2), (128, ⟨1, 2⟩, 4), (96, ⟨2, 4⟩, 0), (80, ⟨2, 4⟩, 4), (192, ⟨2, 4⟩, 5), (16, ⟨6, 12⟩, 4), (2, ⟨8, 16⟩, 2), (16, ⟨8, 16⟩, 4), (24, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row02_pairing_30 :
    g32p_cyclotomicPairingCheck 3456 (1)
      (g32p_pairingCoefficients 6 g32p_row02_terms_30)
      [1, -1, 1] [-3456, -4032, -1152, 1728, 2304, 1152] = true := by
  decide +kernel

def g32p_row02_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (16, ⟨-8, -16⟩, 0), (24, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 4), (16, ⟨-6, -12⟩, 4), (32, ⟨-2, -4⟩, 0), (48, ⟨-2, -4⟩, 2), (96, ⟨-2, -4⟩, 3), (96, ⟨-2, -4⟩, 4), (96, ⟨-2, -4⟩, 5), (128, ⟨-1, -2⟩, 2), (128, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (96, ⟨2, 4⟩, 1), (96, ⟨2, 4⟩, 2), (96, ⟨2, 4⟩, 3), (48, ⟨2, 4⟩, 4), (16, ⟨6, 12⟩, 2), (16, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 2), (24, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row02_pairing_31 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-9, -18⟩, 0), (16, ⟨-9, -18⟩, 2), (16, ⟨-9, -18⟩, 4), (16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (96, ⟨-1, -2⟩, 0), (96, ⟨-1, -2⟩, 2), (96, ⟨-1, -2⟩, 4), (96, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 2), (96, ⟨1, 2⟩, 4), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4), (16, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 2), (16, ⟨9, 18⟩, 4)]

theorem g32p_row02_pairing_32 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (32, ⟨-9, -18⟩, 4), (48, ⟨-3, -6⟩, 1), (32, ⟨-3, -6⟩, 2), (38, ⟨-3, -6⟩, 4), (216, ⟨-1, -2⟩, 2), (144, ⟨-1, -2⟩, 5), (144, ⟨1, 2⟩, 1), (216, ⟨1, 2⟩, 4), (38, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 4), (48, ⟨3, 6⟩, 5), (32, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 4)]

theorem g32p_row02_pairing_33 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (16, ⟨-9, -18⟩, 0), (16, ⟨-9, -18⟩, 2), (16, ⟨-3, -6⟩, 0), (48, ⟨-3, -6⟩, 1), (54, ⟨-3, -6⟩, 4), (96, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 2), (96, ⟨-1, -2⟩, 4), (144, ⟨-1, -2⟩, 5), (96, ⟨1, 2⟩, 0), (144, ⟨1, 2⟩, 1), (96, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 4), (16, ⟨3, 6⟩, 0), (54, ⟨3, 6⟩, 2), (48, ⟨3, 6⟩, 5), (16, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 4), (2, ⟨45, 90⟩, 4)]

theorem g32p_row02_pairing_34 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-9, -18⟩, 0), (16, ⟨-9, -18⟩, 2), (16, ⟨-9, -18⟩, 4), (32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 4), (112, ⟨-1, -2⟩, 0), (112, ⟨-1, -2⟩, 2), (112, ⟨-1, -2⟩, 4), (112, ⟨1, 2⟩, 0), (112, ⟨1, 2⟩, 2), (112, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 4), (16, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 2), (16, ⟨9, 18⟩, 4)]

theorem g32p_row02_pairing_35 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (16, ⟨-6, -12⟩, 0), (40, ⟨-3, -6⟩, 2), (40, ⟨-3, -6⟩, 4), (48, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (144, ⟨-1, -2⟩, 2), (144, ⟨-1, -2⟩, 4), (144, ⟨1, 2⟩, 2), (144, ⟨1, 2⟩, 4), (48, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (40, ⟨3, 6⟩, 2), (40, ⟨3, 6⟩, 4), (16, ⟨6, 12⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row02_pairing_36 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (32, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 2), (16, ⟨-6, -12⟩, 4), (32, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (96, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 2), (48, ⟨-1, -2⟩, 4), (96, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 2), (48, ⟨1, 2⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (32, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4), (32, ⟨6, 12⟩, 0), (16, ⟨6, 12⟩, 2), (16, ⟨6, 12⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row02_pairing_37 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (8, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 4), (16, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 2), (32, ⟨-3, -6⟩, 4), (32, ⟨-2, -4⟩, 0), (20, ⟨-2, -4⟩, 2), (20, ⟨-2, -4⟩, 4), (112, ⟨-1, -2⟩, 0), (88, ⟨-1, -2⟩, 2), (88, ⟨-1, -2⟩, 4), (112, ⟨1, 2⟩, 0), (88, ⟨1, 2⟩, 2), (88, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 0), (20, ⟨2, 4⟩, 2), (20, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 4), (8, ⟨6, 12⟩, 2), (8, ⟨6, 12⟩, 4), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row02_pairing_38 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 2), (16, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 4), (24, ⟨-4, -8⟩, 1), (36, ⟨-4, -8⟩, 2), (2, ⟨-4, -8⟩, 4), (24, ⟨-4, -8⟩, 5), (32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 2), (64, ⟨-3, -6⟩, 4), (16, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 4), (32, ⟨-1, -2⟩, 0), (96, ⟨-1, -2⟩, 1), (32, ⟨-1, -2⟩, 2), (192, ⟨-1, -2⟩, 3), (64, ⟨-1, -2⟩, 4), (96, ⟨-1, -2⟩, 5), (32, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 1), (64, ⟨1, 2⟩, 2), (192, ⟨1, 2⟩, 3), (32, ⟨1, 2⟩, 4), (96, ⟨1, 2⟩, 5), (16, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 2), (32, ⟨3, 6⟩, 0), (64, ⟨3, 6⟩, 2), (32, ⟨3, 6⟩, 4), (24, ⟨4, 8⟩, 1), (2, ⟨4, 8⟩, 2), (36, ⟨4, 8⟩, 4), (24, ⟨4, 8⟩, 5), (16, ⟨6, 12⟩, 0), (16, ⟨6, 12⟩, 2), (2, ⟨60, 120⟩, 4)]

theorem g32p_row02_pairing_39 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 2), (16, ⟨-8, -16⟩, 0), (16, ⟨-8, -16⟩, 2), (32, ⟨-4, -8⟩, 0), (32, ⟨-4, -8⟩, 4), (64, ⟨-2, -4⟩, 4), (64, ⟨2, 4⟩, 2), (32, ⟨4, 8⟩, 0), (32, ⟨4, 8⟩, 2), (16, ⟨8, 16⟩, 0), (16, ⟨8, 16⟩, 4), (2, ⟨64, 128⟩, 4)]

theorem g32p_row02_pairing_40 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (16, ⟨-8, -16⟩, 0), (8, ⟨-8, -16⟩, 2), (8, ⟨-8, -16⟩, 4), (32, ⟨-4, -8⟩, 0), (16, ⟨-4, -8⟩, 2), (16, ⟨-4, -8⟩, 4), (32, ⟨-2, -4⟩, 2), (32, ⟨-2, -4⟩, 4), (32, ⟨2, 4⟩, 2), (32, ⟨2, 4⟩, 4), (32, ⟨4, 8⟩, 0), (16, ⟨4, 8⟩, 2), (16, ⟨4, 8⟩, 4), (16, ⟨8, 16⟩, 0), (8, ⟨8, 16⟩, 2), (8, ⟨8, 16⟩, 4), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 4)]

theorem g32p_row02_pairing_41 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (16, ⟨-8, -16⟩, 0), (8, ⟨-8, -16⟩, 2), (8, ⟨-8, -16⟩, 4), (32, ⟨-4, -8⟩, 2), (32, ⟨-4, -8⟩, 4), (32, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 2), (16, ⟨-2, -4⟩, 4), (32, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 2), (16, ⟨2, 4⟩, 4), (32, ⟨4, 8⟩, 2), (32, ⟨4, 8⟩, 4), (16, ⟨8, 16⟩, 0), (8, ⟨8, 16⟩, 2), (8, ⟨8, 16⟩, 4), (1, ⟨80, 160⟩, 2), (1, ⟨80, 160⟩, 4)]

theorem g32p_row02_pairing_42 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 2), (2, ⟨-9, -18⟩, 2), (24, ⟨-9, -18⟩, 5), (24, ⟨-3, -6⟩, 1), (60, ⟨-3, -6⟩, 4), (144, ⟨-1, -2⟩, 1), (144, ⟨1, 2⟩, 5), (60, ⟨3, 6⟩, 2), (24, ⟨3, 6⟩, 5), (24, ⟨9, 18⟩, 1), (2, ⟨9, 18⟩, 4), (2, ⟨81, 162⟩, 4)]

theorem g32p_row02_pairing_43 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_43)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 4), (16, ⟨-7, 0⟩, 0), (16, ⟨-7, 0⟩, 2), (16, ⟨-7, 0⟩, 4), (16, ⟨-3, 0⟩, 0), (16, ⟨-3, 0⟩, 2), (16, ⟨-3, 0⟩, 4), (76, ⟨-2, 0⟩, 0), (76, ⟨-2, 0⟩, 2), (76, ⟨-2, 0⟩, 4), (96, ⟨-1, 0⟩, 0), (96, ⟨-1, 0⟩, 2), (96, ⟨-1, 0⟩, 4), (96, ⟨1, 0⟩, 0), (96, ⟨1, 0⟩, 2), (96, ⟨1, 0⟩, 4), (76, ⟨2, 0⟩, 0), (76, ⟨2, 0⟩, 2), (76, ⟨2, 0⟩, 4), (16, ⟨3, 0⟩, 0), (16, ⟨3, 0⟩, 2), (16, ⟨3, 0⟩, 4), (16, ⟨7, 0⟩, 0), (16, ⟨7, 0⟩, 2), (16, ⟨7, 0⟩, 4), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row02_pairing_44 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 4), (32, ⟨-6, 0⟩, 0), (32, ⟨-6, 0⟩, 2), (32, ⟨-6, 0⟩, 4), (32, ⟨-3, 0⟩, 0), (32, ⟨-3, 0⟩, 2), (32, ⟨-3, 0⟩, 4), (12, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 2), (12, ⟨-2, 0⟩, 4), (96, ⟨-1, 0⟩, 0), (96, ⟨-1, 0⟩, 2), (96, ⟨-1, 0⟩, 4), (96, ⟨1, 0⟩, 0), (96, ⟨1, 0⟩, 2), (96, ⟨1, 0⟩, 4), (12, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 2), (12, ⟨2, 0⟩, 4), (32, ⟨3, 0⟩, 0), (32, ⟨3, 0⟩, 2), (32, ⟨3, 0⟩, 4), (32, ⟨6, 0⟩, 0), (32, ⟨6, 0⟩, 2), (32, ⟨6, 0⟩, 4), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row02_pairing_45 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 4), (16, ⟨-8, 0⟩, 0), (16, ⟨-8, 0⟩, 2), (16, ⟨-8, 0⟩, 4), (32, ⟨-4, 0⟩, 0), (32, ⟨-4, 0⟩, 2), (32, ⟨-4, 0⟩, 4), (32, ⟨-2, 0⟩, 0), (32, ⟨-2, 0⟩, 2), (32, ⟨-2, 0⟩, 4), (32, ⟨2, 0⟩, 0), (32, ⟨2, 0⟩, 2), (32, ⟨2, 0⟩, 4), (32, ⟨4, 0⟩, 0), (32, ⟨4, 0⟩, 2), (32, ⟨4, 0⟩, 4), (16, ⟨8, 0⟩, 0), (16, ⟨8, 0⟩, 2), (16, ⟨8, 0⟩, 4), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row02_pairing_46 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row02_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 4), (16, ⟨-8, 0⟩, 0), (16, ⟨-8, 0⟩, 2), (16, ⟨-8, 0⟩, 4), (32, ⟨-4, 0⟩, 0), (32, ⟨-4, 0⟩, 2), (32, ⟨-4, 0⟩, 4), (32, ⟨-2, 0⟩, 0), (32, ⟨-2, 0⟩, 2), (32, ⟨-2, 0⟩, 4), (32, ⟨2, 0⟩, 0), (32, ⟨2, 0⟩, 2), (32, ⟨2, 0⟩, 4), (32, ⟨4, 0⟩, 0), (32, ⟨4, 0⟩, 2), (32, ⟨4, 0⟩, 4), (16, ⟨8, 0⟩, 0), (16, ⟨8, 0⟩, 2), (16, ⟨8, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row02_pairing_47 :
    g32p_cyclotomicPairingCheck 3456 (0)
      (g32p_pairingCoefficients 6 g32p_row02_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row02_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 2 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨2, -1, [(6, 1), (31, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row03_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(720, ⟨-1, -2⟩, 2), (720, ⟨-1, -2⟩, 5), (720, ⟨1, 2⟩, 1), (720, ⟨1, 2⟩, 4)]

theorem g32p_row03_pairing_0 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_0)
      [1, -1, 1] [0, 720, 0, 720, 0, -1440] = true := by
  decide +kernel

def g32p_row03_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(120, ⟨-2, -4⟩, 1), (120, ⟨-2, -4⟩, 3), (120, ⟨-2, -4⟩, 5), (120, ⟨2, 4⟩, 1), (120, ⟨2, 4⟩, 3), (120, ⟨2, 4⟩, 5)]

theorem g32p_row03_pairing_1 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (40, ⟨-2, -4⟩, 2), (120, ⟨-2, -4⟩, 3), (40, ⟨-2, -4⟩, 4), (120, ⟨-1, -2⟩, 1), (184, ⟨-1, -2⟩, 2), (184, ⟨-1, -2⟩, 4), (120, ⟨-1, -2⟩, 5), (120, ⟨1, 2⟩, 1), (184, ⟨1, 2⟩, 2), (184, ⟨1, 2⟩, 4), (120, ⟨1, 2⟩, 5), (40, ⟨2, 4⟩, 2), (120, ⟨2, 4⟩, 3), (40, ⟨2, 4⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row03_pairing_2 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (40, ⟨-2, -4⟩, 2), (120, ⟨-2, -4⟩, 3), (40, ⟨-2, -4⟩, 4), (120, ⟨-1, -2⟩, 1), (184, ⟨-1, -2⟩, 2), (184, ⟨-1, -2⟩, 4), (120, ⟨-1, -2⟩, 5), (120, ⟨1, 2⟩, 1), (184, ⟨1, 2⟩, 2), (184, ⟨1, 2⟩, 4), (120, ⟨1, 2⟩, 5), (40, ⟨2, 4⟩, 2), (120, ⟨2, 4⟩, 3), (40, ⟨2, 4⟩, 4), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row03_pairing_3 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row03_pairing_4 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (30, ⟨-3, -6⟩, 1), (80, ⟨-2, -4⟩, 2), (180, ⟨-1, -2⟩, 1), (90, ⟨-1, -2⟩, 2), (260, ⟨-1, -2⟩, 4), (270, ⟨-1, -2⟩, 5), (270, ⟨1, 2⟩, 1), (260, ⟨1, 2⟩, 2), (90, ⟨1, 2⟩, 4), (180, ⟨1, 2⟩, 5), (80, ⟨2, 4⟩, 4), (30, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row03_pairing_5 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (30, ⟨-3, -6⟩, 1), (80, ⟨-2, -4⟩, 2), (180, ⟨-1, -2⟩, 1), (90, ⟨-1, -2⟩, 2), (260, ⟨-1, -2⟩, 4), (270, ⟨-1, -2⟩, 5), (270, ⟨1, 2⟩, 1), (260, ⟨1, 2⟩, 2), (90, ⟨1, 2⟩, 4), (180, ⟨1, 2⟩, 5), (80, ⟨2, 4⟩, 4), (30, ⟨3, 6⟩, 5), (2, ⟨5, 10⟩, 4)]

theorem g32p_row03_pairing_6 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 2), (80, ⟨-3, -6⟩, 2), (270, ⟨-2, -4⟩, 1), (90, ⟨-2, -4⟩, 2), (30, ⟨-2, -4⟩, 5), (240, ⟨-1, -2⟩, 1), (288, ⟨-1, -2⟩, 2), (288, ⟨1, 2⟩, 4), (240, ⟨1, 2⟩, 5), (30, ⟨2, 4⟩, 1), (90, ⟨2, 4⟩, 4), (270, ⟨2, 4⟩, 5), (80, ⟨3, 6⟩, 4), (2, ⟨6, 12⟩, 4)]

theorem g32p_row03_pairing_7 :
    g32p_cyclotomicPairingCheck 4320 (1)
      (g32p_pairingCoefficients 6 g32p_row03_terms_7)
      [1, -1, 1] [-4320, -5040, -1440, 2160, 2880, 1440] = true := by
  decide +kernel

def g32p_row03_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row03_pairing_8 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (30, ⟨-2, -4⟩, 1), (90, ⟨-2, -4⟩, 4), (30, ⟨-2, -4⟩, 5), (240, ⟨-1, -2⟩, 1), (160, ⟨-1, -2⟩, 2), (240, ⟨-1, -2⟩, 5), (240, ⟨1, 2⟩, 1), (160, ⟨1, 2⟩, 4), (240, ⟨1, 2⟩, 5), (30, ⟨2, 4⟩, 1), (90, ⟨2, 4⟩, 2), (30, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row03_pairing_9 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (30, ⟨-2, -4⟩, 1), (90, ⟨-2, -4⟩, 4), (30, ⟨-2, -4⟩, 5), (240, ⟨-1, -2⟩, 1), (160, ⟨-1, -2⟩, 2), (240, ⟨-1, -2⟩, 5), (240, ⟨1, 2⟩, 1), (160, ⟨1, 2⟩, 4), (240, ⟨1, 2⟩, 5), (30, ⟨2, 4⟩, 1), (90, ⟨2, 4⟩, 2), (30, ⟨2, 4⟩, 5), (2, ⟨10, 20⟩, 4)]

theorem g32p_row03_pairing_10 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (30, ⟨-7, -14⟩, 5), (170, ⟨-3, -6⟩, 2), (30, ⟨-3, -6⟩, 5), (180, ⟨-1, -2⟩, 2), (420, ⟨-1, -2⟩, 5), (420, ⟨1, 2⟩, 1), (180, ⟨1, 2⟩, 4), (30, ⟨3, 6⟩, 1), (170, ⟨3, 6⟩, 4), (30, ⟨7, 14⟩, 1), (2, ⟨15, 30⟩, 4)]

theorem g32p_row03_pairing_11 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_11)
      [1, -1, 1] [0, 720, 0, 720, 0, -1440] = true := by
  decide +kernel

def g32p_row03_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (80, ⟨-3, -6⟩, 2), (240, ⟨-2, -4⟩, 5), (480, ⟨-1, -2⟩, 1), (270, ⟨-1, -2⟩, 4), (270, ⟨1, 2⟩, 2), (480, ⟨1, 2⟩, 5), (240, ⟨2, 4⟩, 1), (80, ⟨3, 6⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row03_pairing_12 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row03_pairing_13 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(120, ⟨-2, -4⟩, 1), (120, ⟨-2, -4⟩, 3), (120, ⟨-2, -4⟩, 5), (120, ⟨2, 4⟩, 1), (120, ⟨2, 4⟩, 3), (120, ⟨2, 4⟩, 5)]

theorem g32p_row03_pairing_14 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (80, ⟨-2, -4⟩, 2), (80, ⟨-2, -4⟩, 4), (80, ⟨2, 4⟩, 2), (80, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row03_pairing_15 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (40, ⟨-4, -8⟩, 2), (40, ⟨-4, -8⟩, 4), (120, ⟨-2, -4⟩, 3), (120, ⟨-1, -2⟩, 1), (40, ⟨-1, -2⟩, 2), (40, ⟨-1, -2⟩, 4), (120, ⟨-1, -2⟩, 5), (120, ⟨1, 2⟩, 1), (40, ⟨1, 2⟩, 2), (40, ⟨1, 2⟩, 4), (120, ⟨1, 2⟩, 5), (120, ⟨2, 4⟩, 3), (40, ⟨4, 8⟩, 2), (40, ⟨4, 8⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row03_pairing_16 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (80, ⟨-2, -4⟩, 2), (80, ⟨-2, -4⟩, 4), (80, ⟨2, 4⟩, 2), (80, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row03_pairing_17 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (40, ⟨-4, -8⟩, 2), (40, ⟨-4, -8⟩, 4), (120, ⟨-2, -4⟩, 3), (120, ⟨-1, -2⟩, 1), (40, ⟨-1, -2⟩, 2), (40, ⟨-1, -2⟩, 4), (120, ⟨-1, -2⟩, 5), (120, ⟨1, 2⟩, 1), (40, ⟨1, 2⟩, 2), (40, ⟨1, 2⟩, 4), (120, ⟨1, 2⟩, 5), (120, ⟨2, 4⟩, 3), (40, ⟨4, 8⟩, 2), (40, ⟨4, 8⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row03_pairing_18 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (80, ⟨-2, -4⟩, 2), (80, ⟨-2, -4⟩, 4), (80, ⟨2, 4⟩, 2), (80, ⟨2, 4⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row03_pairing_19 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 2), (80, ⟨-5, -10⟩, 2), (90, ⟨-4, -8⟩, 2), (60, ⟨-4, -8⟩, 5), (80, ⟨-1, -2⟩, 4), (480, ⟨-1, -2⟩, 5), (480, ⟨1, 2⟩, 1), (80, ⟨1, 2⟩, 2), (60, ⟨4, 8⟩, 1), (90, ⟨4, 8⟩, 4), (80, ⟨5, 10⟩, 4), (2, ⟨20, 40⟩, 4)]

theorem g32p_row03_pairing_20 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_20)
      [1, -1, 1] [0, 720, 0, 720, 0, -1440] = true := by
  decide +kernel

def g32p_row03_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 2), (30, ⟨-8, -16⟩, 5), (80, ⟨-3, -6⟩, 2), (240, ⟨-1, -2⟩, 1), (288, ⟨-1, -2⟩, 4), (288, ⟨1, 2⟩, 2), (240, ⟨1, 2⟩, 5), (80, ⟨3, 6⟩, 4), (30, ⟨8, 16⟩, 1), (2, ⟨24, 48⟩, 4)]

theorem g32p_row03_pairing_21 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row03_pairing_22 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (30, ⟨-6, -12⟩, 5), (80, ⟨-3, -6⟩, 4), (90, ⟨-2, -4⟩, 2), (30, ⟨-2, -4⟩, 5), (240, ⟨-1, -2⟩, 1), (240, ⟨1, 2⟩, 5), (30, ⟨2, 4⟩, 1), (90, ⟨2, 4⟩, 4), (80, ⟨3, 6⟩, 2), (30, ⟨6, 12⟩, 1), (2, ⟨30, 60⟩, 4)]

theorem g32p_row03_pairing_23 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_23)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (30, ⟨-6, -12⟩, 5), (80, ⟨-3, -6⟩, 4), (90, ⟨-2, -4⟩, 2), (30, ⟨-2, -4⟩, 5), (240, ⟨-1, -2⟩, 1), (240, ⟨1, 2⟩, 5), (30, ⟨2, 4⟩, 1), (90, ⟨2, 4⟩, 4), (80, ⟨3, 6⟩, 2), (30, ⟨6, 12⟩, 1), (2, ⟨30, 60⟩, 4)]

theorem g32p_row03_pairing_24 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_24)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (30, ⟨-10, -20⟩, 1), (160, ⟨-3, -6⟩, 2), (90, ⟨-2, -4⟩, 2), (30, ⟨-2, -4⟩, 5), (480, ⟨-1, -2⟩, 1), (480, ⟨1, 2⟩, 5), (30, ⟨2, 4⟩, 1), (90, ⟨2, 4⟩, 4), (160, ⟨3, 6⟩, 4), (30, ⟨10, 20⟩, 5), (2, ⟨30, 60⟩, 4)]

theorem g32p_row03_pairing_25 :
    g32p_cyclotomicPairingCheck 4320 (1)
      (g32p_pairingCoefficients 6 g32p_row03_terms_25)
      [1, -1, 1] [-4320, -5040, -1440, 2160, 2880, 1440] = true := by
  decide +kernel

def g32p_row03_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row03_pairing_26 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (144, ⟨-1, -2⟩, 2), (144, ⟨-1, -2⟩, 4), (144, ⟨1, 2⟩, 2), (144, ⟨1, 2⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row03_pairing_27 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (144, ⟨-1, -2⟩, 2), (144, ⟨-1, -2⟩, 4), (144, ⟨1, 2⟩, 2), (144, ⟨1, 2⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row03_pairing_28 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row03_pairing_29 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (30, ⟨-8, -16⟩, 1), (80, ⟨-2, -4⟩, 4), (80, ⟨-1, -2⟩, 2), (240, ⟨-1, -2⟩, 5), (240, ⟨1, 2⟩, 1), (80, ⟨1, 2⟩, 4), (80, ⟨2, 4⟩, 2), (30, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row03_pairing_30 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (30, ⟨-8, -16⟩, 1), (80, ⟨-2, -4⟩, 4), (80, ⟨-1, -2⟩, 2), (240, ⟨-1, -2⟩, 5), (240, ⟨1, 2⟩, 1), (80, ⟨1, 2⟩, 4), (80, ⟨2, 4⟩, 2), (30, ⟨8, 16⟩, 5), (2, ⟨40, 80⟩, 4)]

theorem g32p_row03_pairing_31 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row03_pairing_32 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (60, ⟨-3, -6⟩, 1), (90, ⟨-3, -6⟩, 4), (180, ⟨-1, -2⟩, 2), (180, ⟨-1, -2⟩, 5), (180, ⟨1, 2⟩, 1), (180, ⟨1, 2⟩, 4), (90, ⟨3, 6⟩, 2), (60, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row03_pairing_33 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (60, ⟨-3, -6⟩, 1), (90, ⟨-3, -6⟩, 4), (180, ⟨-1, -2⟩, 2), (180, ⟨-1, -2⟩, 5), (180, ⟨1, 2⟩, 1), (180, ⟨1, 2⟩, 4), (90, ⟨3, 6⟩, 2), (60, ⟨3, 6⟩, 5), (2, ⟨45, 90⟩, 4)]

theorem g32p_row03_pairing_34 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(120, ⟨-2, -4⟩, 1), (120, ⟨-2, -4⟩, 3), (120, ⟨-2, -4⟩, 5), (120, ⟨2, 4⟩, 1), (120, ⟨2, 4⟩, 3), (120, ⟨2, 4⟩, 5)]

theorem g32p_row03_pairing_35 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (40, ⟨-3, -6⟩, 2), (40, ⟨-3, -6⟩, 4), (120, ⟨-2, -4⟩, 3), (120, ⟨-1, -2⟩, 1), (120, ⟨-1, -2⟩, 5), (120, ⟨1, 2⟩, 1), (120, ⟨1, 2⟩, 5), (120, ⟨2, 4⟩, 3), (40, ⟨3, 6⟩, 2), (40, ⟨3, 6⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row03_pairing_36 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (40, ⟨-6, -12⟩, 2), (40, ⟨-6, -12⟩, 4), (40, ⟨6, 12⟩, 2), (40, ⟨6, 12⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row03_pairing_37 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (40, ⟨-3, -6⟩, 2), (40, ⟨-3, -6⟩, 4), (120, ⟨-2, -4⟩, 3), (120, ⟨-1, -2⟩, 1), (120, ⟨-1, -2⟩, 5), (120, ⟨1, 2⟩, 1), (120, ⟨1, 2⟩, 5), (120, ⟨2, 4⟩, 3), (40, ⟨3, 6⟩, 2), (40, ⟨3, 6⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row03_pairing_38 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 2), (30, ⟨-4, -8⟩, 1), (90, ⟨-4, -8⟩, 2), (30, ⟨-4, -8⟩, 5), (160, ⟨-3, -6⟩, 4), (240, ⟨-1, -2⟩, 1), (240, ⟨-1, -2⟩, 5), (240, ⟨1, 2⟩, 1), (240, ⟨1, 2⟩, 5), (160, ⟨3, 6⟩, 2), (30, ⟨4, 8⟩, 1), (90, ⟨4, 8⟩, 4), (30, ⟨4, 8⟩, 5), (2, ⟨60, 120⟩, 4)]

theorem g32p_row03_pairing_39 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 2), (80, ⟨-4, -8⟩, 2), (80, ⟨-2, -4⟩, 4), (288, ⟨-1, -2⟩, 4), (288, ⟨1, 2⟩, 2), (80, ⟨2, 4⟩, 2), (80, ⟨4, 8⟩, 4), (2, ⟨64, 128⟩, 4)]

theorem g32p_row03_pairing_40 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (40, ⟨-4, -8⟩, 2), (40, ⟨-4, -8⟩, 4), (40, ⟨-2, -4⟩, 2), (40, ⟨-2, -4⟩, 4), (144, ⟨-1, -2⟩, 2), (144, ⟨-1, -2⟩, 4), (144, ⟨1, 2⟩, 2), (144, ⟨1, 2⟩, 4), (40, ⟨2, 4⟩, 2), (40, ⟨2, 4⟩, 4), (40, ⟨4, 8⟩, 2), (40, ⟨4, 8⟩, 4), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 4)]

theorem g32p_row03_pairing_41 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (40, ⟨-4, -8⟩, 2), (40, ⟨-4, -8⟩, 4), (40, ⟨-2, -4⟩, 2), (40, ⟨-2, -4⟩, 4), (40, ⟨2, 4⟩, 2), (40, ⟨2, 4⟩, 4), (40, ⟨4, 8⟩, 2), (40, ⟨4, 8⟩, 4), (1, ⟨80, 160⟩, 2), (1, ⟨80, 160⟩, 4)]

theorem g32p_row03_pairing_42 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 2), (30, ⟨-9, -18⟩, 5), (30, ⟨-3, -6⟩, 1), (90, ⟨-3, -6⟩, 4), (180, ⟨-1, -2⟩, 1), (288, ⟨-1, -2⟩, 2), (180, ⟨-1, -2⟩, 4), (180, ⟨1, 2⟩, 2), (288, ⟨1, 2⟩, 4), (180, ⟨1, 2⟩, 5), (90, ⟨3, 6⟩, 2), (30, ⟨3, 6⟩, 5), (30, ⟨9, 18⟩, 1), (2, ⟨81, 162⟩, 4)]

theorem g32p_row03_pairing_43 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_43)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 4), (80, ⟨-2, 0⟩, 0), (80, ⟨-2, 0⟩, 2), (80, ⟨-2, 0⟩, 4), (80, ⟨2, 0⟩, 0), (80, ⟨2, 0⟩, 2), (80, ⟨2, 0⟩, 4), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row03_pairing_44 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 4), (40, ⟨-6, 0⟩, 0), (40, ⟨-6, 0⟩, 2), (40, ⟨-6, 0⟩, 4), (40, ⟨6, 0⟩, 0), (40, ⟨6, 0⟩, 2), (40, ⟨6, 0⟩, 4), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row03_pairing_45 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 4), (40, ⟨-4, 0⟩, 0), (40, ⟨-4, 0⟩, 2), (40, ⟨-4, 0⟩, 4), (40, ⟨-2, 0⟩, 0), (40, ⟨-2, 0⟩, 2), (40, ⟨-2, 0⟩, 4), (144, ⟨-1, 0⟩, 0), (144, ⟨-1, 0⟩, 2), (144, ⟨-1, 0⟩, 4), (144, ⟨1, 0⟩, 0), (144, ⟨1, 0⟩, 2), (144, ⟨1, 0⟩, 4), (40, ⟨2, 0⟩, 0), (40, ⟨2, 0⟩, 2), (40, ⟨2, 0⟩, 4), (40, ⟨4, 0⟩, 0), (40, ⟨4, 0⟩, 2), (40, ⟨4, 0⟩, 4), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row03_pairing_46 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row03_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 4), (40, ⟨-4, 0⟩, 0), (40, ⟨-4, 0⟩, 2), (40, ⟨-4, 0⟩, 4), (40, ⟨-2, 0⟩, 0), (40, ⟨-2, 0⟩, 2), (40, ⟨-2, 0⟩, 4), (40, ⟨2, 0⟩, 0), (40, ⟨2, 0⟩, 2), (40, ⟨2, 0⟩, 4), (40, ⟨4, 0⟩, 0), (40, ⟨4, 0⟩, 2), (40, ⟨4, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row03_pairing_47 :
    g32p_cyclotomicPairingCheck 4320 (0)
      (g32p_pairingCoefficients 6 g32p_row03_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row03_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 3 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨3, 1, [(8, 1), (26, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row04_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(192, ⟨-1, -2⟩, 0), (192, ⟨-1, -2⟩, 1), (192, ⟨-1, -2⟩, 2), (192, ⟨1, 2⟩, 0), (192, ⟨1, 2⟩, 1), (192, ⟨1, 2⟩, 2)]

theorem g32p_row04_pairing_0 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (112, ⟨-1, -2⟩, 0), (112, ⟨-1, -2⟩, 1), (112, ⟨-1, -2⟩, 2), (112, ⟨1, 2⟩, 0), (112, ⟨1, 2⟩, 1), (112, ⟨1, 2⟩, 2), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2)]

theorem g32p_row04_pairing_1 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (32, ⟨-2, -4⟩, 0), (60, ⟨-2, -4⟩, 1), (60, ⟨-2, -4⟩, 2), (184, ⟨-1, -2⟩, 0), (92, ⟨-1, -2⟩, 1), (92, ⟨-1, -2⟩, 2), (184, ⟨1, 2⟩, 0), (92, ⟨1, 2⟩, 1), (92, ⟨1, 2⟩, 2), (32, ⟨2, 4⟩, 0), (60, ⟨2, 4⟩, 1), (60, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row04_pairing_2 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (8, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (48, ⟨-2, -4⟩, 0), (52, ⟨-2, -4⟩, 1), (52, ⟨-2, -4⟩, 2), (120, ⟨-1, -2⟩, 0), (124, ⟨-1, -2⟩, 1), (124, ⟨-1, -2⟩, 2), (120, ⟨1, 2⟩, 0), (124, ⟨1, 2⟩, 1), (124, ⟨1, 2⟩, 2), (48, ⟨2, 4⟩, 0), (52, ⟨2, 4⟩, 1), (52, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row04_pairing_3 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (112, ⟨-1, -2⟩, 0), (112, ⟨-1, -2⟩, 1), (112, ⟨-1, -2⟩, 2), (112, ⟨1, 2⟩, 0), (112, ⟨1, 2⟩, 1), (112, ⟨1, 2⟩, 2), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2)]

theorem g32p_row04_pairing_4 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (48, ⟨-2, -4⟩, 0), (8, ⟨-2, -4⟩, 1), (72, ⟨-2, -4⟩, 2), (120, ⟨-1, -2⟩, 0), (204, ⟨-1, -2⟩, 1), (104, ⟨-1, -2⟩, 2), (120, ⟨1, 2⟩, 0), (104, ⟨1, 2⟩, 1), (204, ⟨1, 2⟩, 2), (48, ⟨2, 4⟩, 0), (72, ⟨2, 4⟩, 1), (8, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (2, ⟨5, 10⟩, 2)]

theorem g32p_row04_pairing_5 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (8, ⟨-3, -6⟩, 0), (10, ⟨-3, -6⟩, 2), (32, ⟨-2, -4⟩, 0), (48, ⟨-2, -4⟩, 1), (48, ⟨-2, -4⟩, 2), (184, ⟨-1, -2⟩, 0), (132, ⟨-1, -2⟩, 1), (112, ⟨-1, -2⟩, 2), (184, ⟨1, 2⟩, 0), (112, ⟨1, 2⟩, 1), (132, ⟨1, 2⟩, 2), (32, ⟨2, 4⟩, 0), (48, ⟨2, 4⟩, 1), (48, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (10, ⟨3, 6⟩, 1), (2, ⟨5, 10⟩, 2)]

theorem g32p_row04_pairing_6 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (40, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (48, ⟨-3, -6⟩, 2), (32, ⟨-2, -4⟩, 0), (92, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (88, ⟨-1, -2⟩, 0), (64, ⟨-1, -2⟩, 1), (136, ⟨-1, -2⟩, 2), (88, ⟨1, 2⟩, 0), (136, ⟨1, 2⟩, 1), (64, ⟨1, 2⟩, 2), (32, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (92, ⟨2, 4⟩, 2), (40, ⟨3, 6⟩, 0), (48, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row04_pairing_7 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 1), (32, ⟨-3, -6⟩, 2), (96, ⟨-1, -2⟩, 0), (96, ⟨-1, -2⟩, 1), (96, ⟨-1, -2⟩, 2), (96, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 1), (96, ⟨1, 2⟩, 2), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 1), (32, ⟨3, 6⟩, 2)]

theorem g32p_row04_pairing_8 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (8, ⟨-5, -10⟩, 0), (8, ⟨-5, -10⟩, 2), (16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 2), (42, ⟨-2, -4⟩, 1), (52, ⟨-2, -4⟩, 2), (232, ⟨-1, -2⟩, 0), (160, ⟨-1, -2⟩, 1), (72, ⟨-1, -2⟩, 2), (232, ⟨1, 2⟩, 0), (72, ⟨1, 2⟩, 1), (160, ⟨1, 2⟩, 2), (52, ⟨2, 4⟩, 1), (42, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 1), (8, ⟨5, 10⟩, 0), (8, ⟨5, 10⟩, 1), (2, ⟨10, 20⟩, 2)]

theorem g32p_row04_pairing_9 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (8, ⟨-5, -10⟩, 1), (8, ⟨-5, -10⟩, 2), (16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (16, ⟨-2, -4⟩, 0), (34, ⟨-2, -4⟩, 1), (44, ⟨-2, -4⟩, 2), (176, ⟨-1, -2⟩, 0), (120, ⟨-1, -2⟩, 1), (168, ⟨-1, -2⟩, 2), (176, ⟨1, 2⟩, 0), (168, ⟨1, 2⟩, 1), (120, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (44, ⟨2, 4⟩, 1), (34, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 2), (8, ⟨5, 10⟩, 1), (8, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 2)]

theorem g32p_row04_pairing_10 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (2, ⟨-7, -14⟩, 1), (40, ⟨-3, -6⟩, 0), (44, ⟨-3, -6⟩, 1), (48, ⟨-3, -6⟩, 2), (32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 1), (88, ⟨-1, -2⟩, 0), (64, ⟨-1, -2⟩, 1), (160, ⟨-1, -2⟩, 2), (88, ⟨1, 2⟩, 0), (160, ⟨1, 2⟩, 1), (64, ⟨1, 2⟩, 2), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 2), (40, ⟨3, 6⟩, 0), (48, ⟨3, 6⟩, 1), (44, ⟨3, 6⟩, 2), (2, ⟨7, 14⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row04_pairing_11 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_11)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (8, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (32, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 1), (32, ⟨-3, -6⟩, 2), (40, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (40, ⟨-2, -4⟩, 2), (32, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (38, ⟨-1, -2⟩, 2), (32, ⟨1, 2⟩, 0), (38, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (40, ⟨2, 4⟩, 0), (40, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 1), (24, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (16, ⟨6, 12⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row04_pairing_12 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 1), (32, ⟨-3, -6⟩, 2), (96, ⟨-1, -2⟩, 0), (96, ⟨-1, -2⟩, 1), (96, ⟨-1, -2⟩, 2), (96, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 1), (96, ⟨1, 2⟩, 2), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 1), (32, ⟨3, 6⟩, 2)]

theorem g32p_row04_pairing_13 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 1), (16, ⟨-6, -12⟩, 2), (48, ⟨-2, -4⟩, 0), (48, ⟨-2, -4⟩, 1), (48, ⟨-2, -4⟩, 2), (48, ⟨2, 4⟩, 0), (48, ⟨2, 4⟩, 1), (48, ⟨2, 4⟩, 2), (16, ⟨6, 12⟩, 0), (16, ⟨6, 12⟩, 1), (16, ⟨6, 12⟩, 2)]

theorem g32p_row04_pairing_14 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-7, -14⟩, 0), (12, ⟨-7, -14⟩, 1), (12, ⟨-7, -14⟩, 2), (8, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (64, ⟨-2, -4⟩, 0), (44, ⟨-2, -4⟩, 1), (44, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 0), (72, ⟨-1, -2⟩, 1), (72, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 2), (64, ⟨2, 4⟩, 0), (44, ⟨2, 4⟩, 1), (44, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (8, ⟨7, 14⟩, 0), (12, ⟨7, 14⟩, 1), (12, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row04_pairing_15 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (8, ⟨-5, -10⟩, 1), (8, ⟨-5, -10⟩, 2), (32, ⟨-4, -8⟩, 0), (16, ⟨-4, -8⟩, 1), (16, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (128, ⟨-1, -2⟩, 0), (120, ⟨-1, -2⟩, 1), (120, ⟨-1, -2⟩, 2), (128, ⟨1, 2⟩, 0), (120, ⟨1, 2⟩, 1), (120, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (32, ⟨4, 8⟩, 0), (16, ⟨4, 8⟩, 1), (16, ⟨4, 8⟩, 2), (8, ⟨5, 10⟩, 1), (8, ⟨5, 10⟩, 2), (8, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row04_pairing_16 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-8, -16⟩, 0), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (8, ⟨-5, -10⟩, 1), (8, ⟨-5, -10⟩, 2), (16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (64, ⟨-2, -4⟩, 0), (44, ⟨-2, -4⟩, 1), (44, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 0), (72, ⟨-1, -2⟩, 1), (72, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 2), (64, ⟨2, 4⟩, 0), (44, ⟨2, 4⟩, 1), (44, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (8, ⟨5, 10⟩, 1), (8, ⟨5, 10⟩, 2), (8, ⟨8, 16⟩, 0), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row04_pairing_17 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (8, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (32, ⟨-4, -8⟩, 0), (16, ⟨-4, -8⟩, 1), (16, ⟨-4, -8⟩, 2), (8, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (120, ⟨-1, -2⟩, 0), (124, ⟨-1, -2⟩, 1), (124, ⟨-1, -2⟩, 2), (120, ⟨1, 2⟩, 0), (124, ⟨1, 2⟩, 1), (124, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (32, ⟨4, 8⟩, 0), (16, ⟨4, 8⟩, 1), (16, ⟨4, 8⟩, 2), (8, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (8, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row04_pairing_18 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-8, -16⟩, 1), (8, ⟨-8, -16⟩, 2), (8, ⟨-5, -10⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (24, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (64, ⟨-2, -4⟩, 0), (44, ⟨-2, -4⟩, 1), (44, ⟨-2, -4⟩, 2), (96, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (96, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (64, ⟨2, 4⟩, 0), (44, ⟨2, 4⟩, 1), (44, ⟨2, 4⟩, 2), (24, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (8, ⟨5, 10⟩, 0), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (8, ⟨8, 16⟩, 1), (8, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row04_pairing_19 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 1), (32, ⟨-5, -10⟩, 0), (32, ⟨-5, -10⟩, 2), (38, ⟨-4, -8⟩, 1), (16, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (96, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (64, ⟨-1, -2⟩, 2), (96, ⟨1, 2⟩, 0), (64, ⟨1, 2⟩, 1), (32, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (38, ⟨4, 8⟩, 2), (32, ⟨5, 10⟩, 0), (32, ⟨5, 10⟩, 1), (2, ⟨20, 40⟩, 2)]

theorem g32p_row04_pairing_20 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_20)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 1), (2, ⟨-8, -16⟩, 1), (8, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (32, ⟨-3, -6⟩, 0), (32, ⟨-3, -6⟩, 2), (40, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (40, ⟨-2, -4⟩, 2), (32, ⟨-1, -2⟩, 0), (32, ⟨-1, -2⟩, 1), (32, ⟨1, 2⟩, 0), (32, ⟨1, 2⟩, 2), (40, ⟨2, 4⟩, 0), (40, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (32, ⟨3, 6⟩, 0), (32, ⟨3, 6⟩, 1), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (16, ⟨6, 12⟩, 2), (2, ⟨8, 16⟩, 2), (2, ⟨24, 48⟩, 2)]

theorem g32p_row04_pairing_21 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_21)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-9, -18⟩, 0), (16, ⟨-9, -18⟩, 1), (16, ⟨-9, -18⟩, 2), (32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (112, ⟨-1, -2⟩, 0), (112, ⟨-1, -2⟩, 1), (112, ⟨-1, -2⟩, 2), (112, ⟨1, 2⟩, 0), (112, ⟨1, 2⟩, 1), (112, ⟨1, 2⟩, 2), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (16, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 1), (16, ⟨9, 18⟩, 2)]

theorem g32p_row04_pairing_22 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_22)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-6, -12⟩, 0), (2, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (32, ⟨-3, -6⟩, 0), (40, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (60, ⟨-2, -4⟩, 1), (40, ⟨-2, -4⟩, 2), (88, ⟨-1, -2⟩, 0), (56, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (88, ⟨1, 2⟩, 0), (144, ⟨1, 2⟩, 1), (56, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (40, ⟨2, 4⟩, 1), (60, ⟨2, 4⟩, 2), (32, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (40, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (2, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row04_pairing_23 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_23)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (10, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (40, ⟨-3, -6⟩, 0), (40, ⟨-3, -6⟩, 1), (100, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 0), (136, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (8, ⟨1, 2⟩, 1), (136, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 1), (100, ⟨2, 4⟩, 2), (40, ⟨3, 6⟩, 0), (40, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 1), (10, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row04_pairing_24 :
    g32p_cyclotomicPairingCheck 1728 (1)
      (g32p_pairingCoefficients 3 g32p_row04_terms_24)
      [1, 1, 1] [-1728, 1152] = true := by
  decide +kernel

def g32p_row04_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (2, ⟨-10, -20⟩, 2), (72, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (72, ⟨-3, -6⟩, 2), (36, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (120, ⟨-1, -2⟩, 0), (168, ⟨-1, -2⟩, 1), (64, ⟨-1, -2⟩, 2), (120, ⟨1, 2⟩, 0), (64, ⟨1, 2⟩, 1), (168, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (72, ⟨3, 6⟩, 0), (72, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (2, ⟨10, 20⟩, 1), (2, ⟨30, 60⟩, 2)]

theorem g32p_row04_pairing_25 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-9, -18⟩, 0), (16, ⟨-9, -18⟩, 1), (16, ⟨-9, -18⟩, 2), (16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (96, ⟨-1, -2⟩, 0), (96, ⟨-1, -2⟩, 1), (96, ⟨-1, -2⟩, 2), (96, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 1), (96, ⟨1, 2⟩, 2), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (16, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 1), (16, ⟨9, 18⟩, 2)]

theorem g32p_row04_pairing_26 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (8, ⟨-9, -18⟩, 0), (12, ⟨-9, -18⟩, 1), (12, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 0), (72, ⟨-1, -2⟩, 1), (72, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (12, ⟨9, 18⟩, 1), (12, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row04_pairing_27 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (16, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (16, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (96, ⟨-1, -2⟩, 0), (48, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (96, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (48, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (16, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row04_pairing_28 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 1), (16, ⟨-6, -12⟩, 2), (48, ⟨-2, -4⟩, 0), (48, ⟨-2, -4⟩, 1), (48, ⟨-2, -4⟩, 2), (48, ⟨2, 4⟩, 0), (48, ⟨2, 4⟩, 1), (48, ⟨2, 4⟩, 2), (16, ⟨6, 12⟩, 0), (16, ⟨6, 12⟩, 1), (16, ⟨6, 12⟩, 2)]

theorem g32p_row04_pairing_29 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (8, ⟨-8, -16⟩, 1), (10, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (56, ⟨-2, -4⟩, 0), (48, ⟨-2, -4⟩, 1), (72, ⟨-2, -4⟩, 2), (64, ⟨-1, -2⟩, 0), (64, ⟨-1, -2⟩, 2), (64, ⟨1, 2⟩, 0), (64, ⟨1, 2⟩, 1), (56, ⟨2, 4⟩, 0), (72, ⟨2, 4⟩, 1), (48, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 2), (10, ⟨8, 16⟩, 1), (8, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 2)]

theorem g32p_row04_pairing_30 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (8, ⟨-8, -16⟩, 0), (10, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 2), (72, ⟨-2, -4⟩, 0), (80, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (64, ⟨-1, -2⟩, 0), (64, ⟨-1, -2⟩, 2), (64, ⟨1, 2⟩, 0), (64, ⟨1, 2⟩, 1), (72, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (80, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨8, 16⟩, 0), (10, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 2)]

theorem g32p_row04_pairing_31 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-9, -18⟩, 0), (16, ⟨-9, -18⟩, 1), (16, ⟨-9, -18⟩, 2), (16, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (96, ⟨-1, -2⟩, 0), (96, ⟨-1, -2⟩, 1), (96, ⟨-1, -2⟩, 2), (96, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 1), (96, ⟨1, 2⟩, 2), (16, ⟨3, 6⟩, 0), (16, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (16, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 1), (16, ⟨9, 18⟩, 2)]

theorem g32p_row04_pairing_32 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (16, ⟨-9, -18⟩, 2), (8, ⟨-3, -6⟩, 0), (16, ⟨-3, -6⟩, 1), (46, ⟨-3, -6⟩, 2), (48, ⟨-1, -2⟩, 0), (120, ⟨-1, -2⟩, 1), (48, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (48, ⟨1, 2⟩, 1), (120, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (46, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (8, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row04_pairing_33 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (16, ⟨-9, -18⟩, 0), (16, ⟨-9, -18⟩, 1), (16, ⟨-3, -6⟩, 0), (54, ⟨-3, -6⟩, 2), (96, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (96, ⟨-1, -2⟩, 2), (96, ⟨1, 2⟩, 0), (96, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (16, ⟨3, 6⟩, 0), (54, ⟨3, 6⟩, 1), (16, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row04_pairing_34 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(16, ⟨-9, -18⟩, 0), (16, ⟨-9, -18⟩, 1), (16, ⟨-9, -18⟩, 2), (32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (112, ⟨-1, -2⟩, 0), (112, ⟨-1, -2⟩, 1), (112, ⟨-1, -2⟩, 2), (112, ⟨1, 2⟩, 0), (112, ⟨1, 2⟩, 1), (112, ⟨1, 2⟩, 2), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (16, ⟨9, 18⟩, 0), (16, ⟨9, 18⟩, 1), (16, ⟨9, 18⟩, 2)]

theorem g32p_row04_pairing_35 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (32, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 1), (24, ⟨-3, -6⟩, 2), (8, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 1), (32, ⟨-2, -4⟩, 2), (88, ⟨-1, -2⟩, 0), (100, ⟨-1, -2⟩, 1), (100, ⟨-1, -2⟩, 2), (88, ⟨1, 2⟩, 0), (100, ⟨1, 2⟩, 1), (100, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 1), (32, ⟨2, 4⟩, 2), (32, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (24, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row04_pairing_36 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (32, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 1), (16, ⟨-6, -12⟩, 2), (16, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 1), (24, ⟨-3, -6⟩, 2), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (48, ⟨-1, -2⟩, 0), (72, ⟨-1, -2⟩, 1), (72, ⟨-1, -2⟩, 2), (48, ⟨1, 2⟩, 0), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 2), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (24, ⟨3, 6⟩, 2), (32, ⟨6, 12⟩, 0), (16, ⟨6, 12⟩, 1), (16, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row04_pairing_37 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (40, ⟨-3, -6⟩, 0), (20, ⟨-3, -6⟩, 1), (20, ⟨-3, -6⟩, 2), (36, ⟨-2, -4⟩, 1), (36, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 0), (72, ⟨-1, -2⟩, 1), (72, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 2), (36, ⟨2, 4⟩, 1), (36, ⟨2, 4⟩, 2), (40, ⟨3, 6⟩, 0), (20, ⟨3, 6⟩, 1), (20, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row04_pairing_38 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 1), (8, ⟨-6, -12⟩, 0), (16, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (36, ⟨-4, -8⟩, 1), (2, ⟨-4, -8⟩, 2), (64, ⟨-3, -6⟩, 0), (64, ⟨-3, -6⟩, 1), (8, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (8, ⟨-2, -4⟩, 2), (64, ⟨-1, -2⟩, 0), (64, ⟨-1, -2⟩, 1), (64, ⟨1, 2⟩, 0), (64, ⟨1, 2⟩, 2), (8, ⟨2, 4⟩, 0), (8, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (64, ⟨3, 6⟩, 0), (64, ⟨3, 6⟩, 2), (2, ⟨4, 8⟩, 1), (36, ⟨4, 8⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (16, ⟨6, 12⟩, 2), (2, ⟨60, 120⟩, 2)]

theorem g32p_row04_pairing_39 :
    g32p_cyclotomicPairingCheck 1728 (1)
      (g32p_pairingCoefficients 3 g32p_row04_terms_39)
      [1, 1, 1] [-1728, 1152] = true := by
  decide +kernel

def g32p_row04_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 1), (8, ⟨-8, -16⟩, 0), (8, ⟨-8, -16⟩, 1), (16, ⟨-8, -16⟩, 2), (32, ⟨-4, -8⟩, 0), (32, ⟨-4, -8⟩, 2), (32, ⟨-2, -4⟩, 0), (32, ⟨-2, -4⟩, 1), (32, ⟨2, 4⟩, 0), (32, ⟨2, 4⟩, 2), (32, ⟨4, 8⟩, 0), (32, ⟨4, 8⟩, 1), (8, ⟨8, 16⟩, 0), (16, ⟨8, 16⟩, 1), (8, ⟨8, 16⟩, 2), (2, ⟨64, 128⟩, 2)]

theorem g32p_row04_pairing_40 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_40)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (8, ⟨-8, -16⟩, 0), (12, ⟨-8, -16⟩, 1), (12, ⟨-8, -16⟩, 2), (32, ⟨-4, -8⟩, 0), (16, ⟨-4, -8⟩, 1), (16, ⟨-4, -8⟩, 2), (32, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 2), (32, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (32, ⟨4, 8⟩, 0), (16, ⟨4, 8⟩, 1), (16, ⟨4, 8⟩, 2), (8, ⟨8, 16⟩, 0), (12, ⟨8, 16⟩, 1), (12, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 2)]

theorem g32p_row04_pairing_41 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (8, ⟨-8, -16⟩, 0), (12, ⟨-8, -16⟩, 1), (12, ⟨-8, -16⟩, 2), (32, ⟨-4, -8⟩, 0), (16, ⟨-4, -8⟩, 1), (16, ⟨-4, -8⟩, 2), (32, ⟨-2, -4⟩, 0), (16, ⟨-2, -4⟩, 1), (16, ⟨-2, -4⟩, 2), (32, ⟨2, 4⟩, 0), (16, ⟨2, 4⟩, 1), (16, ⟨2, 4⟩, 2), (32, ⟨4, 8⟩, 0), (16, ⟨4, 8⟩, 1), (16, ⟨4, 8⟩, 2), (8, ⟨8, 16⟩, 0), (12, ⟨8, 16⟩, 1), (12, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 1), (1, ⟨80, 160⟩, 2)]

theorem g32p_row04_pairing_42 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 1), (2, ⟨-9, -18⟩, 1), (60, ⟨-3, -6⟩, 2), (60, ⟨3, 6⟩, 1), (2, ⟨9, 18⟩, 2), (2, ⟨81, 162⟩, 2)]

theorem g32p_row04_pairing_43 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_43)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 2), (16, ⟨-7, 0⟩, 0), (16, ⟨-7, 0⟩, 1), (16, ⟨-7, 0⟩, 2), (16, ⟨-3, 0⟩, 0), (16, ⟨-3, 0⟩, 1), (16, ⟨-3, 0⟩, 2), (76, ⟨-2, 0⟩, 0), (76, ⟨-2, 0⟩, 1), (76, ⟨-2, 0⟩, 2), (96, ⟨-1, 0⟩, 0), (96, ⟨-1, 0⟩, 1), (96, ⟨-1, 0⟩, 2), (96, ⟨1, 0⟩, 0), (96, ⟨1, 0⟩, 1), (96, ⟨1, 0⟩, 2), (76, ⟨2, 0⟩, 0), (76, ⟨2, 0⟩, 1), (76, ⟨2, 0⟩, 2), (16, ⟨3, 0⟩, 0), (16, ⟨3, 0⟩, 1), (16, ⟨3, 0⟩, 2), (16, ⟨7, 0⟩, 0), (16, ⟨7, 0⟩, 1), (16, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 1), (1, ⟨20, 0⟩, 2)]

theorem g32p_row04_pairing_44 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 2), (32, ⟨-6, 0⟩, 0), (32, ⟨-6, 0⟩, 1), (32, ⟨-6, 0⟩, 2), (32, ⟨-3, 0⟩, 0), (32, ⟨-3, 0⟩, 1), (32, ⟨-3, 0⟩, 2), (12, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 1), (12, ⟨-2, 0⟩, 2), (96, ⟨-1, 0⟩, 0), (96, ⟨-1, 0⟩, 1), (96, ⟨-1, 0⟩, 2), (96, ⟨1, 0⟩, 0), (96, ⟨1, 0⟩, 1), (96, ⟨1, 0⟩, 2), (12, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 1), (12, ⟨2, 0⟩, 2), (32, ⟨3, 0⟩, 0), (32, ⟨3, 0⟩, 1), (32, ⟨3, 0⟩, 2), (32, ⟨6, 0⟩, 0), (32, ⟨6, 0⟩, 1), (32, ⟨6, 0⟩, 2), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 1), (1, ⟨60, 0⟩, 2)]

theorem g32p_row04_pairing_45 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 2), (16, ⟨-8, 0⟩, 0), (16, ⟨-8, 0⟩, 1), (16, ⟨-8, 0⟩, 2), (32, ⟨-4, 0⟩, 0), (32, ⟨-4, 0⟩, 1), (32, ⟨-4, 0⟩, 2), (32, ⟨-2, 0⟩, 0), (32, ⟨-2, 0⟩, 1), (32, ⟨-2, 0⟩, 2), (32, ⟨2, 0⟩, 0), (32, ⟨2, 0⟩, 1), (32, ⟨2, 0⟩, 2), (32, ⟨4, 0⟩, 0), (32, ⟨4, 0⟩, 1), (32, ⟨4, 0⟩, 2), (16, ⟨8, 0⟩, 0), (16, ⟨8, 0⟩, 1), (16, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 1), (1, ⟨64, 0⟩, 2)]

theorem g32p_row04_pairing_46 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row04_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 2), (16, ⟨-8, 0⟩, 0), (16, ⟨-8, 0⟩, 1), (16, ⟨-8, 0⟩, 2), (32, ⟨-4, 0⟩, 0), (32, ⟨-4, 0⟩, 1), (32, ⟨-4, 0⟩, 2), (32, ⟨-2, 0⟩, 0), (32, ⟨-2, 0⟩, 1), (32, ⟨-2, 0⟩, 2), (32, ⟨2, 0⟩, 0), (32, ⟨2, 0⟩, 1), (32, ⟨2, 0⟩, 2), (32, ⟨4, 0⟩, 0), (32, ⟨4, 0⟩, 1), (32, ⟨4, 0⟩, 2), (16, ⟨8, 0⟩, 0), (16, ⟨8, 0⟩, 1), (16, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 1), (1, ⟨80, 0⟩, 2)]

theorem g32p_row04_pairing_47 :
    g32p_cyclotomicPairingCheck 1728 (0)
      (g32p_pairingCoefficients 3 g32p_row04_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row04_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 4 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨4, 1, [(25, 1), (40, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row05_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(54, ⟨-1, -2⟩, 0), (54, ⟨-1, -2⟩, 1), (54, ⟨-1, -2⟩, 2), (54, ⟨1, 2⟩, 0), (54, ⟨1, 2⟩, 1), (54, ⟨1, 2⟩, 2)]

theorem g32p_row05_pairing_0 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_0)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (27, ⟨-2, -4⟩, 1), (27, ⟨-1, -2⟩, 0), (81, ⟨-1, -2⟩, 1), (27, ⟨1, 2⟩, 0), (81, ⟨1, 2⟩, 2), (27, ⟨2, 4⟩, 2), (3, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 2)]

theorem g32p_row05_pairing_1 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row05_terms_1)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row05_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 0), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (10, ⟨-2, -4⟩, 0), (15, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (43, ⟨-1, -2⟩, 0), (42, ⟨-1, -2⟩, 1), (39, ⟨-1, -2⟩, 2), (43, ⟨1, 2⟩, 0), (39, ⟨1, 2⟩, 1), (42, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨4, 8⟩, 0)]

theorem g32p_row05_pairing_2 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 0), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (10, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (43, ⟨-1, -2⟩, 0), (39, ⟨-1, -2⟩, 1), (42, ⟨-1, -2⟩, 2), (43, ⟨1, 2⟩, 0), (42, ⟨1, 2⟩, 1), (39, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨4, 8⟩, 0)]

theorem g32p_row05_pairing_3 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 2), (27, ⟨-2, -4⟩, 1), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (54, ⟨-1, -2⟩, 2), (27, ⟨1, 2⟩, 0), (54, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (27, ⟨2, 4⟩, 2), (3, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1)]

theorem g32p_row05_pairing_4 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 0), (10, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (34, ⟨-2, -4⟩, 0), (15, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (19, ⟨-1, -2⟩, 0), (42, ⟨-1, -2⟩, 1), (39, ⟨-1, -2⟩, 2), (19, ⟨1, 2⟩, 0), (39, ⟨1, 2⟩, 1), (42, ⟨1, 2⟩, 2), (34, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨5, 10⟩, 0)]

theorem g32p_row05_pairing_5 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_5)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 0), (10, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (34, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (15, ⟨-2, -4⟩, 2), (19, ⟨-1, -2⟩, 0), (39, ⟨-1, -2⟩, 1), (42, ⟨-1, -2⟩, 2), (19, ⟨1, 2⟩, 0), (42, ⟨1, 2⟩, 1), (39, ⟨1, 2⟩, 2), (34, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 0)]

theorem g32p_row05_pairing_6 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_6)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 0), (2, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (2, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 0)]

theorem g32p_row05_pairing_7 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(30, ⟨-3, -6⟩, 0), (36, ⟨-3, -6⟩, 1), (54, ⟨-1, -2⟩, 1), (54, ⟨1, 2⟩, 2), (30, ⟨3, 6⟩, 0), (36, ⟨3, 6⟩, 2)]

theorem g32p_row05_pairing_8 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row05_terms_8)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row05_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 0), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 2), (10, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (19, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (33, ⟨-1, -2⟩, 0), (42, ⟨-1, -2⟩, 1), (51, ⟨-1, -2⟩, 2), (33, ⟨1, 2⟩, 0), (51, ⟨1, 2⟩, 1), (42, ⟨1, 2⟩, 2), (19, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 1), (1, ⟨10, 20⟩, 0)]

theorem g32p_row05_pairing_9 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 0), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 1), (10, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 2), (19, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (33, ⟨-1, -2⟩, 0), (51, ⟨-1, -2⟩, 1), (42, ⟨-1, -2⟩, 2), (33, ⟨1, 2⟩, 0), (42, ⟨1, 2⟩, 1), (51, ⟨1, 2⟩, 2), (19, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (10, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 2), (1, ⟨10, 20⟩, 0)]

theorem g32p_row05_pairing_10 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 0), (9, ⟨-7, -14⟩, 0), (26, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (26, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (9, ⟨7, 14⟩, 0), (1, ⟨15, 30⟩, 0)]

theorem g32p_row05_pairing_11 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_11)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 0), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨15, 30⟩, 0)]

theorem g32p_row05_pairing_12 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(30, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (27, ⟨-3, -6⟩, 2), (54, ⟨-1, -2⟩, 1), (54, ⟨1, 2⟩, 2), (30, ⟨3, 6⟩, 0), (27, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2)]

theorem g32p_row05_pairing_13 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-6, -12⟩, 0), (9, ⟨-6, -12⟩, 1), (27, ⟨-2, -4⟩, 0), (27, ⟨-2, -4⟩, 1), (27, ⟨-2, -4⟩, 2), (54, ⟨-1, -2⟩, 2), (54, ⟨1, 2⟩, 1), (27, ⟨2, 4⟩, 0), (27, ⟨2, 4⟩, 1), (27, ⟨2, 4⟩, 2), (3, ⟨6, 12⟩, 0), (9, ⟨6, 12⟩, 2)]

theorem g32p_row05_pairing_14 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (2, ⟨-7, -14⟩, 0), (3, ⟨-7, -14⟩, 1), (3, ⟨-7, -14⟩, 2), (18, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (24, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (18, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (2, ⟨7, 14⟩, 0), (3, ⟨7, 14⟩, 1), (3, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 0)]

theorem g32p_row05_pairing_15 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 2), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (43, ⟨-1, -2⟩, 0), (39, ⟨-1, -2⟩, 1), (42, ⟨-1, -2⟩, 2), (43, ⟨1, 2⟩, 0), (42, ⟨1, 2⟩, 1), (39, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 1), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨20, 40⟩, 0)]

theorem g32p_row05_pairing_16 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 2), (19, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (24, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (19, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 1), (1, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 0)]

theorem g32p_row05_pairing_17 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 1), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (43, ⟨-1, -2⟩, 0), (42, ⟨-1, -2⟩, 1), (39, ⟨-1, -2⟩, 2), (43, ⟨1, 2⟩, 0), (39, ⟨1, 2⟩, 1), (42, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨20, 40⟩, 0)]

theorem g32p_row05_pairing_18 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (1, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 2), (1, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 1), (19, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (24, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (19, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (1, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 2), (1, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (1, ⟨20, 40⟩, 0)]

theorem g32p_row05_pairing_19 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 0), (3, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 2), (9, ⟨-4, -8⟩, 0), (20, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (39, ⟨-1, -2⟩, 1), (39, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (39, ⟨1, 2⟩, 1), (39, ⟨1, 2⟩, 2), (20, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (9, ⟨4, 8⟩, 0), (3, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (1, ⟨20, 40⟩, 0)]

theorem g32p_row05_pairing_20 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_20)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 0), (9, ⟨-8, -16⟩, 0), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (24, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 0), (18, ⟨-2, -4⟩, 1), (18, ⟨-2, -4⟩, 2), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (18, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 2), (24, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (9, ⟨8, 16⟩, 0), (1, ⟨24, 48⟩, 0)]

theorem g32p_row05_pairing_21 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_21)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 2), (27, ⟨-2, -4⟩, 2), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 2), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨2, 4⟩, 1), (3, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 1)]

theorem g32p_row05_pairing_22 :
    g32p_cyclotomicPairingCheck 486 (-1)
      (g32p_pairingCoefficients 3 g32p_row05_terms_22)
      [1, 1, 1] [486, -324] = true := by
  decide +kernel

def g32p_row05_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (10, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (10, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨30, 60⟩, 0)]

theorem g32p_row05_pairing_23 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_23)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 2), (10, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (1, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (10, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (1, ⟨30, 60⟩, 0)]

theorem g32p_row05_pairing_24 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 0), (9, ⟨-10, -20⟩, 0), (26, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (18, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (26, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (9, ⟨10, 20⟩, 0), (1, ⟨30, 60⟩, 0)]

theorem g32p_row05_pairing_25 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_25)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 1), (27, ⟨-3, -6⟩, 0), (27, ⟨-3, -6⟩, 1), (27, ⟨3, 6⟩, 0), (27, ⟨3, 6⟩, 2), (3, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 2)]

theorem g32p_row05_pairing_26 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 3 g32p_row05_terms_26)
      [1, 1, 1] [-486, 324] = true := by
  decide +kernel

def g32p_row05_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 0), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (18, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (18, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 0)]

theorem g32p_row05_pairing_27 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 0), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (18, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (18, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 0)]

theorem g32p_row05_pairing_28 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-6, -12⟩, 0), (9, ⟨-6, -12⟩, 2), (27, ⟨-2, -4⟩, 0), (27, ⟨-2, -4⟩, 1), (27, ⟨-2, -4⟩, 2), (54, ⟨-1, -2⟩, 1), (54, ⟨1, 2⟩, 2), (27, ⟨2, 4⟩, 0), (27, ⟨2, 4⟩, 1), (27, ⟨2, 4⟩, 2), (3, ⟨6, 12⟩, 0), (9, ⟨6, 12⟩, 1)]

theorem g32p_row05_pairing_29 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 0), (10, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (19, ⟨-2, -4⟩, 0), (21, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (30, ⟨-1, -2⟩, 1), (30, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (30, ⟨1, 2⟩, 1), (30, ⟨1, 2⟩, 2), (19, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (21, ⟨2, 4⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (10, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 2), (1, ⟨40, 80⟩, 0)]

theorem g32p_row05_pairing_30 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 0), (10, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 2), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (19, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (21, ⟨-2, -4⟩, 2), (24, ⟨-1, -2⟩, 0), (30, ⟨-1, -2⟩, 1), (30, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 0), (30, ⟨1, 2⟩, 1), (30, ⟨1, 2⟩, 2), (19, ⟨2, 4⟩, 0), (21, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (10, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (1, ⟨40, 80⟩, 0)]

theorem g32p_row05_pairing_31 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 2), (27, ⟨-3, -6⟩, 0), (27, ⟨-3, -6⟩, 1), (27, ⟨3, 6⟩, 0), (27, ⟨3, 6⟩, 2), (3, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 1)]

theorem g32p_row05_pairing_32 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 0), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (27, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (27, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨45, 90⟩, 0)]

theorem g32p_row05_pairing_33 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 0), (2, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (27, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (27, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (2, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨45, 90⟩, 0)]

theorem g32p_row05_pairing_34 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(3, ⟨-9, -18⟩, 0), (9, ⟨-9, -18⟩, 2), (27, ⟨-2, -4⟩, 1), (27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 2), (27, ⟨2, 4⟩, 2), (3, ⟨9, 18⟩, 0), (9, ⟨9, 18⟩, 1)]

theorem g32p_row05_pairing_35 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 2), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (25, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (25, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (1, ⟨60, 120⟩, 0)]

theorem g32p_row05_pairing_36 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (20, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (20, ⟨3, 6⟩, 0), (12, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 0)]

theorem g32p_row05_pairing_37 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (25, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (9, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (25, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨60, 120⟩, 0)]

theorem g32p_row05_pairing_38 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 0), (2, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (9, ⟨-4, -8⟩, 0), (24, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 0), (9, ⟨-2, -4⟩, 1), (9, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨2, 4⟩, 0), (9, ⟨2, 4⟩, 1), (9, ⟨2, 4⟩, 2), (24, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (9, ⟨4, 8⟩, 0), (2, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 0)]

theorem g32p_row05_pairing_39 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_39)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 0), (2, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (24, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (2, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 0)]

theorem g32p_row05_pairing_40 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_40)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 0), (2, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (24, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (24, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (2, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 0)]

theorem g32p_row05_pairing_41 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 0), (2, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (24, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (24, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (2, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 0)]

theorem g32p_row05_pairing_42 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 0), (9, ⟨-9, -18⟩, 0), (9, ⟨9, 18⟩, 0), (1, ⟨81, 162⟩, 0)]

theorem g32p_row05_pairing_43 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_43)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-7, 0⟩, 0), (9, ⟨-7, 0⟩, 1), (9, ⟨-7, 0⟩, 2), (54, ⟨-3, 0⟩, 0), (54, ⟨-1, 0⟩, 1), (54, ⟨-1, 0⟩, 2), (72, ⟨2, 0⟩, 0), (18, ⟨2, 0⟩, 1), (18, ⟨2, 0⟩, 2), (27, ⟨3, 0⟩, 1), (27, ⟨3, 0⟩, 2), (3, ⟨20, 0⟩, 0)]

theorem g32p_row05_pairing_44 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(9, ⟨-6, 0⟩, 1), (9, ⟨-6, 0⟩, 2), (60, ⟨-3, 0⟩, 0), (9, ⟨-3, 0⟩, 1), (9, ⟨-3, 0⟩, 2), (27, ⟨3, 0⟩, 1), (27, ⟨3, 0⟩, 2), (3, ⟨60, 0⟩, 0)]

theorem g32p_row05_pairing_45 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(6, ⟨-8, 0⟩, 0), (9, ⟨-8, 0⟩, 1), (9, ⟨-8, 0⟩, 2), (72, ⟨-2, 0⟩, 0), (9, ⟨-2, 0⟩, 1), (9, ⟨-2, 0⟩, 2), (54, ⟨1, 0⟩, 1), (54, ⟨1, 0⟩, 2), (9, ⟨4, 0⟩, 1), (9, ⟨4, 0⟩, 2), (3, ⟨64, 0⟩, 0)]

theorem g32p_row05_pairing_46 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row05_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(72, ⟨-4, 0⟩, 0), (9, ⟨-4, 0⟩, 1), (9, ⟨-4, 0⟩, 2), (54, ⟨-1, 0⟩, 1), (54, ⟨-1, 0⟩, 2), (9, ⟨2, 0⟩, 1), (9, ⟨2, 0⟩, 2), (6, ⟨8, 0⟩, 0), (9, ⟨8, 0⟩, 1), (9, ⟨8, 0⟩, 2), (3, ⟨80, 0⟩, 0)]

theorem g32p_row05_pairing_47 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 3 g32p_row05_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row05_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 5 ∧ g32SparseVec v.coords =
        (![0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨5, -1, [(2, 1), (9, 1), (23, -1), (27, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row06_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_0 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 0), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3)]

theorem g32p_row06_pairing_1 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 5)]

theorem g32p_row06_pairing_2 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 0), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3)]

theorem g32p_row06_pairing_3 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 4), (4, ⟨-1, -2⟩, 0), (1, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (1, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4)]

theorem g32p_row06_pairing_4 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 5), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 4), (4, ⟨-1, -2⟩, 0), (1, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (1, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 5), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4)]

theorem g32p_row06_pairing_5 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 4), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (1, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (1, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 4), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 5)]

theorem g32p_row06_pairing_6 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_7 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 3), (2, ⟨-3, -6⟩, 4), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 4), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 3), (2, ⟨3, 6⟩, 5)]

theorem g32p_row06_pairing_8 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 3), (2, ⟨-3, -6⟩, 4), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 4), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 3), (2, ⟨3, 6⟩, 5)]

theorem g32p_row06_pairing_9 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 3), (2, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 4), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 5), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 3), (2, ⟨3, 6⟩, 4)]

theorem g32p_row06_pairing_10 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_11 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_11)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_12 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 3), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 3)]

theorem g32p_row06_pairing_13 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 3), (1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 3)]

theorem g32p_row06_pairing_14 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_15 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 3), (1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 3)]

theorem g32p_row06_pairing_16 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (2, ⟨-3, -6⟩, 1), (2, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 3), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 3), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 5)]

theorem g32p_row06_pairing_17 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (4, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5)]

theorem g32p_row06_pairing_18 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 3), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (8, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 3)]

theorem g32p_row06_pairing_19 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_20 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_21 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 5), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (7, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 3), (7, ⟨1, 2⟩, 4), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 4), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4)]

theorem g32p_row06_pairing_22 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_22)
      [1, -1, 1] [0, 24, 0, 24, 0, -48] = true := by
  decide +kernel

def g32p_row06_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 4), (4, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (4, ⟨-1, -2⟩, 3), (7, ⟨-1, -2⟩, 4), (4, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (7, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 5), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 5)]

theorem g32p_row06_pairing_23 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_23)
      [1, -1, 1] [0, -24, 0, -24, 0, 48] = true := by
  decide +kernel

def g32p_row06_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 5), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (7, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (4, ⟨1, 2⟩, 3), (7, ⟨1, 2⟩, 4), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 4), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4)]

theorem g32p_row06_pairing_24 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_24)
      [1, -1, 1] [0, 24, 0, 24, 0, -48] = true := by
  decide +kernel

def g32p_row06_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_25 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 5), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3)]

theorem g32p_row06_pairing_26 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4), (1, ⟨9, 18⟩, 5)]

theorem g32p_row06_pairing_27 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 5), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3)]

theorem g32p_row06_pairing_28 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (1, ⟨-6, -12⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (1, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 4)]

theorem g32p_row06_pairing_29 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (1, ⟨-6, -12⟩, 5), (4, ⟨-2, -4⟩, 0), (4, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (4, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (1, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 4)]

theorem g32p_row06_pairing_30 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 3), (1, ⟨-6, -12⟩, 4), (4, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨2, 4⟩, 0), (4, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 3), (4, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (4, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 5)]

theorem g32p_row06_pairing_31 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 5), (4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 4), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 4), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 5), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4)]

theorem g32p_row06_pairing_32 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 5), (6, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 4), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 4), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 5)]

theorem g32p_row06_pairing_33 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 5), (4, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 3), (1, ⟨-3, -6⟩, 4), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 4), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (1, ⟨3, 6⟩, 5), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4)]

theorem g32p_row06_pairing_34 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 3), (7, ⟨1, 2⟩, 4), (7, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4), (1, ⟨9, 18⟩, 5)]

theorem g32p_row06_pairing_35 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 6 g32p_row06_terms_35)
      [1, -1, 1] [-144, -168, -48, 72, 96, 48] = true := by
  decide +kernel

def g32p_row06_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (4, ⟨-1, -2⟩, 3), (4, ⟨1, 2⟩, 0), (4, ⟨1, 2⟩, 3), (7, ⟨1, 2⟩, 4), (7, ⟨1, 2⟩, 5), (4, ⟨2, 4⟩, 4), (4, ⟨2, 4⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4), (1, ⟨9, 18⟩, 5)]

theorem g32p_row06_pairing_36 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 6 g32p_row06_terms_36)
      [1, -1, 1] [-144, -168, -48, 72, 96, 48] = true := by
  decide +kernel

def g32p_row06_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_37 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (4, ⟨-2, -4⟩, 4), (4, ⟨-2, -4⟩, 5), (4, ⟨-1, -2⟩, 0), (4, ⟨-1, -2⟩, 3), (7, ⟨-1, -2⟩, 4), (7, ⟨-1, -2⟩, 5), (4, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (4, ⟨1, 2⟩, 3), (4, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3)]

theorem g32p_row06_pairing_38 :
    g32p_cyclotomicPairingCheck 144 (-1)
      (g32p_pairingCoefficients 6 g32p_row06_terms_38)
      [1, -1, 1] [144, 168, 48, -72, -96, -48] = true := by
  decide +kernel

def g32p_row06_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_39 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_40 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_41 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_42 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row06_pairing_43 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_43)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 3), (8, ⟨-7, 0⟩, 0), (1, ⟨-7, 0⟩, 2), (1, ⟨-7, 0⟩, 4), (1, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 3), (1, ⟨-3, 0⟩, 4), (8, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 3), (8, ⟨-2, 0⟩, 5), (6, ⟨-1, 0⟩, 2), (6, ⟨-1, 0⟩, 4), (6, ⟨1, 0⟩, 1), (6, ⟨1, 0⟩, 5), (6, ⟨2, 0⟩, 0), (8, ⟨2, 0⟩, 2), (8, ⟨2, 0⟩, 4), (8, ⟨3, 0⟩, 0), (1, ⟨3, 0⟩, 1), (1, ⟨3, 0⟩, 5), (1, ⟨7, 0⟩, 1), (8, ⟨7, 0⟩, 3), (1, ⟨7, 0⟩, 5), (1, ⟨20, 0⟩, 0)]

theorem g32p_row06_pairing_44 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 3), (4, ⟨-6, 0⟩, 2), (4, ⟨-6, 0⟩, 4), (8, ⟨-3, 0⟩, 0), (2, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 3), (2, ⟨-3, 0⟩, 4), (6, ⟨-2, 0⟩, 0), (6, ⟨-1, 0⟩, 1), (6, ⟨-1, 0⟩, 5), (6, ⟨1, 0⟩, 2), (6, ⟨1, 0⟩, 4), (6, ⟨2, 0⟩, 3), (8, ⟨3, 0⟩, 0), (2, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 3), (2, ⟨3, 0⟩, 5), (4, ⟨6, 0⟩, 1), (4, ⟨6, 0⟩, 5), (1, ⟨60, 0⟩, 0)]

theorem g32p_row06_pairing_45 :
    g32p_cyclotomicPairingCheck 144 (1)
      (g32p_pairingCoefficients 6 g32p_row06_terms_45)
      [1, -1, 1] [-96, -72, 0, 24] = true := by
  decide +kernel

def g32p_row06_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 3), (8, ⟨-8, 0⟩, 0), (1, ⟨-8, 0⟩, 2), (1, ⟨-8, 0⟩, 4), (4, ⟨-4, 0⟩, 1), (4, ⟨-4, 0⟩, 5), (4, ⟨-2, 0⟩, 2), (4, ⟨-2, 0⟩, 4), (4, ⟨2, 0⟩, 1), (4, ⟨2, 0⟩, 5), (4, ⟨4, 0⟩, 2), (4, ⟨4, 0⟩, 4), (1, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 3), (1, ⟨8, 0⟩, 5), (1, ⟨64, 0⟩, 0)]

theorem g32p_row06_pairing_46 :
    g32p_cyclotomicPairingCheck 144 (0)
      (g32p_pairingCoefficients 6 g32p_row06_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row06_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 3), (1, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 3), (1, ⟨-8, 0⟩, 5), (4, ⟨-4, 0⟩, 2), (4, ⟨-4, 0⟩, 4), (4, ⟨-2, 0⟩, 1), (4, ⟨-2, 0⟩, 5), (4, ⟨2, 0⟩, 2), (4, ⟨2, 0⟩, 4), (4, ⟨4, 0⟩, 1), (4, ⟨4, 0⟩, 5), (8, ⟨8, 0⟩, 0), (1, ⟨8, 0⟩, 2), (1, ⟨8, 0⟩, 4), (1, ⟨80, 0⟩, 0)]

theorem g32p_row06_pairing_47 :
    g32p_cyclotomicPairingCheck 144 (2)
      (g32p_pairingCoefficients 6 g32p_row06_terms_47)
      [1, -1, 1] [-144, -144] = true := by
  decide +kernel

theorem g32p_row06_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 6 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0, 0, 0],
         ![0, 1, 0, 2]) := by
  refine ⟨⟨6, 1, [(36, 1), (37, 1), (39, -1), (46, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row07_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(648, ⟨-1, -2⟩, 1), (648, ⟨1, 2⟩, 2)]

theorem g32p_row07_pairing_0 :
    g32p_cyclotomicPairingCheck 1944 (1)
      (g32p_pairingCoefficients 3 g32p_row07_terms_0)
      [1, 1, 1] [-1944, 1296] = true := by
  decide +kernel

def g32p_row07_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (144, ⟨-1, -2⟩, 0), (144, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (144, ⟨1, 2⟩, 1), (144, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row07_pairing_1 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_1)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (8, ⟨-3, -6⟩, 0), (10, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 0), (160, ⟨-1, -2⟩, 1), (160, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (160, ⟨1, 2⟩, 1), (160, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 1), (10, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row07_pairing_2 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_2)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (8, ⟨-3, -6⟩, 0), (10, ⟨-2, -4⟩, 1), (10, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 0), (160, ⟨-1, -2⟩, 1), (160, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (160, ⟨1, 2⟩, 1), (160, ⟨1, 2⟩, 2), (10, ⟨2, 4⟩, 1), (10, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (1, ⟨4, 8⟩, 1), (1, ⟨4, 8⟩, 2)]

theorem g32p_row07_pairing_3 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_3)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (144, ⟨-1, -2⟩, 0), (144, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (144, ⟨1, 2⟩, 1), (144, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row07_pairing_4 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_4)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (8, ⟨-3, -6⟩, 0), (176, ⟨-2, -4⟩, 1), (144, ⟨-1, -2⟩, 0), (306, ⟨-1, -2⟩, 1), (20, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (20, ⟨1, 2⟩, 1), (306, ⟨1, 2⟩, 2), (176, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (2, ⟨5, 10⟩, 2)]

theorem g32p_row07_pairing_5 :
    g32p_cyclotomicPairingCheck 1944 (1)
      (g32p_pairingCoefficients 3 g32p_row07_terms_5)
      [1, 1, 1] [-1944, 1296] = true := by
  decide +kernel

def g32p_row07_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 1), (8, ⟨-3, -6⟩, 0), (176, ⟨-2, -4⟩, 1), (144, ⟨-1, -2⟩, 0), (306, ⟨-1, -2⟩, 1), (20, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (20, ⟨1, 2⟩, 1), (306, ⟨1, 2⟩, 2), (176, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (2, ⟨5, 10⟩, 2)]

theorem g32p_row07_pairing_6 :
    g32p_cyclotomicPairingCheck 1944 (1)
      (g32p_pairingCoefficients 3 g32p_row07_terms_6)
      [1, 1, 1] [-1944, 1296] = true := by
  decide +kernel

def g32p_row07_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 1), (12, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (54, ⟨-2, -4⟩, 1), (108, ⟨-1, -2⟩, 2), (108, ⟨1, 2⟩, 1), (54, ⟨2, 4⟩, 2), (16, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (2, ⟨6, 12⟩, 2)]

theorem g32p_row07_pairing_7 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_7)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (144, ⟨-1, -2⟩, 0), (144, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (144, ⟨1, 2⟩, 1), (144, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row07_pairing_8 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_8)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (8, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (62, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 0), (288, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (144, ⟨1, 2⟩, 1), (288, ⟨1, 2⟩, 2), (62, ⟨2, 4⟩, 1), (8, ⟨3, 6⟩, 0), (8, ⟨5, 10⟩, 1), (2, ⟨10, 20⟩, 2)]

theorem g32p_row07_pairing_9 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_9)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 1), (8, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (62, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 0), (288, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (144, ⟨1, 2⟩, 1), (288, ⟨1, 2⟩, 2), (62, ⟨2, 4⟩, 1), (8, ⟨3, 6⟩, 0), (8, ⟨5, 10⟩, 1), (2, ⟨10, 20⟩, 2)]

theorem g32p_row07_pairing_10 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_10)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (222, ⟨-3, -6⟩, 1), (16, ⟨-3, -6⟩, 2), (16, ⟨3, 6⟩, 1), (222, ⟨3, 6⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row07_pairing_11 :
    g32p_cyclotomicPairingCheck 1944 (1)
      (g32p_pairingCoefficients 3 g32p_row07_terms_11)
      [1, 1, 1] [-1944, 1296] = true := by
  decide +kernel

def g32p_row07_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 1), (16, ⟨-6, -12⟩, 1), (12, ⟨-3, -6⟩, 1), (162, ⟨-1, -2⟩, 2), (162, ⟨1, 2⟩, 1), (12, ⟨3, 6⟩, 2), (16, ⟨6, 12⟩, 2), (2, ⟨15, 30⟩, 2)]

theorem g32p_row07_pairing_12 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_12)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (144, ⟨-1, -2⟩, 0), (144, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (144, ⟨1, 2⟩, 1), (144, ⟨1, 2⟩, 2), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2)]

theorem g32p_row07_pairing_13 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_13)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (144, ⟨-1, -2⟩, 0), (144, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (144, ⟨1, 2⟩, 1), (144, ⟨1, 2⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2)]

theorem g32p_row07_pairing_14 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_14)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-7, -14⟩, 1), (8, ⟨-7, -14⟩, 2), (90, ⟨-2, -4⟩, 1), (90, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 1), (144, ⟨1, 2⟩, 2), (90, ⟨2, 4⟩, 1), (90, ⟨2, 4⟩, 2), (8, ⟨7, 14⟩, 1), (8, ⟨7, 14⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row07_pairing_15 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_15)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-6, -12⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (6, ⟨-4, -8⟩, 1), (6, ⟨-4, -8⟩, 2), (144, ⟨-1, -2⟩, 0), (160, ⟨-1, -2⟩, 1), (160, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (160, ⟨1, 2⟩, 1), (160, ⟨1, 2⟩, 2), (6, ⟨4, 8⟩, 1), (6, ⟨4, 8⟩, 2), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (8, ⟨6, 12⟩, 0), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row07_pairing_16 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_16)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (90, ⟨-2, -4⟩, 1), (90, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 0), (72, ⟨-1, -2⟩, 1), (72, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 2), (90, ⟨2, 4⟩, 1), (90, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row07_pairing_17 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_17)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (8, ⟨-6, -12⟩, 0), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (6, ⟨-4, -8⟩, 1), (6, ⟨-4, -8⟩, 2), (144, ⟨-1, -2⟩, 0), (160, ⟨-1, -2⟩, 1), (160, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (160, ⟨1, 2⟩, 1), (160, ⟨1, 2⟩, 2), (6, ⟨4, 8⟩, 1), (6, ⟨4, 8⟩, 2), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (8, ⟨6, 12⟩, 0), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row07_pairing_18 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_18)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (4, ⟨-8, -16⟩, 1), (4, ⟨-8, -16⟩, 2), (4, ⟨-5, -10⟩, 1), (4, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (90, ⟨-2, -4⟩, 1), (90, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 0), (72, ⟨-1, -2⟩, 1), (72, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 2), (90, ⟨2, 4⟩, 1), (90, ⟨2, 4⟩, 2), (8, ⟨3, 6⟩, 0), (4, ⟨5, 10⟩, 1), (4, ⟨5, 10⟩, 2), (4, ⟨8, 16⟩, 1), (4, ⟨8, 16⟩, 2), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 2)]

theorem g32p_row07_pairing_19 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_19)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 1), (12, ⟨-5, -10⟩, 1), (54, ⟨-4, -8⟩, 1), (16, ⟨-2, -4⟩, 1), (108, ⟨-1, -2⟩, 1), (456, ⟨-1, -2⟩, 2), (456, ⟨1, 2⟩, 1), (108, ⟨1, 2⟩, 2), (16, ⟨2, 4⟩, 2), (54, ⟨4, 8⟩, 2), (12, ⟨5, 10⟩, 2), (2, ⟨20, 40⟩, 2)]

theorem g32p_row07_pairing_20 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_20)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 1), (16, ⟨-6, -12⟩, 1), (168, ⟨-3, -6⟩, 1), (168, ⟨3, 6⟩, 2), (16, ⟨6, 12⟩, 2), (2, ⟨24, 48⟩, 2)]

theorem g32p_row07_pairing_21 :
    g32p_cyclotomicPairingCheck 1944 (1)
      (g32p_pairingCoefficients 3 g32p_row07_terms_21)
      [1, 1, 1] [-1944, 1296] = true := by
  decide +kernel

def g32p_row07_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row07_pairing_22 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_22)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (54, ⟨-2, -4⟩, 1), (108, ⟨-1, -2⟩, 2), (108, ⟨1, 2⟩, 1), (54, ⟨2, 4⟩, 2), (12, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 1), (8, ⟨9, 18⟩, 0), (2, ⟨30, 60⟩, 2)]

theorem g32p_row07_pairing_23 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_23)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 1), (12, ⟨-3, -6⟩, 2), (54, ⟨-2, -4⟩, 1), (108, ⟨-1, -2⟩, 2), (108, ⟨1, 2⟩, 1), (54, ⟨2, 4⟩, 2), (12, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (8, ⟨6, 12⟩, 1), (8, ⟨9, 18⟩, 0), (2, ⟨30, 60⟩, 2)]

theorem g32p_row07_pairing_24 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_24)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 1), (196, ⟨-3, -6⟩, 1), (54, ⟨-2, -4⟩, 1), (108, ⟨-1, -2⟩, 2), (108, ⟨1, 2⟩, 1), (54, ⟨2, 4⟩, 2), (196, ⟨3, 6⟩, 2), (2, ⟨30, 60⟩, 2)]

theorem g32p_row07_pairing_25 :
    g32p_cyclotomicPairingCheck 1944 (1)
      (g32p_pairingCoefficients 3 g32p_row07_terms_25)
      [1, 1, 1] [-1944, 1296] = true := by
  decide +kernel

def g32p_row07_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row07_pairing_26 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_26)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row07_pairing_27 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_27)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (1, ⟨36, 72⟩, 1), (1, ⟨36, 72⟩, 2)]

theorem g32p_row07_pairing_28 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_28)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 1), (8, ⟨-6, -12⟩, 2), (144, ⟨-1, -2⟩, 0), (144, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (144, ⟨1, 2⟩, 1), (144, ⟨1, 2⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 1), (8, ⟨6, 12⟩, 2)]

theorem g32p_row07_pairing_29 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_29)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (8, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 0), (20, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 0), (168, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (144, ⟨1, 2⟩, 1), (168, ⟨1, 2⟩, 2), (20, ⟨2, 4⟩, 1), (8, ⟨6, 12⟩, 0), (8, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 2)]

theorem g32p_row07_pairing_30 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_30)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 1), (8, ⟨-8, -16⟩, 2), (8, ⟨-6, -12⟩, 0), (20, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 0), (168, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 0), (144, ⟨1, 2⟩, 1), (168, ⟨1, 2⟩, 2), (20, ⟨2, 4⟩, 1), (8, ⟨6, 12⟩, 0), (8, ⟨8, 16⟩, 1), (2, ⟨40, 80⟩, 2)]

theorem g32p_row07_pairing_31 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_31)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row07_pairing_32 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_32)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (54, ⟨-3, -6⟩, 2), (54, ⟨3, 6⟩, 1), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row07_pairing_33 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_33)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 1), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (54, ⟨-3, -6⟩, 2), (54, ⟨3, 6⟩, 1), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (2, ⟨45, 90⟩, 2)]

theorem g32p_row07_pairing_34 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_34)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 1), (8, ⟨-9, -18⟩, 2), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 1), (8, ⟨9, 18⟩, 2)]

theorem g32p_row07_pairing_35 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_35)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (88, ⟨-3, -6⟩, 1), (88, ⟨-3, -6⟩, 2), (88, ⟨3, 6⟩, 1), (88, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row07_pairing_36 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_36)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (6, ⟨-6, -12⟩, 1), (6, ⟨-6, -12⟩, 2), (8, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (8, ⟨3, 6⟩, 1), (8, ⟨3, 6⟩, 2), (6, ⟨6, 12⟩, 1), (6, ⟨6, 12⟩, 2), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row07_pairing_37 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_37)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (8, ⟨-9, -18⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (88, ⟨-3, -6⟩, 1), (88, ⟨-3, -6⟩, 2), (88, ⟨3, 6⟩, 1), (88, ⟨3, 6⟩, 2), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 2)]

theorem g32p_row07_pairing_38 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_38)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 1), (16, ⟨-6, -12⟩, 1), (54, ⟨-4, -8⟩, 1), (180, ⟨-3, -6⟩, 2), (108, ⟨-1, -2⟩, 1), (108, ⟨1, 2⟩, 2), (180, ⟨3, 6⟩, 1), (54, ⟨4, 8⟩, 2), (16, ⟨6, 12⟩, 2), (2, ⟨60, 120⟩, 2)]

theorem g32p_row07_pairing_39 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_39)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 1), (16, ⟨-8, -16⟩, 2), (12, ⟨-4, -8⟩, 1), (168, ⟨-2, -4⟩, 2), (288, ⟨-1, -2⟩, 1), (288, ⟨1, 2⟩, 2), (168, ⟨2, 4⟩, 1), (12, ⟨4, 8⟩, 2), (16, ⟨8, 16⟩, 1), (2, ⟨64, 128⟩, 2)]

theorem g32p_row07_pairing_40 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_40)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (8, ⟨-8, -16⟩, 1), (8, ⟨-8, -16⟩, 2), (6, ⟨-4, -8⟩, 1), (6, ⟨-4, -8⟩, 2), (84, ⟨-2, -4⟩, 1), (84, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 1), (144, ⟨1, 2⟩, 2), (84, ⟨2, 4⟩, 1), (84, ⟨2, 4⟩, 2), (6, ⟨4, 8⟩, 1), (6, ⟨4, 8⟩, 2), (8, ⟨8, 16⟩, 1), (8, ⟨8, 16⟩, 2), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 2)]

theorem g32p_row07_pairing_41 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_41)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (8, ⟨-8, -16⟩, 1), (8, ⟨-8, -16⟩, 2), (84, ⟨-4, -8⟩, 1), (84, ⟨-4, -8⟩, 2), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (144, ⟨-1, -2⟩, 1), (144, ⟨-1, -2⟩, 2), (144, ⟨1, 2⟩, 1), (144, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (84, ⟨4, 8⟩, 1), (84, ⟨4, 8⟩, 2), (8, ⟨8, 16⟩, 1), (8, ⟨8, 16⟩, 2), (1, ⟨80, 160⟩, 1), (1, ⟨80, 160⟩, 2)]

theorem g32p_row07_pairing_42 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_42)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 1), (54, ⟨-3, -6⟩, 2), (54, ⟨3, 6⟩, 1), (2, ⟨81, 162⟩, 2)]

theorem g32p_row07_pairing_43 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_43)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 2), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 1), (8, ⟨-7, 0⟩, 2), (90, ⟨-2, 0⟩, 0), (90, ⟨-2, 0⟩, 1), (90, ⟨-2, 0⟩, 2), (144, ⟨-1, 0⟩, 0), (144, ⟨-1, 0⟩, 1), (144, ⟨-1, 0⟩, 2), (144, ⟨1, 0⟩, 0), (144, ⟨1, 0⟩, 1), (144, ⟨1, 0⟩, 2), (90, ⟨2, 0⟩, 0), (90, ⟨2, 0⟩, 1), (90, ⟨2, 0⟩, 2), (8, ⟨7, 0⟩, 0), (8, ⟨7, 0⟩, 1), (8, ⟨7, 0⟩, 2), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 1), (1, ⟨20, 0⟩, 2)]

theorem g32p_row07_pairing_44 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_44)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 2), (6, ⟨-6, 0⟩, 0), (6, ⟨-6, 0⟩, 1), (6, ⟨-6, 0⟩, 2), (8, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 1), (8, ⟨-3, 0⟩, 2), (8, ⟨3, 0⟩, 0), (8, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 2), (6, ⟨6, 0⟩, 0), (6, ⟨6, 0⟩, 1), (6, ⟨6, 0⟩, 2), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 1), (1, ⟨60, 0⟩, 2)]

theorem g32p_row07_pairing_45 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_45)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 2), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 2), (6, ⟨-4, 0⟩, 0), (6, ⟨-4, 0⟩, 1), (6, ⟨-4, 0⟩, 2), (84, ⟨-2, 0⟩, 0), (84, ⟨-2, 0⟩, 1), (84, ⟨-2, 0⟩, 2), (144, ⟨-1, 0⟩, 0), (144, ⟨-1, 0⟩, 1), (144, ⟨-1, 0⟩, 2), (144, ⟨1, 0⟩, 0), (144, ⟨1, 0⟩, 1), (144, ⟨1, 0⟩, 2), (84, ⟨2, 0⟩, 0), (84, ⟨2, 0⟩, 1), (84, ⟨2, 0⟩, 2), (6, ⟨4, 0⟩, 0), (6, ⟨4, 0⟩, 1), (6, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 2), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 1), (1, ⟨64, 0⟩, 2)]

theorem g32p_row07_pairing_46 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_46)
      [1, 1, 1] [] = true := by
  decide +kernel

def g32p_row07_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 2), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 2), (84, ⟨-4, 0⟩, 0), (84, ⟨-4, 0⟩, 1), (84, ⟨-4, 0⟩, 2), (6, ⟨-2, 0⟩, 0), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 2), (144, ⟨-1, 0⟩, 0), (144, ⟨-1, 0⟩, 1), (144, ⟨-1, 0⟩, 2), (144, ⟨1, 0⟩, 0), (144, ⟨1, 0⟩, 1), (144, ⟨1, 0⟩, 2), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 1), (6, ⟨2, 0⟩, 2), (84, ⟨4, 0⟩, 0), (84, ⟨4, 0⟩, 1), (84, ⟨4, 0⟩, 2), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 2), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 1), (1, ⟨80, 0⟩, 2)]

theorem g32p_row07_pairing_47 :
    g32p_cyclotomicPairingCheck 1944 (0)
      (g32p_pairingCoefficients 3 g32p_row07_terms_47)
      [1, 1, 1] [] = true := by
  decide +kernel

theorem g32p_row07_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 7 ∧ g32SparseVec v.coords =
        (![1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨7, 1, [(1, 1), (6, 1), (7, 1), (12, 1), (22, 1), (26, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row08_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(108, ⟨-1, -2⟩, 2), (108, ⟨-1, -2⟩, 5), (108, ⟨1, 2⟩, 1), (108, ⟨1, 2⟩, 4)]

theorem g32p_row08_pairing_0 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_0)
      [1, -1, 1] [0, 108, 0, 108, 0, -216] = true := by
  decide +kernel

def g32p_row08_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4)]

theorem g32p_row08_pairing_1 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (8, ⟨-3, -6⟩, 0), (10, ⟨-2, -4⟩, 2), (10, ⟨-2, -4⟩, 4), (16, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (16, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (10, ⟨2, 4⟩, 2), (10, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row08_pairing_2 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (8, ⟨-3, -6⟩, 0), (10, ⟨-2, -4⟩, 2), (10, ⟨-2, -4⟩, 4), (16, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (16, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (10, ⟨2, 4⟩, 2), (10, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (1, ⟨4, 8⟩, 2), (1, ⟨4, 8⟩, 4)]

theorem g32p_row08_pairing_3 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4)]

theorem g32p_row08_pairing_4 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (32, ⟨-2, -4⟩, 2), (54, ⟨-1, -2⟩, 2), (20, ⟨-1, -2⟩, 4), (108, ⟨-1, -2⟩, 5), (108, ⟨1, 2⟩, 1), (20, ⟨1, 2⟩, 2), (54, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (2, ⟨5, 10⟩, 4)]

theorem g32p_row08_pairing_5 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_5)
      [1, -1, 1] [0, 108, 0, 108, 0, -216] = true := by
  decide +kernel

def g32p_row08_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-5, -10⟩, 2), (8, ⟨-3, -6⟩, 0), (32, ⟨-2, -4⟩, 2), (54, ⟨-1, -2⟩, 2), (20, ⟨-1, -2⟩, 4), (108, ⟨-1, -2⟩, 5), (108, ⟨1, 2⟩, 1), (20, ⟨1, 2⟩, 2), (54, ⟨1, 2⟩, 4), (32, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (2, ⟨5, 10⟩, 4)]

theorem g32p_row08_pairing_6 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_6)
      [1, -1, 1] [0, 108, 0, 108, 0, -216] = true := by
  decide +kernel

def g32p_row08_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-6, -12⟩, 2), (12, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (18, ⟨-2, -4⟩, 2), (36, ⟨-2, -4⟩, 5), (72, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 4), (36, ⟨1, 2⟩, 2), (72, ⟨1, 2⟩, 5), (36, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 4), (16, ⟨3, 6⟩, 2), (12, ⟨3, 6⟩, 4), (2, ⟨6, 12⟩, 4)]

theorem g32p_row08_pairing_7 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4)]

theorem g32p_row08_pairing_8 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (8, ⟨-5, -10⟩, 4), (8, ⟨-3, -6⟩, 0), (36, ⟨-2, -4⟩, 1), (26, ⟨-2, -4⟩, 4), (72, ⟨-1, -2⟩, 2), (72, ⟨-1, -2⟩, 5), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 4), (26, ⟨2, 4⟩, 2), (36, ⟨2, 4⟩, 5), (8, ⟨3, 6⟩, 0), (8, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 4)]

theorem g32p_row08_pairing_9 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-10, -20⟩, 2), (8, ⟨-5, -10⟩, 4), (8, ⟨-3, -6⟩, 0), (36, ⟨-2, -4⟩, 1), (26, ⟨-2, -4⟩, 4), (72, ⟨-1, -2⟩, 2), (72, ⟨-1, -2⟩, 5), (72, ⟨1, 2⟩, 1), (72, ⟨1, 2⟩, 4), (26, ⟨2, 4⟩, 2), (36, ⟨2, 4⟩, 5), (8, ⟨3, 6⟩, 0), (8, ⟨5, 10⟩, 2), (2, ⟨10, 20⟩, 4)]

theorem g32p_row08_pairing_10 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (42, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (36, ⟨-3, -6⟩, 5), (36, ⟨3, 6⟩, 1), (16, ⟨3, 6⟩, 2), (42, ⟨3, 6⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row08_pairing_11 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_11)
      [1, -1, 1] [0, 108, 0, 108, 0, -216] = true := by
  decide +kernel

def g32p_row08_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-15, -30⟩, 2), (16, ⟨-6, -12⟩, 2), (12, ⟨-3, -6⟩, 2), (108, ⟨-1, -2⟩, 1), (54, ⟨-1, -2⟩, 4), (54, ⟨1, 2⟩, 2), (108, ⟨1, 2⟩, 5), (12, ⟨3, 6⟩, 4), (16, ⟨6, 12⟩, 4), (2, ⟨15, 30⟩, 4)]

theorem g32p_row08_pairing_12 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 6 g32p_row08_terms_12)
      [1, -1, 1] [-648, -756, -216, 324, 432, 216] = true := by
  decide +kernel

def g32p_row08_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-3, -6⟩, 0), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (8, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4)]

theorem g32p_row08_pairing_13 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 4), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 2), (8, ⟨6, 12⟩, 4)]

theorem g32p_row08_pairing_14 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-7, -14⟩, 2), (8, ⟨-7, -14⟩, 4), (18, ⟨-2, -4⟩, 2), (18, ⟨-2, -4⟩, 4), (18, ⟨2, 4⟩, 2), (18, ⟨2, 4⟩, 4), (8, ⟨7, 14⟩, 2), (8, ⟨7, 14⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row08_pairing_15 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-6, -12⟩, 0), (4, ⟨-5, -10⟩, 2), (4, ⟨-5, -10⟩, 4), (6, ⟨-4, -8⟩, 2), (6, ⟨-4, -8⟩, 4), (16, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (16, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (6, ⟨4, 8⟩, 2), (6, ⟨4, 8⟩, 4), (4, ⟨5, 10⟩, 2), (4, ⟨5, 10⟩, 4), (8, ⟨6, 12⟩, 0), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row08_pairing_16 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (4, ⟨-8, -16⟩, 2), (4, ⟨-8, -16⟩, 4), (4, ⟨-5, -10⟩, 2), (4, ⟨-5, -10⟩, 4), (8, ⟨-3, -6⟩, 0), (18, ⟨-2, -4⟩, 2), (18, ⟨-2, -4⟩, 4), (18, ⟨2, 4⟩, 2), (18, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (4, ⟨5, 10⟩, 2), (4, ⟨5, 10⟩, 4), (4, ⟨8, 16⟩, 2), (4, ⟨8, 16⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row08_pairing_17 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (8, ⟨-6, -12⟩, 0), (4, ⟨-5, -10⟩, 2), (4, ⟨-5, -10⟩, 4), (6, ⟨-4, -8⟩, 2), (6, ⟨-4, -8⟩, 4), (16, ⟨-1, -2⟩, 2), (16, ⟨-1, -2⟩, 4), (16, ⟨1, 2⟩, 2), (16, ⟨1, 2⟩, 4), (6, ⟨4, 8⟩, 2), (6, ⟨4, 8⟩, 4), (4, ⟨5, 10⟩, 2), (4, ⟨5, 10⟩, 4), (8, ⟨6, 12⟩, 0), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row08_pairing_18 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (4, ⟨-8, -16⟩, 2), (4, ⟨-8, -16⟩, 4), (4, ⟨-5, -10⟩, 2), (4, ⟨-5, -10⟩, 4), (8, ⟨-3, -6⟩, 0), (18, ⟨-2, -4⟩, 2), (18, ⟨-2, -4⟩, 4), (18, ⟨2, 4⟩, 2), (18, ⟨2, 4⟩, 4), (8, ⟨3, 6⟩, 0), (4, ⟨5, 10⟩, 2), (4, ⟨5, 10⟩, 4), (4, ⟨8, 16⟩, 2), (4, ⟨8, 16⟩, 4), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 4)]

theorem g32p_row08_pairing_19 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-20, -40⟩, 2), (12, ⟨-5, -10⟩, 2), (18, ⟨-4, -8⟩, 2), (36, ⟨-4, -8⟩, 5), (16, ⟨-2, -4⟩, 2), (36, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 4), (72, ⟨-1, -2⟩, 5), (72, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (36, ⟨1, 2⟩, 4), (16, ⟨2, 4⟩, 4), (36, ⟨4, 8⟩, 1), (18, ⟨4, 8⟩, 4), (12, ⟨5, 10⟩, 4), (2, ⟨20, 40⟩, 4)]

theorem g32p_row08_pairing_20 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_20)
      [1, -1, 1] [0, 216, 0, 216, 0, -432] = true := by
  decide +kernel

def g32p_row08_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-24, -48⟩, 2), (16, ⟨-6, -12⟩, 2), (24, ⟨-3, -6⟩, 2), (24, ⟨3, 6⟩, 4), (16, ⟨6, 12⟩, 4), (2, ⟨24, 48⟩, 4)]

theorem g32p_row08_pairing_21 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 6 g32p_row08_terms_21)
      [1, -1, 1] [-648, -648, -216, 432, 432] = true := by
  decide +kernel

def g32p_row08_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4)]

theorem g32p_row08_pairing_22 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (8, ⟨-9, -18⟩, 0), (8, ⟨-6, -12⟩, 4), (8, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 4), (18, ⟨-2, -4⟩, 2), (36, ⟨-2, -4⟩, 5), (72, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 4), (36, ⟨1, 2⟩, 2), (72, ⟨1, 2⟩, 5), (36, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 4), (12, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (8, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (2, ⟨30, 60⟩, 4)]

theorem g32p_row08_pairing_23 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_23)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (8, ⟨-9, -18⟩, 0), (8, ⟨-6, -12⟩, 4), (8, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 4), (18, ⟨-2, -4⟩, 2), (36, ⟨-2, -4⟩, 5), (72, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 4), (36, ⟨1, 2⟩, 2), (72, ⟨1, 2⟩, 5), (36, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 4), (12, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (8, ⟨6, 12⟩, 2), (8, ⟨9, 18⟩, 0), (2, ⟨30, 60⟩, 4)]

theorem g32p_row08_pairing_24 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_24)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-30, -60⟩, 2), (52, ⟨-3, -6⟩, 2), (18, ⟨-2, -4⟩, 2), (36, ⟨-2, -4⟩, 5), (72, ⟨-1, -2⟩, 1), (36, ⟨-1, -2⟩, 4), (36, ⟨1, 2⟩, 2), (72, ⟨1, 2⟩, 5), (36, ⟨2, 4⟩, 1), (18, ⟨2, 4⟩, 4), (52, ⟨3, 6⟩, 4), (2, ⟨30, 60⟩, 4)]

theorem g32p_row08_pairing_25 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 6 g32p_row08_terms_25)
      [1, -1, 1] [-648, -648, -216, 432, 432] = true := by
  decide +kernel

def g32p_row08_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4)]

theorem g32p_row08_pairing_26 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 4), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row08_pairing_27 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (8, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 4), (8, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 4), (1, ⟨36, 72⟩, 2), (1, ⟨36, 72⟩, 4)]

theorem g32p_row08_pairing_28 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-6, -12⟩, 0), (8, ⟨-6, -12⟩, 2), (8, ⟨-6, -12⟩, 4), (8, ⟨6, 12⟩, 0), (8, ⟨6, 12⟩, 2), (8, ⟨6, 12⟩, 4)]

theorem g32p_row08_pairing_29 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (8, ⟨-8, -16⟩, 4), (8, ⟨-6, -12⟩, 0), (20, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 4), (20, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 4)]

theorem g32p_row08_pairing_30 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-40, -80⟩, 2), (8, ⟨-8, -16⟩, 4), (8, ⟨-6, -12⟩, 0), (20, ⟨-2, -4⟩, 4), (24, ⟨-1, -2⟩, 2), (24, ⟨1, 2⟩, 4), (20, ⟨2, 4⟩, 2), (8, ⟨6, 12⟩, 0), (8, ⟨8, 16⟩, 2), (2, ⟨40, 80⟩, 4)]

theorem g32p_row08_pairing_31 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4)]

theorem g32p_row08_pairing_32 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (36, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 4), (18, ⟨3, 6⟩, 2), (36, ⟨3, 6⟩, 5), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 4), (2, ⟨45, 90⟩, 4)]

theorem g32p_row08_pairing_33 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 6 g32p_row08_terms_33)
      [1, -1, 1] [-648, -756, -216, 324, 432, 216] = true := by
  decide +kernel

def g32p_row08_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-45, -90⟩, 2), (8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (36, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 4), (18, ⟨3, 6⟩, 2), (36, ⟨3, 6⟩, 5), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 4), (2, ⟨45, 90⟩, 4)]

theorem g32p_row08_pairing_34 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 6 g32p_row08_terms_34)
      [1, -1, 1] [-648, -756, -216, 324, 432, 216] = true := by
  decide +kernel

def g32p_row08_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-9, -18⟩, 0), (8, ⟨-9, -18⟩, 2), (8, ⟨-9, -18⟩, 4), (8, ⟨9, 18⟩, 0), (8, ⟨9, 18⟩, 2), (8, ⟨9, 18⟩, 4)]

theorem g32p_row08_pairing_35 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-9, -18⟩, 0), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 4), (16, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (16, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 4), (8, ⟨9, 18⟩, 0), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row08_pairing_36 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (6, ⟨-6, -12⟩, 2), (6, ⟨-6, -12⟩, 4), (8, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 4), (8, ⟨3, 6⟩, 2), (8, ⟨3, 6⟩, 4), (6, ⟨6, 12⟩, 2), (6, ⟨6, 12⟩, 4), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row08_pairing_37 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_37)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (8, ⟨-9, -18⟩, 0), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 4), (16, ⟨-3, -6⟩, 2), (16, ⟨-3, -6⟩, 4), (16, ⟨3, 6⟩, 2), (16, ⟨3, 6⟩, 4), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 4), (8, ⟨9, 18⟩, 0), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 4)]

theorem g32p_row08_pairing_38 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-60, -120⟩, 2), (16, ⟨-6, -12⟩, 2), (18, ⟨-4, -8⟩, 2), (36, ⟨-4, -8⟩, 5), (36, ⟨-3, -6⟩, 4), (36, ⟨-1, -2⟩, 2), (72, ⟨-1, -2⟩, 5), (72, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 4), (36, ⟨3, 6⟩, 2), (36, ⟨4, 8⟩, 1), (18, ⟨4, 8⟩, 4), (16, ⟨6, 12⟩, 4), (2, ⟨60, 120⟩, 4)]

theorem g32p_row08_pairing_39 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_39)
      [1, -1, 1] [0, 216, 0, 216, 0, -432] = true := by
  decide +kernel

def g32p_row08_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-64, -128⟩, 2), (16, ⟨-8, -16⟩, 4), (12, ⟨-4, -8⟩, 2), (24, ⟨-2, -4⟩, 4), (24, ⟨2, 4⟩, 2), (12, ⟨4, 8⟩, 4), (16, ⟨8, 16⟩, 2), (2, ⟨64, 128⟩, 4)]

theorem g32p_row08_pairing_40 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (8, ⟨-8, -16⟩, 2), (8, ⟨-8, -16⟩, 4), (6, ⟨-4, -8⟩, 2), (6, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 4), (12, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 4), (6, ⟨4, 8⟩, 2), (6, ⟨4, 8⟩, 4), (8, ⟨8, 16⟩, 2), (8, ⟨8, 16⟩, 4), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 4)]

theorem g32p_row08_pairing_41 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (8, ⟨-8, -16⟩, 2), (8, ⟨-8, -16⟩, 4), (12, ⟨-4, -8⟩, 2), (12, ⟨-4, -8⟩, 4), (6, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 4), (6, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 4), (12, ⟨4, 8⟩, 2), (12, ⟨4, 8⟩, 4), (8, ⟨8, 16⟩, 2), (8, ⟨8, 16⟩, 4), (1, ⟨80, 160⟩, 2), (1, ⟨80, 160⟩, 4)]

theorem g32p_row08_pairing_42 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-81, -162⟩, 2), (36, ⟨-3, -6⟩, 1), (18, ⟨-3, -6⟩, 4), (18, ⟨3, 6⟩, 2), (36, ⟨3, 6⟩, 5), (2, ⟨81, 162⟩, 4)]

theorem g32p_row08_pairing_43 :
    g32p_cyclotomicPairingCheck 648 (1)
      (g32p_pairingCoefficients 6 g32p_row08_terms_43)
      [1, -1, 1] [-648, -756, -216, 324, 432, 216] = true := by
  decide +kernel

def g32p_row08_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 0), (1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 4), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 2), (8, ⟨-7, 0⟩, 4), (18, ⟨-2, 0⟩, 0), (18, ⟨-2, 0⟩, 2), (18, ⟨-2, 0⟩, 4), (18, ⟨2, 0⟩, 0), (18, ⟨2, 0⟩, 2), (18, ⟨2, 0⟩, 4), (8, ⟨7, 0⟩, 0), (8, ⟨7, 0⟩, 2), (8, ⟨7, 0⟩, 4), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row08_pairing_44 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 0), (1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 4), (6, ⟨-6, 0⟩, 0), (6, ⟨-6, 0⟩, 2), (6, ⟨-6, 0⟩, 4), (8, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 4), (8, ⟨3, 0⟩, 0), (8, ⟨3, 0⟩, 2), (8, ⟨3, 0⟩, 4), (6, ⟨6, 0⟩, 0), (6, ⟨6, 0⟩, 2), (6, ⟨6, 0⟩, 4), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row08_pairing_45 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 0), (1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 4), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 2), (8, ⟨-8, 0⟩, 4), (6, ⟨-4, 0⟩, 0), (6, ⟨-4, 0⟩, 2), (6, ⟨-4, 0⟩, 4), (12, ⟨-2, 0⟩, 0), (12, ⟨-2, 0⟩, 2), (12, ⟨-2, 0⟩, 4), (12, ⟨2, 0⟩, 0), (12, ⟨2, 0⟩, 2), (12, ⟨2, 0⟩, 4), (6, ⟨4, 0⟩, 0), (6, ⟨4, 0⟩, 2), (6, ⟨4, 0⟩, 4), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 2), (8, ⟨8, 0⟩, 4), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row08_pairing_46 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row08_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 0), (1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 4), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 2), (8, ⟨-8, 0⟩, 4), (12, ⟨-4, 0⟩, 0), (12, ⟨-4, 0⟩, 2), (12, ⟨-4, 0⟩, 4), (6, ⟨-2, 0⟩, 0), (6, ⟨-2, 0⟩, 2), (6, ⟨-2, 0⟩, 4), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 2), (6, ⟨2, 0⟩, 4), (12, ⟨4, 0⟩, 0), (12, ⟨4, 0⟩, 2), (12, ⟨4, 0⟩, 4), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 2), (8, ⟨8, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row08_pairing_47 :
    g32p_cyclotomicPairingCheck 648 (0)
      (g32p_pairingCoefficients 6 g32p_row08_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row08_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 8 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨8, -1, [(13, 1), (22, 1), (26, 1), (34, 1), (35, 1), (44, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row09_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (27, ⟨-1, -2⟩, 3), (27, ⟨-1, -2⟩, 4), (27, ⟨-1, -2⟩, 5), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (27, ⟨1, 2⟩, 3), (27, ⟨1, 2⟩, 4), (27, ⟨1, 2⟩, 5)]

theorem g32p_row09_pairing_0 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row09_pairing_1 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (33, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (33, ⟨-1, -2⟩, 3), (30, ⟨-1, -2⟩, 4), (30, ⟨-1, -2⟩, 5), (33, ⟨1, 2⟩, 0), (30, ⟨1, 2⟩, 1), (30, ⟨1, 2⟩, 2), (33, ⟨1, 2⟩, 3), (7, ⟨1, 2⟩, 4), (7, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (1, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 5)]

theorem g32p_row09_pairing_2 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (6, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (25, ⟨-1, -2⟩, 1), (25, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (25, ⟨1, 2⟩, 4), (25, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (1, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 5)]

theorem g32p_row09_pairing_3 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row09_pairing_4 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 5), (15, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (7, ⟨-2, -4⟩, 2), (15, ⟨-2, -4⟩, 3), (12, ⟨-2, -4⟩, 4), (7, ⟨-2, -4⟩, 5), (12, ⟨-1, -2⟩, 0), (19, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (12, ⟨-1, -2⟩, 3), (19, ⟨-1, -2⟩, 4), (15, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 0), (15, ⟨1, 2⟩, 1), (19, ⟨1, 2⟩, 2), (12, ⟨1, 2⟩, 3), (15, ⟨1, 2⟩, 4), (19, ⟨1, 2⟩, 5), (15, ⟨2, 4⟩, 0), (7, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (15, ⟨2, 4⟩, 3), (7, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 4)]

theorem g32p_row09_pairing_5 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 0), (15, ⟨-2, -4⟩, 1), (7, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 3), (15, ⟨-2, -4⟩, 4), (7, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (1, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (1, ⟨-1, -2⟩, 4), (21, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 0), (7, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 3), (7, ⟨2, 4⟩, 4), (15, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 4)]

theorem g32p_row09_pairing_6 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (5, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 5), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 4)]

theorem g32p_row09_pairing_7 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row09_pairing_8 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 2), (1, ⟨-10, -20⟩, 5), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 3), (1, ⟨-5, -10⟩, 4), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (1, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (3, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 2), (3, ⟨5, 10⟩, 3), (1, ⟨5, 10⟩, 5), (1, ⟨10, 20⟩, 1), (1, ⟨10, 20⟩, 4)]

theorem g32p_row09_pairing_9 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 2), (1, ⟨-10, -20⟩, 5), (1, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 5), (3, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (33, ⟨-1, -2⟩, 0), (33, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (33, ⟨-1, -2⟩, 3), (33, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (33, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (33, ⟨1, 2⟩, 2), (33, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (33, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (1, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (3, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (1, ⟨10, 20⟩, 1), (1, ⟨10, 20⟩, 4)]

theorem g32p_row09_pairing_10 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 2), (1, ⟨-15, -30⟩, 5), (15, ⟨-3, -6⟩, 0), (14, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (15, ⟨-3, -6⟩, 3), (14, ⟨-3, -6⟩, 4), (9, ⟨-3, -6⟩, 5), (15, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (14, ⟨3, 6⟩, 2), (15, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 4), (14, ⟨3, 6⟩, 5), (1, ⟨15, 30⟩, 1), (1, ⟨15, 30⟩, 4)]

theorem g32p_row09_pairing_11 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_11)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 2), (1, ⟨-15, -30⟩, 5), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 5), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (2, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨15, 30⟩, 1), (1, ⟨15, 30⟩, 4)]

theorem g32p_row09_pairing_12 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row09_pairing_13 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (4, ⟨-6, -12⟩, 4), (4, ⟨-6, -12⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 3), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 5)]

theorem g32p_row09_pairing_14 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (3, ⟨-7, -14⟩, 0), (3, ⟨-7, -14⟩, 1), (3, ⟨-7, -14⟩, 2), (3, ⟨-7, -14⟩, 3), (2, ⟨-7, -14⟩, 4), (2, ⟨-7, -14⟩, 5), (15, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (15, ⟨-2, -4⟩, 3), (15, ⟨-2, -4⟩, 4), (15, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (15, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (15, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (3, ⟨7, 14⟩, 0), (2, ⟨7, 14⟩, 1), (2, ⟨7, 14⟩, 2), (3, ⟨7, 14⟩, 3), (3, ⟨7, 14⟩, 4), (3, ⟨7, 14⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row09_pairing_15 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 3), (24, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (25, ⟨-1, -2⟩, 4), (25, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (25, ⟨1, 2⟩, 1), (25, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (3, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row09_pairing_16 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (3, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (15, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (15, ⟨-2, -4⟩, 3), (15, ⟨-2, -4⟩, 4), (15, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (15, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (15, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (3, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 3), (1, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row09_pairing_17 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 3), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 3), (30, ⟨-1, -2⟩, 0), (33, ⟨-1, -2⟩, 1), (33, ⟨-1, -2⟩, 2), (30, ⟨-1, -2⟩, 3), (7, ⟨-1, -2⟩, 4), (7, ⟨-1, -2⟩, 5), (30, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (30, ⟨1, 2⟩, 3), (33, ⟨1, 2⟩, 4), (33, ⟨1, 2⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (3, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 3), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row09_pairing_18 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row09_terms_18)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row09_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 3), (1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (15, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (15, ⟨-2, -4⟩, 3), (15, ⟨-2, -4⟩, 4), (15, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (15, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (15, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 3), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row09_pairing_19 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 5), (3, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 3), (3, ⟨-5, -10⟩, 4), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (2, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (21, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (2, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (3, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 2), (3, ⟨5, 10⟩, 3), (3, ⟨5, 10⟩, 5), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 4)]

theorem g32p_row09_pairing_20 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 2), (1, ⟨-24, -48⟩, 5), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 5), (12, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 3), (12, ⟨-3, -6⟩, 4), (6, ⟨-3, -6⟩, 5), (12, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (12, ⟨3, 6⟩, 3), (6, ⟨3, 6⟩, 4), (12, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (2, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨24, 48⟩, 1), (1, ⟨24, 48⟩, 4)]

theorem g32p_row09_pairing_21 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row09_pairing_22 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 3), (1, ⟨-6, -12⟩, 4), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 5), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row09_pairing_23 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_23)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 5), (1, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (3, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row09_pairing_24 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_24)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row09_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (18, ⟨-3, -6⟩, 0), (18, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (18, ⟨-3, -6⟩, 3), (18, ⟨-3, -6⟩, 4), (8, ⟨-3, -6⟩, 5), (18, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (18, ⟨3, 6⟩, 2), (18, ⟨3, 6⟩, 3), (8, ⟨3, 6⟩, 4), (18, ⟨3, 6⟩, 5), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row09_pairing_25 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row09_pairing_26 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (1, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (6, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (6, ⟨9, 18⟩, 4), (6, ⟨9, 18⟩, 5), (1, ⟨36, 72⟩, 4), (1, ⟨36, 72⟩, 5)]

theorem g32p_row09_pairing_27 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row09_terms_27)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row09_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (1, ⟨36, 72⟩, 4), (1, ⟨36, 72⟩, 5)]

theorem g32p_row09_pairing_28 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (4, ⟨-6, -12⟩, 4), (4, ⟨-6, -12⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 3), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 5)]

theorem g32p_row09_pairing_29 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 2), (1, ⟨-40, -80⟩, 5), (1, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 5), (6, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (21, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 5), (1, ⟨40, 80⟩, 1), (1, ⟨40, 80⟩, 4)]

theorem g32p_row09_pairing_30 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_30)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row09_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 2), (1, ⟨-40, -80⟩, 5), (3, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 3), (1, ⟨-8, -16⟩, 4), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (30, ⟨-1, -2⟩, 0), (30, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (30, ⟨-1, -2⟩, 3), (30, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (30, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (30, ⟨1, 2⟩, 2), (30, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (30, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 5), (3, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (1, ⟨8, 16⟩, 5), (1, ⟨40, 80⟩, 1), (1, ⟨40, 80⟩, 4)]

theorem g32p_row09_pairing_31 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_31)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row09_pairing_32 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 2), (1, ⟨-45, -90⟩, 5), (1, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (6, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (6, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4), (6, ⟨9, 18⟩, 5), (1, ⟨45, 90⟩, 1), (1, ⟨45, 90⟩, 4)]

theorem g32p_row09_pairing_33 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 2), (1, ⟨-45, -90⟩, 5), (4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (1, ⟨45, 90⟩, 1), (1, ⟨45, 90⟩, 4)]

theorem g32p_row09_pairing_34 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_34)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row09_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row09_pairing_35 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (3, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (12, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 3), (13, ⟨-3, -6⟩, 4), (13, ⟨-3, -6⟩, 5), (12, ⟨3, 6⟩, 0), (13, ⟨3, 6⟩, 1), (13, ⟨3, 6⟩, 2), (12, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 4), (9, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (3, ⟨9, 18⟩, 5), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row09_pairing_36 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row09_terms_36)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row09_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row09_pairing_37 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row09_terms_37)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row09_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-9, -18⟩, 5), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (15, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (15, ⟨-3, -6⟩, 3), (13, ⟨-3, -6⟩, 4), (13, ⟨-3, -6⟩, 5), (15, ⟨3, 6⟩, 0), (13, ⟨3, 6⟩, 1), (13, ⟨3, 6⟩, 2), (15, ⟨3, 6⟩, 3), (6, ⟨3, 6⟩, 4), (6, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row09_pairing_38 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_38)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 5), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 5), (15, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (15, ⟨-3, -6⟩, 2), (15, ⟨-3, -6⟩, 3), (6, ⟨-3, -6⟩, 4), (15, ⟨-3, -6⟩, 5), (15, ⟨3, 6⟩, 0), (15, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (15, ⟨3, 6⟩, 3), (15, ⟨3, 6⟩, 4), (6, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (2, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 4)]

theorem g32p_row09_pairing_39 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_39)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row09_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 5), (3, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (2, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 3), (3, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 3), (12, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 5), (3, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 4), (2, ⟨8, 16⟩, 5), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 4)]

theorem g32p_row09_pairing_40 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_40)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row09_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (3, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (2, ⟨-8, -16⟩, 4), (2, ⟨-8, -16⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 3), (3, ⟨-4, -8⟩, 4), (3, ⟨-4, -8⟩, 5), (12, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 3), (12, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 3), (3, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 4), (3, ⟨8, 16⟩, 5), (1, ⟨64, 128⟩, 4), (1, ⟨64, 128⟩, 5)]

theorem g32p_row09_pairing_41 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row09_terms_41)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row09_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (3, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (3, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (12, ⟨-4, -8⟩, 0), (12, ⟨-4, -8⟩, 1), (12, ⟨-4, -8⟩, 2), (12, ⟨-4, -8⟩, 3), (6, ⟨-4, -8⟩, 4), (6, ⟨-4, -8⟩, 5), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (12, ⟨4, 8⟩, 0), (6, ⟨4, 8⟩, 1), (6, ⟨4, 8⟩, 2), (12, ⟨4, 8⟩, 3), (12, ⟨4, 8⟩, 4), (12, ⟨4, 8⟩, 5), (3, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (2, ⟨8, 16⟩, 4), (2, ⟨8, 16⟩, 5), (1, ⟨80, 160⟩, 4), (1, ⟨80, 160⟩, 5)]

theorem g32p_row09_pairing_42 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row09_terms_42)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row09_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 2), (1, ⟨-81, -162⟩, 5), (1, ⟨81, 162⟩, 1), (1, ⟨81, 162⟩, 4)]

theorem g32p_row09_pairing_43 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_43)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row09_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 3), (1, ⟨-20, 0⟩, 5), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 2), (8, ⟨-7, 0⟩, 4), (36, ⟨-2, 0⟩, 1), (36, ⟨-2, 0⟩, 3), (36, ⟨-2, 0⟩, 5), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 2), (36, ⟨-1, 0⟩, 4), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 3), (36, ⟨1, 0⟩, 5), (36, ⟨2, 0⟩, 0), (36, ⟨2, 0⟩, 2), (36, ⟨2, 0⟩, 4), (8, ⟨7, 0⟩, 1), (8, ⟨7, 0⟩, 3), (8, ⟨7, 0⟩, 5), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row09_pairing_44 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 3), (1, ⟨-60, 0⟩, 5), (6, ⟨-6, 0⟩, 0), (6, ⟨-6, 0⟩, 2), (6, ⟨-6, 0⟩, 4), (8, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 4), (8, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 3), (8, ⟨3, 0⟩, 5), (6, ⟨6, 0⟩, 1), (6, ⟨6, 0⟩, 3), (6, ⟨6, 0⟩, 5), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row09_pairing_45 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 3), (1, ⟨-64, 0⟩, 5), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 2), (8, ⟨-8, 0⟩, 4), (6, ⟨-4, 0⟩, 1), (6, ⟨-4, 0⟩, 3), (6, ⟨-4, 0⟩, 5), (30, ⟨-2, 0⟩, 0), (30, ⟨-2, 0⟩, 2), (30, ⟨-2, 0⟩, 4), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 3), (36, ⟨-1, 0⟩, 5), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 2), (36, ⟨1, 0⟩, 4), (30, ⟨2, 0⟩, 1), (30, ⟨2, 0⟩, 3), (30, ⟨2, 0⟩, 5), (6, ⟨4, 0⟩, 0), (6, ⟨4, 0⟩, 2), (6, ⟨4, 0⟩, 4), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 3), (8, ⟨8, 0⟩, 5), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row09_pairing_46 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row09_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 3), (1, ⟨-80, 0⟩, 5), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 3), (8, ⟨-8, 0⟩, 5), (30, ⟨-4, 0⟩, 0), (30, ⟨-4, 0⟩, 2), (30, ⟨-4, 0⟩, 4), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 3), (6, ⟨-2, 0⟩, 5), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 2), (36, ⟨-1, 0⟩, 4), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 3), (36, ⟨1, 0⟩, 5), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 2), (6, ⟨2, 0⟩, 4), (30, ⟨4, 0⟩, 1), (30, ⟨4, 0⟩, 3), (30, ⟨4, 0⟩, 5), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 2), (8, ⟨8, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row09_pairing_47 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row09_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row09_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 9 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨9, -2, [(19, 1), (28, 1), (37, 1), (38, 1), (42, 1), (43, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row10_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (27, ⟨-1, -2⟩, 3), (27, ⟨-1, -2⟩, 4), (27, ⟨-1, -2⟩, 5), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (27, ⟨1, 2⟩, 3), (27, ⟨1, 2⟩, 4), (27, ⟨1, 2⟩, 5)]

theorem g32p_row10_pairing_0 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row10_pairing_1 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (6, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (25, ⟨-1, -2⟩, 1), (25, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (25, ⟨1, 2⟩, 4), (25, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (1, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 5)]

theorem g32p_row10_pairing_2 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (33, ⟨-1, -2⟩, 0), (7, ⟨-1, -2⟩, 1), (7, ⟨-1, -2⟩, 2), (33, ⟨-1, -2⟩, 3), (30, ⟨-1, -2⟩, 4), (30, ⟨-1, -2⟩, 5), (33, ⟨1, 2⟩, 0), (30, ⟨1, 2⟩, 1), (30, ⟨1, 2⟩, 2), (33, ⟨1, 2⟩, 3), (7, ⟨1, 2⟩, 4), (7, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (1, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 5)]

theorem g32p_row10_pairing_3 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row10_pairing_4 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (12, ⟨-2, -4⟩, 0), (15, ⟨-2, -4⟩, 1), (7, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 3), (15, ⟨-2, -4⟩, 4), (7, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (1, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (1, ⟨-1, -2⟩, 4), (21, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 0), (7, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 3), (7, ⟨2, 4⟩, 4), (15, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 4)]

theorem g32p_row10_pairing_5 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 5), (15, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (7, ⟨-2, -4⟩, 2), (15, ⟨-2, -4⟩, 3), (12, ⟨-2, -4⟩, 4), (7, ⟨-2, -4⟩, 5), (12, ⟨-1, -2⟩, 0), (19, ⟨-1, -2⟩, 1), (15, ⟨-1, -2⟩, 2), (12, ⟨-1, -2⟩, 3), (19, ⟨-1, -2⟩, 4), (15, ⟨-1, -2⟩, 5), (12, ⟨1, 2⟩, 0), (15, ⟨1, 2⟩, 1), (19, ⟨1, 2⟩, 2), (12, ⟨1, 2⟩, 3), (15, ⟨1, 2⟩, 4), (19, ⟨1, 2⟩, 5), (15, ⟨2, 4⟩, 0), (7, ⟨2, 4⟩, 1), (12, ⟨2, 4⟩, 2), (15, ⟨2, 4⟩, 3), (7, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 4)]

theorem g32p_row10_pairing_6 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (5, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 5), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 4)]

theorem g32p_row10_pairing_7 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row10_pairing_8 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 2), (1, ⟨-10, -20⟩, 5), (1, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 5), (3, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (33, ⟨-1, -2⟩, 0), (33, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (33, ⟨-1, -2⟩, 3), (33, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (33, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (33, ⟨1, 2⟩, 2), (33, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (33, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (1, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (3, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (1, ⟨10, 20⟩, 1), (1, ⟨10, 20⟩, 4)]

theorem g32p_row10_pairing_9 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 2), (1, ⟨-10, -20⟩, 5), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 3), (1, ⟨-5, -10⟩, 4), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (1, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (3, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 2), (3, ⟨5, 10⟩, 3), (1, ⟨5, 10⟩, 5), (1, ⟨10, 20⟩, 1), (1, ⟨10, 20⟩, 4)]

theorem g32p_row10_pairing_10 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 2), (1, ⟨-15, -30⟩, 5), (15, ⟨-3, -6⟩, 0), (14, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (15, ⟨-3, -6⟩, 3), (14, ⟨-3, -6⟩, 4), (9, ⟨-3, -6⟩, 5), (15, ⟨3, 6⟩, 0), (9, ⟨3, 6⟩, 1), (14, ⟨3, 6⟩, 2), (15, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 4), (14, ⟨3, 6⟩, 5), (1, ⟨15, 30⟩, 1), (1, ⟨15, 30⟩, 4)]

theorem g32p_row10_pairing_11 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_11)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 2), (1, ⟨-15, -30⟩, 5), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 5), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (2, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨15, 30⟩, 1), (1, ⟨15, 30⟩, 4)]

theorem g32p_row10_pairing_12 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row10_pairing_13 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (4, ⟨-6, -12⟩, 4), (4, ⟨-6, -12⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 3), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 5)]

theorem g32p_row10_pairing_14 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (3, ⟨-7, -14⟩, 0), (3, ⟨-7, -14⟩, 1), (3, ⟨-7, -14⟩, 2), (3, ⟨-7, -14⟩, 3), (2, ⟨-7, -14⟩, 4), (2, ⟨-7, -14⟩, 5), (15, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (15, ⟨-2, -4⟩, 3), (15, ⟨-2, -4⟩, 4), (15, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (15, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (15, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (3, ⟨7, 14⟩, 0), (2, ⟨7, 14⟩, 1), (2, ⟨7, 14⟩, 2), (3, ⟨7, 14⟩, 3), (3, ⟨7, 14⟩, 4), (3, ⟨7, 14⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row10_pairing_15 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_15)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 3), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 3), (30, ⟨-1, -2⟩, 0), (33, ⟨-1, -2⟩, 1), (33, ⟨-1, -2⟩, 2), (30, ⟨-1, -2⟩, 3), (7, ⟨-1, -2⟩, 4), (7, ⟨-1, -2⟩, 5), (30, ⟨1, 2⟩, 0), (7, ⟨1, 2⟩, 1), (7, ⟨1, 2⟩, 2), (30, ⟨1, 2⟩, 3), (33, ⟨1, 2⟩, 4), (33, ⟨1, 2⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (3, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 3), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row10_pairing_16 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row10_terms_16)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row10_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 3), (1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (15, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (15, ⟨-2, -4⟩, 3), (15, ⟨-2, -4⟩, 4), (15, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (15, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (15, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 3), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row10_pairing_17 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 3), (24, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (25, ⟨-1, -2⟩, 4), (25, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (25, ⟨1, 2⟩, 1), (25, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (3, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row10_pairing_18 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (3, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (15, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (15, ⟨-2, -4⟩, 3), (15, ⟨-2, -4⟩, 4), (15, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (15, ⟨2, 4⟩, 0), (15, ⟨2, 4⟩, 1), (15, ⟨2, 4⟩, 2), (15, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (3, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 3), (1, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row10_pairing_19 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 5), (3, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 3), (3, ⟨-5, -10⟩, 4), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (2, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (21, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (2, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (3, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 2), (3, ⟨5, 10⟩, 3), (3, ⟨5, 10⟩, 5), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 4)]

theorem g32p_row10_pairing_20 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 2), (1, ⟨-24, -48⟩, 5), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 5), (12, ⟨-3, -6⟩, 0), (12, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 3), (12, ⟨-3, -6⟩, 4), (6, ⟨-3, -6⟩, 5), (12, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (12, ⟨3, 6⟩, 2), (12, ⟨3, 6⟩, 3), (6, ⟨3, 6⟩, 4), (12, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (2, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨24, 48⟩, 1), (1, ⟨24, 48⟩, 4)]

theorem g32p_row10_pairing_21 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_21)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row10_pairing_22 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 5), (1, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (3, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row10_pairing_23 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_23)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row10_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 3), (1, ⟨-6, -12⟩, 4), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 5), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row10_pairing_24 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_24)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (18, ⟨-3, -6⟩, 0), (18, ⟨-3, -6⟩, 1), (8, ⟨-3, -6⟩, 2), (18, ⟨-3, -6⟩, 3), (18, ⟨-3, -6⟩, 4), (8, ⟨-3, -6⟩, 5), (18, ⟨3, 6⟩, 0), (8, ⟨3, 6⟩, 1), (18, ⟨3, 6⟩, 2), (18, ⟨3, 6⟩, 3), (8, ⟨3, 6⟩, 4), (18, ⟨3, 6⟩, 5), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row10_pairing_25 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_25)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row10_pairing_26 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (1, ⟨36, 72⟩, 4), (1, ⟨36, 72⟩, 5)]

theorem g32p_row10_pairing_27 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (1, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (6, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (6, ⟨9, 18⟩, 4), (6, ⟨9, 18⟩, 5), (1, ⟨36, 72⟩, 4), (1, ⟨36, 72⟩, 5)]

theorem g32p_row10_pairing_28 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row10_terms_28)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row10_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (4, ⟨-6, -12⟩, 4), (4, ⟨-6, -12⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 3), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 5)]

theorem g32p_row10_pairing_29 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 2), (1, ⟨-40, -80⟩, 5), (3, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 3), (1, ⟨-8, -16⟩, 4), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (30, ⟨-1, -2⟩, 0), (30, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (30, ⟨-1, -2⟩, 3), (30, ⟨-1, -2⟩, 4), (6, ⟨-1, -2⟩, 5), (30, ⟨1, 2⟩, 0), (6, ⟨1, 2⟩, 1), (30, ⟨1, 2⟩, 2), (30, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (30, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 5), (3, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (1, ⟨8, 16⟩, 5), (1, ⟨40, 80⟩, 1), (1, ⟨40, 80⟩, 4)]

theorem g32p_row10_pairing_30 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_30)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 2), (1, ⟨-40, -80⟩, 5), (1, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 5), (6, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (21, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 5), (1, ⟨40, 80⟩, 1), (1, ⟨40, 80⟩, 4)]

theorem g32p_row10_pairing_31 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_31)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row10_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row10_pairing_32 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 2), (1, ⟨-45, -90⟩, 5), (4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (1, ⟨45, 90⟩, 1), (1, ⟨45, 90⟩, 4)]

theorem g32p_row10_pairing_33 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_33)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row10_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 2), (1, ⟨-45, -90⟩, 5), (1, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (6, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (6, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4), (6, ⟨9, 18⟩, 5), (1, ⟨45, 90⟩, 1), (1, ⟨45, 90⟩, 4)]

theorem g32p_row10_pairing_34 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row10_pairing_35 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-9, -18⟩, 5), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (15, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (15, ⟨-3, -6⟩, 3), (13, ⟨-3, -6⟩, 4), (13, ⟨-3, -6⟩, 5), (15, ⟨3, 6⟩, 0), (13, ⟨3, 6⟩, 1), (13, ⟨3, 6⟩, 2), (15, ⟨3, 6⟩, 3), (6, ⟨3, 6⟩, 4), (6, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row10_pairing_36 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_36)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row10_pairing_37 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row10_terms_37)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row10_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (3, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (12, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (9, ⟨-3, -6⟩, 2), (12, ⟨-3, -6⟩, 3), (13, ⟨-3, -6⟩, 4), (13, ⟨-3, -6⟩, 5), (12, ⟨3, 6⟩, 0), (13, ⟨3, 6⟩, 1), (13, ⟨3, 6⟩, 2), (12, ⟨3, 6⟩, 3), (9, ⟨3, 6⟩, 4), (9, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (3, ⟨9, 18⟩, 5), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row10_pairing_38 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row10_terms_38)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row10_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 5), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 5), (15, ⟨-3, -6⟩, 0), (6, ⟨-3, -6⟩, 1), (15, ⟨-3, -6⟩, 2), (15, ⟨-3, -6⟩, 3), (6, ⟨-3, -6⟩, 4), (15, ⟨-3, -6⟩, 5), (15, ⟨3, 6⟩, 0), (15, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 2), (15, ⟨3, 6⟩, 3), (15, ⟨3, 6⟩, 4), (6, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (2, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 4)]

theorem g32p_row10_pairing_39 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_39)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row10_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 5), (3, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (2, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 3), (3, ⟨-4, -8⟩, 4), (12, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (12, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 0), (12, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 3), (12, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 5), (3, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 4), (2, ⟨8, 16⟩, 5), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 4)]

theorem g32p_row10_pairing_40 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_40)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row10_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (3, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (2, ⟨-8, -16⟩, 4), (2, ⟨-8, -16⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 3), (3, ⟨-4, -8⟩, 4), (3, ⟨-4, -8⟩, 5), (12, ⟨-2, -4⟩, 0), (12, ⟨-2, -4⟩, 1), (12, ⟨-2, -4⟩, 2), (12, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (9, ⟨-1, -2⟩, 4), (9, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (9, ⟨1, 2⟩, 1), (9, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (12, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (12, ⟨2, 4⟩, 3), (12, ⟨2, 4⟩, 4), (12, ⟨2, 4⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 3), (3, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 4), (3, ⟨8, 16⟩, 5), (1, ⟨64, 128⟩, 4), (1, ⟨64, 128⟩, 5)]

theorem g32p_row10_pairing_41 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row10_terms_41)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row10_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (3, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (3, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (12, ⟨-4, -8⟩, 0), (12, ⟨-4, -8⟩, 1), (12, ⟨-4, -8⟩, 2), (12, ⟨-4, -8⟩, 3), (6, ⟨-4, -8⟩, 4), (6, ⟨-4, -8⟩, 5), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (9, ⟨-1, -2⟩, 0), (9, ⟨-1, -2⟩, 1), (9, ⟨-1, -2⟩, 2), (9, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (9, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (9, ⟨1, 2⟩, 3), (9, ⟨1, 2⟩, 4), (9, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (12, ⟨4, 8⟩, 0), (6, ⟨4, 8⟩, 1), (6, ⟨4, 8⟩, 2), (12, ⟨4, 8⟩, 3), (12, ⟨4, 8⟩, 4), (12, ⟨4, 8⟩, 5), (3, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (2, ⟨8, 16⟩, 4), (2, ⟨8, 16⟩, 5), (1, ⟨80, 160⟩, 4), (1, ⟨80, 160⟩, 5)]

theorem g32p_row10_pairing_42 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row10_terms_42)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row10_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 2), (1, ⟨-81, -162⟩, 5), (1, ⟨81, 162⟩, 1), (1, ⟨81, 162⟩, 4)]

theorem g32p_row10_pairing_43 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_43)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row10_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 3), (1, ⟨-20, 0⟩, 5), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 2), (8, ⟨-7, 0⟩, 4), (36, ⟨-2, 0⟩, 1), (36, ⟨-2, 0⟩, 3), (36, ⟨-2, 0⟩, 5), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 2), (36, ⟨-1, 0⟩, 4), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 3), (36, ⟨1, 0⟩, 5), (36, ⟨2, 0⟩, 0), (36, ⟨2, 0⟩, 2), (36, ⟨2, 0⟩, 4), (8, ⟨7, 0⟩, 1), (8, ⟨7, 0⟩, 3), (8, ⟨7, 0⟩, 5), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row10_pairing_44 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 3), (1, ⟨-60, 0⟩, 5), (6, ⟨-6, 0⟩, 0), (6, ⟨-6, 0⟩, 2), (6, ⟨-6, 0⟩, 4), (8, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 4), (8, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 3), (8, ⟨3, 0⟩, 5), (6, ⟨6, 0⟩, 1), (6, ⟨6, 0⟩, 3), (6, ⟨6, 0⟩, 5), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row10_pairing_45 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 3), (1, ⟨-64, 0⟩, 5), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 2), (8, ⟨-8, 0⟩, 4), (6, ⟨-4, 0⟩, 1), (6, ⟨-4, 0⟩, 3), (6, ⟨-4, 0⟩, 5), (30, ⟨-2, 0⟩, 0), (30, ⟨-2, 0⟩, 2), (30, ⟨-2, 0⟩, 4), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 3), (36, ⟨-1, 0⟩, 5), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 2), (36, ⟨1, 0⟩, 4), (30, ⟨2, 0⟩, 1), (30, ⟨2, 0⟩, 3), (30, ⟨2, 0⟩, 5), (6, ⟨4, 0⟩, 0), (6, ⟨4, 0⟩, 2), (6, ⟨4, 0⟩, 4), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 3), (8, ⟨8, 0⟩, 5), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row10_pairing_46 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row10_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 3), (1, ⟨-80, 0⟩, 5), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 3), (8, ⟨-8, 0⟩, 5), (30, ⟨-4, 0⟩, 0), (30, ⟨-4, 0⟩, 2), (30, ⟨-4, 0⟩, 4), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 3), (6, ⟨-2, 0⟩, 5), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 2), (36, ⟨-1, 0⟩, 4), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 3), (36, ⟨1, 0⟩, 5), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 2), (6, ⟨2, 0⟩, 4), (30, ⟨4, 0⟩, 1), (30, ⟨4, 0⟩, 3), (30, ⟨4, 0⟩, 5), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 2), (8, ⟨8, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row10_pairing_47 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row10_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row10_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 10 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨10, -3, [(17, 1), (29, 1), (38, 1), (39, 1), (42, 1), (43, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row11_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (27, ⟨-1, -2⟩, 3), (27, ⟨-1, -2⟩, 4), (27, ⟨-1, -2⟩, 5), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (27, ⟨1, 2⟩, 3), (27, ⟨1, 2⟩, 4), (27, ⟨1, 2⟩, 5)]

theorem g32p_row11_pairing_0 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row11_pairing_1 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (6, ⟨-1, -2⟩, 0), (61, ⟨-1, -2⟩, 1), (61, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 3), (61, ⟨1, 2⟩, 4), (61, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (1, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 5)]

theorem g32p_row11_pairing_2 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row11_terms_2)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row11_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (6, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (25, ⟨-1, -2⟩, 1), (25, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (25, ⟨1, 2⟩, 4), (25, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (1, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 5)]

theorem g32p_row11_pairing_3 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_3)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row11_pairing_4 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 5), (6, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (25, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (25, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (1, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (1, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (25, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (25, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 4)]

theorem g32p_row11_pairing_5 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_5)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row11_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (25, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (25, ⟨-2, -4⟩, 5), (6, ⟨-1, -2⟩, 0), (37, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (37, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (37, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (37, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (25, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (25, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 4)]

theorem g32p_row11_pairing_6 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_6)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (5, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 5), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 4)]

theorem g32p_row11_pairing_7 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row11_pairing_8 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 2), (1, ⟨-10, -20⟩, 5), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 3), (1, ⟨-5, -10⟩, 4), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (1, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (3, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 2), (3, ⟨5, 10⟩, 3), (1, ⟨5, 10⟩, 5), (1, ⟨10, 20⟩, 1), (1, ⟨10, 20⟩, 4)]

theorem g32p_row11_pairing_9 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_9)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 2), (1, ⟨-10, -20⟩, 5), (1, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 5), (3, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (60, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (60, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 0), (60, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 3), (60, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (1, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (3, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (1, ⟨10, 20⟩, 1), (1, ⟨10, 20⟩, 4)]

theorem g32p_row11_pairing_10 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_10)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row11_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 2), (1, ⟨-15, -30⟩, 5), (6, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (27, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (5, ⟨-3, -6⟩, 4), (27, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (27, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 3), (27, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 5), (1, ⟨15, 30⟩, 1), (1, ⟨15, 30⟩, 4)]

theorem g32p_row11_pairing_11 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_11)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row11_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 2), (1, ⟨-15, -30⟩, 5), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 5), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (2, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨15, 30⟩, 1), (1, ⟨15, 30⟩, 4)]

theorem g32p_row11_pairing_12 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row11_pairing_13 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (4, ⟨-6, -12⟩, 4), (4, ⟨-6, -12⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 3), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 5)]

theorem g32p_row11_pairing_14 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (3, ⟨-7, -14⟩, 0), (3, ⟨-7, -14⟩, 1), (3, ⟨-7, -14⟩, 2), (3, ⟨-7, -14⟩, 3), (2, ⟨-7, -14⟩, 4), (2, ⟨-7, -14⟩, 5), (6, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (24, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (3, ⟨7, 14⟩, 0), (2, ⟨7, 14⟩, 1), (2, ⟨7, 14⟩, 2), (3, ⟨7, 14⟩, 3), (3, ⟨7, 14⟩, 4), (3, ⟨7, 14⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row11_pairing_15 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row11_terms_15)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row11_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 3), (24, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (25, ⟨-1, -2⟩, 4), (25, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (25, ⟨1, 2⟩, 1), (25, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (3, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row11_pairing_16 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (3, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (6, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (24, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (3, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 3), (1, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row11_pairing_17 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row11_terms_17)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row11_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 3), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 3), (3, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (61, ⟨-1, -2⟩, 4), (61, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (61, ⟨1, 2⟩, 1), (61, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (3, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 3), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row11_pairing_18 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 3), (1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (6, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (36, ⟨-1, -2⟩, 4), (36, ⟨-1, -2⟩, 5), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (24, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 3), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row11_pairing_19 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_19)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 5), (3, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 3), (3, ⟨-5, -10⟩, 4), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (2, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (21, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (2, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (3, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 2), (3, ⟨5, 10⟩, 3), (3, ⟨5, 10⟩, 5), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 4)]

theorem g32p_row11_pairing_20 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 2), (1, ⟨-24, -48⟩, 5), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 5), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (24, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (24, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (24, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (2, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨24, 48⟩, 1), (1, ⟨24, 48⟩, 4)]

theorem g32p_row11_pairing_21 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_21)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row11_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row11_pairing_22 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 3), (1, ⟨-6, -12⟩, 4), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 5), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row11_pairing_23 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_23)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 5), (1, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (3, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row11_pairing_24 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_24)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row11_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (9, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (26, ⟨-3, -6⟩, 2), (9, ⟨-3, -6⟩, 3), (9, ⟨-3, -6⟩, 4), (26, ⟨-3, -6⟩, 5), (9, ⟨3, 6⟩, 0), (26, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (9, ⟨3, 6⟩, 3), (26, ⟨3, 6⟩, 4), (9, ⟨3, 6⟩, 5), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row11_pairing_25 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_25)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row11_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row11_pairing_26 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (1, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (6, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (6, ⟨9, 18⟩, 4), (6, ⟨9, 18⟩, 5), (1, ⟨36, 72⟩, 4), (1, ⟨36, 72⟩, 5)]

theorem g32p_row11_pairing_27 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row11_terms_27)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row11_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (1, ⟨36, 72⟩, 4), (1, ⟨36, 72⟩, 5)]

theorem g32p_row11_pairing_28 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_28)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (4, ⟨-6, -12⟩, 4), (4, ⟨-6, -12⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 3), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 5)]

theorem g32p_row11_pairing_29 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 2), (1, ⟨-40, -80⟩, 5), (1, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 5), (6, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (21, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 5), (1, ⟨40, 80⟩, 1), (1, ⟨40, 80⟩, 4)]

theorem g32p_row11_pairing_30 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_30)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row11_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 2), (1, ⟨-40, -80⟩, 5), (3, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 3), (1, ⟨-8, -16⟩, 4), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (60, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (60, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (60, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (60, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 5), (3, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (1, ⟨8, 16⟩, 5), (1, ⟨40, 80⟩, 1), (1, ⟨40, 80⟩, 4)]

theorem g32p_row11_pairing_31 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_31)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row11_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row11_pairing_32 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 2), (1, ⟨-45, -90⟩, 5), (1, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (6, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (6, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4), (6, ⟨9, 18⟩, 5), (1, ⟨45, 90⟩, 1), (1, ⟨45, 90⟩, 4)]

theorem g32p_row11_pairing_33 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_33)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 2), (1, ⟨-45, -90⟩, 5), (4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (1, ⟨45, 90⟩, 1), (1, ⟨45, 90⟩, 4)]

theorem g32p_row11_pairing_34 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_34)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row11_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row11_pairing_35 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (3, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-3, -6⟩, 0), (27, ⟨-3, -6⟩, 1), (27, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (27, ⟨3, 6⟩, 4), (27, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (3, ⟨9, 18⟩, 5), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row11_pairing_36 :
    g32p_cyclotomicPairingCheck 486 (2)
      (g32p_pairingCoefficients 6 g32p_row11_terms_36)
      [1, -1, 1] [-972, -1134, -324, 486, 648, 324] = true := by
  decide +kernel

def g32p_row11_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row11_pairing_37 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row11_terms_37)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row11_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-9, -18⟩, 5), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 1), (24, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 3), (24, ⟨3, 6⟩, 4), (24, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row11_pairing_38 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row11_terms_38)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row11_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 5), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (24, ⟨-3, -6⟩, 4), (6, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (24, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 3), (6, ⟨3, 6⟩, 4), (24, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (2, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 4)]

theorem g32p_row11_pairing_39 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 5), (3, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (2, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 3), (3, ⟨-4, -8⟩, 4), (3, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (24, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 5), (3, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 4), (2, ⟨8, 16⟩, 5), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 4)]

theorem g32p_row11_pairing_40 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (3, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (2, ⟨-8, -16⟩, 4), (2, ⟨-8, -16⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 3), (3, ⟨-4, -8⟩, 4), (3, ⟨-4, -8⟩, 5), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (24, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (3, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 3), (3, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 4), (3, ⟨8, 16⟩, 5), (1, ⟨64, 128⟩, 4), (1, ⟨64, 128⟩, 5)]

theorem g32p_row11_pairing_41 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (3, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (3, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 3), (24, ⟨-4, -8⟩, 4), (24, ⟨-4, -8⟩, 5), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (3, ⟨4, 8⟩, 0), (24, ⟨4, 8⟩, 1), (24, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (3, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (2, ⟨8, 16⟩, 4), (2, ⟨8, 16⟩, 5), (1, ⟨80, 160⟩, 4), (1, ⟨80, 160⟩, 5)]

theorem g32p_row11_pairing_42 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 2), (1, ⟨-81, -162⟩, 5), (1, ⟨81, 162⟩, 1), (1, ⟨81, 162⟩, 4)]

theorem g32p_row11_pairing_43 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_43)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row11_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 3), (1, ⟨-20, 0⟩, 5), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 2), (8, ⟨-7, 0⟩, 4), (36, ⟨-2, 0⟩, 1), (36, ⟨-2, 0⟩, 3), (36, ⟨-2, 0⟩, 5), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 2), (36, ⟨-1, 0⟩, 4), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 3), (36, ⟨1, 0⟩, 5), (36, ⟨2, 0⟩, 0), (36, ⟨2, 0⟩, 2), (36, ⟨2, 0⟩, 4), (8, ⟨7, 0⟩, 1), (8, ⟨7, 0⟩, 3), (8, ⟨7, 0⟩, 5), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row11_pairing_44 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 3), (1, ⟨-60, 0⟩, 5), (6, ⟨-6, 0⟩, 0), (6, ⟨-6, 0⟩, 2), (6, ⟨-6, 0⟩, 4), (8, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 4), (8, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 3), (8, ⟨3, 0⟩, 5), (6, ⟨6, 0⟩, 1), (6, ⟨6, 0⟩, 3), (6, ⟨6, 0⟩, 5), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row11_pairing_45 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 3), (1, ⟨-64, 0⟩, 5), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 2), (8, ⟨-8, 0⟩, 4), (6, ⟨-4, 0⟩, 1), (6, ⟨-4, 0⟩, 3), (6, ⟨-4, 0⟩, 5), (30, ⟨-2, 0⟩, 0), (30, ⟨-2, 0⟩, 2), (30, ⟨-2, 0⟩, 4), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 3), (36, ⟨-1, 0⟩, 5), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 2), (36, ⟨1, 0⟩, 4), (30, ⟨2, 0⟩, 1), (30, ⟨2, 0⟩, 3), (30, ⟨2, 0⟩, 5), (6, ⟨4, 0⟩, 0), (6, ⟨4, 0⟩, 2), (6, ⟨4, 0⟩, 4), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 3), (8, ⟨8, 0⟩, 5), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row11_pairing_46 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row11_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 3), (1, ⟨-80, 0⟩, 5), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 3), (8, ⟨-8, 0⟩, 5), (30, ⟨-4, 0⟩, 0), (30, ⟨-4, 0⟩, 2), (30, ⟨-4, 0⟩, 4), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 3), (6, ⟨-2, 0⟩, 5), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 2), (36, ⟨-1, 0⟩, 4), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 3), (36, ⟨1, 0⟩, 5), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 2), (6, ⟨2, 0⟩, 4), (30, ⟨4, 0⟩, 1), (30, ⟨4, 0⟩, 3), (30, ⟨4, 0⟩, 5), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 2), (8, ⟨8, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row11_pairing_47 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row11_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row11_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 11 ∧ g32SparseVec v.coords =
        (![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨11, -1, [(3, 1), (16, 1), (18, 1), (28, 1), (37, 2), (38, 1), (39, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row12_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(27, ⟨-1, -2⟩, 0), (27, ⟨-1, -2⟩, 1), (27, ⟨-1, -2⟩, 2), (27, ⟨-1, -2⟩, 3), (27, ⟨-1, -2⟩, 4), (27, ⟨-1, -2⟩, 5), (27, ⟨1, 2⟩, 0), (27, ⟨1, 2⟩, 1), (27, ⟨1, 2⟩, 2), (27, ⟨1, 2⟩, 3), (27, ⟨1, 2⟩, 4), (27, ⟨1, 2⟩, 5)]

theorem g32p_row12_pairing_0 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_0)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row12_pairing_1 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_1)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (6, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (25, ⟨-1, -2⟩, 1), (25, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (25, ⟨1, 2⟩, 4), (25, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (1, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 5)]

theorem g32p_row12_pairing_2 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_2)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (6, ⟨-1, -2⟩, 0), (61, ⟨-1, -2⟩, 1), (61, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 3), (61, ⟨1, 2⟩, 4), (61, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (1, ⟨4, 8⟩, 4), (1, ⟨4, 8⟩, 5)]

theorem g32p_row12_pairing_3 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row12_terms_3)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row12_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row12_pairing_4 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_4)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-2, -4⟩, 0), (6, ⟨-2, -4⟩, 1), (25, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (25, ⟨-2, -4⟩, 5), (6, ⟨-1, -2⟩, 0), (37, ⟨-1, -2⟩, 1), (3, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (37, ⟨-1, -2⟩, 4), (3, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 0), (3, ⟨1, 2⟩, 1), (37, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 3), (3, ⟨1, 2⟩, 4), (37, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (25, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (25, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 4)]

theorem g32p_row12_pairing_5 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_5)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 5), (6, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (25, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (25, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (1, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (1, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (25, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (25, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (1, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 4)]

theorem g32p_row12_pairing_6 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_6)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row12_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (5, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 5), (1, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 4)]

theorem g32p_row12_pairing_7 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_7)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row12_pairing_8 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_8)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 2), (1, ⟨-10, -20⟩, 5), (1, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 5), (3, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (6, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (60, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 3), (6, ⟨-1, -2⟩, 4), (60, ⟨-1, -2⟩, 5), (6, ⟨1, 2⟩, 0), (60, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 2), (6, ⟨1, 2⟩, 3), (60, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (1, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨5, 10⟩, 1), (1, ⟨5, 10⟩, 2), (3, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (1, ⟨10, 20⟩, 1), (1, ⟨10, 20⟩, 4)]

theorem g32p_row12_pairing_9 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_9)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row12_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 2), (1, ⟨-10, -20⟩, 5), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 3), (1, ⟨-5, -10⟩, 4), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (1, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (24, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (3, ⟨5, 10⟩, 0), (1, ⟨5, 10⟩, 2), (3, ⟨5, 10⟩, 3), (1, ⟨5, 10⟩, 5), (1, ⟨10, 20⟩, 1), (1, ⟨10, 20⟩, 4)]

theorem g32p_row12_pairing_10 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_10)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 2), (1, ⟨-15, -30⟩, 5), (6, ⟨-3, -6⟩, 0), (5, ⟨-3, -6⟩, 1), (27, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (5, ⟨-3, -6⟩, 4), (27, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (27, ⟨3, 6⟩, 1), (5, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 3), (27, ⟨3, 6⟩, 4), (5, ⟨3, 6⟩, 5), (1, ⟨15, 30⟩, 1), (1, ⟨15, 30⟩, 4)]

theorem g32p_row12_pairing_11 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_11)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row12_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 2), (1, ⟨-15, -30⟩, 5), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 5), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (2, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨15, 30⟩, 1), (1, ⟨15, 30⟩, 4)]

theorem g32p_row12_pairing_12 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_12)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (4, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (4, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (4, ⟨3, 6⟩, 5)]

theorem g32p_row12_pairing_13 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_13)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (4, ⟨-6, -12⟩, 4), (4, ⟨-6, -12⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 3), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 5)]

theorem g32p_row12_pairing_14 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_14)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (3, ⟨-7, -14⟩, 0), (3, ⟨-7, -14⟩, 1), (3, ⟨-7, -14⟩, 2), (3, ⟨-7, -14⟩, 3), (2, ⟨-7, -14⟩, 4), (2, ⟨-7, -14⟩, 5), (6, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (24, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (3, ⟨7, 14⟩, 0), (2, ⟨7, 14⟩, 1), (2, ⟨7, 14⟩, 2), (3, ⟨7, 14⟩, 3), (3, ⟨7, 14⟩, 4), (3, ⟨7, 14⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row12_pairing_15 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row12_terms_15)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row12_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 3), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 3), (3, ⟨-1, -2⟩, 0), (6, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (61, ⟨-1, -2⟩, 4), (61, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (61, ⟨1, 2⟩, 1), (61, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (6, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (3, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 3), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (1, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row12_pairing_16 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_16)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (3, ⟨-5, -10⟩, 0), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 3), (1, ⟨-3, -6⟩, 0), (1, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (3, ⟨-3, -6⟩, 5), (6, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (36, ⟨-1, -2⟩, 4), (36, ⟨-1, -2⟩, 5), (36, ⟨1, 2⟩, 1), (36, ⟨1, 2⟩, 2), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (24, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (3, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 3), (3, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 3), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (1, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row12_pairing_17 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_17)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (1, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 3), (24, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (24, ⟨-1, -2⟩, 3), (25, ⟨-1, -2⟩, 4), (25, ⟨-1, -2⟩, 5), (24, ⟨1, 2⟩, 0), (25, ⟨1, 2⟩, 1), (25, ⟨1, 2⟩, 2), (24, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (3, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row12_pairing_18 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_18)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 1), (1, ⟨-20, -40⟩, 2), (3, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (1, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (1, ⟨-5, -10⟩, 1), (1, ⟨-5, -10⟩, 2), (3, ⟨-5, -10⟩, 4), (3, ⟨-5, -10⟩, 5), (1, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 3), (6, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (24, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (6, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (24, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (1, ⟨3, 6⟩, 0), (1, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨5, 10⟩, 1), (3, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 5), (3, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 3), (1, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 5), (1, ⟨20, 40⟩, 4), (1, ⟨20, 40⟩, 5)]

theorem g32p_row12_pairing_19 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row12_terms_19)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row12_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 5), (3, ⟨-5, -10⟩, 0), (3, ⟨-5, -10⟩, 1), (3, ⟨-5, -10⟩, 3), (3, ⟨-5, -10⟩, 4), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (2, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (24, ⟨-1, -2⟩, 1), (21, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (24, ⟨-1, -2⟩, 4), (21, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (21, ⟨1, 2⟩, 1), (24, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (21, ⟨1, 2⟩, 4), (24, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (2, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (2, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (3, ⟨5, 10⟩, 0), (3, ⟨5, 10⟩, 2), (3, ⟨5, 10⟩, 3), (3, ⟨5, 10⟩, 5), (1, ⟨20, 40⟩, 1), (1, ⟨20, 40⟩, 4)]

theorem g32p_row12_pairing_20 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_20)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 2), (1, ⟨-24, -48⟩, 5), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 5), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (24, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (24, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 0), (24, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (24, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (2, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨24, 48⟩, 1), (1, ⟨24, 48⟩, 4)]

theorem g32p_row12_pairing_21 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_21)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row12_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row12_pairing_22 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_22)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 5), (1, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (4, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (3, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row12_pairing_23 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_23)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row12_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 3), (1, ⟨-6, -12⟩, 4), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (4, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (3, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (3, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (4, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (1, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 5), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row12_pairing_24 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_24)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 2), (1, ⟨-30, -60⟩, 5), (9, ⟨-3, -6⟩, 0), (9, ⟨-3, -6⟩, 1), (26, ⟨-3, -6⟩, 2), (9, ⟨-3, -6⟩, 3), (9, ⟨-3, -6⟩, 4), (26, ⟨-3, -6⟩, 5), (9, ⟨3, 6⟩, 0), (26, ⟨3, 6⟩, 1), (9, ⟨3, 6⟩, 2), (9, ⟨3, 6⟩, 3), (26, ⟨3, 6⟩, 4), (9, ⟨3, 6⟩, 5), (1, ⟨30, 60⟩, 1), (1, ⟨30, 60⟩, 4)]

theorem g32p_row12_pairing_25 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_25)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row12_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row12_pairing_26 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_26)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (1, ⟨36, 72⟩, 4), (1, ⟨36, 72⟩, 5)]

theorem g32p_row12_pairing_27 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_27)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 1), (1, ⟨-36, -72⟩, 2), (1, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (6, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (6, ⟨9, 18⟩, 4), (6, ⟨9, 18⟩, 5), (1, ⟨36, 72⟩, 4), (1, ⟨36, 72⟩, 5)]

theorem g32p_row12_pairing_28 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row12_terms_28)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row12_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-6, -12⟩, 0), (4, ⟨-6, -12⟩, 1), (4, ⟨-6, -12⟩, 2), (4, ⟨-6, -12⟩, 3), (4, ⟨-6, -12⟩, 4), (4, ⟨-6, -12⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (4, ⟨6, 12⟩, 0), (4, ⟨6, 12⟩, 1), (4, ⟨6, 12⟩, 2), (4, ⟨6, 12⟩, 3), (4, ⟨6, 12⟩, 4), (4, ⟨6, 12⟩, 5)]

theorem g32p_row12_pairing_29 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_29)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 2), (1, ⟨-40, -80⟩, 5), (3, ⟨-8, -16⟩, 0), (1, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 3), (1, ⟨-8, -16⟩, 4), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (3, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (3, ⟨-1, -2⟩, 0), (3, ⟨-1, -2⟩, 1), (60, ⟨-1, -2⟩, 2), (3, ⟨-1, -2⟩, 3), (3, ⟨-1, -2⟩, 4), (60, ⟨-1, -2⟩, 5), (3, ⟨1, 2⟩, 0), (60, ⟨1, 2⟩, 1), (3, ⟨1, 2⟩, 2), (3, ⟨1, 2⟩, 3), (60, ⟨1, 2⟩, 4), (3, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (6, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (6, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 5), (3, ⟨8, 16⟩, 0), (1, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (1, ⟨8, 16⟩, 5), (1, ⟨40, 80⟩, 1), (1, ⟨40, 80⟩, 4)]

theorem g32p_row12_pairing_30 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_30)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row12_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 2), (1, ⟨-40, -80⟩, 5), (1, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (1, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 5), (6, ⟨-2, -4⟩, 0), (1, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 3), (1, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (21, ⟨-1, -2⟩, 0), (21, ⟨-1, -2⟩, 1), (24, ⟨-1, -2⟩, 2), (21, ⟨-1, -2⟩, 3), (21, ⟨-1, -2⟩, 4), (24, ⟨-1, -2⟩, 5), (21, ⟨1, 2⟩, 0), (24, ⟨1, 2⟩, 1), (21, ⟨1, 2⟩, 2), (21, ⟨1, 2⟩, 3), (24, ⟨1, 2⟩, 4), (21, ⟨1, 2⟩, 5), (6, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (1, ⟨2, 4⟩, 2), (6, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 1), (1, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨8, 16⟩, 1), (1, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 5), (1, ⟨40, 80⟩, 1), (1, ⟨40, 80⟩, 4)]

theorem g32p_row12_pairing_31 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_31)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row12_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row12_pairing_32 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_32)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 2), (1, ⟨-45, -90⟩, 5), (4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (1, ⟨45, 90⟩, 1), (1, ⟨45, 90⟩, 4)]

theorem g32p_row12_pairing_33 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_33)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row12_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 2), (1, ⟨-45, -90⟩, 5), (1, ⟨-9, -18⟩, 0), (6, ⟨-9, -18⟩, 1), (1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (6, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 1), (6, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (1, ⟨9, 18⟩, 4), (6, ⟨9, 18⟩, 5), (1, ⟨45, 90⟩, 1), (1, ⟨45, 90⟩, 4)]

theorem g32p_row12_pairing_34 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_34)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(4, ⟨-9, -18⟩, 0), (4, ⟨-9, -18⟩, 1), (4, ⟨-9, -18⟩, 2), (4, ⟨-9, -18⟩, 3), (4, ⟨-9, -18⟩, 4), (4, ⟨-9, -18⟩, 5), (4, ⟨9, 18⟩, 0), (4, ⟨9, 18⟩, 1), (4, ⟨9, 18⟩, 2), (4, ⟨9, 18⟩, 3), (4, ⟨9, 18⟩, 4), (4, ⟨9, 18⟩, 5)]

theorem g32p_row12_pairing_35 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_35)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (1, ⟨-9, -18⟩, 0), (1, ⟨-9, -18⟩, 3), (3, ⟨-9, -18⟩, 4), (3, ⟨-9, -18⟩, 5), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 4), (3, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 1), (24, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 3), (24, ⟨3, 6⟩, 4), (24, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (3, ⟨9, 18⟩, 1), (3, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 3), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row12_pairing_36 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row12_terms_36)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row12_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (3, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-3, -6⟩, 0), (3, ⟨-3, -6⟩, 1), (3, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 0), (2, ⟨3, 6⟩, 1), (2, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (3, ⟨3, 6⟩, 4), (3, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 3), (3, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row12_pairing_37 :
    g32p_cyclotomicPairingCheck 486 (1)
      (g32p_pairingCoefficients 6 g32p_row12_terms_37)
      [1, -1, 1] [-486, -567, -162, 243, 324, 162] = true := by
  decide +kernel

def g32p_row12_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 1), (1, ⟨-60, -120⟩, 2), (1, ⟨-9, -18⟩, 0), (3, ⟨-9, -18⟩, 1), (3, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 3), (3, ⟨-6, -12⟩, 0), (1, ⟨-6, -12⟩, 1), (1, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-3, -6⟩, 0), (27, ⟨-3, -6⟩, 1), (27, ⟨-3, -6⟩, 2), (3, ⟨-3, -6⟩, 3), (4, ⟨-3, -6⟩, 4), (4, ⟨-3, -6⟩, 5), (3, ⟨3, 6⟩, 0), (4, ⟨3, 6⟩, 1), (4, ⟨3, 6⟩, 2), (3, ⟨3, 6⟩, 3), (27, ⟨3, 6⟩, 4), (27, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (3, ⟨6, 12⟩, 3), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 5), (1, ⟨9, 18⟩, 0), (1, ⟨9, 18⟩, 3), (3, ⟨9, 18⟩, 4), (3, ⟨9, 18⟩, 5), (1, ⟨60, 120⟩, 4), (1, ⟨60, 120⟩, 5)]

theorem g32p_row12_pairing_38 :
    g32p_cyclotomicPairingCheck 486 (2)
      (g32p_pairingCoefficients 6 g32p_row12_terms_38)
      [1, -1, 1] [-972, -1134, -324, 486, 648, 324] = true := by
  decide +kernel

def g32p_row12_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 5), (3, ⟨-6, -12⟩, 0), (3, ⟨-6, -12⟩, 1), (2, ⟨-6, -12⟩, 2), (3, ⟨-6, -12⟩, 3), (3, ⟨-6, -12⟩, 4), (2, ⟨-6, -12⟩, 5), (6, ⟨-3, -6⟩, 0), (24, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 3), (24, ⟨-3, -6⟩, 4), (6, ⟨-3, -6⟩, 5), (6, ⟨3, 6⟩, 0), (6, ⟨3, 6⟩, 1), (24, ⟨3, 6⟩, 2), (6, ⟨3, 6⟩, 3), (6, ⟨3, 6⟩, 4), (24, ⟨3, 6⟩, 5), (3, ⟨6, 12⟩, 0), (2, ⟨6, 12⟩, 1), (3, ⟨6, 12⟩, 2), (3, ⟨6, 12⟩, 3), (2, ⟨6, 12⟩, 4), (3, ⟨6, 12⟩, 5), (1, ⟨60, 120⟩, 1), (1, ⟨60, 120⟩, 4)]

theorem g32p_row12_pairing_39 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_39)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 5), (3, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (2, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 3), (3, ⟨-4, -8⟩, 4), (3, ⟨-2, -4⟩, 0), (24, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (24, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (24, ⟨2, 4⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 5), (3, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 4), (2, ⟨8, 16⟩, 5), (1, ⟨64, 128⟩, 1), (1, ⟨64, 128⟩, 4)]

theorem g32p_row12_pairing_40 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_40)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 1), (1, ⟨-64, -128⟩, 2), (3, ⟨-8, -16⟩, 0), (3, ⟨-8, -16⟩, 1), (3, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (2, ⟨-8, -16⟩, 4), (2, ⟨-8, -16⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 3), (3, ⟨-4, -8⟩, 4), (3, ⟨-4, -8⟩, 5), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 1), (3, ⟨-2, -4⟩, 2), (3, ⟨-2, -4⟩, 3), (24, ⟨-2, -4⟩, 4), (24, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 3), (18, ⟨-1, -2⟩, 4), (18, ⟨-1, -2⟩, 5), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 1), (18, ⟨1, 2⟩, 2), (18, ⟨1, 2⟩, 3), (3, ⟨2, 4⟩, 0), (24, ⟨2, 4⟩, 1), (24, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (3, ⟨2, 4⟩, 4), (3, ⟨2, 4⟩, 5), (3, ⟨4, 8⟩, 0), (3, ⟨4, 8⟩, 1), (3, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 3), (3, ⟨8, 16⟩, 0), (2, ⟨8, 16⟩, 1), (2, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (3, ⟨8, 16⟩, 4), (3, ⟨8, 16⟩, 5), (1, ⟨64, 128⟩, 4), (1, ⟨64, 128⟩, 5)]

theorem g32p_row12_pairing_41 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_41)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 1), (1, ⟨-80, -160⟩, 2), (3, ⟨-8, -16⟩, 0), (2, ⟨-8, -16⟩, 1), (2, ⟨-8, -16⟩, 2), (3, ⟨-8, -16⟩, 3), (3, ⟨-8, -16⟩, 4), (3, ⟨-8, -16⟩, 5), (3, ⟨-4, -8⟩, 0), (3, ⟨-4, -8⟩, 1), (3, ⟨-4, -8⟩, 2), (3, ⟨-4, -8⟩, 3), (24, ⟨-4, -8⟩, 4), (24, ⟨-4, -8⟩, 5), (3, ⟨-2, -4⟩, 0), (3, ⟨-2, -4⟩, 3), (3, ⟨-2, -4⟩, 4), (3, ⟨-2, -4⟩, 5), (18, ⟨-1, -2⟩, 0), (18, ⟨-1, -2⟩, 1), (18, ⟨-1, -2⟩, 2), (18, ⟨-1, -2⟩, 3), (18, ⟨1, 2⟩, 0), (18, ⟨1, 2⟩, 3), (18, ⟨1, 2⟩, 4), (18, ⟨1, 2⟩, 5), (3, ⟨2, 4⟩, 0), (3, ⟨2, 4⟩, 1), (3, ⟨2, 4⟩, 2), (3, ⟨2, 4⟩, 3), (3, ⟨4, 8⟩, 0), (24, ⟨4, 8⟩, 1), (24, ⟨4, 8⟩, 2), (3, ⟨4, 8⟩, 3), (3, ⟨4, 8⟩, 4), (3, ⟨4, 8⟩, 5), (3, ⟨8, 16⟩, 0), (3, ⟨8, 16⟩, 1), (3, ⟨8, 16⟩, 2), (3, ⟨8, 16⟩, 3), (2, ⟨8, 16⟩, 4), (2, ⟨8, 16⟩, 5), (1, ⟨80, 160⟩, 4), (1, ⟨80, 160⟩, 5)]

theorem g32p_row12_pairing_42 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_42)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 2), (1, ⟨-81, -162⟩, 5), (1, ⟨81, 162⟩, 1), (1, ⟨81, 162⟩, 4)]

theorem g32p_row12_pairing_43 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_43)
      [1, -1, 1] [0, 81, 0, 81, 0, -162] = true := by
  decide +kernel

def g32p_row12_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 1), (1, ⟨-20, 0⟩, 3), (1, ⟨-20, 0⟩, 5), (8, ⟨-7, 0⟩, 0), (8, ⟨-7, 0⟩, 2), (8, ⟨-7, 0⟩, 4), (36, ⟨-2, 0⟩, 1), (36, ⟨-2, 0⟩, 3), (36, ⟨-2, 0⟩, 5), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 2), (36, ⟨-1, 0⟩, 4), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 3), (36, ⟨1, 0⟩, 5), (36, ⟨2, 0⟩, 0), (36, ⟨2, 0⟩, 2), (36, ⟨2, 0⟩, 4), (8, ⟨7, 0⟩, 1), (8, ⟨7, 0⟩, 3), (8, ⟨7, 0⟩, 5), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 2), (1, ⟨20, 0⟩, 4)]

theorem g32p_row12_pairing_44 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_44)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 1), (1, ⟨-60, 0⟩, 3), (1, ⟨-60, 0⟩, 5), (6, ⟨-6, 0⟩, 0), (6, ⟨-6, 0⟩, 2), (6, ⟨-6, 0⟩, 4), (8, ⟨-3, 0⟩, 0), (8, ⟨-3, 0⟩, 2), (8, ⟨-3, 0⟩, 4), (8, ⟨3, 0⟩, 1), (8, ⟨3, 0⟩, 3), (8, ⟨3, 0⟩, 5), (6, ⟨6, 0⟩, 1), (6, ⟨6, 0⟩, 3), (6, ⟨6, 0⟩, 5), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 2), (1, ⟨60, 0⟩, 4)]

theorem g32p_row12_pairing_45 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_45)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 1), (1, ⟨-64, 0⟩, 3), (1, ⟨-64, 0⟩, 5), (8, ⟨-8, 0⟩, 0), (8, ⟨-8, 0⟩, 2), (8, ⟨-8, 0⟩, 4), (6, ⟨-4, 0⟩, 1), (6, ⟨-4, 0⟩, 3), (6, ⟨-4, 0⟩, 5), (30, ⟨-2, 0⟩, 0), (30, ⟨-2, 0⟩, 2), (30, ⟨-2, 0⟩, 4), (36, ⟨-1, 0⟩, 1), (36, ⟨-1, 0⟩, 3), (36, ⟨-1, 0⟩, 5), (36, ⟨1, 0⟩, 0), (36, ⟨1, 0⟩, 2), (36, ⟨1, 0⟩, 4), (30, ⟨2, 0⟩, 1), (30, ⟨2, 0⟩, 3), (30, ⟨2, 0⟩, 5), (6, ⟨4, 0⟩, 0), (6, ⟨4, 0⟩, 2), (6, ⟨4, 0⟩, 4), (8, ⟨8, 0⟩, 1), (8, ⟨8, 0⟩, 3), (8, ⟨8, 0⟩, 5), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 2), (1, ⟨64, 0⟩, 4)]

theorem g32p_row12_pairing_46 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_46)
      [1, -1, 1] [] = true := by
  decide +kernel

def g32p_row12_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 1), (1, ⟨-80, 0⟩, 3), (1, ⟨-80, 0⟩, 5), (8, ⟨-8, 0⟩, 1), (8, ⟨-8, 0⟩, 3), (8, ⟨-8, 0⟩, 5), (30, ⟨-4, 0⟩, 0), (30, ⟨-4, 0⟩, 2), (30, ⟨-4, 0⟩, 4), (6, ⟨-2, 0⟩, 1), (6, ⟨-2, 0⟩, 3), (6, ⟨-2, 0⟩, 5), (36, ⟨-1, 0⟩, 0), (36, ⟨-1, 0⟩, 2), (36, ⟨-1, 0⟩, 4), (36, ⟨1, 0⟩, 1), (36, ⟨1, 0⟩, 3), (36, ⟨1, 0⟩, 5), (6, ⟨2, 0⟩, 0), (6, ⟨2, 0⟩, 2), (6, ⟨2, 0⟩, 4), (30, ⟨4, 0⟩, 1), (30, ⟨4, 0⟩, 3), (30, ⟨4, 0⟩, 5), (8, ⟨8, 0⟩, 0), (8, ⟨8, 0⟩, 2), (8, ⟨8, 0⟩, 4), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 2), (1, ⟨80, 0⟩, 4)]

theorem g32p_row12_pairing_47 :
    g32p_cyclotomicPairingCheck 486 (0)
      (g32p_pairingCoefficients 6 g32p_row12_terms_47)
      [1, -1, 1] [] = true := by
  decide +kernel

theorem g32p_row12_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 12 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨12, -2, [(4, 1), (16, 1), (20, 1), (29, 1), (37, 1), (38, 1), (39, 2)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row13_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_0 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_0)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 10), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4)]

theorem g32p_row13_pairing_1 :
    g32p_cyclotomicPairingCheck 24 (-1)
      (g32p_pairingCoefficients 12 g32p_row13_terms_1)
      [1, 0, -1, 0, 1] [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8] = true := by
  decide +kernel

def g32p_row13_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 8), (1, ⟨1, 2⟩, 10), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 8), (1, ⟨3, 6⟩, 10)]

theorem g32p_row13_pairing_2 :
    g32p_cyclotomicPairingCheck 24 (1)
      (g32p_pairingCoefficients 12 g32p_row13_terms_2)
      [1, 0, -1, 0, 1] [-24, 0, -28, 0, -8, 0, 12, 0, 16, 0, 8] = true := by
  decide +kernel

def g32p_row13_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 10), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4)]

theorem g32p_row13_pairing_3 :
    g32p_cyclotomicPairingCheck 24 (-1)
      (g32p_pairingCoefficients 12 g32p_row13_terms_3)
      [1, 0, -1, 0, 1] [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8] = true := by
  decide +kernel

def g32p_row13_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 10), (2, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨1, 2⟩, 4), (2, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 10), (2, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 8)]

theorem g32p_row13_pairing_4 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_4)
      [1, 0, -1, 0, 1] [0, -2, 2, -2, 0, -2, 2, -2, 0, 4, -4, 4] = true := by
  decide +kernel

def g32p_row13_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 10), (2, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨1, 2⟩, 4), (2, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 10), (2, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 8)]

theorem g32p_row13_pairing_5 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_5)
      [1, 0, -1, 0, 1] [0, -2, 2, -2, 0, -2, 2, -2, 0, 4, -4, 4] = true := by
  decide +kernel

def g32p_row13_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 8), (1, ⟨-1, -2⟩, 4), (2, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 10), (2, ⟨-1, -2⟩, 11), (2, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 8), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 10)]

theorem g32p_row13_pairing_6 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_6)
      [1, 0, -1, 0, 1] [0, 2, -2, 2, 0, 2, -2, 2, 0, -4, 4, -4] = true := by
  decide +kernel

def g32p_row13_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_7 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_7)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 8), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 7), (2, ⟨1, 2⟩, 5), (2, ⟨1, 2⟩, 11), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 10)]

theorem g32p_row13_pairing_8 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_8)
      [1, 0, -1, 0, 1] [0, -2, -6, -2, 0, -2, -6, -2, 0, 4, 12, 4] = true := by
  decide +kernel

def g32p_row13_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 8), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 7), (2, ⟨1, 2⟩, 5), (2, ⟨1, 2⟩, 11), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 10)]

theorem g32p_row13_pairing_9 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_9)
      [1, 0, -1, 0, 1] [0, -2, -6, -2, 0, -2, -6, -2, 0, 4, 12, 4] = true := by
  decide +kernel

def g32p_row13_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 10), (2, ⟨-1, -2⟩, 5), (2, ⟨-1, -2⟩, 11), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 7), (2, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 8)]

theorem g32p_row13_pairing_10 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_10)
      [1, 0, -1, 0, 1] [0, 2, 6, 2, 0, 2, 6, 2, 0, -4, -12, -4] = true := by
  decide +kernel

def g32p_row13_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_11 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_11)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_12 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_12)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 8), (1, ⟨3, 6⟩, 10)]

theorem g32p_row13_pairing_13 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_13)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 8), (1, ⟨-6, -12⟩, 10), (1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨2, 4⟩, 8), (1, ⟨2, 4⟩, 10), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 4)]

theorem g32p_row13_pairing_14 :
    g32p_cyclotomicPairingCheck 24 (-1)
      (g32p_pairingCoefficients 12 g32p_row13_terms_14)
      [1, 0, -1, 0, 1] [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8] = true := by
  decide +kernel

def g32p_row13_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_15 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_15)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 8), (1, ⟨-6, -12⟩, 10), (1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨2, 4⟩, 8), (1, ⟨2, 4⟩, 10), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 4)]

theorem g32p_row13_pairing_16 :
    g32p_cyclotomicPairingCheck 24 (-1)
      (g32p_pairingCoefficients 12 g32p_row13_terms_16)
      [1, 0, -1, 0, 1] [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8] = true := by
  decide +kernel

def g32p_row13_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 8), (1, ⟨3, 6⟩, 10)]

theorem g32p_row13_pairing_17 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_17)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 4), (1, ⟨-2, -4⟩, 8), (1, ⟨-2, -4⟩, 10), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨6, 12⟩, 8), (1, ⟨6, 12⟩, 10)]

theorem g32p_row13_pairing_18 :
    g32p_cyclotomicPairingCheck 24 (1)
      (g32p_pairingCoefficients 12 g32p_row13_terms_18)
      [1, 0, -1, 0, 1] [-24, 0, -28, 0, -8, 0, 12, 0, 16, 0, 8] = true := by
  decide +kernel

def g32p_row13_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 8), (1, ⟨3, 6⟩, 10)]

theorem g32p_row13_pairing_19 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_19)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_20 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_20)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_21 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_21)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 10), (2, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 4), (2, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 10), (1, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 8), (2, ⟨1, 2⟩, 11), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 8)]

theorem g32p_row13_pairing_22 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_22)
      [1, 0, -1, 0, 1] [0, -2, 10, -2, 0, -2, 10, -2, 0, 4, -20, 4] = true := by
  decide +kernel

def g32p_row13_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 8), (1, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 8), (2, ⟨-1, -2⟩, 11), (2, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 4), (2, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 10), (1, ⟨9, 18⟩, 4), (1, ⟨9, 18⟩, 10)]

theorem g32p_row13_pairing_23 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_23)
      [1, 0, -1, 0, 1] [0, 2, -10, 2, 0, 2, -10, 2, 0, -4, 20, -4] = true := by
  decide +kernel

def g32p_row13_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 10), (2, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 4), (2, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 10), (1, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 8), (2, ⟨1, 2⟩, 11), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 8)]

theorem g32p_row13_pairing_24 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_24)
      [1, 0, -1, 0, 1] [0, -2, 10, -2, 0, -2, 10, -2, 0, 4, -20, 4] = true := by
  decide +kernel

def g32p_row13_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_25 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_25)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 8), (1, ⟨-9, -18⟩, 10), (1, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 4)]

theorem g32p_row13_pairing_26 :
    g32p_cyclotomicPairingCheck 24 (-3)
      (g32p_pairingCoefficients 12 g32p_row13_terms_26)
      [1, 0, -1, 0, 1] [72, 0, 84, 0, 24, 0, -36, 0, -48, 0, -24] = true := by
  decide +kernel

def g32p_row13_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 4), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 8), (1, ⟨3, 6⟩, 10), (1, ⟨9, 18⟩, 8), (1, ⟨9, 18⟩, 10)]

theorem g32p_row13_pairing_27 :
    g32p_cyclotomicPairingCheck 24 (3)
      (g32p_pairingCoefficients 12 g32p_row13_terms_27)
      [1, 0, -1, 0, 1] [-72, 0, -84, 0, -24, 0, 36, 0, 48, 0, 24] = true := by
  decide +kernel

def g32p_row13_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 8), (1, ⟨-9, -18⟩, 10), (1, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 4)]

theorem g32p_row13_pairing_28 :
    g32p_cyclotomicPairingCheck 24 (-3)
      (g32p_pairingCoefficients 12 g32p_row13_terms_28)
      [1, 0, -1, 0, 1] [72, 0, 84, 0, 24, 0, -36, 0, -48, 0, -24] = true := by
  decide +kernel

def g32p_row13_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 10), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 10), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 8), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 8)]

theorem g32p_row13_pairing_29 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_29)
      [1, 0, -1, 0, 1] [0, 0, 8, 0, 0, 0, 8, 0, 0, 0, -16] = true := by
  decide +kernel

def g32p_row13_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 10), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 10), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 8), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 8)]

theorem g32p_row13_pairing_30 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_30)
      [1, 0, -1, 0, 1] [0, 0, 8, 0, 0, 0, 8, 0, 0, 0, -16] = true := by
  decide +kernel

def g32p_row13_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 8), (1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 8), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 10), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 10)]

theorem g32p_row13_pairing_31 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_31)
      [1, 0, -1, 0, 1] [0, 0, -8, 0, 0, 0, -8, 0, 0, 0, 16] = true := by
  decide +kernel

def g32p_row13_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 10), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 8), (2, ⟨-1, -2⟩, 5), (2, ⟨-1, -2⟩, 11), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 7), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 10), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 8)]

theorem g32p_row13_pairing_32 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_32)
      [1, 0, -1, 0, 1] [0, 2, 6, 2, 0, 2, 6, 2, 0, -4, -12, -4] = true := by
  decide +kernel

def g32p_row13_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 8), (1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 10), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 7), (2, ⟨1, 2⟩, 5), (2, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 8), (1, ⟨9, 18⟩, 4), (1, ⟨9, 18⟩, 10)]

theorem g32p_row13_pairing_33 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_33)
      [1, 0, -1, 0, 1] [0, -2, -6, -2, 0, -2, -6, -2, 0, 4, 12, 4] = true := by
  decide +kernel

def g32p_row13_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 10), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 8), (2, ⟨-1, -2⟩, 5), (2, ⟨-1, -2⟩, 11), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 7), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 10), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 8)]

theorem g32p_row13_pairing_34 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_34)
      [1, 0, -1, 0, 1] [0, 2, 6, 2, 0, 2, 6, 2, 0, -4, -12, -4] = true := by
  decide +kernel

def g32p_row13_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 4), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 10), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨9, 18⟩, 8), (1, ⟨9, 18⟩, 10)]

theorem g32p_row13_pairing_35 :
    g32p_cyclotomicPairingCheck 24 (2)
      (g32p_pairingCoefficients 12 g32p_row13_terms_35)
      [1, 0, -1, 0, 1] [-48, 0, -56, 0, -16, 0, 24, 0, 32, 0, 16] = true := by
  decide +kernel

def g32p_row13_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 4), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 10), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨9, 18⟩, 8), (1, ⟨9, 18⟩, 10)]

theorem g32p_row13_pairing_36 :
    g32p_cyclotomicPairingCheck 24 (2)
      (g32p_pairingCoefficients 12 g32p_row13_terms_36)
      [1, 0, -1, 0, 1] [-48, 0, -56, 0, -16, 0, 24, 0, 32, 0, 16] = true := by
  decide +kernel

def g32p_row13_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_37 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_37)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 8), (1, ⟨-9, -18⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 8), (1, ⟨1, 2⟩, 10), (1, ⟨1, 2⟩, 11), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 4)]

theorem g32p_row13_pairing_38 :
    g32p_cyclotomicPairingCheck 24 (-2)
      (g32p_pairingCoefficients 12 g32p_row13_terms_38)
      [1, 0, -1, 0, 1] [48, 0, 56, 0, 16, 0, -24, 0, -32, 0, -16] = true := by
  decide +kernel

def g32p_row13_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_39 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_39)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_40 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_40)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_41 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_41)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_42 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_42)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row13_pairing_43 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row13_terms_43)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row13_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 6), (1, ⟨-7, 0⟩, 4), (1, ⟨-7, 0⟩, 8), (1, ⟨-3, 0⟩, 2), (1, ⟨-3, 0⟩, 10), (1, ⟨-2, 0⟩, 3), (1, ⟨-2, 0⟩, 9), (1, ⟨-1, 0⟩, 1), (1, ⟨-1, 0⟩, 5), (1, ⟨-1, 0⟩, 7), (1, ⟨-1, 0⟩, 11), (1, ⟨1, 0⟩, 1), (1, ⟨1, 0⟩, 5), (1, ⟨1, 0⟩, 7), (1, ⟨1, 0⟩, 11), (1, ⟨2, 0⟩, 3), (1, ⟨2, 0⟩, 9), (1, ⟨3, 0⟩, 4), (1, ⟨3, 0⟩, 8), (1, ⟨7, 0⟩, 2), (1, ⟨7, 0⟩, 10), (1, ⟨20, 0⟩, 0)]

theorem g32p_row13_pairing_44 :
    g32p_cyclotomicPairingCheck 24 (2)
      (g32p_pairingCoefficients 12 g32p_row13_terms_44)
      [1, 0, -1, 0, 1] [-28, 0, -24, 0, 0, 0, 4] = true := by
  decide +kernel

def g32p_row13_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 6), (1, ⟨-3, 0⟩, 2), (1, ⟨-3, 0⟩, 4), (1, ⟨-3, 0⟩, 8), (1, ⟨-3, 0⟩, 10), (1, ⟨-2, 0⟩, 3), (1, ⟨-2, 0⟩, 9), (1, ⟨-1, 0⟩, 1), (1, ⟨-1, 0⟩, 5), (1, ⟨-1, 0⟩, 7), (1, ⟨-1, 0⟩, 11), (1, ⟨1, 0⟩, 1), (1, ⟨1, 0⟩, 5), (1, ⟨1, 0⟩, 7), (1, ⟨1, 0⟩, 11), (1, ⟨2, 0⟩, 3), (1, ⟨2, 0⟩, 9), (1, ⟨3, 0⟩, 2), (1, ⟨3, 0⟩, 4), (1, ⟨3, 0⟩, 8), (1, ⟨3, 0⟩, 10), (1, ⟨60, 0⟩, 0)]

theorem g32p_row13_pairing_45 :
    g32p_cyclotomicPairingCheck 24 (5)
      (g32p_pairingCoefficients 12 g32p_row13_terms_45)
      [1, 0, -1, 0, 1] [-60, 0, -60] = true := by
  decide +kernel

def g32p_row13_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 6), (1, ⟨-8, 0⟩, 4), (1, ⟨-8, 0⟩, 8), (1, ⟨8, 0⟩, 2), (1, ⟨8, 0⟩, 10), (1, ⟨64, 0⟩, 0)]

theorem g32p_row13_pairing_46 :
    g32p_cyclotomicPairingCheck 24 (6)
      (g32p_pairingCoefficients 12 g32p_row13_terms_46)
      [1, 0, -1, 0, 1] [-80, 0, -72, 0, 0, 0, 8] = true := by
  decide +kernel

def g32p_row13_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 6), (1, ⟨-8, 0⟩, 2), (1, ⟨-8, 0⟩, 10), (1, ⟨8, 0⟩, 4), (1, ⟨8, 0⟩, 8), (1, ⟨80, 0⟩, 0)]

theorem g32p_row13_pairing_47 :
    g32p_cyclotomicPairingCheck 24 (6)
      (g32p_pairingCoefficients 12 g32p_row13_terms_47)
      [1, 0, -1, 0, 1] [-64, 0, -72, 0, 0, 0, -8] = true := by
  decide +kernel

theorem g32p_row13_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 13 ∧ g32SparseVec v.coords =
        (![0, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -3, 3, -3, 0, 0, 0, 0, 0, 0, 2, 2, 0, -2, 0, 0, 0, 0, 0],
         ![2, 5, 6, 6]) := by
  refine ⟨⟨13, -1, [(2, -1), (3, 1), (4, -1), (15, -1), (17, -1), (19, 1), (27, -3), (28, 3), (29, -3), (36, 2), (37, 2), (39, -2), (46, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row14_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 4), (2, ⟨-1, -2⟩, 7), (2, ⟨-1, -2⟩, 10), (2, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 5), (2, ⟨1, 2⟩, 8), (2, ⟨1, 2⟩, 11)]

theorem g32p_row14_pairing_0 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_0)
      [1, 0, -1, 0, 1] [0, -2, 2, -2, 0, -2, 2, -2, 0, 4, -4, 4] = true := by
  decide +kernel

def g32p_row14_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 10), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4)]

theorem g32p_row14_pairing_1 :
    g32p_cyclotomicPairingCheck 24 (-1)
      (g32p_pairingCoefficients 12 g32p_row14_terms_1)
      [1, 0, -1, 0, 1] [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8] = true := by
  decide +kernel

def g32p_row14_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-2, -4⟩, 8), (2, ⟨-2, -4⟩, 10), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4)]

theorem g32p_row14_pairing_2 :
    g32p_cyclotomicPairingCheck 24 (-1)
      (g32p_pairingCoefficients 12 g32p_row14_terms_2)
      [1, 0, -1, 0, 1] [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8] = true := by
  decide +kernel

def g32p_row14_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 10), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 8), (1, ⟨1, 2⟩, 10), (1, ⟨1, 2⟩, 11)]

theorem g32p_row14_pairing_3 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_3)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row14_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 10), (2, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨1, 2⟩, 4), (2, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 10), (2, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 8)]

theorem g32p_row14_pairing_4 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_4)
      [1, 0, -1, 0, 1] [0, -2, 2, -2, 0, -2, 2, -2, 0, 4, -4, 4] = true := by
  decide +kernel

def g32p_row14_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 5), (2, ⟨-1, -2⟩, 8), (2, ⟨-1, -2⟩, 11), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 4), (2, ⟨1, 2⟩, 7), (2, ⟨1, 2⟩, 10)]

theorem g32p_row14_pairing_5 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_5)
      [1, 0, -1, 0, 1] [0, 2, -2, 2, 0, 2, -2, 2, 0, -4, 4, -4] = true := by
  decide +kernel

def g32p_row14_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 8), (1, ⟨-2, -4⟩, 10), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 8), (1, ⟨2, 4⟩, 10)]

theorem g32p_row14_pairing_6 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_6)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row14_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 8), (1, ⟨-1, -2⟩, 4), (2, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 10), (2, ⟨-1, -2⟩, 11), (2, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 8), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 10)]

theorem g32p_row14_pairing_7 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_7)
      [1, 0, -1, 0, 1] [0, 2, -2, 2, 0, 2, -2, 2, 0, -4, 4, -4] = true := by
  decide +kernel

def g32p_row14_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(2, ⟨-3, -6⟩, 2), (2, ⟨-3, -6⟩, 8), (2, ⟨-1, -2⟩, 1), (2, ⟨-1, -2⟩, 7), (2, ⟨1, 2⟩, 5), (2, ⟨1, 2⟩, 11), (2, ⟨3, 6⟩, 4), (2, ⟨3, 6⟩, 10)]

theorem g32p_row14_pairing_8 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_8)
      [1, 0, -1, 0, 1] [0, -2, -6, -2, 0, -2, -6, -2, 0, 4, 12, 4] = true := by
  decide +kernel

def g32p_row14_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 8), (1, ⟨-2, -4⟩, 10), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 8), (1, ⟨2, 4⟩, 10)]

theorem g32p_row14_pairing_9 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_9)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row14_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 8), (2, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨1, 2⟩, 4), (2, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 10), (2, ⟨1, 2⟩, 11), (1, ⟨5, 10⟩, 4), (1, ⟨5, 10⟩, 10)]

theorem g32p_row14_pairing_10 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_10)
      [1, 0, -1, 0, 1] [0, -2, -6, -2, 0, -2, -6, -2, 0, 4, 12, 4] = true := by
  decide +kernel

def g32p_row14_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 8), (1, ⟨-1, -2⟩, 4), (2, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 10), (2, ⟨-1, -2⟩, 11), (2, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 8), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 10)]

theorem g32p_row14_pairing_11 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_11)
      [1, 0, -1, 0, 1] [0, 2, -2, 2, 0, 2, -2, 2, 0, -4, 4, -4] = true := by
  decide +kernel

def g32p_row14_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 10), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 10), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 8), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 8)]

theorem g32p_row14_pairing_12 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_12)
      [1, 0, -1, 0, 1] [0, 0, 8, 0, 0, 0, 8, 0, 0, 0, -16] = true := by
  decide +kernel

def g32p_row14_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 8), (1, ⟨3, 6⟩, 10)]

theorem g32p_row14_pairing_13 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_13)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row14_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 8), (1, ⟨-6, -12⟩, 10), (1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨2, 4⟩, 8), (1, ⟨2, 4⟩, 10), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 4)]

theorem g32p_row14_pairing_14 :
    g32p_cyclotomicPairingCheck 24 (-1)
      (g32p_pairingCoefficients 12 g32p_row14_terms_14)
      [1, 0, -1, 0, 1] [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8] = true := by
  decide +kernel

def g32p_row14_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-7, -14⟩, 8), (1, ⟨-7, -14⟩, 10), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 8), (1, ⟨3, 6⟩, 10), (1, ⟨7, 14⟩, 2), (1, ⟨7, 14⟩, 4)]

theorem g32p_row14_pairing_15 :
    g32p_cyclotomicPairingCheck 24 (-1)
      (g32p_pairingCoefficients 12 g32p_row14_terms_15)
      [1, 0, -1, 0, 1] [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8] = true := by
  decide +kernel

def g32p_row14_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 4), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 10), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨5, 10⟩, 8), (1, ⟨5, 10⟩, 10)]

theorem g32p_row14_pairing_16 :
    g32p_cyclotomicPairingCheck 24 (1)
      (g32p_pairingCoefficients 12 g32p_row14_terms_16)
      [1, 0, -1, 0, 1] [-24, 0, -28, 0, -8, 0, 12, 0, 16, 0, 8] = true := by
  decide +kernel

def g32p_row14_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 2), (1, ⟨-5, -10⟩, 4), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 8), (1, ⟨3, 6⟩, 10), (1, ⟨5, 10⟩, 8), (1, ⟨5, 10⟩, 10)]

theorem g32p_row14_pairing_17 :
    g32p_cyclotomicPairingCheck 24 (2)
      (g32p_pairingCoefficients 12 g32p_row14_terms_17)
      [1, 0, -1, 0, 1] [-48, 0, -56, 0, -16, 0, 24, 0, 32, 0, 16] = true := by
  decide +kernel

def g32p_row14_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (1, ⟨-1, -2⟩, 4), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 10), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 8), (1, ⟨1, 2⟩, 10), (1, ⟨1, 2⟩, 11)]

theorem g32p_row14_pairing_18 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_18)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row14_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 4), (1, ⟨8, 16⟩, 8), (1, ⟨8, 16⟩, 10)]

theorem g32p_row14_pairing_19 :
    g32p_cyclotomicPairingCheck 24 (2)
      (g32p_pairingCoefficients 12 g32p_row14_terms_19)
      [1, 0, -1, 0, 1] [-48, 0, -56, 0, -16, 0, 24, 0, 32, 0, 16] = true := by
  decide +kernel

def g32p_row14_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 8), (1, ⟨-2, -4⟩, 10), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 8), (1, ⟨2, 4⟩, 10)]

theorem g32p_row14_pairing_20 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_20)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row14_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 10), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 10), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 8), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 8)]

theorem g32p_row14_pairing_21 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_21)
      [1, 0, -1, 0, 1] [0, 0, 8, 0, 0, 0, 8, 0, 0, 0, -16] = true := by
  decide +kernel

def g32p_row14_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 10), (2, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 4), (2, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 10), (1, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 8), (2, ⟨1, 2⟩, 11), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 8)]

theorem g32p_row14_pairing_22 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_22)
      [1, 0, -1, 0, 1] [0, -2, 10, -2, 0, -2, 10, -2, 0, 4, -20, 4] = true := by
  decide +kernel

def g32p_row14_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 10), (2, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨1, 2⟩, 4), (2, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 10), (2, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 8)]

theorem g32p_row14_pairing_23 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_23)
      [1, 0, -1, 0, 1] [0, -2, 2, -2, 0, -2, 2, -2, 0, 4, -4, 4] = true := by
  decide +kernel

def g32p_row14_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 8), (1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 8), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 10), (1, ⟨6, 12⟩, 4), (1, ⟨6, 12⟩, 10)]

theorem g32p_row14_pairing_24 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_24)
      [1, 0, -1, 0, 1] [0, 0, -8, 0, 0, 0, -8, 0, 0, 0, 16] = true := by
  decide +kernel

def g32p_row14_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 10), (2, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨1, 2⟩, 4), (2, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 10), (2, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 8)]

theorem g32p_row14_pairing_25 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_25)
      [1, 0, -1, 0, 1] [0, -2, 2, -2, 0, -2, 2, -2, 0, 4, -4, 4] = true := by
  decide +kernel

def g32p_row14_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 8), (1, ⟨-9, -18⟩, 10), (1, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 4)]

theorem g32p_row14_pairing_26 :
    g32p_cyclotomicPairingCheck 24 (-3)
      (g32p_pairingCoefficients 12 g32p_row14_terms_26)
      [1, 0, -1, 0, 1] [72, 0, 84, 0, 24, 0, -36, 0, -48, 0, -24] = true := by
  decide +kernel

def g32p_row14_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 8), (1, ⟨-9, -18⟩, 10), (1, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 4)]

theorem g32p_row14_pairing_27 :
    g32p_cyclotomicPairingCheck 24 (-3)
      (g32p_pairingCoefficients 12 g32p_row14_terms_27)
      [1, 0, -1, 0, 1] [72, 0, 84, 0, 24, 0, -36, 0, -48, 0, -24] = true := by
  decide +kernel

def g32p_row14_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row14_pairing_28 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_28)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row14_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 10), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 10), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 8), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 8)]

theorem g32p_row14_pairing_29 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_29)
      [1, 0, -1, 0, 1] [0, 0, 8, 0, 0, 0, 8, 0, 0, 0, -16] = true := by
  decide +kernel

def g32p_row14_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 8), (1, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 10)]

theorem g32p_row14_pairing_30 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_30)
      [1, 0, -1, 0, 1] [0, 0, -8, 0, 0, 0, -8, 0, 0, 0, 16] = true := by
  decide +kernel

def g32p_row14_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-2, -4⟩, 2), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 8), (1, ⟨-2, -4⟩, 10), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 8), (1, ⟨2, 4⟩, 10)]

theorem g32p_row14_pairing_31 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_31)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row14_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 10), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 8), (2, ⟨-1, -2⟩, 5), (2, ⟨-1, -2⟩, 11), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 7), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 10), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 8)]

theorem g32p_row14_pairing_32 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_32)
      [1, 0, -1, 0, 1] [0, 2, 6, 2, 0, 2, 6, 2, 0, -4, -12, -4] = true := by
  decide +kernel

def g32p_row14_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 10), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 8), (2, ⟨-1, -2⟩, 5), (2, ⟨-1, -2⟩, 11), (2, ⟨1, 2⟩, 1), (2, ⟨1, 2⟩, 7), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 10), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 8)]

theorem g32p_row14_pairing_33 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_33)
      [1, 0, -1, 0, 1] [0, 2, 6, 2, 0, 2, 6, 2, 0, -4, -12, -4] = true := by
  decide +kernel

def g32p_row14_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row14_pairing_34 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_34)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row14_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-9, -18⟩, 2), (1, ⟨-9, -18⟩, 4), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 10), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨9, 18⟩, 8), (1, ⟨9, 18⟩, 10)]

theorem g32p_row14_pairing_35 :
    g32p_cyclotomicPairingCheck 24 (2)
      (g32p_pairingCoefficients 12 g32p_row14_terms_35)
      [1, 0, -1, 0, 1] [-48, 0, -56, 0, -16, 0, 24, 0, 32, 0, 16] = true := by
  decide +kernel

def g32p_row14_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 8), (1, ⟨-1, -2⟩, 10), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 2), (1, ⟨1, 2⟩, 4), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4)]

theorem g32p_row14_pairing_36 :
    g32p_cyclotomicPairingCheck 24 (-1)
      (g32p_pairingCoefficients 12 g32p_row14_terms_36)
      [1, 0, -1, 0, 1] [24, 0, 28, 0, 8, 0, -12, 0, -16, 0, -8] = true := by
  decide +kernel

def g32p_row14_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 4), (1, ⟨-3, -6⟩, 8), (1, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 1), (1, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 7), (1, ⟨-1, -2⟩, 11), (1, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 5), (1, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 2), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 8), (1, ⟨3, 6⟩, 10)]

theorem g32p_row14_pairing_37 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_37)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row14_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 2), (1, ⟨-6, -12⟩, 4), (1, ⟨-2, -4⟩, 8), (1, ⟨-2, -4⟩, 10), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (1, ⟨6, 12⟩, 8), (1, ⟨6, 12⟩, 10)]

theorem g32p_row14_pairing_38 :
    g32p_cyclotomicPairingCheck 24 (1)
      (g32p_pairingCoefficients 12 g32p_row14_terms_38)
      [1, 0, -1, 0, 1] [-24, 0, -28, 0, -8, 0, 12, 0, 16, 0, 8] = true := by
  decide +kernel

def g32p_row14_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 10), (1, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 10), (1, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 8), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 8)]

theorem g32p_row14_pairing_39 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_39)
      [1, 0, -1, 0, 1] [0, 0, 8, 0, 0, 0, 8, 0, 0, 0, -16] = true := by
  decide +kernel

def g32p_row14_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 8), (1, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 10)]

theorem g32p_row14_pairing_40 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_40)
      [1, 0, -1, 0, 1] [0, 0, -8, 0, 0, 0, -8, 0, 0, 0, 16] = true := by
  decide +kernel

def g32p_row14_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-8, -16⟩, 8), (1, ⟨-8, -16⟩, 10), (1, ⟨8, 16⟩, 2), (1, ⟨8, 16⟩, 4)]

theorem g32p_row14_pairing_41 :
    g32p_cyclotomicPairingCheck 24 (-2)
      (g32p_pairingCoefficients 12 g32p_row14_terms_41)
      [1, 0, -1, 0, 1] [48, 0, 56, 0, 16, 0, -24, 0, -32, 0, -16] = true := by
  decide +kernel

def g32p_row14_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 4), (1, ⟨8, 16⟩, 8), (1, ⟨8, 16⟩, 10)]

theorem g32p_row14_pairing_42 :
    g32p_cyclotomicPairingCheck 24 (2)
      (g32p_pairingCoefficients 12 g32p_row14_terms_42)
      [1, 0, -1, 0, 1] [-48, 0, -56, 0, -16, 0, 24, 0, 32, 0, 16] = true := by
  decide +kernel

def g32p_row14_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row14_pairing_43 :
    g32p_cyclotomicPairingCheck 24 (0)
      (g32p_pairingCoefficients 12 g32p_row14_terms_43)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row14_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 6), (1, ⟨-7, 0⟩, 4), (1, ⟨-7, 0⟩, 8), (1, ⟨-3, 0⟩, 2), (1, ⟨-3, 0⟩, 10), (1, ⟨-2, 0⟩, 3), (1, ⟨-2, 0⟩, 9), (1, ⟨-1, 0⟩, 1), (1, ⟨-1, 0⟩, 5), (1, ⟨-1, 0⟩, 7), (1, ⟨-1, 0⟩, 11), (1, ⟨1, 0⟩, 1), (1, ⟨1, 0⟩, 5), (1, ⟨1, 0⟩, 7), (1, ⟨1, 0⟩, 11), (1, ⟨2, 0⟩, 3), (1, ⟨2, 0⟩, 9), (1, ⟨3, 0⟩, 4), (1, ⟨3, 0⟩, 8), (1, ⟨7, 0⟩, 2), (1, ⟨7, 0⟩, 10), (1, ⟨20, 0⟩, 0)]

theorem g32p_row14_pairing_44 :
    g32p_cyclotomicPairingCheck 24 (2)
      (g32p_pairingCoefficients 12 g32p_row14_terms_44)
      [1, 0, -1, 0, 1] [-28, 0, -24, 0, 0, 0, 4] = true := by
  decide +kernel

def g32p_row14_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 6), (1, ⟨-3, 0⟩, 2), (1, ⟨-3, 0⟩, 4), (1, ⟨-3, 0⟩, 8), (1, ⟨-3, 0⟩, 10), (1, ⟨-2, 0⟩, 3), (1, ⟨-2, 0⟩, 9), (1, ⟨-1, 0⟩, 1), (1, ⟨-1, 0⟩, 5), (1, ⟨-1, 0⟩, 7), (1, ⟨-1, 0⟩, 11), (1, ⟨1, 0⟩, 1), (1, ⟨1, 0⟩, 5), (1, ⟨1, 0⟩, 7), (1, ⟨1, 0⟩, 11), (1, ⟨2, 0⟩, 3), (1, ⟨2, 0⟩, 9), (1, ⟨3, 0⟩, 2), (1, ⟨3, 0⟩, 4), (1, ⟨3, 0⟩, 8), (1, ⟨3, 0⟩, 10), (1, ⟨60, 0⟩, 0)]

theorem g32p_row14_pairing_45 :
    g32p_cyclotomicPairingCheck 24 (5)
      (g32p_pairingCoefficients 12 g32p_row14_terms_45)
      [1, 0, -1, 0, 1] [-60, 0, -60] = true := by
  decide +kernel

def g32p_row14_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 6), (1, ⟨-8, 0⟩, 4), (1, ⟨-8, 0⟩, 8), (1, ⟨8, 0⟩, 2), (1, ⟨8, 0⟩, 10), (1, ⟨64, 0⟩, 0)]

theorem g32p_row14_pairing_46 :
    g32p_cyclotomicPairingCheck 24 (6)
      (g32p_pairingCoefficients 12 g32p_row14_terms_46)
      [1, 0, -1, 0, 1] [-80, 0, -72, 0, 0, 0, 8] = true := by
  decide +kernel

def g32p_row14_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 6), (1, ⟨-8, 0⟩, 2), (1, ⟨-8, 0⟩, 10), (1, ⟨8, 0⟩, 4), (1, ⟨8, 0⟩, 8), (1, ⟨80, 0⟩, 0)]

theorem g32p_row14_pairing_47 :
    g32p_cyclotomicPairingCheck 24 (6)
      (g32p_pairingCoefficients 12 g32p_row14_terms_47)
      [1, 0, -1, 0, 1] [-64, 0, -72, 0, 0, 0, -8] = true := by
  decide +kernel

theorem g32p_row14_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 14 ∧ g32SparseVec v.coords =
        (![0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, -3, -3, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1, 0, 0, -2, 2, 0],
         ![2, 5, 6, 6]) := by
  refine ⟨⟨14, -1, [(2, -1), (3, -1), (15, -1), (16, -1), (17, 1), (18, 2), (20, 2), (27, -3), (28, -3), (36, 2), (37, -1), (39, 1), (42, -2), (43, 2), (46, 1)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row15_terms_0 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(8, ⟨-1, -2⟩, 1), (8, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 7), (8, ⟨-1, -2⟩, 10), (8, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 5), (8, ⟨1, 2⟩, 8), (8, ⟨1, 2⟩, 11)]

theorem g32p_row15_pairing_0 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_0)
      [1, 0, -1, 0, 1] [0, -8, 8, -8, 0, -8, 8, -8, 0, 16, -16, 16] = true := by
  decide +kernel

def g32p_row15_terms_1 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row15_pairing_1 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_1)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row15_terms_2 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (1, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨-2, -4⟩, 7), (4, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (1, ⟨-2, -4⟩, 11), (1, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨2, 4⟩, 7), (2, ⟨2, 4⟩, 8), (2, ⟨2, 4⟩, 10), (1, ⟨2, 4⟩, 11), (1, ⟨4, 8⟩, 8), (1, ⟨4, 8⟩, 10)]

theorem g32p_row15_pairing_2 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_2)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row15_terms_3 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-4, -8⟩, 2), (1, ⟨-4, -8⟩, 4), (1, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨-2, -4⟩, 7), (4, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (1, ⟨-2, -4⟩, 11), (1, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨2, 4⟩, 7), (2, ⟨2, 4⟩, 8), (2, ⟨2, 4⟩, 10), (1, ⟨2, 4⟩, 11), (1, ⟨4, 8⟩, 8), (1, ⟨4, 8⟩, 10)]

theorem g32p_row15_pairing_3 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_3)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row15_terms_4 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row15_pairing_4 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_4)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row15_terms_5 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 4), (1, ⟨-5, -10⟩, 10), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 8), (8, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 7), (6, ⟨-1, -2⟩, 10), (6, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 5), (6, ⟨1, 2⟩, 8), (8, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 10), (1, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 8)]

theorem g32p_row15_pairing_5 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_5)
      [1, 0, -1, 0, 1] [0, -8, 8, -8, 0, -8, 8, -8, 0, 16, -16, 16] = true := by
  decide +kernel

def g32p_row15_terms_6 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-5, -10⟩, 4), (1, ⟨-5, -10⟩, 10), (1, ⟨-3, -6⟩, 2), (1, ⟨-3, -6⟩, 8), (8, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 4), (8, ⟨-1, -2⟩, 7), (6, ⟨-1, -2⟩, 10), (6, ⟨1, 2⟩, 2), (8, ⟨1, 2⟩, 5), (6, ⟨1, 2⟩, 8), (8, ⟨1, 2⟩, 11), (1, ⟨3, 6⟩, 4), (1, ⟨3, 6⟩, 10), (1, ⟨5, 10⟩, 2), (1, ⟨5, 10⟩, 8)]

theorem g32p_row15_pairing_6 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_6)
      [1, 0, -1, 0, 1] [0, -8, 8, -8, 0, -8, 8, -8, 0, 16, -16, 16] = true := by
  decide +kernel

def g32p_row15_terms_7 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 10), (8, ⟨-2, -4⟩, 1), (1, ⟨-2, -4⟩, 2), (6, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 7), (1, ⟨-2, -4⟩, 8), (6, ⟨-2, -4⟩, 10), (6, ⟨2, 4⟩, 2), (1, ⟨2, 4⟩, 4), (8, ⟨2, 4⟩, 5), (6, ⟨2, 4⟩, 8), (1, ⟨2, 4⟩, 10), (8, ⟨2, 4⟩, 11), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 8)]

theorem g32p_row15_pairing_7 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_7)
      [1, 0, -1, 0, 1] [0, -16, 16, -16, 0, -16, 16, -16, 0, 32, -32, 32] = true := by
  decide +kernel

def g32p_row15_terms_8 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row15_pairing_8 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_8)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row15_terms_9 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 4), (1, ⟨-10, -20⟩, 10), (2, ⟨-2, -4⟩, 1), (7, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (2, ⟨-2, -4⟩, 7), (7, ⟨-2, -4⟩, 10), (6, ⟨-2, -4⟩, 11), (6, ⟨2, 4⟩, 1), (7, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 5), (6, ⟨2, 4⟩, 7), (7, ⟨2, 4⟩, 8), (2, ⟨2, 4⟩, 11), (1, ⟨10, 20⟩, 2), (1, ⟨10, 20⟩, 8)]

theorem g32p_row15_pairing_9 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_9)
      [1, 0, -1, 0, 1] [0, 8, 24, 8, 0, 8, 24, 8, 0, -16, -48, -16] = true := by
  decide +kernel

def g32p_row15_terms_10 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-10, -20⟩, 4), (1, ⟨-10, -20⟩, 10), (2, ⟨-2, -4⟩, 1), (7, ⟨-2, -4⟩, 4), (6, ⟨-2, -4⟩, 5), (2, ⟨-2, -4⟩, 7), (7, ⟨-2, -4⟩, 10), (6, ⟨-2, -4⟩, 11), (6, ⟨2, 4⟩, 1), (7, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 5), (6, ⟨2, 4⟩, 7), (7, ⟨2, 4⟩, 8), (2, ⟨2, 4⟩, 11), (1, ⟨10, 20⟩, 2), (1, ⟨10, 20⟩, 8)]

theorem g32p_row15_pairing_10 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_10)
      [1, 0, -1, 0, 1] [0, 8, 24, 8, 0, 8, 24, 8, 0, -16, -48, -16] = true := by
  decide +kernel

def g32p_row15_terms_11 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 4), (1, ⟨-15, -30⟩, 10), (1, ⟨-7, -14⟩, 4), (1, ⟨-7, -14⟩, 10), (6, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 7), (6, ⟨-1, -2⟩, 2), (2, ⟨-1, -2⟩, 5), (6, ⟨-1, -2⟩, 8), (2, ⟨-1, -2⟩, 11), (2, ⟨1, 2⟩, 1), (6, ⟨1, 2⟩, 4), (2, ⟨1, 2⟩, 7), (6, ⟨1, 2⟩, 10), (6, ⟨3, 6⟩, 5), (6, ⟨3, 6⟩, 11), (1, ⟨7, 14⟩, 2), (1, ⟨7, 14⟩, 8), (1, ⟨15, 30⟩, 2), (1, ⟨15, 30⟩, 8)]

theorem g32p_row15_pairing_11 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_11)
      [1, 0, -1, 0, 1] [0, -16, 16, -16, 0, -16, 16, -16, 0, 32, -32, 32] = true := by
  decide +kernel

def g32p_row15_terms_12 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-15, -30⟩, 4), (1, ⟨-15, -30⟩, 10), (2, ⟨-3, -6⟩, 1), (6, ⟨-3, -6⟩, 4), (2, ⟨-3, -6⟩, 7), (6, ⟨-3, -6⟩, 10), (1, ⟨-1, -2⟩, 2), (6, ⟨-1, -2⟩, 5), (1, ⟨-1, -2⟩, 8), (6, ⟨-1, -2⟩, 11), (6, ⟨1, 2⟩, 1), (1, ⟨1, 2⟩, 4), (6, ⟨1, 2⟩, 7), (1, ⟨1, 2⟩, 10), (6, ⟨3, 6⟩, 2), (2, ⟨3, 6⟩, 5), (6, ⟨3, 6⟩, 8), (2, ⟨3, 6⟩, 11), (1, ⟨15, 30⟩, 2), (1, ⟨15, 30⟩, 8)]

theorem g32p_row15_pairing_12 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_12)
      [1, 0, -1, 0, 1] [0, 0, 32, 0, 0, 0, 32, 0, 0, 0, -64] = true := by
  decide +kernel

def g32p_row15_terms_13 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row15_pairing_13 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_13)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row15_terms_14 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row15_pairing_14 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_14)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row15_terms_15 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (1, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨-2, -4⟩, 7), (4, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (1, ⟨-2, -4⟩, 11), (1, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨2, 4⟩, 7), (2, ⟨2, 4⟩, 8), (2, ⟨2, 4⟩, 10), (1, ⟨2, 4⟩, 11), (1, ⟨20, 40⟩, 8), (1, ⟨20, 40⟩, 10)]

theorem g32p_row15_pairing_15 :
    g32p_cyclotomicPairingCheck 96 (1)
      (g32p_pairingCoefficients 12 g32p_row15_terms_15)
      [1, 0, -1, 0, 1] [-96, 0, -112, 0, -32, 0, 48, 0, 64, 0, 32] = true := by
  decide +kernel

def g32p_row15_terms_16 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (1, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨-2, -4⟩, 7), (4, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (1, ⟨-2, -4⟩, 11), (1, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨2, 4⟩, 7), (2, ⟨2, 4⟩, 8), (2, ⟨2, 4⟩, 10), (1, ⟨2, 4⟩, 11), (1, ⟨20, 40⟩, 8), (1, ⟨20, 40⟩, 10)]

theorem g32p_row15_pairing_16 :
    g32p_cyclotomicPairingCheck 96 (1)
      (g32p_pairingCoefficients 12 g32p_row15_terms_16)
      [1, 0, -1, 0, 1] [-96, 0, -112, 0, -32, 0, 48, 0, 64, 0, 32] = true := by
  decide +kernel

def g32p_row15_terms_17 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (1, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨-2, -4⟩, 7), (4, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (1, ⟨-2, -4⟩, 11), (1, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨2, 4⟩, 7), (2, ⟨2, 4⟩, 8), (2, ⟨2, 4⟩, 10), (1, ⟨2, 4⟩, 11), (1, ⟨20, 40⟩, 8), (1, ⟨20, 40⟩, 10)]

theorem g32p_row15_pairing_17 :
    g32p_cyclotomicPairingCheck 96 (1)
      (g32p_pairingCoefficients 12 g32p_row15_terms_17)
      [1, 0, -1, 0, 1] [-96, 0, -112, 0, -32, 0, 48, 0, 64, 0, 32] = true := by
  decide +kernel

def g32p_row15_terms_18 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (1, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨-2, -4⟩, 7), (4, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (1, ⟨-2, -4⟩, 11), (1, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨2, 4⟩, 7), (2, ⟨2, 4⟩, 8), (2, ⟨2, 4⟩, 10), (1, ⟨2, 4⟩, 11), (1, ⟨20, 40⟩, 8), (1, ⟨20, 40⟩, 10)]

theorem g32p_row15_pairing_18 :
    g32p_cyclotomicPairingCheck 96 (1)
      (g32p_pairingCoefficients 12 g32p_row15_terms_18)
      [1, 0, -1, 0, 1] [-96, 0, -112, 0, -32, 0, 48, 0, 64, 0, 32] = true := by
  decide +kernel

def g32p_row15_terms_19 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 2), (1, ⟨-20, -40⟩, 4), (1, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨-2, -4⟩, 7), (4, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (1, ⟨-2, -4⟩, 11), (1, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨2, 4⟩, 7), (2, ⟨2, 4⟩, 8), (2, ⟨2, 4⟩, 10), (1, ⟨2, 4⟩, 11), (1, ⟨20, 40⟩, 8), (1, ⟨20, 40⟩, 10)]

theorem g32p_row15_pairing_19 :
    g32p_cyclotomicPairingCheck 96 (1)
      (g32p_pairingCoefficients 12 g32p_row15_terms_19)
      [1, 0, -1, 0, 1] [-96, 0, -112, 0, -32, 0, 48, 0, 64, 0, 32] = true := by
  decide +kernel

def g32p_row15_terms_20 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, -40⟩, 4), (1, ⟨-20, -40⟩, 10), (6, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 4), (6, ⟨-4, -8⟩, 7), (1, ⟨-4, -8⟩, 10), (1, ⟨4, 8⟩, 2), (6, ⟨4, 8⟩, 5), (1, ⟨4, 8⟩, 8), (6, ⟨4, 8⟩, 11), (1, ⟨20, 40⟩, 2), (1, ⟨20, 40⟩, 8)]

theorem g32p_row15_pairing_20 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_20)
      [1, 0, -1, 0, 1] [0, -24, 24, -24, 0, -24, 24, -24, 0, 48, -48, 48] = true := by
  decide +kernel

def g32p_row15_terms_21 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-24, -48⟩, 4), (1, ⟨-24, -48⟩, 10), (1, ⟨-8, -16⟩, 4), (1, ⟨-8, -16⟩, 10), (1, ⟨8, 16⟩, 2), (1, ⟨8, 16⟩, 8), (1, ⟨24, 48⟩, 2), (1, ⟨24, 48⟩, 8)]

theorem g32p_row15_pairing_21 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_21)
      [1, 0, -1, 0, 1] [0, 0, 32, 0, 0, 0, 32, 0, 0, 0, -64] = true := by
  decide +kernel

def g32p_row15_terms_22 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row15_pairing_22 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_22)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row15_terms_23 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 4), (1, ⟨-30, -60⟩, 10), (1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 10), (8, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 7), (6, ⟨-2, -4⟩, 10), (6, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 5), (6, ⟨2, 4⟩, 8), (8, ⟨2, 4⟩, 11), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 8), (1, ⟨30, 60⟩, 2), (1, ⟨30, 60⟩, 8)]

theorem g32p_row15_pairing_23 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_23)
      [1, 0, -1, 0, 1] [0, -16, 48, -16, 0, -16, 48, -16, 0, 32, -96, 32] = true := by
  decide +kernel

def g32p_row15_terms_24 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 4), (1, ⟨-30, -60⟩, 10), (1, ⟨-6, -12⟩, 4), (1, ⟨-6, -12⟩, 10), (8, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 4), (8, ⟨-2, -4⟩, 7), (6, ⟨-2, -4⟩, 10), (6, ⟨2, 4⟩, 2), (8, ⟨2, 4⟩, 5), (6, ⟨2, 4⟩, 8), (8, ⟨2, 4⟩, 11), (1, ⟨6, 12⟩, 2), (1, ⟨6, 12⟩, 8), (1, ⟨30, 60⟩, 2), (1, ⟨30, 60⟩, 8)]

theorem g32p_row15_pairing_24 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_24)
      [1, 0, -1, 0, 1] [0, -16, 48, -16, 0, -16, 48, -16, 0, 32, -96, 32] = true := by
  decide +kernel

def g32p_row15_terms_25 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-30, -60⟩, 4), (1, ⟨-30, -60⟩, 10), (1, ⟨-10, -20⟩, 2), (1, ⟨-10, -20⟩, 8), (6, ⟨-2, -4⟩, 1), (6, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 5), (6, ⟨-2, -4⟩, 7), (6, ⟨-2, -4⟩, 8), (2, ⟨-2, -4⟩, 11), (2, ⟨2, 4⟩, 1), (6, ⟨2, 4⟩, 4), (6, ⟨2, 4⟩, 5), (2, ⟨2, 4⟩, 7), (6, ⟨2, 4⟩, 10), (6, ⟨2, 4⟩, 11), (1, ⟨10, 20⟩, 4), (1, ⟨10, 20⟩, 10), (1, ⟨30, 60⟩, 2), (1, ⟨30, 60⟩, 8)]

theorem g32p_row15_pairing_25 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_25)
      [1, 0, -1, 0, 1] [0, -8, 8, -8, 0, -8, 8, -8, 0, 16, -16, 16] = true := by
  decide +kernel

def g32p_row15_terms_26 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row15_pairing_26 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_26)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row15_terms_27 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (1, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨-2, -4⟩, 7), (4, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (1, ⟨-2, -4⟩, 11), (1, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨2, 4⟩, 7), (2, ⟨2, 4⟩, 8), (2, ⟨2, 4⟩, 10), (1, ⟨2, 4⟩, 11), (1, ⟨36, 72⟩, 8), (1, ⟨36, 72⟩, 10)]

theorem g32p_row15_pairing_27 :
    g32p_cyclotomicPairingCheck 96 (2)
      (g32p_pairingCoefficients 12 g32p_row15_terms_27)
      [1, 0, -1, 0, 1] [-192, 0, -224, 0, -64, 0, 96, 0, 128, 0, 64] = true := by
  decide +kernel

def g32p_row15_terms_28 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-36, -72⟩, 2), (1, ⟨-36, -72⟩, 4), (1, ⟨-2, -4⟩, 1), (2, ⟨-2, -4⟩, 2), (2, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨-2, -4⟩, 7), (4, ⟨-2, -4⟩, 8), (4, ⟨-2, -4⟩, 10), (1, ⟨-2, -4⟩, 11), (1, ⟨2, 4⟩, 1), (4, ⟨2, 4⟩, 2), (4, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨2, 4⟩, 7), (2, ⟨2, 4⟩, 8), (2, ⟨2, 4⟩, 10), (1, ⟨2, 4⟩, 11), (1, ⟨36, 72⟩, 8), (1, ⟨36, 72⟩, 10)]

theorem g32p_row15_pairing_28 :
    g32p_cyclotomicPairingCheck 96 (2)
      (g32p_pairingCoefficients 12 g32p_row15_terms_28)
      [1, 0, -1, 0, 1] [-192, 0, -224, 0, -64, 0, 96, 0, 128, 0, 64] = true := by
  decide +kernel

def g32p_row15_terms_29 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row15_pairing_29 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_29)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row15_terms_30 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 4), (1, ⟨-40, -80⟩, 10), (1, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 8), (1, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 10), (1, ⟨40, 80⟩, 2), (1, ⟨40, 80⟩, 8)]

theorem g32p_row15_pairing_30 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_30)
      [1, 0, -1, 0, 1] [0, 0, 32, 0, 0, 0, 32, 0, 0, 0, -64] = true := by
  decide +kernel

def g32p_row15_terms_31 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-40, -80⟩, 4), (1, ⟨-40, -80⟩, 10), (1, ⟨-8, -16⟩, 2), (1, ⟨-8, -16⟩, 8), (1, ⟨8, 16⟩, 4), (1, ⟨8, 16⟩, 10), (1, ⟨40, 80⟩, 2), (1, ⟨40, 80⟩, 8)]

theorem g32p_row15_pairing_31 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_31)
      [1, 0, -1, 0, 1] [0, 0, 32, 0, 0, 0, 32, 0, 0, 0, -64] = true := by
  decide +kernel

def g32p_row15_terms_32 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row15_pairing_32 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_32)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row15_terms_33 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 4), (1, ⟨-45, -90⟩, 10), (1, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 5), (1, ⟨-3, -6⟩, 8), (6, ⟨-3, -6⟩, 11), (2, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 4), (2, ⟨-1, -2⟩, 7), (6, ⟨-1, -2⟩, 10), (6, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 5), (6, ⟨1, 2⟩, 8), (2, ⟨1, 2⟩, 11), (6, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 4), (6, ⟨3, 6⟩, 7), (1, ⟨3, 6⟩, 10), (1, ⟨45, 90⟩, 2), (1, ⟨45, 90⟩, 8)]

theorem g32p_row15_pairing_33 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_33)
      [1, 0, -1, 0, 1] [0, 16, 48, 16, 0, 16, 48, 16, 0, -32, -96, -32] = true := by
  decide +kernel

def g32p_row15_terms_34 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-45, -90⟩, 4), (1, ⟨-45, -90⟩, 10), (1, ⟨-3, -6⟩, 2), (6, ⟨-3, -6⟩, 5), (1, ⟨-3, -6⟩, 8), (6, ⟨-3, -6⟩, 11), (2, ⟨-1, -2⟩, 1), (6, ⟨-1, -2⟩, 4), (2, ⟨-1, -2⟩, 7), (6, ⟨-1, -2⟩, 10), (6, ⟨1, 2⟩, 2), (2, ⟨1, 2⟩, 5), (6, ⟨1, 2⟩, 8), (2, ⟨1, 2⟩, 11), (6, ⟨3, 6⟩, 1), (1, ⟨3, 6⟩, 4), (6, ⟨3, 6⟩, 7), (1, ⟨3, 6⟩, 10), (1, ⟨45, 90⟩, 2), (1, ⟨45, 90⟩, 8)]

theorem g32p_row15_pairing_34 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_34)
      [1, 0, -1, 0, 1] [0, 16, 48, 16, 0, 16, 48, 16, 0, -32, -96, -32] = true := by
  decide +kernel

def g32p_row15_terms_35 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  []

theorem g32p_row15_pairing_35 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_35)
      [1, 0, -1, 0, 1] [] = true := by
  decide +kernel

def g32p_row15_terms_36 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (1, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨-2, -4⟩, 7), (2, ⟨-2, -4⟩, 8), (2, ⟨-2, -4⟩, 10), (1, ⟨-2, -4⟩, 11), (1, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨2, 4⟩, 7), (4, ⟨2, 4⟩, 8), (4, ⟨2, 4⟩, 10), (1, ⟨2, 4⟩, 11), (1, ⟨60, 120⟩, 8), (1, ⟨60, 120⟩, 10)]

theorem g32p_row15_pairing_36 :
    g32p_cyclotomicPairingCheck 96 (4)
      (g32p_pairingCoefficients 12 g32p_row15_terms_36)
      [1, 0, -1, 0, 1] [-384, 0, -448, 0, -128, 0, 192, 0, 256, 0, 128] = true := by
  decide +kernel

def g32p_row15_terms_37 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (1, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨-2, -4⟩, 7), (2, ⟨-2, -4⟩, 8), (2, ⟨-2, -4⟩, 10), (1, ⟨-2, -4⟩, 11), (1, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨2, 4⟩, 7), (4, ⟨2, 4⟩, 8), (4, ⟨2, 4⟩, 10), (1, ⟨2, 4⟩, 11), (1, ⟨60, 120⟩, 8), (1, ⟨60, 120⟩, 10)]

theorem g32p_row15_pairing_37 :
    g32p_cyclotomicPairingCheck 96 (4)
      (g32p_pairingCoefficients 12 g32p_row15_terms_37)
      [1, 0, -1, 0, 1] [-384, 0, -448, 0, -128, 0, 192, 0, 256, 0, 128] = true := by
  decide +kernel

def g32p_row15_terms_38 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 2), (1, ⟨-60, -120⟩, 4), (1, ⟨-2, -4⟩, 1), (4, ⟨-2, -4⟩, 2), (4, ⟨-2, -4⟩, 4), (1, ⟨-2, -4⟩, 5), (1, ⟨-2, -4⟩, 7), (2, ⟨-2, -4⟩, 8), (2, ⟨-2, -4⟩, 10), (1, ⟨-2, -4⟩, 11), (1, ⟨2, 4⟩, 1), (2, ⟨2, 4⟩, 2), (2, ⟨2, 4⟩, 4), (1, ⟨2, 4⟩, 5), (1, ⟨2, 4⟩, 7), (4, ⟨2, 4⟩, 8), (4, ⟨2, 4⟩, 10), (1, ⟨2, 4⟩, 11), (1, ⟨60, 120⟩, 8), (1, ⟨60, 120⟩, 10)]

theorem g32p_row15_pairing_38 :
    g32p_cyclotomicPairingCheck 96 (4)
      (g32p_pairingCoefficients 12 g32p_row15_terms_38)
      [1, 0, -1, 0, 1] [-384, 0, -448, 0, -128, 0, 192, 0, 256, 0, 128] = true := by
  decide +kernel

def g32p_row15_terms_39 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, -120⟩, 4), (1, ⟨-60, -120⟩, 10), (6, ⟨-4, -8⟩, 1), (1, ⟨-4, -8⟩, 2), (6, ⟨-4, -8⟩, 7), (1, ⟨-4, -8⟩, 8), (1, ⟨4, 8⟩, 4), (6, ⟨4, 8⟩, 5), (1, ⟨4, 8⟩, 10), (6, ⟨4, 8⟩, 11), (1, ⟨60, 120⟩, 2), (1, ⟨60, 120⟩, 8)]

theorem g32p_row15_pairing_39 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_39)
      [1, 0, -1, 0, 1] [0, -24, 56, -24, 0, -24, 56, -24, 0, 48, -112, 48] = true := by
  decide +kernel

def g32p_row15_terms_40 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 4), (1, ⟨-64, -128⟩, 10), (1, ⟨64, 128⟩, 2), (1, ⟨64, 128⟩, 8)]

theorem g32p_row15_pairing_40 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_40)
      [1, 0, -1, 0, 1] [0, 0, 64, 0, 0, 0, 64, 0, 0, 0, -128] = true := by
  decide +kernel

def g32p_row15_terms_41 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, -128⟩, 2), (1, ⟨-64, -128⟩, 4), (1, ⟨64, 128⟩, 8), (1, ⟨64, 128⟩, 10)]

theorem g32p_row15_pairing_41 :
    g32p_cyclotomicPairingCheck 96 (4)
      (g32p_pairingCoefficients 12 g32p_row15_terms_41)
      [1, 0, -1, 0, 1] [-384, 0, -448, 0, -128, 0, 192, 0, 256, 0, 128] = true := by
  decide +kernel

def g32p_row15_terms_42 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, -160⟩, 2), (1, ⟨-80, -160⟩, 4), (1, ⟨80, 160⟩, 8), (1, ⟨80, 160⟩, 10)]

theorem g32p_row15_pairing_42 :
    g32p_cyclotomicPairingCheck 96 (5)
      (g32p_pairingCoefficients 12 g32p_row15_terms_42)
      [1, 0, -1, 0, 1] [-480, 0, -560, 0, -160, 0, 240, 0, 320, 0, 160] = true := by
  decide +kernel

def g32p_row15_terms_43 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-81, -162⟩, 4), (1, ⟨-81, -162⟩, 10), (1, ⟨-9, -18⟩, 4), (1, ⟨-9, -18⟩, 10), (6, ⟨-3, -6⟩, 2), (8, ⟨-3, -6⟩, 5), (6, ⟨-3, -6⟩, 8), (8, ⟨-3, -6⟩, 11), (8, ⟨3, 6⟩, 1), (6, ⟨3, 6⟩, 4), (8, ⟨3, 6⟩, 7), (6, ⟨3, 6⟩, 10), (1, ⟨9, 18⟩, 2), (1, ⟨9, 18⟩, 8), (1, ⟨81, 162⟩, 2), (1, ⟨81, 162⟩, 8)]

theorem g32p_row15_pairing_43 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_43)
      [1, 0, -1, 0, 1] [0, 24, 72, 24, 0, 24, 72, 24, 0, -48, -144, -48] = true := by
  decide +kernel

def g32p_row15_terms_44 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-20, 0⟩, 2), (1, ⟨-20, 0⟩, 6), (1, ⟨-20, 0⟩, 10), (4, ⟨-2, 0⟩, 0), (1, ⟨-2, 0⟩, 1), (2, ⟨-2, 0⟩, 2), (1, ⟨-2, 0⟩, 3), (4, ⟨-2, 0⟩, 4), (1, ⟨-2, 0⟩, 5), (2, ⟨-2, 0⟩, 6), (1, ⟨-2, 0⟩, 7), (4, ⟨-2, 0⟩, 8), (1, ⟨-2, 0⟩, 9), (2, ⟨-2, 0⟩, 10), (1, ⟨-2, 0⟩, 11), (2, ⟨2, 0⟩, 0), (1, ⟨2, 0⟩, 1), (4, ⟨2, 0⟩, 2), (1, ⟨2, 0⟩, 3), (2, ⟨2, 0⟩, 4), (1, ⟨2, 0⟩, 5), (4, ⟨2, 0⟩, 6), (1, ⟨2, 0⟩, 7), (2, ⟨2, 0⟩, 8), (1, ⟨2, 0⟩, 9), (4, ⟨2, 0⟩, 10), (1, ⟨2, 0⟩, 11), (1, ⟨20, 0⟩, 0), (1, ⟨20, 0⟩, 4), (1, ⟨20, 0⟩, 8)]

theorem g32p_row15_pairing_44 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_44)
      [1, 0, -1, 0, 1] [16, 0, 0, 0, 0, 0, -16] = true := by
  decide +kernel

def g32p_row15_terms_45 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-60, 0⟩, 2), (1, ⟨-60, 0⟩, 6), (1, ⟨-60, 0⟩, 10), (2, ⟨-2, 0⟩, 0), (1, ⟨-2, 0⟩, 1), (4, ⟨-2, 0⟩, 2), (1, ⟨-2, 0⟩, 3), (2, ⟨-2, 0⟩, 4), (1, ⟨-2, 0⟩, 5), (4, ⟨-2, 0⟩, 6), (1, ⟨-2, 0⟩, 7), (2, ⟨-2, 0⟩, 8), (1, ⟨-2, 0⟩, 9), (4, ⟨-2, 0⟩, 10), (1, ⟨-2, 0⟩, 11), (4, ⟨2, 0⟩, 0), (1, ⟨2, 0⟩, 1), (2, ⟨2, 0⟩, 2), (1, ⟨2, 0⟩, 3), (4, ⟨2, 0⟩, 4), (1, ⟨2, 0⟩, 5), (2, ⟨2, 0⟩, 6), (1, ⟨2, 0⟩, 7), (4, ⟨2, 0⟩, 8), (1, ⟨2, 0⟩, 9), (2, ⟨2, 0⟩, 10), (1, ⟨2, 0⟩, 11), (1, ⟨60, 0⟩, 0), (1, ⟨60, 0⟩, 4), (1, ⟨60, 0⟩, 8)]

theorem g32p_row15_pairing_45 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_45)
      [1, 0, -1, 0, 1] [64, 0, 0, 0, 0, 0, -64] = true := by
  decide +kernel

def g32p_row15_terms_46 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-64, 0⟩, 2), (1, ⟨-64, 0⟩, 6), (1, ⟨-64, 0⟩, 10), (1, ⟨64, 0⟩, 0), (1, ⟨64, 0⟩, 4), (1, ⟨64, 0⟩, 8)]

theorem g32p_row15_pairing_46 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_46)
      [1, 0, -1, 0, 1] [64, 0, 0, 0, 0, 0, -64] = true := by
  decide +kernel

def g32p_row15_terms_47 : List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  [(1, ⟨-80, 0⟩, 2), (1, ⟨-80, 0⟩, 6), (1, ⟨-80, 0⟩, 10), (1, ⟨80, 0⟩, 0), (1, ⟨80, 0⟩, 4), (1, ⟨80, 0⟩, 8)]

theorem g32p_row15_pairing_47 :
    g32p_cyclotomicPairingCheck 96 (0)
      (g32p_pairingCoefficients 12 g32p_row15_terms_47)
      [1, 0, -1, 0, 1] [80, 0, 0, 0, 0, 0, -80] = true := by
  decide +kernel

theorem g32p_row15_coordinates :
    ∃ v ∈ g32VectorTable,
      v.i = 15 ∧ g32SparseVec v.coords =
        (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 4, 4, 4, 0, 0, 4, 5, 0],
         ![0, 0, 0, 0]) := by
  refine ⟨⟨15, -1, [(16, 1), (17, 1), (18, 1), (19, 1), (20, 1), (28, 2), (29, 2), (37, 4), (38, 4), (39, 4), (42, 4), (43, 5)]⟩, by decide, rfl, by decide⟩

end HodgeLean.Foundations.Program

end
