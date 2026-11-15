import HodgeLean.Foundations.Program.MilneCentralizerDefs

/-! # Matrix coordinates for the first stage of Milne M1

Concrete central idempotents, bilinear adjoints and exchanged matrix pairs.
These constructions use transpose over ℂ without complex conjugation.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.Program

/-- The identity in one matrix block and zero in the other blocks.
Source: Milne (1999), Lemma 3.5, product decomposition of a semisimple algebra. -/
def m1_blockId (s : ℕ) (d : Fin s → ℕ) (i : Fin s) :
    (j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) ℂ :=
  Pi.single i 1

example (s : ℕ) (d : Fin s → ℕ) (i : Fin s) : m1_blockId s d i i = 1 := by
  simp only [m1_blockId, Pi.single_eq_same]

/-- The adjoint in matrix coordinates for a bilinear form with Gram matrix B.
Source: Milne (1999), Lemma 3.5, cases (b) and (c). -/
def m1_gramAdjoint (n : ℕ) (B X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  B⁻¹ * X.transpose * B

example (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    m1_gramAdjoint n 1 X = X.transpose := by
  simp [m1_gramAdjoint]

/-- Transpose exchanges the two simple blocks of a paired factor.
Source: Milne (1999), Lemma 3.5, case (a). -/
def m1_exchange (n : ℕ)
    (X : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ :=
  (X.2.transpose, X.1.transpose)

example (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :
    m1_exchange n (m1_exchange n X) = X := by
  simp only [m1_exchange, Matrix.transpose_transpose]

-- A reflection is retained, including its determinant of minus one.
example :
    m1_gramAdjoint 1 1 (-1) * (-1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 ∧
      Matrix.det (-1 : Matrix (Fin 1) (Fin 1) ℂ) = -1 := by
  constructor
  · simp [m1_gramAdjoint]
  · simp

-- A paired factor contains inverse scalings, not just equal scalings.
example :
    m1_exchange 1 ((2 : ℂ) • 1, (2 : ℂ)⁻¹ • 1) *
      (((2 : ℂ) • 1, (2 : ℂ)⁻¹ • 1) :
        Matrix (Fin 1) (Fin 1) ℂ × Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
  apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [m1_exchange, Matrix.mul_apply, Matrix.transpose_apply]

-- Existing GL invariant theory supplies the balanced mixed-tensor branch.
example (n k : ℕ) :
    (SchurWeyl.mixedRep ℂ (Fin n → ℂ) (Fin k) (Fin k)).invariants =
      Submodule.span ℂ (Set.range (SchurWeyl.contraction ℂ (Fin n → ℂ) (Fin k))) :=
  SchurWeyl.invariants_mixedRep_eq_span_contraction

end HodgeLean.Foundations.Program
