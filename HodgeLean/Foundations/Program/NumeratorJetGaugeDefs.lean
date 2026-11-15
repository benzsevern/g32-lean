import HodgeLean.Foundations.Program.NumeratorJetConjData
import HodgeLean.Foundations.Program.NumeratorJetGaugeData
import HodgeLean.Foundations.Program.NumeratorJetGaugeInvData
import HodgeLean.Foundations.Program.NumeratorJetRCoeffData
import HodgeLean.Foundations.Program.NumeratorJetQCoeffData
import HodgeLean.Foundations.Program.NumeratorJetBasisData
import HodgeLean.Foundations.Program.NumeratorJetRegularData
import HodgeLean.Foundations.Program.KernelFramesFamilyMirror

/-! # Rational convolutions for the gauge and Laurent coefficient jets -/

namespace HodgeLean.Foundations.Program
open Matrix

/-- Truncated Cauchy convolution of rational matrix sequences. -/
def b65e_convQ {l m n : Type*} [Fintype m] (A : ℕ → Matrix l m ℚ) (B : ℕ → Matrix m n ℚ)
    (k : ℕ) : Matrix l n ℚ :=
  ∑ a ∈ Finset.range (k + 1), A a * B (k - a)

/-- Natural-indexed stored eigenbasis jets. -/
def b65e_basisN (k : Fin 4) (a : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  b65e_basisJetQ k (Fin.ofNat 8 a)

/-- Natural-indexed stored inverse eigenbasis jets. -/
def b65e_basisInvN (k : Fin 4) (a : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  b65e_basisInvJetQ k (Fin.ofNat 8 a)

/-- Natural-indexed stored regular-part jets. -/
def b65e_taylorN (k : Fin 4) (l : ℕ) (a : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  b65e_taylorJetQ k (Fin.ofNat 5 l) (Fin.ofNat 8 a)

/-- Natural-indexed stored conjugated regular-part jets. -/
def b65e_conjN (k : Fin 4) (l : ℕ) (a : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  b65e_conjJetQ k (Fin.ofNat 5 l) (Fin.ofNat 8 a)

/-- Natural-indexed stored gauge jets. -/
def b65e_gaugeN (k : Fin 4) (m : ℕ) (a : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  b65e_gaugeJetQ k (Fin.ofNat 6 m) (Fin.ofNat 8 a)

/-- Natural-indexed stored inverse gauge jets. -/
def b65e_gaugeInvN (k : Fin 4) (m : ℕ) (a : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  b65e_gaugeInvJetQ k (Fin.ofNat 6 m) (Fin.ofNat 8 a)

/-- Right side of the gauge recursion for the stored jets. -/
def b65e_gaugeRhsQ (k : Fin 4) (m : ℕ) (n : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.of fun i j ↦
    if (m : ℚ) + b65q_lamQ k j - b65q_lamQ k i = 0 then 0 else
      (∑ l ∈ Finset.range m, b65e_convQ (b65e_conjN k l) (b65e_gaugeN k (m - 1 - l)) n) i j /
        ((m : ℚ) + b65q_lamQ k j - b65q_lamQ k i)

/-- Right side of the inverse-series recursion for the stored jets. -/
def b65e_gaugeInvRhsQ (k : Fin 4) (m : ℕ) (n : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  -∑ j ∈ Finset.range m, b65e_convQ (b65e_gaugeN k (j + 1)) (b65e_gaugeInvN k (m - 1 - j)) n

end HodgeLean.Foundations.Program
