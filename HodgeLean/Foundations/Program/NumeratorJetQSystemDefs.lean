import HodgeLean.Foundations.Program.NumeratorJetQBetaData
import HodgeLean.Foundations.Program.NumeratorJetLeftDefs
import HodgeLean.Foundations.Program.NumeratorJetQCoeffData
import HodgeLean.Foundations.Program.NumeratorJetDefs
import HodgeLean.Foundations.Program.NumeratorJetGaugeDefs

/-! # Rational definitions for the q-system jets -/

namespace HodgeLean.Foundations.Program
open Matrix

/-- Taylor coefficients of a beta entry, from the stored q-coefficient and beta-weight jets. -/
def b65e_betaJetQ (k j : Fin 4) (n : ℤ) (e : Fin 2) (v : Fin 6) (d : ℕ) : ℚ :=
  if 0 ≤ n then
    ∑ l ∈ Finset.range (n.toNat + 1), ∑ i : Fin 4, ∑ a ∈ Finset.range (d + 1),
      b65e_qCoeffJetQ k (Fin.ofNat 6 (n.toNat - l)) (Fin.ofNat 8 a) j i *
        b65e_betaWeightQ k e (Fin.ofNat 3 l) v i (Fin.ofNat 8 (d - a))
  else 0

/-- The finite formula for the beta columns of the q-system jets. -/
def b65e_qBetaFormulaQ (d : ℕ) : Matrix (Fin 57) (Fin 12) ℚ := fun r c ↦
  if h : r.val < 53 then
    b65e_betaJetQ (b65q_qRow ⟨r.val, h⟩).1 (b65q_qRow ⟨r.val, h⟩).2.1 (b65q_qRow ⟨r.val, h⟩).2.2
      ⟨c.val / 6, by omega⟩ ⟨c.val % 6, by omega⟩ d
  else b65e_betaInfQ ⟨c.val / 6, by omega⟩ ⟨c.val % 6, by omega⟩ ⟨r.val - 53, by omega⟩ d

/-- Order-`n` Taylor coefficients of the q-system, from the stored jets. -/
def b65e_qSystemJetQ (n : ℕ) : Matrix (Fin 57) (Fin 48) ℚ := fun r c ↦
  if h : r.val < 53 then
    if hc : c.val < 36 then
      b65q_principalEntryQ (fun k m ↦ b65e_qCoeffJetQ k (Fin.ofNat 6 m) (Fin.ofNat 8 n))
        (b65q_qRow ⟨r.val, h⟩).1 (b65q_qRow ⟨r.val, h⟩).2.1 (b65q_qRow ⟨r.val, h⟩).2.2 ⟨c.val, hc⟩
    else b65e_qBetaJetQ (Fin.ofNat 8 n) r ⟨c.val - 36, by omega⟩
  else
    if hc : c.val < 36 then
      (if n = 0 then b65q_infinityEntryQ ⟨r.val - 53, by omega⟩ ⟨c.val, hc⟩ else 0)
    else b65e_qBetaJetQ (Fin.ofNat 8 n) r ⟨c.val - 36, by omega⟩

/-- Natural-indexed stored q-frame jets. -/
def b65e_qFrameN (a : ℕ) : Matrix (Fin 48) (Fin 3) ℚ := b65e_qFrameJet (Fin.ofNat 8 a)

end HodgeLean.Foundations.Program
