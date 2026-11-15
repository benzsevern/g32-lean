import HodgeLean.Foundations.Program.ComponentTransportCertifiedChain
import HodgeLean.Foundations.Program.BraidBridgesThree

/-! # Half-turn tracks and column loop coordinates
HC no distance; AV milestone no distance.
-/
noncomputable section
open Complex Set Topology
namespace HodgeLean.Foundations.Program

/-- The two adjacent finite marks rotate through a signed half-turn about their midpoint.
Source: Völklein, Groups as Galois Groups, Chapters 9–10, elementary braid generators. -/
def b66h_track (j : Fin 11) (ε : ℝ) (t : ℝ) (k : Fin 12) : ℂ :=
  let a := mr_marks j.castSucc
  let b := mr_marks j.succ
  let c := (a + b) / 2
  if k = j.castSucc ∨ k = j.succ then
    c + (mr_marks k - c) * Complex.exp (ε * Real.pi * Complex.I * (t : ℂ))
  else mr_marks k

example (j : Fin 11) (ε : ℝ) : b66h_track j ε 0 = mr_marks := by
  funext k
  simp only [b66h_track, ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  split_ifs <;> ring

/-- Column coordinates in the opposite fundamental group: reverse and invert the peripheral classes.
Source: b65s_columnRoot; MarkedRootCoverDefs, chronological concatenation convention. -/
def b66h_loop (i : Fin 13) : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ :=
  MulOpposite.op ((b63gP_loops i.rev)⁻¹)

example : b66h_loop 0 = MulOpposite.op ((b63gP_loops 12)⁻¹) := rfl

end HodgeLean.Foundations.Program
