import HodgeLean.Foundations.Program.NumeratorJetLeftData
import HodgeLean.Foundations.Program.NumeratorJetRegularDefs
import HodgeLean.Foundations.Program.KernelFramesFamilyMirror
import HodgeLean.Foundations.Program.NumeratorJetPowerMoments

/-! # Rational definitions for the left-eigenvector and beta-weight jets -/

namespace HodgeLean.Foundations.Program
open Matrix

/-- The constant trace of the moving residues on a fibre. -/
def b65e_traceQ (e : Fin 2) : ℚ := Matrix.trace (b65q_BQ e)

/-- Left side of the left-eigenvector recursion in sextic coordinates. -/
def b65e_leftEigLhsQ (e : Fin 2) (j : Fin 4) (n : Fin 8) (c : Fin 6) : ℚ :=
  ∑ a ∈ Finset.range (n.val + 1), ∑ i : Fin 4,
    b65e_coordinateMulQ e (b65e_leftCoordsQ e i (Fin.ofNat 8 a))
      (fun s ↦ b65e_movingJet (Fin.ofNat 8 (n.val - a)) e s i j) c

/-- The finite trace formula for the beta weights. -/
def b65e_betaWeightFormulaQ (k : Fin 4) (e : Fin 2) (l : Fin 3) (v : Fin 6) (i : Fin 4)
    (n : Fin 8) : ℚ :=
  -∑ b ∈ Finset.range (n.val + 1), ∑ c : Fin 6,
    b65e_coordinateMulQ e (b65e_leftCoordsQ e i (Fin.ofNat 8 b))
      (b65e_invPowerCoordsQ k e (Fin.ofNat 5 l.val) (Fin.ofNat 8 (n.val - b))) c *
    b65e_powerMomentQ ⟨c.val + v.val, by omega⟩ e

/-- Traced infinity weights `Σ_x x^v w_x(θ)_i`, Taylor coefficients. -/
def b65e_betaInfQ (e : Fin 2) (v : Fin 6) (i : Fin 4) (n : ℕ) : ℚ :=
  ∑ c : Fin 6, b65e_leftCoordsQ e i (Fin.ofNat 8 n) c * b65e_powerMomentQ ⟨c.val + v.val, by omega⟩ e

end HodgeLean.Foundations.Program
