import HodgeLean.Foundations.Program.NumeratorJetRegularData
import HodgeLean.Foundations.Program.NumeratorJetCoordinateAlgebra
import HodgeLean.Foundations.Program.NumeratorJetFirstOrder
import HodgeLean.Foundations.Program.NumeratorJetDefs

/-! # Rational definitions for the regular-part coefficient jets -/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Sextic coordinates of `x − t_k`. -/
def b65e_shiftCoordsQ (k : Fin 4) : Fin 6 → ℚ :=
  fun c ↦ if c = 0 then -b65k_fixed k else if c = 1 then 1 else 0

/-- The right side of the inverse-power recursion. -/
def b65e_invPowerRhsQ (k : Fin 4) (e : Fin 2) (l : Fin 5) (m : Fin 8) (c : Fin 6) : ℚ :=
  if l.val = 0 then (if m.val = 0 ∧ c = 0 then 1 else 0)
  else b65e_invPowerCoordsQ k e (Fin.ofNat 5 (l.val - 1)) m c

/-- The left side of the inverse-power recursion. -/
def b65e_invPowerLhsQ (k : Fin 4) (e : Fin 2) (l : Fin 5) (m : Fin 8) (c : Fin 6) : ℚ :=
  b65e_coordinateMulQ e (b65e_shiftCoordsQ k) (b65e_invPowerCoordsQ k e l m) c +
    if m.val = 0 then 0 else
      b65e_coordinateMulQ e (b65e_velocityQ e)
        (b65e_invPowerCoordsQ k e l (Fin.ofNat 8 (m.val - 1))) c

/-- Fixed-source part of the regular-part coefficient jets. -/
def b65e_taylorFixedQ (k : Fin 4) (l : Fin 5) (n : Fin 8) : Matrix (Fin 4) (Fin 4) ℚ :=
  ∑ r : Fin 4, if r = k then 0 else
    (-((b65k_fixed r - b65k_fixed k) ^ (l.val + 1))⁻¹) • b65e_fixedJet n r

/-- Moving-source part of the regular-part coefficient jets, traced by power moments. -/
def b65e_taylorMovingQ (k : Fin 4) (l : Fin 5) (n : Fin 8) : Matrix (Fin 4) (Fin 4) ℚ :=
  ∑ e : Fin 2, ∑ a ∈ Finset.range (n.val + 1), ∑ c : Fin 6, ∑ d : Fin 6,
    (b65e_invPowerCoordsQ k e l (Fin.ofNat 8 a) c *
      b65e_powerMomentQ ⟨c.val + d.val, by omega⟩ e) •
      b65e_movingJet (Fin.ofNat 8 (n.val - a)) e d

end HodgeLean.Foundations.Program
