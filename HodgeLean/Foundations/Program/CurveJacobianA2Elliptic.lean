import HodgeLean.Foundations.Program.CurveJacobianAEllipticAJ

/-! # Track B3, lane A2: the elliptic period lattice

The periods of the two coordinate loops generate the period lattice of the square elliptic curve.
-/

noncomputable section

set_option maxHeartbeats 400000

open Manifold

namespace HodgeLean.Foundations.Program

/-- The `a` and `b` periods generate the period lattice of the square elliptic curve. -/
theorem CurveJacobianA2_latticePeriod_span
    (u : b3_periodLattice b3_EllipticModel b3_Elliptic) :
    ∃ m n : ℤ, u = m • b3_latticePeriod _ _ b3A_loopA + n • b3_latticePeriod _ _ b3A_loopB := by
  obtain ⟨x, hx⟩ := b3A_lattice_dz u
  refine ⟨x 0, x 1, ?_⟩
  apply Subtype.ext
  apply b3A_linearDual_ext (b3A_lattice_mem_linearDual u)
    (b3A_lattice_mem_linearDual
      (x 0 • b3_latticePeriod _ _ b3A_loopA + x 1 • b3_latticePeriod _ _ b3A_loopB))
  refine hx.trans ?_
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_zsmul, Pi.add_apply]
  have ha : b3_period _ _ b3A_loopA b3A_dz = 1 := by
    change b3_pathPeriod _ _ b3_ellipticA b3A_dz = 1
    rw [b3A_ellipticA_eq, b3A_line_pathPeriod, b3A_formFunctional_dz,
      b3A_φ_e0]
  have hb : b3_period _ _ b3A_loopB b3A_dz = Complex.I := by
    change b3_pathPeriod _ _ b3_ellipticB b3A_dz = Complex.I
    rw [b3A_ellipticB_eq, b3A_line_pathPeriod, b3A_formFunctional_dz,
      b3A_φ_e1]
  change _ = (x 0 : ℤ) • b3_period _ _ b3A_loopA b3A_dz +
    (x 1 : ℤ) • b3_period _ _ b3A_loopB b3A_dz
  rw [ha, hb]
  simp only [zsmul_eq_mul, mul_one]
  ring

end HodgeLean.Foundations.Program
