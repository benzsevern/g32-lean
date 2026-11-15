import HodgeLean.Foundations.Program.G32Native.AbelCollisionCoordinateDerivative
import HodgeLean.Foundations.Program.G32Native.AbelCollisionRootPolynomial

/-! # First variation of an actual descended local trace -/
noncomputable section
set_option maxHeartbeats 400000
open Filter Polynomial
open scoped BigOperators Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- Lower monic coefficients of the exact unordered root tuple. -/
def collisionMonicCoefficients {m : ℕ} (z : Fin m → ℂ) : Fin m → ℂ :=
  fun j => (∏ i : Fin m, (X - C (z i))).coeff j.val

/-- The polynomial root path varies exactly one coordinate of the coefficient vector. -/
theorem collisionRootTuple_coefficients (j : ℕ) {n : ℕ} (hn : 0 < n)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (t : ℂ) :
    collisionMonicCoefficients (collisionRootTuple j n ζ t) =
      Pi.single ⟨j, Nat.lt_add_of_pos_right hn⟩ (-(t ^ n)) := by
  classical
  ext i
  rw [collisionMonicCoefficients, collisionRootTuple_coefficient j hn hζ t]
  by_cases he : i = ⟨j, Nat.lt_add_of_pos_right hn⟩
  · subst i
    simp only [Pi.single_eq_same, ite_true]
  · have hv : i.val ≠ j := by intro hv; apply he; exact Fin.ext hv
    simp only [hv, ite_false, Pi.single_eq_of_ne he]

/-- The root path tends to the full collision tuple. -/
theorem collisionRootTuple_tendsto (j n : ℕ) (ζ : ℂ) :
    Tendsto (collisionRootTuple j n ζ) (𝓝 (0 : ℂ)) (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simpa only [collisionRootTuple, Fin.append_left, Pi.zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℂ => (0 : ℂ)) (𝓝 0) (𝓝 0))
  · have hc : Continuous (fun t : ℂ => ζ ^ k.val * t) := continuous_const.mul continuous_id
    simpa only [collisionRootTuple, Fin.append_right, Pi.zero_apply, mul_zero] using
      (hc.continuousAt (x := (0 : ℂ))).tendsto


/-- A literal local trace equation gives its coefficient directional derivative at every multiplicity. -/
theorem collision_descended_trace_derivative (j : ℕ) {n : ℕ} (hn : 0 < n)
    (f : (Fin (j + n) → ℂ) → ℂ) (H : ℂ → ℂ)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hf : DifferentiableAt ℂ f 0) (hp : HasFPowerSeriesAt H p 0)
    (c : ℂ) (he : ∀ᶠ z in 𝓝 (0 : Fin (j + n) → ℂ),
      f (collisionMonicCoefficients z) = (∑ i, H (z i)) + c) :
    fderiv ℂ f 0 (Pi.single ⟨j, Nat.lt_add_of_pos_right hn⟩ 1) =
      -(n : ℂ) * p.coeff n := by
  obtain ⟨ζ, hζ⟩ := collision_primitive_root_exists hn
  apply monic_coordinate_first_variation hn _ hζ f H p hf hp ((j : ℂ) * H 0 + c)
  filter_upwards [(collisionRootTuple_tendsto j n ζ).eventually he] with t ht
  rw [collisionRootTuple_coefficients j hn hζ t,
    collisionRootTuple_trace] at ht
  exact ht.trans (by ring)

/-- The same formula applies to each coefficient index of a fixed block. -/
theorem collision_descended_trace_derivative_at_index {m : ℕ} (j : Fin m)
    (f : (Fin m → ℂ) → ℂ) (H : ℂ → ℂ)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hf : DifferentiableAt ℂ f 0) (hp : HasFPowerSeriesAt H p 0)
    (c : ℂ) (he : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ),
      f (collisionMonicCoefficients z) = (∑ i, H (z i)) + c) :
    fderiv ℂ f 0 (Pi.single j 1) = -((m - j.val : ℕ) : ℂ) * p.coeff (m - j.val) := by
  rcases j with ⟨j, hj⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hj)
  have hn : 0 < n := by omega
  simpa only [Nat.add_sub_cancel_left] using
    collision_descended_trace_derivative j hn f H p hf hp c he

#print axioms collision_descended_trace_derivative_at_index
#print axioms collisionRootTuple_coefficients
#print axioms collisionRootTuple_tendsto
#print axioms collision_descended_trace_derivative
end HodgeLean.Foundations.Program.G32Native
