import HodgeLean.Foundations.Program.SchoenTowerL1bActionOrbitLimit

noncomputable section
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A primitive lifted return and an asymptotic logarithmic step determine
the exponential tangent scalar, allowing the step to vary along the orbit. -/
theorem s2v_l1b_action_asymptotic_rotation_scalar
    {X : Type*} (l : Filter X) [NeBot l]
    (F D : X → X) (L : X → ℂ) (hF : Tendsto F l l)
    (a : ℂ) (hs : Tendsto (fun x => L (F x) - L x) l (𝓝 a))
    (N : ℕ) (hN : 0 < N) (ε : ℤ)
    (hreturn : ∀ᶠ x in l, F^[N] x = D x)
    (hdeck : ∀ᶠ x in l, L (D x) = L x + (ε : ℂ) * (2 * Real.pi * Complex.I)) :
    Complex.exp a = Complex.exp ((ε : ℂ) * (2 * Real.pi * Complex.I) / (N : ℂ)) := by
  have ht := s2v_l1b_action_lift_orbit_displacement_limit l F L hF a hs N
  have he : (fun _ : X => (ε : ℂ) * (2 * Real.pi * Complex.I)) =ᶠ[l]
      (fun x => L (F^[N] x) - L x) := by
    filter_upwards [hreturn, hdeck] with x hr hd
    rw [hr, hd, add_sub_cancel_left]
  have hp : (N : ℂ) * a = (ε : ℂ) * (2 * Real.pi * Complex.I) :=
    tendsto_nhds_unique ht (tendsto_const_nhds.congr' he)
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have ha : a = (ε : ℂ) * (2 * Real.pi * Complex.I) / (N : ℂ) :=
    (eq_div_iff hn).mpr (by rwa [mul_comm])
  rw [ha]

end HodgeLean.Foundations.Program
