import HodgeLean.Foundations.Program.SchoenTowerL1bActionLiftArithmetic
import Mathlib.Topology.Algebra.Ring.Basic

noncomputable section
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A step limit along an end-preserving lift determines each finite orbit's
total logarithmic displacement limit. -/
theorem s2v_l1b_action_lift_orbit_displacement_limit
    {X : Type*} (l : Filter X) (F : X → X) (L : X → ℂ)
    (hF : Tendsto F l l) (a : ℂ)
    (hs : Tendsto (fun x => L (F x) - L x) l (𝓝 a)) (n : ℕ) :
    Tendsto (fun x => L (F^[n] x) - L x) l (𝓝 ((n : ℂ) * a)) := by
  induction n with
  | zero =>
    simpa only [Function.iterate_zero_apply, sub_self, Nat.cast_zero, zero_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : X => (0 : ℂ)) l (𝓝 0))
  | succ n ih =>
    have ht := (hs.comp (hF.iterate n)).add ih
    convert ht using 1
    · funext x
      simp only [Function.comp_apply, Function.iterate_succ_apply']
      ring
    · congr 1
      push_cast
      ring

end HodgeLean.Foundations.Program
