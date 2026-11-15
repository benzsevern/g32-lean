import HodgeLean.Foundations.Program.SchoenTowerL1bActionSourceLiftContinuity
import HodgeLean.Foundations.Program.SchoenTowerL1bActionEndLogComparison
import HodgeLean.Foundations.Program.SchoenTowerL1bActionLiftEnd
import HodgeLean.Foundations.Program.SchoenTowerL1bActionOrbitScalar
import HodgeLean.Foundations.Program.SchoenTowerL1bActionSourceOrbit

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A continuous local conjugacy with signed logarithmic deck action
transports a positive primitive lifted return to the target tangent scalar. -/
theorem s2v_l1b_action_conjugate_lift_scalar
    (f g H L : ℂ → ℂ) (a b : ℂ)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hH0 : H 0 = 0)
    (hf : HasDerivAt f (Complex.exp a) 0) (hg : HasDerivAt g (Complex.exp b) 0)
    (hfc : ∀ᶠ z : ℂ in 𝓝 0, ContinuousAt f z)
    (hgc : ∀ᶠ z : ℂ in 𝓝 0, ContinuousAt g z)
    (hHc : ContinuousAt H 0)
    (hconj : ∀ᶠ z : ℂ in 𝓝 0, H (f z) = g (H z))
    (B : ℝ) (hLc : ContinuousOn L {z : ℂ | z.re < B})
    (heL : ∀ z, z.re < B → Complex.exp (L z) = H (Complex.exp z))
    (ε : ℤ) (hdeck : ∀ z, z.re < B →
      L (z + 2 * Real.pi * Complex.I) = L z + (ε : ℂ) * (2 * Real.pi * Complex.I))
    (N : ℕ) (hN : 0 < N)
    (hreturn : ∀ᶠ z : ℂ in comap Complex.re atBot,
      (s2v_l1b_action_sourceLift f a)^[N] z = z + 2 * Real.pi * Complex.I) :
    Complex.exp b = Complex.exp ((ε : ℂ) * (2 * Real.pi * Complex.I) / (N : ℂ)) := by
  let l := comap Complex.re atBot
  let F := s2v_l1b_action_sourceLift f a
  let G := s2v_l1b_action_sourceLift g b
  haveI : NeBot l := Filter.comap_neBot (fun s hs => by
    obtain ⟨t, ht⟩ := Filter.nonempty_of_mem hs
    exact ⟨(t : ℂ), by simpa only [Complex.ofReal_re] using ht⟩)
  have hFl : Tendsto F l l := s2v_l1b_action_sourceLift_tendsto_left f a hf0 hf
  have hLl : Tendsto L l l := s2v_l1b_action_log_lift_tendsto_left H L hHc hH0 B heL
  have hLe : ∀ᶠ z : ℂ in l, Complex.exp (L z) = H (Complex.exp z) := by
    filter_upwards [(tendsto_comap : Tendsto Complex.re l atBot).eventually
      (eventually_lt_atBot B)] with z hz
    exact heL z hz
  have hFe : ∀ᶠ z : ℂ in l, Complex.exp (F z) = f (Complex.exp z) := by
    simpa only [Function.iterate_one] using
      s2v_l1b_action_sourceLift_iterate_exp_eventually f a hf0 hf 1
  have hGe : ∀ᶠ z : ℂ in l, Complex.exp (G z) = g (Complex.exp z) := by
    simpa only [Function.iterate_one] using
      s2v_l1b_action_sourceLift_iterate_exp_eventually g b hg0 hg 1
  have he : Tendsto Complex.exp l (𝓝 (0 : ℂ)) := by
    change Tendsto Complex.exp (comap Complex.re atBot) (𝓝 (0 : ℂ))
    rw [← Complex.comap_exp_nhds_zero]
    exact tendsto_comap
  have hprojection : ∀ᶠ z : ℂ in l,
      Complex.exp (L (F z)) = Complex.exp (G (L z)) := by
    filter_upwards [hFl.eventually hLe, hFe, he.eventually hconj, hLe,
      hLl.eventually hGe] with z hLF hFz hcz hLz hGL
    calc
      Complex.exp (L (F z)) = H (Complex.exp (F z)) := hLF
      _ = H (f (Complex.exp z)) := congrArg H hFz
      _ = g (H (Complex.exp z)) := hcz
      _ = g (Complex.exp (L z)) := congrArg g hLz.symm
      _ = Complex.exp (G (L z)) := hGL.symm
  have hLc' : ∀ᶠ z : ℂ in l, ContinuousAt L z :=
    s2v_l1b_action_halfplane_eventually_continuousAt L B hLc
  have hFc : ∀ᶠ z : ℂ in l, ContinuousAt F z :=
    s2v_l1b_action_sourceLift_eventually_continuousAt f a hf0 hf hfc
  have hGc : ∀ᶠ z : ℂ in l, ContinuousAt G z :=
    s2v_l1b_action_sourceLift_eventually_continuousAt g b hg0 hg hgc
  have hLFc : ∀ᶠ z : ℂ in l, ContinuousAt (fun w => L (F w)) z := by
    filter_upwards [hFl.eventually hLc', hFc] with z hLz hFz
    simpa only [Function.comp_def] using ContinuousAt.comp (f := F) (g := L) hLz hFz
  have hGLc : ∀ᶠ z : ℂ in l, ContinuousAt (fun w => G (L w)) z := by
    filter_upwards [hLl.eventually hGc, hLc'] with z hGz hLz
    simpa only [Function.comp_def] using ContinuousAt.comp (f := L) (g := G) hGz hLz
  obtain ⟨m, hm⟩ := s2v_l1b_action_end_log_lifts_differ_int
    (fun z => L (F z)) (fun z => G (L z)) hLFc hGLc hprojection
  have herror := (s2v_l1b_action_sourceLift_error_tendsto g b hg0 hg).comp hLl
  have hstep : Tendsto (fun z => L (F z) - L z) l
      (𝓝 (b + (m : ℂ) * (2 * Real.pi * Complex.I))) := by
    have ht := herror.add_const (b + (m : ℂ) * (2 * Real.pi * Complex.I))
    have heq : (fun z => G (L z) - L z - b +
        (b + (m : ℂ) * (2 * Real.pi * Complex.I))) =ᶠ[l] (fun z => L (F z) - L z) := by
      filter_upwards [hm] with z hz
      rw [hz]
      ring
    simpa only [Function.comp_def, zero_add] using ht.congr' heq
  have hd : ∀ᶠ z : ℂ in l,
      L (z + 2 * Real.pi * Complex.I) = L z + (ε : ℂ) * (2 * Real.pi * Complex.I) := by
    filter_upwards [(tendsto_comap : Tendsto Complex.re l atBot).eventually
      (eventually_lt_atBot B)] with z hz
    exact hdeck z hz
  have hs := s2v_l1b_action_asymptotic_rotation_scalar l F
    (fun z => z + 2 * Real.pi * Complex.I) L hFl
    (b + (m : ℂ) * (2 * Real.pi * Complex.I)) hstep N hN ε hreturn hd
  simpa only [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one] using hs

end HodgeLean.Foundations.Program
