import HodgeLean.Foundations.Program.RelativeFrameFamilyFilled

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem rf7_degree_of_punctured_coordinate {Y : Type} [TopologicalSpace Y]
    (q : Y → ℂ) (hq : Continuous q) (c : ℂ) (ρ : ℝ) (k : ℕ) (hk : 0 < k)
    (v : rf7_nonzeroLocus q hq c → ℂ) (hv : Function.Injective v)
    (hrange : range v = {w : ℂ | w ≠ 0 ∧ ‖w‖ ^ k < ρ})
    (hpower : ∀ y, q y.val = c + v y ^ k)
    (z : ℂ) (hz : z ∈ Metric.ball c ρ) (hnz : z ≠ c) : Nat.card (q ⁻¹' {z}) = k := by
  classical
  let U := rf7_nonzeroLocus q hq c
  have hU (y : q ⁻¹' {z}) : q y.val ≠ c := fun h ↦ hnz (y.2.symm.trans h)
  let F : (q ⁻¹' {z}) → {w : ℂ // w ^ k = z - c} := fun y ↦
    ⟨v ⟨y.val, hU y⟩, by
      have hh := hpower ⟨y.val, hU y⟩
      rw [show q y.val = z from y.2] at hh
      linear_combination -hh⟩
  have hFi : Function.Injective F := by
    intro y y' h
    have hh : (F y).val = (F y').val := congrArg Subtype.val h
    have hh' := hv hh
    have hh'' : y.val = y'.val := congrArg (fun u : U ↦ u.val) hh'
    exact Subtype.ext hh''
  have hFs : Function.Surjective F := by
    rintro ⟨w, hw⟩
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, zero_pow hk.ne'] at hw
      exact hnz (sub_eq_zero.mp hw.symm)
    have hwmem : w ≠ 0 ∧ ‖w‖ ^ k < ρ := by
      refine ⟨hw0, ?_⟩
      rw [← norm_pow, hw]
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have hwR : w ∈ {w : ℂ | w ≠ 0 ∧ ‖w‖ ^ k < ρ} := hwmem
    obtain ⟨u, hu⟩ := hrange.symm ▸ hwR
    have hqu : q u.val = z := by
      rw [hpower, hu, hw]
      ring
    refine ⟨⟨u.val, hqu⟩, Subtype.ext ?_⟩
    change v ⟨u.val, hU ⟨u.val, hqu⟩⟩ = w
    exact hu
  exact (Nat.card_congr (Equiv.ofBijective F ⟨hFi, hFs⟩)).trans
    (rf7_power_fibre_card k hk (z - c) (sub_ne_zero.mpr hnz))

end HodgeLean.Foundations.Program
