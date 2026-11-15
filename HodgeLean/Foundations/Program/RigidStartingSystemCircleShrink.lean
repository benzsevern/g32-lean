import HodgeLean.Foundations.Program.RiemannRochProofs
import HodgeLean.Foundations.Program.RigidStartingSystemPathUnits

noncomputable section
open Set Metric
namespace HodgeLean.Foundations.Program

theorem b65r_shrink_circle_transport (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (U : Set ℂ) (hU : IsOpen U) (A : ℂ → E →L[ℂ] E) (hA : AnalyticOnNhd ℂ A U)
    (ψ : ℂ → ℂ) (R : ℝ)
    (q : C({z : ℂ // ‖z‖ < R ∧ z ≠ 0},U))
    (hq : ∀ z, (q z : ℂ) = ψ z) (G : E →L[ℂ] E)
    (s : ℝ) (hs : 0 < s)
    (hsmall : ∀ v : ℂ, v ≠ 0 → ‖v‖ < s →
      ∃ C : (E →L[ℂ] E)ˣ,
        b65f_transport E A (fun t ↦ ψ (Complex.exp (2*Real.pi*Complex.I*(t : ℂ))*v)) =
          C.val*G*(C⁻¹).val)
    (w : ℂ) (hw0 : w ≠ 0) (hw : ‖w‖ < R) :
    ∃ C : (E →L[ℂ] E)ˣ,
      b65f_transport E A (fun t ↦ ψ (Complex.exp (2*Real.pi*Complex.I*(t : ℂ))*w)) =
        C.val*G*(C⁻¹).val := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  let a : ℝ := min 1 (s/(2*‖w‖))
  have ha : 0 < a := lt_min zero_lt_one (div_pos hs (by positivity))
  have ha1 : a ≤ 1 := min_le_left _ _
  have haw : ‖(a : ℂ)*w‖ < s := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
    have hb := (le_div_iff₀ (by positivity : 0 < 2*‖w‖)).mp (min_le_right 1 (s/(2*‖w‖)))
    change a*(2*‖w‖) ≤ s at hb
    nlinarith
  obtain ⟨j,g,hjg,⟨H⟩⟩ := RiemannRochTop_punctured_disk_shrink_homotopy R a ha ha1
  obtain ⟨p,hp⟩ := RiemannRochTop_positive_circle_path R w hw hw0
  let K := (ContinuousMap.Homotopy.refl q).comp H
  let old := p.map (q.comp j).continuous
  let small := p.map (q.comp g).continuous
  have htrace (v : ℂ) (f : C({z : ℂ // ‖z‖ < R ∧ z ≠ 0},
      {z : ℂ // ‖z‖ < R ∧ z ≠ 0}))
      (hf : ∀ z, (f z : ℂ) = v*(z : ℂ)) :
      ∀ t : unitInterval, ((p.map (q.comp f).continuous) t : ℂ) =
        ψ (Complex.exp (2*Real.pi*Complex.I*((t : ℝ) : ℂ))*(v*w)) := by
    intro t
    change (q (f (p t)) : ℂ) = _
    rw [hq,hf,hp]
    have he : (((t : ℝ)*(2*Real.pi) : ℝ) : ℂ)*Complex.I =
        2*Real.pi*Complex.I*((t : ℝ) : ℂ) := by push_cast; ring
    rw [he]
    congr 1
    ring
  have hOld := htrace 1 j (fun z ↦ by simpa using (hjg z).1)
  have hSmall := htrace (a : ℂ) g (fun z ↦ (hjg z).2)
  have hsmallC : ∃ C : (E →L[ℂ] E)ˣ,
      b65f_transport E A (fun t ↦ (small.extend t).val) = C.val*G*(C⁻¹).val := by
    obtain ⟨C,hC⟩ := hsmall ((a : ℂ)*w)
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne') hw0) haw
    refine ⟨C,?_⟩
    rw [← hC]
    apply b65r_transport_eqOn
    intro t ht
    dsimp only
    rw [Path.extend_apply _ ht]
    exact hSmall ⟨t,ht⟩
  let k := (K.symm.evalAt ⟨w,hw,hw0⟩).symm
  obtain ⟨C,hC⟩ := b65r_stemmed_transport E U hU A hA k small G hsmallC
  have hh : ((k.trans small).trans k.symm).Homotopic old := by
    apply (Path.Homotopic.trans_assoc k small k.symm).trans
    simpa only [k,Path.symm_symm] using
      RiemannRochTop_homotopy_loop_conjugacy K.symm ⟨w,hw,hw0⟩ p
  refine ⟨C,?_⟩
  rw [← hC,b65f_homotopy_invariance E U hU A hA _ _ _ _ hh]
  apply b65r_transport_eqOn
  intro t ht
  dsimp only
  rw [Path.extend_apply _ ht]
  simpa only [one_mul] using (hOld ⟨t,ht⟩).symm

end HodgeLean.Foundations.Program
