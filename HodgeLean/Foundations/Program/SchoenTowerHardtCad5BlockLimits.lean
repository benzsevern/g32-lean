import HodgeLean.Foundations.Program.SchoenTowerT11bDefs

/-! Ambient limit transport under actual output and parameter coordinate splitting. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_block_closure_split {q n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin (q + n))))
    (t : EuclideanSpace ℝ (Fin q)) (a : EuclideanSpace ℝ (Fin n))
    (hx : WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a i)) ∈ closure S) :
    (t, a) ∈ closure {p : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) |
      WithLp.toLp 2 (Fin.append (fun i => p.1 i) (fun i => p.2 i)) ∈ S} := by
  let split : EuclideanSpace ℝ (Fin (q + n)) →
      EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) := fun x =>
    (WithLp.toLp 2 (fun i => x (i.castAdd n)), WithLp.toLp 2 (fun i => x (i.natAdd q)))
  have hs : Continuous split :=
    ((PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i =>
      (continuous_apply (i.castAdd n)).comp (PiLp.continuous_ofLp 2 _)))).prodMk
    ((PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i =>
      (continuous_apply (i.natAdd q)).comp (PiLp.continuous_ofLp 2 _))))
  have himage : split '' S ⊆ {p : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) |
      WithLp.toLp 2 (Fin.append (fun i => p.1 i) (fun i => p.2 i)) ∈ S} := by
    rintro _ ⟨x, hx, rfl⟩
    have heta : WithLp.toLp 2 (Fin.append (fun i => x (i.castAdd n))
        (fun i => x (i.natAdd q))) = x := by
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Fin.append_left, Fin.append_right]
    change WithLp.toLp 2 (Fin.append (fun i => x (i.castAdd n))
      (fun i => x (i.natAdd q))) ∈ S
    rw [heta]
    exact hx
  have hcl := mem_closure_image hs.continuousAt hx
  have heq : split (WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a i))) = (t, a) := by
    apply Prod.ext <;> ext i <;> simp only [split, Fin.append_left, Fin.append_right]
  rw [heq] at hcl
  exact closure_mono himage hcl

end HodgeLean.Foundations.Program
