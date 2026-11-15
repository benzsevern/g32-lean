import HodgeLean.Foundations.Program.G32Native.PELZariskiRationalMaps

noncomputable section
open MvPolynomial
namespace HodgeLean.Foundations
variable {k : Type*} [Field k] {n : ℕ}

/-- Conjugation of a fixed matrix is a regular map in the conjugating matrix. -/
theorem pel_continuous_conjugating (x : Matrix.GeneralLinearGroup (Fin n) k) :
    @Continuous _ _ (g1_zariski k n) (g1_zariski k n) (fun g => g⁻¹ * x * g) := by
  let V := g1_varMatrix k n
  let D := V.det
  let Q := V.adjugate * x.val.map C * V
  apply pel_continuous_of_denominator D (fun i => Q i.1 i.2) _
  · intro g
    change eval (g1_coords g) V.det ≠ 0
    rw [RingHom.map_det, g1_mapMatrix_eval_varMatrix]
    exact g.det_ne_zero
  · intro g i
    have hunit : g.val * (g⁻¹).val = 1 := congrArg Units.val (mul_inv_cancel g)
    have ha : g.val.adjugate = g.val.det • (g⁻¹).val := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) k => M * (g⁻¹).val)
        (Matrix.adjugate_mul g.val)
      simpa only [Matrix.mul_assoc, hunit, Matrix.mul_one, Matrix.smul_mul,
        Matrix.one_mul] using h
    have hx : (eval (g1_coords g)).mapMatrix (x.val.map C) = x.val := by
      ext a b
      simp
    have hm : (eval (g1_coords g)).mapMatrix Q =
        g.val.det • ((g⁻¹).val * x.val * g.val) := by
      dsimp [Q]
      rw [map_mul, map_mul, RingHom.map_adjugate,
        g1_mapMatrix_eval_varMatrix, hx, ha, Matrix.smul_mul, Matrix.smul_mul]
    have hd : eval (g1_coords g) D = g.val.det := by
      dsimp [D]
      rw [RingHom.map_det, g1_mapMatrix_eval_varMatrix]
    rw [hd]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) k => M i.1 i.2) hm

/-- The matrices sending a fixed subgroup into itself by inverse conjugation
form a Zariski closed set when that subgroup is Zariski closed. -/
theorem pel_isClosed_conjugation_condition
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) k))
    (hH : @IsClosed _ (g1_zariski k n) (H : Set _)) :
    @IsClosed _ (g1_zariski k n) {g | ∀ x ∈ H, g⁻¹ * x * g ∈ H} := by
  letI := g1_zariski k n
  have he : {g | ∀ x ∈ H, g⁻¹ * x * g ∈ H} =
      ⋂ x ∈ H, (fun g => g⁻¹ * x * g) ⁻¹' (H : Set _) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [he]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    hH.preimage (pel_continuous_conjugating x)

end HodgeLean.Foundations
