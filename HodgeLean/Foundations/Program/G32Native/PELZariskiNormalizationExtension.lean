import HodgeLean.Foundations.Program.G32Native.PELZariskiNormalizer

noncomputable section
open MvPolynomial
namespace HodgeLean.Foundations
variable {k : Type*} [Field k] {n : ℕ}

/-- Matrix inversion is continuous for the matrix Zariski topology. -/
theorem pel_zariski_continuous_inv :
    @Continuous _ _ (g1_zariski k n) (g1_zariski k n)
      (fun g : Matrix.GeneralLinearGroup (Fin n) k => g⁻¹) := by
  let V := g1_varMatrix k n
  apply pel_continuous_of_denominator V.det (fun i => V.adjugate i.1 i.2) _
  · intro g
    rw [RingHom.map_det, g1_mapMatrix_eval_varMatrix]
    exact g.det_ne_zero
  · intro g i
    have hunit : g.val * (g⁻¹).val = 1 := congrArg Units.val (mul_inv_cancel g)
    have ha : g.val.adjugate = g.val.det • (g⁻¹).val := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) k => M * (g⁻¹).val)
        (Matrix.adjugate_mul g.val)
      simpa only [Matrix.mul_assoc, hunit, Matrix.mul_one, Matrix.smul_mul,
        Matrix.one_mul] using h
    have hm : (eval (g1_coords g)).mapMatrix V.adjugate =
        g.val.det • (g⁻¹).val := by
      rw [RingHom.map_adjugate, g1_mapMatrix_eval_varMatrix, ha]
    rw [RingHom.map_det, g1_mapMatrix_eval_varMatrix]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) k => M i.1 i.2) hm

/-- The normalizer of a Zariski closed subgroup is Zariski closed. -/
theorem pel_zariski_isClosed_normalizer
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) k))
    (hH : @IsClosed _ (g1_zariski k n) (H : Set _)) :
    @IsClosed _ (g1_zariski k n) (Subgroup.normalizer (H : Set (Matrix.GeneralLinearGroup (Fin n) k))).carrier := by
  letI := g1_zariski k n
  have hC := pel_isClosed_conjugation_condition H hH
  have he : (Subgroup.normalizer (H : Set (Matrix.GeneralLinearGroup (Fin n) k))).carrier =
      {g | ∀ x ∈ H, g⁻¹ * x * g ∈ H} ∩
      (fun g => g⁻¹) ⁻¹' {g | ∀ x ∈ H, g⁻¹ * x * g ∈ H} := by
    ext g
    change (g ∈ Subgroup.normalizer (H : Set _)) ↔ _
    rw [Subgroup.mem_normalizer_iff'']
    change (∀ x, x ∈ H ↔ g⁻¹ * x * g ∈ H) ↔
      (∀ x ∈ H, g⁻¹ * x * g ∈ H) ∧ (∀ x ∈ H, g⁻¹⁻¹ * x * g⁻¹ ∈ H)
    constructor
    · intro h
      refine ⟨fun x hx => (h x).mp hx, fun x hx => ?_⟩
      apply (h (g * x * g⁻¹)).mpr
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel, mul_one] using hx
    · rintro ⟨h, hi⟩ x
      refine ⟨h x, fun hx => ?_⟩
      have hh := hi (g⁻¹ * x * g) hx
      simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hh
  rw [he]
  exact hC.inter (hC.preimage pel_zariski_continuous_inv)

/-- A conjugation inclusion holding on a set holds on its Zariski closure. -/
theorem pel_normalization_on_zariski_closure
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) k))
    (hH : @IsClosed _ (g1_zariski k n) (H : Set _))
    (S : Set (Matrix.GeneralLinearGroup (Fin n) k))
    (hS : ∀ g ∈ S, ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    ∀ g ∈ @closure _ (g1_zariski k n) S, ∀ x ∈ H, g⁻¹ * x * g ∈ H := by
  exact @closure_minimal _ (g1_zariski k n) S _ hS
    (pel_isClosed_conjugation_condition H hH)

end HodgeLean.Foundations
