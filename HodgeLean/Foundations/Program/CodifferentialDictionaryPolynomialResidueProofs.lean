import HodgeLean.Foundations.Program.CodifferentialDictionaryNormalizedResidueProofs

noncomputable section
open Filter Topology
namespace HodgeLean.Foundations.Program

theorem b66d_polynomial_branch_residue (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ)
    (k : Fin 12) (N : Fin 10 → ℂ) (n : ℕ)
    (hab : a * b ≠ 0) (hba : b - a ≠ 0)
    (hs : poles (Sum.inr k) ≠ 0)
    (hR : b65g_rest poles k (poles (Sum.inr k)) ≠ 0) (hn : 0 < n) :
    TauCeti.Contour.residue (fun z : ℂ =>
      let s := b66d_inverseNormalize a b (b65s_normalize a b (poles (Sum.inr k)) + z ^ n)
      ((n : ℂ) * z ^ (n - 1))⁻¹ *
        ((1 / 4 : ℂ) * (∑ j : Fin 10, N j * s ^ j.val) / (b65q_denominator poles).eval s *
          (s ^ 2 / (a * b / (b - a)) * ((n : ℂ) * z ^ (n - 1))) ^ 2)) 0 =
      (n : ℂ) / 4 * ((∑ j : Fin 10, N j * poles (Sum.inr k) ^ j.val) /
        (b65g_rest poles k (poles (Sum.inr k)) *
          (a * b / ((b - a) * poles (Sum.inr k) ^ 2)))) := by
  let J : ℂ → ℂ := fun s => (∑ j : Fin 10, N j * s ^ j.val) / b65g_rest poles k s
  have hJ : AnalyticAt ℂ J (poles (Sum.inr k)) := by
    apply AnalyticAt.div
    · fun_prop
    · unfold b65g_rest
      fun_prop
    · exact hR
  have hh := b66d_normalized_power_residue hab hba hs hn hJ
  have heq : (fun z : ℂ =>
      let s := b66d_inverseNormalize a b (b65s_normalize a b (poles (Sum.inr k)) + z ^ n)
      ((n : ℂ) * z ^ (n - 1))⁻¹ *
        ((1 / 4 : ℂ) * (∑ j : Fin 10, N j * s ^ j.val) / (b65q_denominator poles).eval s *
          (s ^ 2 / (a * b / (b - a)) * ((n : ℂ) * z ^ (n - 1))) ^ 2)) =
      (fun z : ℂ => ((n : ℂ) * z ^ (n - 1))⁻¹ *
        ((1 / 4 : ℂ) * J (b66d_inverseNormalize a b (b65s_normalize a b (poles (Sum.inr k)) + z ^ n)) /
          (b66d_inverseNormalize a b (b65s_normalize a b (poles (Sum.inr k)) + z ^ n) - poles (Sum.inr k)) *
          ((b66d_inverseNormalize a b (b65s_normalize a b (poles (Sum.inr k)) + z ^ n)) ^ 2 /
            (a * b / (b - a)) * ((n : ℂ) * z ^ (n - 1))) ^ 2)) := by
    funext z
    dsimp [J]
    rw [b65g_denominator_eval poles k]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, hh]
  dsimp [J]
  field_simp

end HodgeLean.Foundations.Program
