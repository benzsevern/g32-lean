import HodgeLean.Foundations.Program.CodifferentialDictionaryNumeratorEvaluationProofs
import HodgeLean.Foundations.Program.CodifferentialDictionaryRamificationProofs

noncomputable section
open Filter Topology
namespace HodgeLean.Foundations.Program

def b66d_inverseNormalize (a b w : ℂ) : ℂ := a * b / (b - w * (b - a))

theorem b66d_inverseNormalize_hasDerivAt {a b w : ℂ} (hw : b - w * (b - a) ≠ 0) :
    HasDerivAt (b66d_inverseNormalize a b)
      (a * b * (b - a) / (b - w * (b - a)) ^ 2) w := by
  have h := (hasDerivAt_const w (a * b)).div ((hasDerivAt_const w b).sub
    ((hasDerivAt_id w).mul_const (b - a))) hw
  convert h using 1
  · rfl
  · simp only [Pi.sub_apply, id]
    ring

theorem b66d_inverseNormalize_center {a b s : ℂ}
    (hab : a * b ≠ 0) (hba : b - a ≠ 0) (hs : s ≠ 0) :
    b66d_inverseNormalize a b (b65s_normalize a b s) = s := by
  have hden : b - b65s_normalize a b s * (b - a) = a * b / s := by
    unfold b65s_normalize
    field_simp
    ring
  rw [b66d_inverseNormalize, hden]
  field_simp [hab]
  exact div_self hab

theorem b66d_inverseNormalize_difference {a b s w : ℂ}
    (hab : a * b ≠ 0) (hba : b - a ≠ 0) (hs : s ≠ 0)
    (hw : b - w * (b - a) ≠ 0) :
    b66d_inverseNormalize a b w - s =
      b66d_inverseNormalize a b w * s / (a * b / (b - a)) * (w - b65s_normalize a b s) := by
  have ha := (mul_ne_zero_iff.mp hab).1
  have hb := (mul_ne_zero_iff.mp hab).2
  unfold b66d_inverseNormalize b65s_normalize
  field_simp
  ring

theorem b66d_inverseNormalize_derivative_scaled {a b w : ℂ}
    (hab : a * b ≠ 0) (hba : b - a ≠ 0) (hw : b - w * (b - a) ≠ 0) :
    HasDerivAt (b66d_inverseNormalize a b)
      ((b66d_inverseNormalize a b w) ^ 2 / (a * b / (b - a))) w := by
  convert b66d_inverseNormalize_hasDerivAt hw using 1
  unfold b66d_inverseNormalize
  field_simp


end HodgeLean.Foundations.Program
