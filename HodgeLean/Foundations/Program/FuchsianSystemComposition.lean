import HodgeLean.Foundations.Program.FuchsianSystemConvergence

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65f_reverseProduct_add {M : Type*} [Monoid M] (f : ℕ → M) (n m : ℕ) :
    b65f_reverseProduct f (n + m) =
      b65f_reverseProduct (fun i ↦ f (n + i)) m * b65f_reverseProduct f n := by
  induction m with
  | zero => simp [b65f_reverseProduct]
  | succ m ih =>
    rw [Nat.add_succ, b65f_reverseProduct_succ, ih, b65f_reverseProduct_succ, mul_assoc]

theorem b65f_polygon_trans {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) {U : Set ℂ} {x y z : U}
    (γ : Path x y) (δ : Path y z) (N : ℕ) :
    b65f_polygon E A (fun t ↦ ((γ.trans δ).extend t).val) (N + 1) =
      b65f_polygon E A (fun t ↦ (δ.extend t).val) N *
        b65f_polygon E A (fun t ↦ (γ.extend t).val) N := by
  let k := 2 ^ N
  have hk : 0 < k := pow_pos (by norm_num) N
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hkR : (k : ℝ) = (2 : ℝ) ^ N := by simp [k]
  let f : ℕ → E →L[ℂ] E := fun i ↦ b65f_segment E A
    (((γ.trans δ).extend ((i : ℝ) / (2 * k))).val)
    (((γ.trans δ).extend (((i : ℝ) + 1) / (2 * k))).val)
  let g : ℕ → E →L[ℂ] E := fun i ↦ b65f_segment E A
    ((γ.extend ((i : ℝ) / k)).val) ((γ.extend (((i : ℝ) + 1) / k)).val)
  let d : ℕ → E →L[ℂ] E := fun i ↦ b65f_segment E A
    ((δ.extend ((i : ℝ) / k)).val) ((δ.extend (((i : ℝ) + 1) / k)).val)
  have hleft : b65f_reverseProduct f k = b65f_reverseProduct g k := by
    apply b65f_reverseProduct_congr
    intro i hi
    have hiR : (i : ℝ) + 1 ≤ k := by exact_mod_cast (show i + 1 ≤ k by omega)
    have h0 : (i : ℝ) / (2 * k) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
      linarith
    have h1 : ((i : ℝ) + 1) / (2 * k) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
      linarith
    have he0 : 2 * ((i : ℝ) / (2 * k)) = (i : ℝ) / k := by field_simp
    have he1 : 2 * (((i : ℝ) + 1) / (2 * k)) = ((i : ℝ) + 1) / k := by field_simp
    simp only [f, g, Path.extend_trans_of_le_half γ δ h0,
      Path.extend_trans_of_le_half γ δ h1, he0, he1]
  have hright : b65f_reverseProduct (fun i ↦ f (k + i)) k = b65f_reverseProduct d k := by
    apply b65f_reverseProduct_congr
    intro i hi
    have h0 : 1 / 2 ≤ ((k : ℝ) + i) / (2 * k) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
      have : (0 : ℝ) ≤ i := by positivity
      linarith
    have h1 : 1 / 2 ≤ ((k : ℝ) + i + 1) / (2 * k) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
      have : (0 : ℝ) ≤ i := by positivity
      linarith
    have he0 : 2 * (((k : ℝ) + i) / (2 * k)) - 1 = (i : ℝ) / k := by field_simp; ring
    have he1 : 2 * (((k : ℝ) + i + 1) / (2 * k)) - 1 = ((i : ℝ) + 1) / k := by field_simp; ring
    simp only [f, d, Nat.cast_add, Path.extend_trans_of_half_le γ δ h0,
      Path.extend_trans_of_half_le γ δ h1, he0, he1]
  have hh := b65f_reverseProduct_add f k k
  rw [hleft, hright] at hh
  simpa [b65f_polygon, b65f_reverseProduct, f, g, d, k, pow_succ, two_mul, mul_comm] using hh

end HodgeLean.Foundations.Program
