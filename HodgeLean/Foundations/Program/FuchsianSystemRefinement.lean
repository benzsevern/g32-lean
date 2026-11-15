import HodgeLean.Foundations.Program.FuchsianSystemPolygon

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

def b65f_reverseProduct {M : Type*} [Monoid M] (f : ℕ → M) (n : ℕ) : M :=
  (List.ofFn (fun i : Fin n ↦ f i.val)).reverse.prod

theorem b65f_reverseProduct_succ {M : Type*} [Monoid M] (f : ℕ → M) (n : ℕ) :
    b65f_reverseProduct f (n + 1) = f n * b65f_reverseProduct f n := by
  simp only [b65f_reverseProduct, List.ofFn_succ', Fin.val_castSucc, Fin.val_last,
    List.concat_eq_append, List.reverse_concat, List.prod_cons]

theorem b65f_reverseProduct_pairs {M : Type*} [Monoid M] (f : ℕ → M) (n : ℕ) :
    b65f_reverseProduct f (2 * n) =
      b65f_reverseProduct (fun i ↦ f (2 * i + 1) * f (2 * i)) n := by
  induction n with
  | zero => simp [b65f_reverseProduct]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      b65f_reverseProduct_succ, b65f_reverseProduct_succ, ih,
      b65f_reverseProduct_succ, mul_assoc]

theorem b65f_reverseProduct_congr {M : Type*} [Monoid M] {f g : ℕ → M} {n : ℕ}
    (h : ∀ i < n, f i = g i) : b65f_reverseProduct f n = b65f_reverseProduct g n := by
  unfold b65f_reverseProduct
  congr 3
  funext i
  exact h i.val i.isLt

theorem b65f_segment_local_cocycle {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {A : ℂ → E →L[ℂ] E}
    {u v w : ℂ} {r : ℝ} (hr : 0 < r)
    (hA : AnalyticOnNhd ℂ A (ball u r)) (hv : dist v u < r / 4)
    (hw : dist w u < r / 4) :
    b65f_segment E A v w * b65f_segment E A u v = b65f_segment E A u w := by
  have hsub : ball v (r / 2) ⊆ ball u r := by
    intro x hx
    have hh := dist_triangle x v u
    have hx' := mem_ball.mp hx
    apply mem_ball.mpr
    linarith
  have hwv : w ∈ ball v (r / 2) := by
    apply mem_ball.mpr
    have hh := dist_triangle w u v
    rw [dist_comm u v] at hh
    linarith
  exact b65f_segment_propagates (by positivity) (hA.mono hsub)
    (fun z hz ↦ b65f_segment_hasDerivAt hA (hsub hz)) hwv

end HodgeLean.Foundations.Program
