import HodgeLean.Foundations.Program.SchoenTowerL1bReducedResidualFactorization
import HodgeLean.Foundations.Program.SchoenTowerL1bChartFactorization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A reduced residual chart gives the weighted identity for all retained branches. -/
theorem s2v_l1b_weighted_all_branches_reduced_chart
    {X Y : Scheme} (f : X ⟶ Y) {J : Type*} [Fintype J] [DecidableEq J]
    (D : J → Y.IdealSheafData) (K : Y.IdealSheafData)
    (U : X.affineOpens) (s e : Γ(X, U))
    (hs : (Ideal.span {s}).IsRadical)
    (he : IsRegular (Ideal.Quotient.mk (Ideal.span {s}) e))
    (p q : J) (hpq : p ≠ q)
    (hDp : ((D p).comap f).ideal U = Ideal.span {s * e})
    (hDq : ((D q).comap f).ideal U = Ideal.span {e})
    (hK : (K.comap f).ideal U = Ideal.span {e})
    (hrest : ∀ j, j ≠ p → j ≠ q →
      (s2c_strictTransform f (D j) K).ideal U = ((D j).comap f).ideal U)
    (n : J → ℕ) (m : ℕ) (hn : n p + n q = m) :
    (∏ j, (((D j).comap f).ideal U) ^ n j) =
      (∏ j, ((s2c_strictTransform f (D j) K).ideal U) ^ n j) *
        ((K.comap f).ideal U) ^ m := by
  let A := fun j => ((D j).comap f).ideal U
  let T := fun j => (s2c_strictTransform f (D j) K).ideal U
  let E := (K.comap f).ideal U
  have hfactor (j : J) : A j = T j * E ^
      (if j = p then 1 else if j = q then 1 else 0) := by
    by_cases hjp : j = p
    · subst j
      dsimp only [A, T, E]
      rw [ite_eq_left rfl, pow_one,
        s2v_l1b_strictTransform_reduced_residual_chart f (D p) K U s e hs he hDp hK,
        hDp, hK, Ideal.span_singleton_mul_span_singleton]
    · by_cases hjq : j = q
      · subst j
        dsimp only [A, T, E]
        rw [ite_eq_right hjp, ite_eq_left rfl, pow_one,
          s2v_l1b_strictTransform_exceptional_chart f (D q) K U (hDq.trans hK.symm),
          ← Ideal.one_eq_top, one_mul, hDq, hK]
      · rw [ite_eq_right hjp, ite_eq_right hjq, pow_zero, mul_one]
        exact (hrest j hjp hjq).symm
  have H := s2v_l1b_paired_product_transport A T (fun _ : Unit => E) n
    (fun _ => p) (fun _ => q) (fun _ => hpq) m (fun _ => hn)
    (fun j => by simpa only [Fintype.prod_unique] using hfactor j)
  simpa only [Fintype.prod_unique] using H

/-- Reduced residual charts glue to the weighted total-transform identity, allowing several components. -/
theorem s2v_l1b_weighted_transform_of_reduced_chart_cover
    {X Y : Scheme} (f : X ⟶ Y) {J A : Type*}
    [Fintype J] [DecidableEq J]
    (D : J → Y.IdealSheafData) (K : Y.IdealSheafData)
    (p q : J) (hpq : p ≠ q) (n : J → ℕ) (m : ℕ) (hn : n p + n q = m)
    (U : A → X.affineOpens) (hcover : ⨆ a, (U a).1 = ⊤)
    (s e : ∀ a, Γ(X, U a))
    (hs : ∀ a, (Ideal.span {s a}).IsRadical)
    (he : ∀ a, IsRegular (Ideal.Quotient.mk (Ideal.span {s a}) (e a)))
    (hK : ∀ a, (K.comap f).ideal (U a) = Ideal.span {e a})
    (hshape : ∀ a,
      (((D p).comap f).ideal (U a) = Ideal.span {s a * e a} ∧
        ((D q).comap f).ideal (U a) = Ideal.span {e a}) ∨
      (((D q).comap f).ideal (U a) = Ideal.span {s a * e a} ∧
        ((D p).comap f).ideal (U a) = Ideal.span {e a}))
    (hrest : ∀ a j, j ≠ p → j ≠ q →
      (((D j).comap f).ideal (U a)).IsRadical ∧
      ∀ Q ∈ (((D j).comap f).ideal (U a)).minimalPrimes,
        ¬ (K.comap f).ideal (U a) ≤ Q) :
    (∏ j, ((D j).comap f) ^ n j) =
      (∏ j, (s2c_strictTransform f (D j) K) ^ n j) * (K.comap f) ^ m := by
  have hrest' (a : A) (j : J) (hjp : j ≠ p) (hjq : j ≠ q) :
      (s2c_strictTransform f (D j) K).ideal (U a) = ((D j).comap f).ideal (U a) :=
    s2v_l1b_strictTransform_ideal_reduced_chart f (D j) K (U a)
      (hrest a j hjp hjq).1 (hrest a j hjp hjq).2
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hcover
  intro a
  simp only [s2v_l1b_ideal_sections_prod, Scheme.IdealSheafData.ideal_pow,
    Scheme.IdealSheafData.ideal_mul, Pi.pow_apply, Pi.mul_apply]
  rcases hshape a with ⟨hDp, hDq⟩ | ⟨hDq, hDp⟩
  · exact s2v_l1b_weighted_all_branches_reduced_chart f D K (U a) (s a) (e a)
      (hs a) (he a) p q hpq hDp hDq (hK a) (hrest' a) n m hn
  · exact s2v_l1b_weighted_all_branches_reduced_chart f D K (U a) (s a) (e a)
      (hs a) (he a) q p hpq.symm hDq hDp (hK a)
      (fun j hjq hjp => hrest' a j hjp hjq) n m (by omega)

end HodgeLean.Foundations.Program
