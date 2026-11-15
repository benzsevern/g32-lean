import HodgeLean.Foundations.Program.SchoenTowerL1bStrictTransformChart

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Finite ideal-sheaf products evaluate to the corresponding products in the actual section ring. -/
theorem s2v_l1b_ideal_sections_prod
    {X : Scheme} {J : Type*} [Fintype J]
    (D : J → X.IdealSheafData) (U : X.affineOpens) :
    (∏ j, D j).ideal U = ∏ j, (D j).ideal U := by
  let ev : X.IdealSheafData →* Ideal Γ(X, U) :=
    { toFun := fun I => I.ideal U
      map_one' := by simp only [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.ideal_top, Pi.top_apply, Ideal.one_eq_top]
      map_mul' := fun _ _ => rfl }
  exact map_prod ev D Finset.univ

/-- A cover by the two prime residual chart types gives the weighted total-transform identity of ideal sheaves. -/
theorem s2v_l1b_weighted_transform_of_prime_chart_cover
    {X Y : Scheme} (f : X ⟶ Y) {J A : Type*}
    [Fintype J] [DecidableEq J]
    (D : J → Y.IdealSheafData) (K : Y.IdealSheafData)
    (p q : J) (hpq : p ≠ q) (n : J → ℕ) (m : ℕ) (hn : n p + n q = m)
    (U : A → X.affineOpens) (hcover : ⨆ a, (U a).1 = ⊤)
    (s e : ∀ a, Γ(X, U a))
    (hprime : ∀ a, (Ideal.span {s a}).IsPrime)
    (he : ∀ a, e a ∉ Ideal.span {s a})
    (hK : ∀ a, (K.comap f).ideal (U a) = Ideal.span {e a})
    (hshape : ∀ a,
      (((D p).comap f).ideal (U a) = Ideal.span {s a * e a} ∧
        ((D q).comap f).ideal (U a) = Ideal.span {e a}) ∨
      (((D q).comap f).ideal (U a) = Ideal.span {s a * e a} ∧
        ((D p).comap f).ideal (U a) = Ideal.span {e a}))
    (hrest : ∀ a j, j ≠ p → j ≠ q →
      (s2c_strictTransform f (D j) K).ideal (U a) = ((D j).comap f).ideal (U a)) :
    (∏ j, ((D j).comap f) ^ n j) =
      (∏ j, (s2c_strictTransform f (D j) K) ^ n j) * (K.comap f) ^ m := by
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hcover
  intro a
  letI := hprime a
  simp only [s2v_l1b_ideal_sections_prod, Scheme.IdealSheafData.ideal_pow,
    Scheme.IdealSheafData.ideal_mul, Pi.pow_apply, Pi.mul_apply]
  rcases hshape a with ⟨hDp, hDq⟩ | ⟨hDq, hDp⟩
  · exact s2v_l1b_weighted_all_branches_chart f D K (U a) (s a) (e a)
      (he a) p q hpq hDp hDq (hK a) (hrest a) n m hn
  · exact s2v_l1b_weighted_all_branches_chart f D K (U a) (s a) (e a)
      (he a) q p hpq.symm hDq hDp (hK a)
      (fun j hjq hjp => hrest a j hjp hjq) n m (by omega)

/-- Prime or absent unselected branches need no separate strict-transform identity on the chart cover. -/
theorem s2v_l1b_weighted_transform_of_prime_branch_charts
    {X Y : Scheme} (f : X ⟶ Y) {J A : Type*}
    [Fintype J] [DecidableEq J]
    (D : J → Y.IdealSheafData) (K : Y.IdealSheafData)
    (p q : J) (hpq : p ≠ q) (n : J → ℕ) (m : ℕ) (hn : n p + n q = m)
    (U : A → X.affineOpens) (hcover : ⨆ a, (U a).1 = ⊤)
    (s e : ∀ a, Γ(X, U a))
    (hprime : ∀ a, (Ideal.span {s a}).IsPrime)
    (he : ∀ a, e a ∉ Ideal.span {s a})
    (hK : ∀ a, (K.comap f).ideal (U a) = Ideal.span {e a})
    (hshape : ∀ a,
      (((D p).comap f).ideal (U a) = Ideal.span {s a * e a} ∧
        ((D q).comap f).ideal (U a) = Ideal.span {e a}) ∨
      (((D q).comap f).ideal (U a) = Ideal.span {s a * e a} ∧
        ((D p).comap f).ideal (U a) = Ideal.span {e a}))
    (hrest : ∀ a j, j ≠ p → j ≠ q →
      ((D j).comap f).ideal (U a) = ⊤ ∨
        (((D j).comap f).ideal (U a)).IsPrime ∧
          ¬ (K.comap f).ideal (U a) ≤ ((D j).comap f).ideal (U a)) :
    (∏ j, ((D j).comap f) ^ n j) =
      (∏ j, (s2c_strictTransform f (D j) K) ^ n j) * (K.comap f) ^ m := by
  apply s2v_l1b_weighted_transform_of_prime_chart_cover f D K p q hpq n m hn
    U hcover s e hprime he hK hshape
  intro a j hjp hjq
  rcases hrest a j hjp hjq with hunit | ⟨hprime, hmiss⟩
  · rw [s2v_l1b_strictTransform_unit_chart f (D j) K (U a) hunit, hunit]
  · letI := hprime
    exact s2v_l1b_strictTransform_prime_unchanged f (D j) K (U a) hmiss

end HodgeLean.Foundations.Program
