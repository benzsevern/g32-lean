import HodgeLean.Foundations.Program.SchoenTowerL1bReducedWeightedCover

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual etale coordinate equations give the weighted one-step identity on a blowup chart. -/
theorem s2v_l1b_weighted_transform_etale_chart
    {X Y : Scheme} (f : X ⟶ Y) {J : Type*} [Fintype J] [DecidableEq J]
    (D : J → Y.IdealSheafData) (K : Y.IdealSheafData)
    (U : X.affineOpens) {k σ : Type*} [CommRing k] [IsDomain k]
    (c : k →+* Γ(X, U)) (z : σ → Γ(X, U))
    (het : (MvPolynomial.eval₂Hom c z).Etale)
    (a b : σ) (hab : a ≠ b) (p q : J) (hpq : p ≠ q)
    (hDp : ((D p).comap f).ideal U = Ideal.span {z a * z b})
    (hDq : ((D q).comap f).ideal U = Ideal.span {z b})
    (hK : (K.comap f).ideal U = Ideal.span {z b})
    (hrest : ∀ j, j ≠ p → j ≠ q →
      ((D j).comap f).ideal U = ⊤ ∨
      ∃ t : σ, t ≠ b ∧ ((D j).comap f).ideal U = Ideal.span {z t})
    (n : J → ℕ) (m : ℕ) (hn : n p + n q = m) :
    (∏ j, (((D j).comap f).ideal U) ^ n j) =
      (∏ j, ((s2c_strictTransform f (D j) K).ideal U) ^ n j) *
        ((K.comap f).ideal U) ^ m := by
  apply s2v_l1b_weighted_all_branches_reduced_chart f D K U (z a) (z b)
    (s2v_l1b_etale_coordinate_radical c z het a)
    (s2v_l1b_etale_coordinate_pair c z het b a hab.symm).2
    p q hpq hDp hDq hK _ n m hn
  intro j hjp hjq
  rcases hrest j hjp hjq with hunit | ⟨t, htb, ht⟩
  · rw [s2v_l1b_strictTransform_unit_chart f (D j) K U hunit, hunit]
  · rw [s2v_l1b_strictTransform_etale_coordinate f (D j) K U c z het t b htb ht
      (by rw [hK]; exact Ideal.subset_span (Set.mem_singleton _)), ht]

end HodgeLean.Foundations.Program
