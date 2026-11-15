import HodgeLean.Foundations.Program.SchoenTowerL1bEtaleWeightedChart
import HodgeLean.Foundations.Program.SchoenTowerL1bAffineIdeal

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Base coordinate equations and the actual chart section map give the weighted transform identity. -/
theorem s2v_l1b_weighted_coordinate_pullback
    {X Y : Scheme} (f : X ⟶ Y) {J σ : Type*}
    [Fintype J] [DecidableEq J] [DecidableEq σ]
    (D : J → Y.IdealSheafData) (K : Y.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) (hV : V.1 ≤ f ⁻¹ᵁ U.1)
    {k : Type*} [CommRing k] [IsDomain k]
    (c : k →+* Γ(X, V)) (z : σ → Γ(Y, U)) (w : σ → Γ(X, V))
    (het : (MvPolynomial.eval₂Hom c w).Etale)
    (a b : σ) (hab : a ≠ b) (p q : J) (hpq : p ≠ q)
    (hcoords : ∀ t, (f.appLE U.1 V.1 hV).hom (z t) =
      if t = a then w a * w b else w t)
    (hDp : (D p).ideal U = Ideal.span {z a})
    (hDq : (D q).ideal U = Ideal.span {z b})
    (hK : K.ideal U = Ideal.span {z a, z b})
    (hrest : ∀ j, j ≠ p → j ≠ q → (D j).ideal U = ⊤ ∨
      ∃ t, t ≠ a ∧ t ≠ b ∧ (D j).ideal U = Ideal.span {z t})
    (n : J → ℕ) (m : ℕ) (hn : n p + n q = m) :
    (∏ j, (((D j).comap f).ideal V) ^ n j) =
      (∏ j, ((s2c_strictTransform f (D j) K).ideal V) ^ n j) *
        ((K.comap f).ideal V) ^ m := by
  have ha := hcoords a
  have hb := hcoords b
  rw [if_pos rfl] at ha
  rw [if_neg hab.symm] at hb
  have hDp' : ((D p).comap f).ideal V = Ideal.span {w a * w b} := by
    rw [s2v_l1b_comap_ideal_affine_charts f (D p) U V hV, hDp,
      Ideal.map_span, Set.image_singleton, ha]
  have hDq' : ((D q).comap f).ideal V = Ideal.span {w b} := by
    rw [s2v_l1b_comap_ideal_affine_charts f (D q) U V hV, hDq,
      Ideal.map_span, Set.image_singleton, hb]
  have hK' : (K.comap f).ideal V = Ideal.span {w b} := by
    rw [s2v_l1b_comap_ideal_affine_charts f K U V hV, hK,
      Ideal.map_span, Set.image_insert_eq, Set.image_singleton, ha, hb]
    exact Ideal.span_pair_eq_span_right_iff_dvd.mpr (dvd_mul_left _ _)
  apply s2v_l1b_weighted_transform_etale_chart f D K V c w het a b hab
    p q hpq hDp' hDq' hK' _ n m hn
  intro j hjp hjq
  rcases hrest j hjp hjq with hunit | ⟨t, hta, htb, ht⟩
  · left
    rw [s2v_l1b_comap_ideal_affine_charts f (D j) U V hV, hunit, Ideal.map_top]
  · right
    refine ⟨t, htb, ?_⟩
    rw [s2v_l1b_comap_ideal_affine_charts f (D j) U V hV, ht,
      Ideal.map_span, Set.image_singleton, hcoords, if_neg hta]

end HodgeLean.Foundations.Program
