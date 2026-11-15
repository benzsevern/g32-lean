import HodgeLean.Foundations.Program.SchoenTowerL1bEtaleBranchStep
import HodgeLean.Foundations.Program.SchoenTowerL1bReducedResidualFactorization

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The selected residual branch and every untouched coordinate retain exact equations in an actual successor chart. -/
theorem s2v_l1b_successor_branch_equations
    {X Y : Scheme} (f : X ⟶ Y) {J σ : Type*} [DecidableEq σ]
    (D : J → Y.IdealSheafData) (K : Y.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) (hV : V.1 ≤ f ⁻¹ᵁ U.1)
    {k : Type*} [CommRing k] [IsDomain k]
    (c : k →+* Γ(X, V)) (z : σ → Γ(Y, U)) (w : σ → Γ(X, V))
    (het : (MvPolynomial.eval₂Hom c w).Etale)
    (a b : σ) (hab : a ≠ b) (p q : J)
    (hcoords : ∀ t, (f.appLE U.1 V.1 hV).hom (z t) =
      if t = a then w a * w b else w t)
    (hDp : (D p).ideal U = Ideal.span {z a})
    (hDq : (D q).ideal U = Ideal.span {z b})
    (hK : K.ideal U = Ideal.span {z a, z b})
    (hrest : ∀ j, j ≠ p → j ≠ q → (D j).ideal U = ⊤ ∨
      ∃ t, t ≠ a ∧ t ≠ b ∧ (D j).ideal U = Ideal.span {z t}) :
    (s2c_strictTransform f (D p) K).ideal V = Ideal.span {w a} ∧
    (s2c_strictTransform f (D q) K).ideal V = ⊤ ∧
    ∀ j, j ≠ p → j ≠ q →
      (s2c_strictTransform f (D j) K).ideal V = ⊤ ∨
      ∃ t, t ≠ a ∧ t ≠ b ∧
        (s2c_strictTransform f (D j) K).ideal V = Ideal.span {w t} := by
  have ha : (f.appLE U.1 V.1 hV).hom (z a) = w a * w b := by
    rw [hcoords, ite_eq_left rfl]
  have hb : (f.appLE U.1 V.1 hV).hom (z b) = w b := by
    rw [hcoords, ite_eq_right hab.symm]
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
  refine ⟨?_, ?_, ?_⟩
  · exact s2v_l1b_strictTransform_reduced_residual_chart f (D p) K V (w a) (w b)
      (s2v_l1b_etale_coordinate_radical c w het a)
      (s2v_l1b_etale_coordinate_pair c w het b a hab.symm).2 hDp' hK'
  · exact s2v_l1b_strictTransform_exceptional_chart f (D q) K V (hDq'.trans hK'.symm)
  · intro j hjp hjq
    rcases hrest j hjp hjq with hunit | ⟨t, hta, htb, ht⟩
    · left
      apply s2v_l1b_strictTransform_unit_chart
      rw [s2v_l1b_comap_ideal_affine_charts f (D j) U V hV, hunit, Ideal.map_top]
    · right
      refine ⟨t, hta, htb, ?_⟩
      apply s2v_l1b_etale_chart_branch_step f (D j) K U V hV c z w het
        a b t hab hta htb hcoords ht
      rw [hK]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

end HodgeLean.Foundations.Program
