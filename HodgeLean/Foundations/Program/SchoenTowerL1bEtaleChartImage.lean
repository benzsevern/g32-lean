import HodgeLean.Foundations.Program.SchoenTowerL1bEtaleSectionBlowup
import HodgeLean.Foundations.Program.SchoenTowerL1bComparisonSections

/-! Etale coordinates on the actual image of a binomial chart.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
universe u
namespace HodgeLean.Foundations.Program

/-- An actual open binomial chart carries etale coordinates in its affine image.
The equations use the actual pullback of each base section. -/
theorem s2v_l1b_etale_binomial_chart_image
    {X B : Scheme.{u}} (p : X ⟶ B) (U : B.affineOpens)
    {k σ : Type u} [CommRing k] [DecidableEq σ]
    (c : k →+* Γ(B, U)) (z : σ → Γ(B, U))
    (het : (MvPolynomial.eval₂Hom c z).Etale) (a b : σ) (hab : a ≠ b)
    (j : Spec (CommRingCat.of (s2v_L1bChart (z a) (z b))) ⟶ X)
    [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span
        {Polynomial.C (z a) - Polynomial.X * Polynomial.C (z b)})).comp Polynomial.C)) ≫
          U.2.fromSpec) :
    ∃ (V : X.affineOpens) (hV : V.1 ≤ p ⁻¹ᵁ U.1) (w : σ → Γ(X, V)),
      V.1 = j ''ᵁ ⊤ ∧
      (MvPolynomial.eval₂Hom ((p.appLE U.1 V.1 hV).hom.comp c) w).Etale ∧
      (∀ t, (p.appLE U.1 V.1 hV).hom (z t) =
        if t = a then w a * w b else w t) := by
  let q := Ideal.Quotient.mk (Ideal.span
    {Polynomial.C (z a) - Polynomial.X * Polynomial.C (z b)})
  let coeff := q.comp Polynomial.C
  obtain ⟨V, hV, e, hVe, he⟩ := s2v_l1b_chart_image_sections p U
    (CommRingCat.of (s2v_L1bChart (z a) (z b))) j (CommRingCat.ofHom coeff) hj
  obtain ⟨w, hw, hwe⟩ := s2v_l1b_etale_section_binomial_chart c z het a b hab
  let c' := (p.appLE U.1 V.1 hV).hom.comp c
  have hmap : MvPolynomial.eval₂Hom c' (fun t => e (w t)) =
      e.toRingHom.comp (MvPolynomial.eval₂Hom (coeff.comp c) w) := by
    apply MvPolynomial.ringHom_ext
    · intro d
      rw [MvPolynomial.eval₂Hom_C]
      change c' d = e ((MvPolynomial.eval₂Hom (coeff.comp c) w) (MvPolynomial.C d))
      rw [MvPolynomial.eval₂Hom_C]
      exact (RingHom.congr_fun he (c d)).symm
    · intro t
      rw [MvPolynomial.eval₂Hom_X']
      change e (w t) = e ((MvPolynomial.eval₂Hom (coeff.comp c) w) (MvPolynomial.X t))
      rw [MvPolynomial.eval₂Hom_X']
  refine ⟨V, hV, fun t => e (w t), hVe, ?_, ?_⟩
  · change (MvPolynomial.eval₂Hom c' (fun t => e (w t))).Etale
    rw [hmap]
    exact RingHom.Etale.stableUnderComposition _ _ hw
      (RingHom.Etale.of_bijective e.bijective)
  · intro t
    have H := congrArg e (hwe t)
    have Hc := RingHom.congr_fun he (z t)
    change e (q (Polynomial.C (z t))) = (p.appLE U.1 V.1 hV).hom (z t) at Hc
    rw [Hc] at H
    by_cases hta : t = a
    · rw [ite_eq_left hta, map_mul] at H
      rw [ite_eq_left hta]
      exact H
    · rw [ite_eq_right hta] at H ⊢
      exact H

end HodgeLean.Foundations.Program
