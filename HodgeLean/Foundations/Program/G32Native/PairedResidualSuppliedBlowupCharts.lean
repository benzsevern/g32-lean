import HodgeLean.Foundations.Program.SchoenTowerL1bChartsSplit

/-! # Quotient-ring charts of the supplied universal blow-up -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native.FibreC
open HodgeLean.Foundations.Program

/-- Regular local centre generators identify the actual supplied blow-up charts,
with the coefficient maps and the entire inverse-image cover retained. -/
theorem residual_supplied_blowup_pair_charts
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (I : B.left.IdealSheafData)
    (hcartier : ∀ x : X.left, ∃ V : X.left.affineOpens, x ∈ V.1 ∧
      Nonempty (((I.comap p.left).ideal V) ≃ₗ[Γ(X.left, V)] Γ(X.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ V : T.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! u : T ⟶ X, u ≫ p = f)
    (U : B.left.affineOpens) (u v : Γ(B.left, U))
    (hI : I.ideal U = Ideal.span {u, v})
    (hv : IsRegular v) (hu : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u))
    (hu' : IsRegular u) (hv' : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v)) :
    ∃ (V₁ V₂ : X.left.affineOpens)
      (h₁ : V₁.1 ≤ p.left ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p.left ⁻¹ᵁ U.1)
      (e₁ : ring u v ≃+* Γ(X.left, V₁)) (e₂ : ring v u ≃+* Γ(X.left, V₂)),
      V₁.1 ⊔ V₂.1 = p.left ⁻¹ᵁ U.1 ∧
      e₁.toRingHom.comp (coeff u v) = (p.left.appLE U.1 V₁.1 h₁).hom ∧
      e₂.toRingHom.comp (coeff v u) = (p.left.appLE U.1 V₂.1 h₂).hom := by
  obtain ⟨M, j₁, j₂, π, hj₁, hj₂, hcover, hπ₁, hπ₂, _, hlift⟩ :=
    s2v_l1b_charts_overlap_descent Γ(B.left, U) u v hv hu hu' hv'
  obtain ⟨_, _, V₁, V₂, h₁, h₂, e₁, e₂, hc, he₁, he₂⟩ :=
    s2v_l1b_charts_blowup_comparison B X p I hcartier hblowup U u v hI hv hu hu' hv'
      M j₁ j₂ π ⟨hj₁, hj₂, hcover, hπ₁, hπ₂, hlift⟩
  exact ⟨V₁, V₂, h₁, h₂, e₁, e₂, hc, he₁, he₂⟩

#print axioms residual_supplied_blowup_pair_charts
end HodgeLean.Foundations.Program.G32Native.FibreC
