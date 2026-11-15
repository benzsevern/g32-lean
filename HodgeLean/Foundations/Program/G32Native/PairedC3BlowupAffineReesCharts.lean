import HodgeLean.Foundations.Program.SchoenTowerL1b

/-! # Affine presentations for a supplied blow-up with chosen centre generators -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Any regular pair generating the centre on an affine open supplies the
two actual affine Rees charts of the given universal blow-up over that open.
Source: Hartshorne, Algebraic Geometry, II.7.13–II.7.14. -/
theorem paired_c3_blowup_affine_rees_charts
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (I : B.left.IdealSheafData)
    (hcartier : ∀ z : X.left, ∃ V : X.left.affineOpens, z ∈ V.1 ∧
      Nonempty (((I.comap p.left).ideal V) ≃ₗ[Γ(X.left, V)] Γ(X.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ z : T.left, ∃ V : T.left.affineOpens, z ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! k : T ⟶ X, k ≫ p = f)
    (U : B.left.affineOpens) (u v : Γ(B.left, U))
    (hI : I.ideal U = Ideal.span {u, v})
    (hv : IsRegular v) (hu : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u))
    (hu' : IsRegular u) (hv' : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v)) :
    ∃ (V₁ V₂ : X.left.affineOpens)
      (h₁ : V₁.1 ≤ p.left ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p.left ⁻¹ᵁ U.1)
      (s : Γ(X.left, V₁)) (t : Γ(X.left, V₂)),
      V₁.1 ⊔ V₂.1 = p.left ⁻¹ᵁ U.1 ∧
      let f₁ := (p.left.appLE U.1 V₁.1 h₁).hom
      let f₂ := (p.left.appLE U.1 V₂.1 h₂).hom
      f₁ u = s * f₁ v ∧ f₂ v = t * f₂ u ∧
      Function.Surjective (Polynomial.eval₂RingHom f₁ s) ∧
      RingHom.ker (Polynomial.eval₂RingHom f₁ s) =
        Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v} ∧
      Function.Surjective (Polynomial.eval₂RingHom f₂ t) ∧
      RingHom.ker (Polynomial.eval₂RingHom f₂ t) =
        Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u} := by
  obtain ⟨M, j₁, j₂, π, hj₁, hj₂, hMcover, hπ₁, hπ₂, hoverlap, hlift⟩ :=
    s2v_l1b_charts_overlap_descent Γ(B.left, U) u v hv hu hu' hv'
  obtain ⟨eM, heM, V₁, V₂, h₁, h₂, e₁, e₂, hcover, hf₁, hf₂⟩ :=
    s2v_l1b_charts_blowup_comparison B X p
      I
      hcartier hblowup U u v hI hv hu hu' hv' M j₁ j₂ π ⟨hj₁, hj₂, hMcover, hπ₁, hπ₂, hlift⟩
  have hp₁ := s2v_l1b_chart_presentation_transport u v e₁
  have hp₂ := s2v_l1b_chart_presentation_transport v u e₂
  dsimp only at hp₁ hp₂
  rw [hf₁] at hp₁
  rw [hf₂] at hp₂
  refine ⟨V₁, V₂, h₁, h₂,
    e₁ (Ideal.Quotient.mk (Ideal.span
      {Polynomial.C u - Polynomial.X * Polynomial.C v}) Polynomial.X),
    e₂ (Ideal.Quotient.mk (Ideal.span
      {Polynomial.C v - Polynomial.X * Polynomial.C u}) Polynomial.X), hcover, ?_⟩
  refine ⟨?_, ?_, hp₁.1, hp₁.2, hp₂.1, hp₂.2⟩
  · rw [← hf₁]
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_mul] using
      congrArg e₁ (s2v_l1b_chart_relation u v)
  · rw [← hf₂]
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_mul] using
      congrArg e₂ (s2v_l1b_chart_relation v u)

#print axioms paired_c3_blowup_affine_rees_charts
end HodgeLean.Foundations.Program.G32Native
