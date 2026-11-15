import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageThree.Basic

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
open scoped BigOperators
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

theorem divided_equations {K : Type*} [Field K] (m α : ℕ)
    (hm : 0 < m) (hα : α ≤ m) (ε t u v : K) (hu : u ≠ 0) (hv : v ≠ 0)
    (ht : t ^ m = ε * u ^ α * v ^ (m - α)) :
    dividedGenerator t v ^ m = ε * (u / v) ^ α ∧
    dividedGenerator t u ^ m = ε * (v / u) ^ (m - α) := by
  have hr := TameMonomialCover.pair_rescaling K 0 m α (m - α) hm
    (Nat.add_sub_of_le hα) (fun _ => 0) ε t u v (fun _ => 1) hu hv
    (by simpa only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] using ht)
  constructor
  · simpa only [dividedGenerator, Finset.univ_eq_empty, Finset.prod_empty, mul_one] using hr.2
  · simpa only [dividedGenerator, Finset.univ_eq_empty, Finset.prod_empty, mul_one] using hr.1

theorem regular_chart_restrictions
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (I : B.left.IdealSheafData)
    (hcartier : ∀ z : X.left, ∃ V : X.left.affineOpens, z ∈ V.1 ∧
      Nonempty (((I.comap p.left).ideal V) ≃ₗ[Γ(X.left, V)] Γ(X.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ z : T.left, ∃ V : T.left.affineOpens, z ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! k : T ⟶ X, k ≫ p = f)
    (K : Type) [Field K] (η : Spec ↧K ⟶ X.left)
    [QuasiCompact η] [QuasiSeparated η] [IsDominant η]
    (U : B.left.affineOpens) (u v : Γ(B.left, U))
    (hI : I.ideal U = Ideal.span {u, v})
    (hnu : ¬ IsUnit u) (hnv : ¬ IsUnit v)
    (hv : IsRegular v) (hu : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u))
    (hu' : IsRegular u) (hv' : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v)) :
    ∃ (V₁ V₂ : X.left.affineOpens)
      (h₁ : V₁.1 ≤ p.left ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p.left ⁻¹ᵁ U.1)
      (s₁ : Γ(X.left, V₁)) (s₂ : Γ(X.left, V₂)),
      V₁.1 ⊔ V₂.1 = p.left ⁻¹ᵁ U.1 ∧
      (p.left.appLE U.1 V₁.1 h₁).hom u = s₁ * (p.left.appLE U.1 V₁.1 h₁).hom v ∧
      (p.left.appLE U.1 V₂.1 h₂).hom v = s₂ * (p.left.appLE U.1 V₂.1 h₂).hom u ∧
      ∀ V : X.left.affineOpens, V = V₁ ∨ V = V₂ →
        ∃ (ηV : Spec ↧K ⟶ V.1.toScheme) (hηV : ηV ≫ V.1.ι = η)
          (N : pullback η.fromNormalization V.1.ι ≅
            Spec ↧(normalizedChart (StageThree.fieldCoeff ηV))),
          StageThree.restrictedFieldPoint η V.1.ι ηV hηV ≫ N.hom =
            Spec.map (CommRingCat.ofHom (normalizedChart (StageThree.fieldCoeff ηV)).subtype) ∧
          N.hom ≫ Spec.map (CommRingCat.ofHom
            (StageTwo.integralCoeff (StageThree.fieldCoeff ηV))) =
            pullback.snd η.fromNormalization V.1.ι ≫ V.1.toScheme.toSpecΓ := by
  obtain ⟨M, j₁, j₂, π, hj₁, hj₂, hMcover, hπ₁, hπ₂, _, hlift⟩ :=
    s2v_l1b_charts_overlap_descent Γ(B.left, U) u v hv hu hu' hv'
  obtain ⟨_, _, V₁, V₂, h₁, h₂, e₁, e₂, hcover, hf₁, hf₂⟩ :=
    s2v_l1b_charts_blowup_comparison B X p I hcartier hblowup U u v hI
      hv hu hu' hv' M j₁ j₂ π ⟨hj₁, hj₂, hMcover, hπ₁, hπ₂, hlift⟩
  have hne {V : X.left.affineOpens} (u v : Γ(B.left, U))
      (e : s2v_L1bChart u v ≃+* Γ(X.left, V)) (hunit : ¬ IsUnit u) : Nonempty V.1 := by
    haveI : Nontrivial Γ(X.left, V) := StageThree.quotient_chart_nontrivial
      (e.toRingHom.comp ((Ideal.Quotient.mk _).comp Polynomial.C))
      (e (RegularPairChart.ratio u v)) u v hunit
      (s2v_l1b_chart_presentation_transport u v e).2
    exact StageThree.affineOpen_nonempty _ V
  refine ⟨V₁, V₂, h₁, h₂, e₁ (RegularPairChart.ratio u v),
    e₂ (RegularPairChart.ratio v u), hcover, ?_, ?_, ?_⟩
  · rw [← hf₁]
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      map_mul] using congrArg e₁ (s2v_l1b_chart_relation u v)
  · rw [← hf₂]
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      map_mul] using congrArg e₂ (s2v_l1b_chart_relation v u)
  · intro V hV
    haveI : Nonempty V.1 := by
      rcases hV with rfl | rfl
      · exact hne u v e₁ hnu
      · exact hne v u e₂ hnv
    obtain ⟨ηV, ⟨hηV, _⟩, _⟩ := s2v_i2a_dominant_field_point_open_factor V.1.ι η
    obtain ⟨N, hN, hstruct, _⟩ := StageThree.affine_restriction_aux η V.1.ι ηV hηV
    exact ⟨ηV, hηV, N, hN, hstruct⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
