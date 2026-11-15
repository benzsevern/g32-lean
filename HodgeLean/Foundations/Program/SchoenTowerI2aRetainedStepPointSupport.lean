import HodgeLean.Foundations.Program.SchoenTowerI2aAffineBasePairSupport
import HodgeLean.Foundations.Program.SchoenTowerI2aUnitCentrePointSupport

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every retained step admits an actual affine etale point chart with exact
labeled branch support, including both paired and unit-centre cases, and retains
the specified dominant original-field point.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13. -/
theorem s2v_i2a_retained_step_point_exact_support
    (n : ℕ) (Y B U : Over (Spec ↧ℂ))
    [IsIntegral B.left] [IsLocallyNoetherian B.left] [IsAffine U.left] [IsIntegral U.left]
    (b : B ⟶ Y) (K : Y.left.IdealSheafData)
    (u₀ : U ⟶ Y) [IsOpenImmersion u₀.left]
    (c : MvPolynomial (Fin n) ℂ →+* Γ(U.left, ⊤)) (hc : c.Etale)
    (hcC : c.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom)
    (huniv : ∀ (Z : Over (Spec ↧ℂ)) (h : Z ⟶ Y),
      (∀ p : Z.left, ∃ U : Z.left.affineOpens, p ∈ U.1 ∧
        Nonempty (((K.comap h.left).ideal U) ≃ₗ[Γ(Z.left, U)] Γ(Z.left, U))) →
      ∃! v : Z ⟶ B, v ≫ b = h)
    (hcartier : ∀ p : B.left, ∃ U : B.left.affineOpens, p ∈ U.1 ∧
      Nonempty (((K.comap b.left).ideal U) ≃ₗ[Γ(B.left, U)] Γ(B.left, U)))
    {T : Type} [Fintype T] [DecidableEq T]
    (D : T → Y.left.IdealSheafData) (J₀ : Finset T) (κ₀ : J₀ ↪ Fin n)
    (α β : T) (hαβ : α ≠ β) (hK : K = D α ⊔ D β)
    (hD : ∀ t : J₀, ((D t).comap u₀.left).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {c (MvPolynomial.X (κ₀ t))})
    (habsent : ∀ t, t ∉ J₀ → ((D t).comap u₀.left).ideal ⟨⊤, isAffineOpen_top _⟩ = ⊤)
    (x : ComplexPoint B) (hx : b.left x.underlying ∈ Set.range u₀.left)
    {L : Type} [Field L] (η : Spec (CommRingCat.of L) ⟶ B.left) [IsDominant η] :
    ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (u : V ⟶ B) (q : ComplexPoint V),
      IsOpenImmersion u.left ∧ Point.map u q = x ∧
      ∃ ηV : Spec (CommRingCat.of L) ⟶ V.left, ηV ≫ u.left = η ∧ IsDominant ηV ∧
      ∃ (a : MvPolynomial (Fin n) ℂ →+* Γ(V.left, ⊤))
        (J : Finset T) (κ : J ↪ Fin n) (z : T → Γ(V.left, ⊤)),
        J ⊆ J₀ ∧ a.Etale ∧
        a.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ V.hom.appTop).hom ∧
        (∀ t, t ∈ J ↔ x.underlying ∈ (s2c_strictTransform b.left (D t) K).support) ∧
        (∀ t : J, z t = a (MvPolynomial.X (κ t))) ∧
        (∀ t, t ∉ J → z t = 1) ∧
        (∀ t, ((s2c_strictTransform b.left (D t) K).comap u.left).ideal
          ⟨⊤, @isAffineOpen_top V.left hV⟩ = Ideal.span {z t}) := by
  classical
  by_cases hboth : α ∈ J₀ ∧ β ∈ J₀
  · let α₀ : J₀ := ⟨α, hboth.1⟩
    let β₀ : J₀ := ⟨β, hboth.2⟩
    have hne : α₀ ≠ β₀ := fun h => hαβ (congrArg Subtype.val h)
    have hcentre : (K.comap u₀.left).ideal ⟨⊤, isAffineOpen_top _⟩ =
        Ideal.span {c (MvPolynomial.X (κ₀ α₀)), c (MvPolynomial.X (κ₀ β₀))} := by
      rw [hK, Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.ideal_sup]
      change ((D α).comap u₀.left).ideal ⟨⊤, isAffineOpen_top _⟩ ⊔
        ((D β).comap u₀.left).ideal ⟨⊤, isAffineOpen_top _⟩ = _
      rw [hD α₀, hD β₀, ← Ideal.span_union]
      simp only [Set.singleton_union]
    obtain ⟨t₀, _, V, hV, u, q, hu, hq, ηV, hηV, hdom, a, J, κ, z,
        hJ, ha, haC, hsupp, hz, hab, hideals⟩ :=
      s2v_i2a_affine_base_pair_point_exact_support n Y B U b K u₀ c hc hcC huniv hcartier
        D J₀ κ₀ α₀ β₀ hne hcentre hD habsent x hx η
    exact ⟨V, hV, u, q, hu, hq, ηV, hηV, hdom, a, J, κ, z,
      hJ.trans (Finset.erase_subset _ _), ha, haC, hsupp, hz, hab, hideals⟩
  · have hcentre : K.comap u₀.left = ⊤ := by
      apply Scheme.IdealSheafData.ext_of_isAffine
      rw [hK, Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.ideal_sup]
      change ((D α).comap u₀.left).ideal ⟨⊤, isAffineOpen_top _⟩ ⊔
        ((D β).comap u₀.left).ideal ⟨⊤, isAffineOpen_top _⟩ = ⊤
      by_cases hα : α ∈ J₀
      · have hβ : β ∉ J₀ := fun h => hboth ⟨hα, h⟩
        rw [habsent β hβ, sup_top_eq]
      · rw [habsent α hα, top_sup_eq]
    exact s2v_i2a_unit_centre_point_exact_support n Y B U b K u₀ c hc hcC huniv
      D J₀ κ₀ hcentre hD habsent x hx η

end HodgeLean.Foundations.Program
