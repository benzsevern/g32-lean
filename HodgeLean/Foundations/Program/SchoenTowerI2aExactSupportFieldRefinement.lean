import HodgeLean.Foundations.Program.SchoenTowerI2aExactSupportRefinement
import HodgeLean.Foundations.Program.SchoenTowerI2aFieldOpenFactor

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Exact support refinement retains the specified dominant original-field
point in the actual refined chart, together with its complex point, scalar
structure and every principal branch ideal.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5, principal open restriction. -/
theorem s2v_i2a_exact_support_refinement_with_original_field
    {K : Type} [Field K]
    (U X : Over (Spec ↧ℂ)) [IsAffine U.left] (u : U ⟶ X) [IsOpenImmersion u.left]
    (η : Spec (CommRingCat.of K) ⟶ X.left) [IsDominant η]
    (p : ComplexPoint U) (n : ℕ) (c : MvPolynomial (Fin n) ℂ →+* Γ(U.left, ⊤))
    (hc : c.Etale)
    (hcC : c.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom)
    {T : Type} [Fintype T] (D : T → X.left.IdealSheafData)
    (J₀ : Finset T) (κ₀ : J₀ ↪ Fin n) (f : T → Γ(U.left, ⊤))
    (hf : ∀ t, ((D t).comap u.left).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {f t})
    (hcoord : ∀ t : J₀, f t = c (MvPolynomial.X (κ₀ t)))
    (habsent : ∀ t, t ∉ J₀ → f t = 1) :
    ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (r : V ⟶ U) (q : ComplexPoint V),
      IsOpenImmersion r.left ∧ Point.map r q = p ∧
      ∃ ηV : Spec (CommRingCat.of K) ⟶ V.left, ηV ≫ (r ≫ u).left = η ∧ IsDominant ηV ∧
      ∃ (a : MvPolynomial (Fin n) ℂ →+* Γ(V.left, ⊤))
        (J : Finset T) (κ : J ↪ Fin n) (z : T → Γ(V.left, ⊤)),
        J ⊆ J₀ ∧ a = r.left.appTop.hom.comp c ∧ a.Etale ∧
        a.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ V.hom.appTop).hom ∧
        (∀ t, t ∈ J ↔ (Point.map u p).underlying ∈ (D t).support) ∧
        (∀ t : J, z t = a (MvPolynomial.X (κ t))) ∧
        (∀ t, t ∉ J → z t = 1) ∧
        (∀ t, ((D t).comap (r ≫ u).left).ideal ⟨⊤, @isAffineOpen_top V.left hV⟩ =
          Ideal.span {z t}) := by
  obtain ⟨V, hV, r, q, hr, hq, a, J, κ, z, hJ, ha, haEt, haC, hsupp, hz, hab, hideals⟩ :=
    s2v_i2a_exact_support_coordinate_refinement U X u p n c hc hcC D J₀ κ₀ f hf hcoord habsent
  letI : IsAffine V.left := hV
  letI : IsOpenImmersion r.left := hr
  letI : Nonempty V.left := ⟨q.underlying⟩
  haveI : IsOpenImmersion (r ≫ u).left := inferInstanceAs (IsOpenImmersion (r.left ≫ u.left))
  obtain ⟨ηV, hηV, _⟩ := s2v_i2a_dominant_field_point_open_factor (r ≫ u).left η
  exact ⟨V, hV, r, q, hr, hq, ηV, hηV.1, hηV.2,
    a, J, κ, z, hJ, ha, haEt, haC, hsupp, hz, hab, hideals⟩

end HodgeLean.Foundations.Program
