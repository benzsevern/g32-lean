import HodgeLean.Foundations.Program.SchoenTowerI2aStrictSupportRefinement
import HodgeLean.Foundations.Program.SchoenTowerI2aFieldOpenFactor
import HodgeLean.Foundations.Program.SchoenSelectedGeometryOpenPoints

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A spectrum chart with one removed branch coordinate refines at the specified
complex point to exact branch support while retaining the specified dominant
original-field point and the actual scalar structure.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5, principal open restriction. -/
theorem s2v_i2a_spectrum_point_exact_support_refinement
    {L : Type} [Field L] (C : Type) [CommRing C]
    (X : Over (Spec ↧ℂ)) (g : Spec (CommRingCat.of C) ⟶ X.left) [IsOpenImmersion g]
    (x : ComplexPoint X) (hx : x.underlying ∈ Set.range g)
    (η : Spec (CommRingCat.of L) ⟶ X.left) [IsDominant η]
    (n : ℕ) (c : MvPolynomial (Fin n) ℂ →+* C) (hc : c.Etale)
    (hcC : ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom.comp c).comp MvPolynomial.C =
      ((Scheme.ΓSpecIso ↧ℂ).inv ≫ (g ≫ X.hom).appTop).hom)
    {T : Type} [Fintype T] [DecidableEq T] (D : T → X.left.IdealSheafData)
    (J₀ : Finset T) (κ₀ : J₀ ↪ Fin n) (t₀ : J₀)
    (hbranch : ∀ t : J₀, ((D t).comap g).ideal ⟨⊤, isAffineOpen_top _⟩ =
      if κ₀ t = κ₀ t₀ then ⊤ else Ideal.span
        {((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c (MvPolynomial.X (κ₀ t))))})
    (habsent : ∀ t, t ∉ J₀ → ((D t).comap g).ideal ⟨⊤, isAffineOpen_top _⟩ = ⊤) :
    ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (u : V ⟶ X) (q : ComplexPoint V),
      IsOpenImmersion u.left ∧ Point.map u q = x ∧
      ∃ ηV : Spec (CommRingCat.of L) ⟶ V.left, ηV ≫ u.left = η ∧ IsDominant ηV ∧
      ∃ (a : MvPolynomial (Fin n) ℂ →+* Γ(V.left, ⊤))
        (J : Finset T) (κ : J ↪ Fin n) (z : T → Γ(V.left, ⊤)),
        J ⊆ J₀.erase t₀ ∧ a.Etale ∧
        a.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ V.hom.appTop).hom ∧
        (∀ t, t ∈ J ↔ x.underlying ∈ (D t).support) ∧
        (∀ t : J, z t = a (MvPolynomial.X (κ t))) ∧
        (∀ t, t ∉ J → z t = 1) ∧
        (∀ t, ((D t).comap u.left).ideal ⟨⊤, @isAffineOpen_top V.left hV⟩ =
          Ideal.span {z t}) := by
  let U : Over (Spec ↧ℂ) := Over.mk (g ≫ X.hom)
  let u₀ : U ⟶ X := Over.homMk g rfl
  haveI : IsOpenImmersion u₀.left := inferInstanceAs (IsOpenImmersion g)
  haveI : IsAffine U.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of C)))
  obtain ⟨p, hp⟩ := s0_open_immersion_lift_complex_point u₀ x hx
  let cΓ := (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom.comp c
  have hcΓ : cΓ.Etale := s2v_l1a_etale_ringHom_comp _ _ hc
    (RingHom.Etale.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.bijective)
  obtain ⟨V, hV, r, q, hr, hq, a, J, κ, z, hJ, _, ha, haC, hsupp, hz, hab, hideals⟩ :=
    s2v_i2a_exact_support_after_removed_coordinate U X u₀ p n cΓ hcΓ hcC
      D J₀ κ₀ t₀ hbranch habsent
  letI : IsAffine V.left := hV
  letI : IsOpenImmersion r.left := hr
  letI : Nonempty V.left := ⟨q.underlying⟩
  haveI : IsOpenImmersion (r ≫ u₀).left := inferInstanceAs (IsOpenImmersion (r.left ≫ u₀.left))
  obtain ⟨ηV, hηV, _⟩ := s2v_i2a_dominant_field_point_open_factor (r ≫ u₀).left η
  refine ⟨V, hV, r ≫ u₀, q, inferInstance, ?_, ηV, hηV.1, hηV.2,
    a, J, κ, z, hJ, ha, haC, ?_, hz, hab, hideals⟩
  · change Point.map u₀ (Point.map r q) = x
    rw [hq, hp]
  · simpa only [hp] using hsupp

end HodgeLean.Foundations.Program
