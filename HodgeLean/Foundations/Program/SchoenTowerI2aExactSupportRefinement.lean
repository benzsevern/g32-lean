import HodgeLean.Foundations.Program.SchoenTowerI2aAbsentBranchNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerI2aPrincipalSupport

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Any finite family of actual coordinate branch equations refines at its
specified point to exactly the present labels, with every absent equation one.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5, principal open restriction. -/
theorem s2v_i2a_exact_support_coordinate_refinement
    (U X : Over (Spec ↧ℂ)) [IsAffine U.left] (u : U ⟶ X) [IsOpenImmersion u.left]
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
      ∃ (a : MvPolynomial (Fin n) ℂ →+* Γ(V.left, ⊤))
        (J : Finset T) (κ : J ↪ Fin n) (z : T → Γ(V.left, ⊤)),
        J ⊆ J₀ ∧ a = r.left.appTop.hom.comp c ∧ a.Etale ∧
        a.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ V.hom.appTop).hom ∧
        (∀ t, t ∈ J ↔ (Point.map u p).underlying ∈ (D t).support) ∧
        (∀ t : J, z t = a (MvPolynomial.X (κ t))) ∧
        (∀ t, t ∉ J → z t = 1) ∧
        (∀ t, ((D t).comap (r ≫ u).left).ideal ⟨⊤, @isAffineOpen_top V.left hV⟩ =
          Ideal.span {z t}) := by
  classical
  let J := J₀.filter (fun t => Point.evaluate ⊤ (f t) p = 0)
  have hsubset : J ⊆ J₀ := Finset.filter_subset _ _
  have hzero (t : T) : t ∈ J ↔ Point.evaluate ⊤ (f t) p = 0 := by
    constructor
    · exact fun h => (Finset.mem_filter.mp h).2
    · intro h
      apply Finset.mem_filter.mpr
      refine ⟨?_, h⟩
      by_contra ht
      rw [habsent t ht] at h
      rw [← s2t_affinePointAlgHom_apply] at h
      simpa using h
  have hne (t : T) (ht : t ∉ J) : Point.evaluate ⊤ (f t) p ≠ 0 :=
    fun h => ht ((hzero t).mpr h)
  obtain ⟨V, hV, r, q, hr, hq, hunits⟩ :=
    s2v_i2a_absent_branch_unit_neighborhood U p J f hne
  letI : IsAffine V.left := hV
  letI : IsOpenImmersion r.left := hr
  let a := r.left.appTop.hom.comp c
  let κ : J ↪ Fin n :=
    ⟨fun t => κ₀ ⟨t, hsubset t.property⟩, fun t s h =>
      Subtype.ext (congrArg (fun q : J₀ => q.val) (κ₀.injective h))⟩
  let z (t : T) : Γ(V.left, ⊤) := if ht : t ∈ J then a (MvPolynomial.X (κ ⟨t, ht⟩)) else 1
  have ha : a.Etale := RingHom.Etale.stableUnderComposition _ _ hc
    (HasRingHomProperty.appTop (P := @Etale) r.left inferInstance)
  have haC : a.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ V.hom.appTop).hom := by
    change (r.left.appTop.hom.comp c).comp MvPolynomial.C = _
    rw [RingHom.comp_assoc, hcC]
    change ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop ≫ r.left.appTop).hom = _
    rw [← Scheme.Hom.comp_appTop, r.w]
  refine ⟨V, hV, r, q, hr, hq, a, J, κ, z, hsubset, rfl, ha, haC, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [hzero]
    exact (s2v_i2a_principal_pullback_support_evaluation U X u (D t) (f t) (hf t) p).symm
  · intro t
    simp only [z, dif_pos t.property]
  · intro t ht
    simp only [z, dif_neg ht]
  · intro t
    have H := s2v_l1a_curve_point_equation_pullback u.left r.left (D t) (f t) (hf t)
    change ((D t).comap (r.left ≫ u.left)).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {z t}
    by_cases ht : t ∈ J
    · rw [hcoord ⟨t, hsubset ht⟩] at H
      simp only [z, dif_pos ht]
      exact H
    · rw [Ideal.span_singleton_eq_top.mpr (hunits t ht)] at H
      simpa only [z, dif_neg ht, Ideal.span_singleton_one] using H

end HodgeLean.Foundations.Program
