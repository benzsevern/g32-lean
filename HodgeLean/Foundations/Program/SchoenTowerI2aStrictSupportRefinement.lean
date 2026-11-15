import HodgeLean.Foundations.Program.SchoenTowerI2aExactSupportRefinement

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual strict branch equations after removing a selected coordinate
refine to exactly the remaining support at the specified point, preserving an
injective assignment of coordinate slots and every absent unit equation.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5, principal open restriction. -/
theorem s2v_i2a_exact_support_after_removed_coordinate
    (U X : Over (Spec ↧ℂ)) [IsAffine U.left] (u : U ⟶ X) [IsOpenImmersion u.left]
    (p : ComplexPoint U) (n : ℕ) (c : MvPolynomial (Fin n) ℂ →+* Γ(U.left, ⊤))
    (hc : c.Etale)
    (hcC : c.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom)
    {T : Type} [Fintype T] [DecidableEq T] (D : T → X.left.IdealSheafData)
    (J₀ : Finset T) (κ₀ : J₀ ↪ Fin n) (t₀ : J₀)
    (hbranch : ∀ t : J₀, ((D t).comap u.left).ideal ⟨⊤, isAffineOpen_top _⟩ =
      if κ₀ t = κ₀ t₀ then ⊤ else Ideal.span {c (MvPolynomial.X (κ₀ t))})
    (habsent : ∀ t, t ∉ J₀ → ((D t).comap u.left).ideal ⟨⊤, isAffineOpen_top _⟩ = ⊤) :
    ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (r : V ⟶ U) (q : ComplexPoint V),
      IsOpenImmersion r.left ∧ Point.map r q = p ∧
      ∃ (a : MvPolynomial (Fin n) ℂ →+* Γ(V.left, ⊤))
        (J : Finset T) (κ : J ↪ Fin n) (z : T → Γ(V.left, ⊤)),
        J ⊆ J₀.erase t₀ ∧ a = r.left.appTop.hom.comp c ∧ a.Etale ∧
        a.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ V.hom.appTop).hom ∧
        (∀ t, t ∈ J ↔ (Point.map u p).underlying ∈ (D t).support) ∧
        (∀ t : J, z t = a (MvPolynomial.X (κ t))) ∧
        (∀ t, t ∉ J → z t = 1) ∧
        (∀ t, ((D t).comap (r ≫ u).left).ideal ⟨⊤, @isAffineOpen_top V.left hV⟩ =
          Ideal.span {z t}) := by
  classical
  let J₁ := J₀.erase t₀
  have hsub : J₁ ⊆ J₀ := Finset.erase_subset _ _
  let κ₁ : J₁ ↪ Fin n :=
    ⟨fun t => κ₀ ⟨t, hsub t.property⟩, fun t s h =>
      Subtype.ext (congrArg (fun q : J₀ => q.val) (κ₀.injective h))⟩
  let f (t : T) : Γ(U.left, ⊤) :=
    if ht : t ∈ J₁ then c (MvPolynomial.X (κ₁ ⟨t, ht⟩)) else 1
  have hf (t : T) : ((D t).comap u.left).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {f t} := by
    by_cases ht : t ∈ J₁
    · have hne : κ₀ ⟨t, hsub ht⟩ ≠ κ₀ t₀ := by
        intro heq
        exact (Finset.mem_erase.mp ht).1 (congrArg (fun q : J₀ => q.val) (κ₀.injective heq))
      have H := hbranch ⟨t, hsub ht⟩
      rw [if_neg hne] at H
      simp only [f, dif_pos ht]
      exact H
    · simp only [f, dif_neg ht, Ideal.span_singleton_one]
      by_cases ht₀ : t ∈ J₀
      · have heq : t = t₀ := by
          by_contra hne
          exact ht (Finset.mem_erase.mpr ⟨hne, ht₀⟩)
        subst t
        simpa using hbranch t₀
      · exact habsent t ht₀
  have hcoord (t : J₁) : f t = c (MvPolynomial.X (κ₁ t)) := by
    simp only [f, dif_pos t.property]
  have hab (t : T) (ht : t ∉ J₁) : f t = 1 := by simp only [f, dif_neg ht]
  exact s2v_i2a_exact_support_coordinate_refinement U X u p n c hc hcC D J₁ κ₁ f hf hcoord hab

end HodgeLean.Foundations.Program
