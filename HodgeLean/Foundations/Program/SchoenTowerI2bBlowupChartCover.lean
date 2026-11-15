import HodgeLean.Foundations.Program.SchoenTowerI2bCoefficientPointLift

/-! Covering actual upper points by the two selected algebraic charts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program

/-- The two retained algebraic chart lifts cover every actual upper point over the affine base chart.
Source: Cartier affine refinement, the coefficient-open cover, and uniqueness of retained lifts. -/
theorem s2v_i2b_retained_blowup_chart_point_cover
    (X Y U : Over (Spec ↧ℂ)) [IsAffine U.left]
    (a : U ⟶ X) [IsOpenImmersion a.left] (b : Y ⟶ X) (I : X.left.IdealSheafData)
    (hcartier : ∀ y : Y.left, ∃ V : Y.left.affineOpens, y ∈ V.1 ∧
      Nonempty (((I.comap b.left).ideal V) ≃ₗ[Γ(Y.left, V)] Γ(Y.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ X),
      (∀ x : T.left, ∃ W : T.left.affineOpens, x ∈ W.1 ∧
        Nonempty (((I.comap f.left).ideal W) ≃ₗ[Γ(T.left, W)] Γ(T.left, W))) →
      ∃! g : T ⟶ Y, g ≫ b = f)
    (u v : Γ(U.left, ⊤))
    (hI : (I.comap a.left).ideal ⟨⊤, isAffineOpen_top U.left⟩ = Ideal.span {u, v}) :
    let Q := s2v_L1bChart u v
    letI : CommRing Q := inferInstanceAs (CommRing (s2v_L1bChart u v))
    let Q' := s2v_L1bChart v u
    letI : CommRing Q' := inferInstanceAs (CommRing (s2v_L1bChart v u))
    let q : Polynomial Γ(U.left, ⊤) →+* Q := Ideal.Quotient.mk _
    let q' : Polynomial Γ(U.left, ⊤) →+* Q' := Ideal.Quotient.mk _
    let f := Spec.map (CommRingCat.ofHom (q.comp Polynomial.C)) ≫ U.left.isoSpec.inv
    let f' := Spec.map (CommRingCat.ofHom (q'.comp Polynomial.C)) ≫ U.left.isoSpec.inv
    ∀ g : Spec (CommRingCat.of Q) ⟶ Y.left, g ≫ b.left = f ≫ a.left →
    ∀ g' : Spec (CommRingCat.of Q') ⟶ Y.left, g' ≫ b.left = f' ≫ a.left →
    ∀ y : Y.left, b.left y ∈ Set.range a.left → y ∈ Set.range g ∨ y ∈ Set.range g' := by
  dsimp only
  intro g hg g' hg' y hy
  obtain ⟨V₀, hyV₀, hfree₀⟩ := hcartier y
  let W := b.left ⁻¹ᵁ a.left.opensRange
  obtain ⟨V, hyV, _, hVW, hfreeV⟩ := s2e_cartier_affine_refinement
    (I.comap b.left) V₀ hfree₀ y hyV₀ W hy
  let Vo : Over (Spec ↧ℂ) := Over.mk (V.1.ι ≫ Y.hom)
  letI : IsAffine Vo.left := V.2
  let j : Vo ⟶ Y := Over.homMk V.1.ι rfl
  have hrange : Set.range (V.1.ι ≫ b.left) ⊆ Set.range a.left := by
    rintro _ ⟨z, rfl⟩
    exact hVW z.property
  let t₀ := IsOpenImmersion.lift a.left (V.1.ι ≫ b.left) hrange
  have ht₀ : t₀ ≫ a.left = V.1.ι ≫ b.left := IsOpenImmersion.lift_fac _ _ _
  let t : Vo ⟶ U := Over.homMk t₀ (by
    rw [← a.w, ← Category.assoc, ht₀]
    exact (j ≫ b).w)
  have hj : j ≫ b = t ≫ a := by
    apply Over.OverMorphism.ext
    exact ht₀.symm
  let J := (I.comap b.left).comap V.1.ι
  have hJ : J = I.comap (j ≫ b).left := by
    change (I.comap b.left).comap V.1.ι = I.comap (V.1.ι ≫ b.left)
    rw [Scheme.IdealSheafData.comap_comp]
  have hJfree := s2e_cartier_free_on_open_subscheme (I.comap b.left) V.1 hfreeV
  have hJt : J = (I.comap a.left).comap t.left := by
    rw [hJ, hj]
    change I.comap (t.left ≫ a.left) = _
    rw [Scheme.IdealSheafData.comap_comp]
  have hJgen : J.ideal ⟨⊤, isAffineOpen_top Vo.left⟩ =
      Ideal.span {t.left.appTop.hom u, t.left.appTop.hom v} := by
    rw [hJt, s2e_affine_comap_ideal, hI, Ideal.map_span, Set.image_pair]
    rfl
  have hu : t.left.appTop.hom u ∈ J.ideal ⟨⊤, isAffineOpen_top Vo.left⟩ := by
    rw [hJgen]
    exact Ideal.subset_span (by simp)
  have hv : t.left.appTop.hom v ∈ J.ideal ⟨⊤, isAffineOpen_top Vo.left⟩ := by
    rw [hJgen]
    exact Ideal.subset_span (by simp)
  obtain ⟨e⟩ := hJfree
  let yV : Vo.left := ⟨y, hyV⟩
  rcases s2v_i2b_invertible_ideal_coefficient_point_cover Vo.left
      (J.ideal ⟨⊤, isAffineOpen_top Vo.left⟩)
      (t.left.appTop.hom u) (t.left.appTop.hom v) hu hv hJgen e yV with hU | hV
  · obtain ⟨z, hz⟩ := s2v_i2b_coefficient_point_chart_lift X Y U Vo a b t j hj I
      hblowup J hJ v u hv hu e yV hU g' hg'
    exact Or.inr ⟨z, hz⟩
  · obtain ⟨z, hz⟩ := s2v_i2b_coefficient_point_chart_lift X Y U Vo a b t j hj I
      hblowup J hJ u v hu hv e yV hV g hg
    exact Or.inl ⟨z, hz⟩

end HodgeLean.Foundations.Program
