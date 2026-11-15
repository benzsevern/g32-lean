import HodgeLean.Foundations.Program.SchoenTowerL1bPrincipalChart

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A nonzero principal equation on an affine open immersion stays nonzero on its image. -/
theorem s2v_l1b_divisor_nonzero_equation_on_chart_image
    {X Y : Scheme} [IsAffine X] (u : X ⟶ Y) [IsOpenImmersion u]
    (I : Y.IdealSheafData) (g : Γ(X, ⊤)) (hg0 : g ≠ 0)
    (hg : (I.comap u).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {g}) :
    ∃ V : Y.affineOpens, Set.range u ⊆ V.1 ∧
      ∃ a : Γ(Y, V), I.ideal V = Ideal.span {a} ∧ a ≠ 0 := by
  let V : Y.affineOpens := ⟨u ''ᵁ ⊤, (isAffineOpen_top X).image_of_isOpenImmersion u⟩
  refine ⟨V, ?_, (u.appIso ⊤).inv.hom g, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hg
    have H := congrArg (Ideal.map (u.appIso ⊤).inv.hom) hg
    rw [Ideal.map_comap_of_surjective _
      (ConcreteCategory.bijective_of_isIso (u.appIso ⊤).inv).surjective,
      Ideal.map_span, Set.image_singleton] at H
    exact H
  · intro hz
    apply hg0
    exact (ConcreteCategory.bijective_of_isIso (u.appIso ⊤).inv).injective
      (hz.trans (map_zero (u.appIso ⊤).inv.hom).symm)

end HodgeLean.Foundations.Program
