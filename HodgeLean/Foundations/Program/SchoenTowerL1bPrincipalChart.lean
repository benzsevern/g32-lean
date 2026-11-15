import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A principal equation on an affine open immersion gives a principal equation on its image. -/
theorem s2v_l1b_principal_equation_on_chart_image
    {X Y : Scheme} [IsAffine X] (u : X ⟶ Y) [IsOpenImmersion u]
    (I : Y.IdealSheafData) (g : Γ(X, ⊤))
    (hg : (I.comap u).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {g}) :
    ∃ V : Y.affineOpens, Set.range u ⊆ V.1 ∧
      ∃ a : Γ(Y, V), I.ideal V = Ideal.span {a} := by
  let V : Y.affineOpens := ⟨u ''ᵁ ⊤, (isAffineOpen_top X).image_of_isOpenImmersion u⟩
  refine ⟨V, ?_, (u.appIso ⊤).inv.hom g, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hg
    have H := congrArg (Ideal.map (u.appIso ⊤).inv.hom) hg
    rw [Ideal.map_comap_of_surjective _
      (ConcreteCategory.bijective_of_isIso (u.appIso ⊤).inv).surjective,
      Ideal.map_span, Set.image_singleton] at H
    exact H

end HodgeLean.Foundations.Program
