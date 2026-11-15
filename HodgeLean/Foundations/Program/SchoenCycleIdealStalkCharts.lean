import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Chart independence of actual ideal stalks -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Restriction to a smaller affine chart preserves the ideal generated in the stalk.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5. -/
theorem s2e_ideal_stalk_affine_restriction
    {X : Scheme} (I : X.IdealSheafData) (U V : X.affineOpens)
    (hVU : V ≤ U) (x : X) (hxV : x ∈ V.1) :
    Ideal.map (X.presheaf.germ U.1 x (hVU hxV)).hom (I.ideal U) =
      Ideal.map (X.presheaf.germ V.1 x hxV).hom (I.ideal V) := by
  rw [← I.map_ideal hVU, Ideal.map_map, ← CommRingCat.hom_comp]
  simp only [homOfLE_leOfHom, TopCat.Presheaf.germ_res']

/-- Two affine charts give the same ideal in a point's stalk.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5. -/
theorem s2e_ideal_stalk_affine_chart_independent
    {X : Scheme} (I : X.IdealSheafData) (U V : X.affineOpens)
    (x : X) (hxU : x ∈ U.1) (hxV : x ∈ V.1) :
    Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U) =
      Ideal.map (X.presheaf.germ V.1 x hxV).hom (I.ideal V) := by
  obtain ⟨W, hW, hxW, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U.1 ⊓ V.1 from ⟨hxU, hxV⟩)
  exact (s2e_ideal_stalk_affine_restriction I U ⟨W, hW⟩
    (fun _ hy => (hsub hy).1) x hxW).trans
    (s2e_ideal_stalk_affine_restriction I V ⟨W, hW⟩
      (fun _ hy => (hsub hy).2) x hxW).symm

end HodgeLean.Foundations.Program
