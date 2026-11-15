import HodgeLean.Foundations.Program.SchoenTowerL1bAffineIdeal

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Extension of an ideal sheaf to a stalk commutes with the actual scheme pullback. -/
theorem s2v_l1b_divisor_comap_ideal_germ
    {X Y : Scheme} (f : X ⟶ Y) (I : Y.IdealSheafData)
    (x : X) (U : Y.affineOpens) (V : X.affineOpens)
    (hxU : f x ∈ U.1) (hxV : x ∈ V.1) :
    ((I.comap f).ideal V).map (X.presheaf.germ V.1 x hxV).hom =
      ((I.ideal U).map (Y.presheaf.germ U.1 (f x) hxU).hom).map (f.stalkMap x).hom := by
  obtain ⟨W, hW, hxW, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V.1 ⊓ f ⁻¹ᵁ U.1 from ⟨hxV, hxU⟩)
  let Wb : X.affineOpens := ⟨W, hW⟩
  have hWV : Wb ≤ V := fun _ hw => (hsub hw).1
  have hWU : W ≤ f ⁻¹ᵁ U.1 := fun _ hw => (hsub hw).2
  have hleft : ((I.comap f).ideal V).map (X.presheaf.germ V.1 x hxV).hom =
      ((I.comap f).ideal Wb).map (X.presheaf.germ W x hxW).hom := by
    rw [← (I.comap f).map_ideal hWV, Ideal.map_map, ← CommRingCat.hom_comp]
    change _ = ((I.comap f).ideal V).map
      ((X.presheaf.map (homOfLE (X := X.Opens) hWV).op ≫ X.presheaf.germ W x hxW).hom)
    rw [X.presheaf.germ_res]
  rw [hleft, s2v_l1b_comap_ideal_affine_charts f I U Wb hWU,
    Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 1
  rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res, Scheme.Hom.germ_stalkMap]

end HodgeLean.Foundations.Program
