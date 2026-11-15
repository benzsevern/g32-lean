import HodgeLean.Foundations.Program.SchoenCycleC1OpenCentreSections

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- On arbitrary compatible affine neighbourhoods, the actual pulled-back
ideal is extension along the original restricted section map. -/
theorem s2e_c1_affine_comap_appLE
    {X Y : Scheme} (f : X ⟶ Y) (J : Y.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    (J.comap f).ideal V = Ideal.map (f.appLE U.1 V.1 hVU).hom (J.ideal U) := by
  let f' := f.resLE U.1 V.1 hVU
  have he : (J.comap U.1.ι).comap f' = (J.comap f).comap V.1.ι := by
    rw [← J.comap_comp, Scheme.Hom.resLE_comp_ι, J.comap_comp]
  have hnat : f'.appTop ≫ V.1.topIso.hom =
      U.1.topIso.hom ≫ f.appLE U.1 V.1 hVU := by
    dsimp only [f', Scheme.Hom.appTop]
    rw [Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    (J.comap f).ideal V = Ideal.map V.1.topIso.hom.hom
        (((J.comap f).comap V.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩) :=
      (s2e_c1_open_centre_sections X (J.comap f) V).symm
    _ = Ideal.map V.1.topIso.hom.hom
        (Ideal.map f'.appTop.hom ((J.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩)) := by
      rw [← he, s2e_affine_comap_ideal]
    _ = Ideal.map (f.appLE U.1 V.1 hVU).hom
        (Ideal.map U.1.topIso.hom.hom ((J.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩)) := by
      rw [Ideal.map_map, Ideal.map_map]
      exact congrArg (fun φ => Ideal.map φ ((J.comap U.1.ι).ideal
        ⟨⊤, isAffineOpen_top _⟩)) (congrArg CommRingCat.Hom.hom hnat)
    _ = Ideal.map (f.appLE U.1 V.1 hVU).hom (J.ideal U) := by
      rw [s2e_c1_open_centre_sections]

end HodgeLean.Foundations.Program
