import HodgeLean.Foundations.Program.SchoenCycleAffineIdeals

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The canonical open-section identification retains the original ideal,
including its actual module of sections on the affine neighbourhood. -/
theorem s2e_c1_open_centre_sections
    (X : Scheme) (J : X.IdealSheafData) (U : X.affineOpens) :
    Ideal.map U.1.topIso.hom.hom
      ((J.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩) = J.ideal U := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.Opens.ι_appIso]
  simp only [Iso.refl_inv, CommRingCat.hom_id, Ideal.comap_id]
  let W : X.affineOpens := ⟨U.1.ι ''ᵁ ⊤,
    (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩
  have hUW : U ≤ W := U.1.ι_image_top.symm.le
  exact J.map_ideal hUW

end HodgeLean.Foundations.Program
