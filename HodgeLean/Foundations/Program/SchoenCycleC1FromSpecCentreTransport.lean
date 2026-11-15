import HodgeLean.Foundations.Program.SchoenCycleC1OpenCentreSections

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The canonical spectrum chart of an actual affine neighbourhood carries
precisely the original centre section ideal under the standard section map. -/
theorem s2e_c1_fromSpec_centre_transport
    (X : Scheme) (J : X.IdealSheafData) (U : X.affineOpens) :
    J.comap U.2.fromSpec = Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso Γ(X, U.1)).inv.hom (J.ideal U)) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [IsAffineOpen.fromSpec, J.comap_comp, s2e_affine_comap_ideal,
    IsAffineOpen.isoSpec_inv_appTop]
  change Ideal.map ((Scheme.ΓSpecIso Γ(X, U.1)).inv.hom.comp U.1.topIso.hom.hom)
    ((J.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩) = _
  rw [← Ideal.map_map, s2e_c1_open_centre_sections]
  simp

end HodgeLean.Foundations.Program
