import HodgeLean.Foundations.Program.SchoenTowerI2aCartierCoefficientTransport
import HodgeLean.Foundations.Program.SchoenCycleCartierCharts
import HodgeLean.Foundations.Program.SchoenCycleAffineIdeals
import Mathlib.AlgebraicGeometry.Properties

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The retained Cartier test yields an actual integral coefficient spectrum
neighborhood at the specified point with a free global pulled-back ideal.
Source: Hartshorne, Algebraic Geometry, II.5, affine ideal sheaves;
Mathlib, `Scheme.isoSpec` and `Scheme.IdealSheafData.comap_comp`. -/
theorem s2v_i2a_cartier_spectrum_neighborhood
    (X : Scheme.{0}) [IsIntegral X] (K : X.IdealSheafData) (p : X)
    (hfree : ∃ U : X.affineOpens, p ∈ U.1 ∧
      Nonempty ((K.ideal U) ≃ₗ[Γ(X, U)] Γ(X, U))) :
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S)
      (v : Spec (CommRingCat.of S) ⟶ X), IsOpenImmersion v ∧ p ∈ Set.range v ∧
      Nonempty (((K.comap v).ideal ⟨⊤, isAffineOpen_top _⟩)
        ≃ₗ[Γ(Spec (CommRingCat.of S), ⊤)] Γ(Spec (CommRingCat.of S), ⊤)) := by
  obtain ⟨U, hp, hU⟩ := hfree
  letI : IsAffine U.1.toScheme := U.2
  letI : Nonempty U.1.toScheme := ⟨⟨p, hp⟩⟩
  haveI : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
  let S := Γ(U.1.toScheme, ⊤)
  let v : Spec S ⟶ X := U.1.toScheme.isoSpec.inv ≫ U.1.ι
  have hfreeU := s2e_cartier_free_on_open_subscheme K U.1 hU
  refine ⟨S, inferInstance, inferInstance, v, inferInstance, ?_, ?_⟩
  · refine ⟨U.1.toScheme.isoSpec.hom ⟨p, hp⟩, ?_⟩
    change (U.1.toScheme.isoSpec.hom ≫ U.1.toScheme.isoSpec.inv ≫ U.1.ι) ⟨p, hp⟩ = p
    simp
  · change Nonempty (((K.comap (U.1.toScheme.isoSpec.inv ≫ U.1.ι)).ideal
        ⟨⊤, isAffineOpen_top _⟩) ≃ₗ[Γ(Spec S, ⊤)] Γ(Spec S, ⊤))
    rw [Scheme.IdealSheafData.comap_comp, s2e_affine_comap_ideal]
    exact s2v_i2a_cartier_ideal_ring_equiv
      (asIso U.1.toScheme.isoSpec.inv.appTop).commRingCatIsoToRingEquiv _ hfreeU

end HodgeLean.Foundations.Program
