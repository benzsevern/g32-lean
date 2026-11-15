import HodgeLean.Foundations.Program.SchoenTowerI2aCartierCoefficientTransport
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A free Cartier module on an affine open source gives the free actual
ideal module on its image affine open in the target.
Source: Mathlib, `Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion`
and `Scheme.Hom.appIso`. -/
theorem s2v_i2a_cartier_free_on_open_image
    {X Y : Scheme.{0}} [IsAffine X] (f : X ⟶ Y) [IsOpenImmersion f]
    (K : Y.IdealSheafData)
    (hfree : Nonempty (((K.comap f).ideal ⟨⊤, isAffineOpen_top X⟩)
      ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤))) :
    Nonempty ((K.ideal ⟨f ''ᵁ ⊤, (isAffineOpen_top X).image_of_isOpenImmersion f⟩)
      ≃ₗ[Γ(Y, f ''ᵁ ⊤)] Γ(Y, f ''ᵁ ⊤)) := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hfree
  have H := s2v_i2a_cartier_ideal_ring_equiv
    (f.appIso ⊤).symm.commRingCatIsoToRingEquiv _ hfree
  change Nonempty ((((K.ideal ⟨f ''ᵁ ⊤, (isAffineOpen_top X).image_of_isOpenImmersion f⟩).comap
    (f.appIso ⊤).inv.hom).map (f.appIso ⊤).inv.hom) ≃ₗ[Γ(Y, f ''ᵁ ⊤)] Γ(Y, f ''ᵁ ⊤)) at H
  have hs : Function.Surjective (f.appIso ⊤).inv.hom :=
    (f.appIso ⊤).symm.commRingCatIsoToRingEquiv.surjective
  rwa [Ideal.map_comap_of_surjective (f.appIso ⊤).inv.hom hs] at H

end HodgeLean.Foundations.Program
