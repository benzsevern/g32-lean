import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.RingHom.Etale

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
universe u
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Identifying the base coefficient ring retains etaleness and the same original chart coordinates. -/
theorem etale_coordinate_coefficient_equiv
    {k k' R ι : Type u} [CommRing k] [CommRing k'] [CommRing R]
    (e : k' ≃+* k) (c : k →+* R) (z : ι → R)
    (h : (MvPolynomial.eval₂Hom c z).Etale) :
    (MvPolynomial.eval₂Hom (c.comp e.toRingHom) z).Etale := by
  have hmap : MvPolynomial.eval₂Hom (c.comp e.toRingHom) z =
      (MvPolynomial.eval₂Hom c z).comp (MvPolynomial.mapEquiv ι e).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      change c (e a) = (MvPolynomial.eval₂Hom c z) ((MvPolynomial.mapEquiv ι e) (MvPolynomial.C a))
      rw [MvPolynomial.mapEquiv_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C] <;> rfl
    · intro j
      rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
      change z j = (MvPolynomial.eval₂Hom c z) ((MvPolynomial.mapEquiv ι e) (MvPolynomial.X j))
      rw [MvPolynomial.mapEquiv_apply, MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
  rw [hmap]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (MvPolynomial.mapEquiv ι e).bijective) h

end AlgebraicGeometry.RamifiedNormalization.StageFour
