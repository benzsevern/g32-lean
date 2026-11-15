import HodgeLean.Foundations.Program.G32Native.PairedC3NormalizedChartSmooth

/-! # Smoothness in the original supplied residual coordinate ring -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- A coefficient-preserving identification of the actual residual ring
with a polynomial ring transfers smoothness of the base to its actual
coordinate map, including any affine change of polynomial coordinate. -/
theorem pairedC3_supplied_projection_smooth
    (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    (E : B ≃+* A[X]) (c : R →+* B)
    (hc : ∀ r, E (c r) = C (algebraMap R A r))
    (e : A[X] ≃ₐ[A] A[X])
    (hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    Smooth (Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom c (E.symm (e X))))) := by
  have hmap : Polynomial.eval₂RingHom c (E.symm (e X)) =
      E.symm.toRingHom.comp
        (e.toRingEquiv.toRingHom.comp (Polynomial.mapRingHom (algebraMap R A))) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C,
        coe_mapRingHom, Polynomial.map_C]
      change c r = E.symm (e (C (algebraMap R A r)))
      rw [show e (C (algebraMap R A r)) = C (algebraMap R A r) from
        e.commutes (algebraMap R A r)]
      rw [← hc r, RingEquiv.symm_apply_apply]
    · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X,
        coe_mapRingHom, Polynomial.map_X]
      rfl
  letI : IsIso (CommRingCat.ofHom E.symm.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr E.symm.bijective
  letI : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr e.bijective
  letI := pairedC3_polynomial_projection_smooth R A hs
  rw [hmap]
  change Smooth (Spec.map
    ((CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap R A)) ≫
      CommRingCat.ofHom e.toRingEquiv.toRingHom) ≫ CommRingCat.ofHom E.symm.toRingHom))
  rw [Spec.map_comp, Spec.map_comp]
  infer_instance

#print axioms pairedC3_supplied_projection_smooth
end HodgeLean.Foundations.Program.G32Native
