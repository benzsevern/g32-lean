import Mathlib.Basic.Complex.Basic
import HodgeLean.Foundations.Program.SchoenCycleU1DualCongr
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Transporting the complex dual-number test -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A residue-field algebra equivalence transports injectivity of the actual
complex dual-number test to dual numbers over that residue field.
Source: Hartshorne, Algebraic Geometry, II.8, tangent vectors and scalar change. -/
theorem s2e_u1_dual_separation_transport
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (hsep : Function.Injective (fun u : Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))) ⟶ X => u ≫ f))
    (K : Type) [CommRing K] [Algebra ℂ K] (e : K ≃ₐ[ℂ] ℂ) :
    Function.Injective (fun u : Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber K)))) ⟶ X => u ≫ f) := by
  let D₀ : Over (Spec ↧ℂ) := Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))))
  let D : Over (Spec ↧ℂ) := Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber K))))
  let ed := s2e_u1_dualNumberCongr e
  let es : D₀.left ≅ D.left := Scheme.Spec.mapIso ed.toRingEquiv.toCommRingCatIso.op
  let E : D₀ ≅ D := Over.isoMk es (by
    change Spec.map (CommRingCat.ofHom ed.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber K))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact ed.toAlgHom.comp_algebraMap)
  change Function.Injective (fun u : D ⟶ X => u ≫ f)
  intro u v huv
  apply (cancel_epi E.hom).mp
  apply hsep
  simpa only [Category.assoc] using congrArg (fun w => E.hom ≫ w) huv

end HodgeLean.Foundations.Program
