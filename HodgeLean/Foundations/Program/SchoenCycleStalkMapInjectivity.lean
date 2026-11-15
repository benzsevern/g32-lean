import HodgeLean.Foundations.Program.SchoenCycleNilpotentCurvePoints

/-! # Faithfulness of fixed-point local stalk data -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- At a fixed point, equal actual morphisms from a local spectrum have equal
specified local stalk maps.
Source: Mathlib, AlgebraicGeometry.SpecToEquivOfLocalRing;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_stalkMap_to_base_morphism_injective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (p : X.left) (A : Type) [CommRing A] [Algebra ℂ A] [IsLocalRing A]
    (f g : X.left.presheaf.stalk p →+* A) [IsLocalHom f] [IsLocalHom g]
    (hf : ∀ c, f (HodgeLean.Foundations.Curves.stalkC p c) = algebraMap ℂ A c)
    (hg : ∀ c, g (HodgeLean.Foundations.Curves.stalkC p c) = algebraMap ℂ A c)
    (h : s2e_stalkMap_to_base_morphism X p A f hf =
      s2e_stalkMap_to_base_morphism X p A g hg) : f = g := by
  have he := congrArg (fun u => SpecToEquivOfLocalRing X.left (CommRingCat.of A) u.left) h
  rw [s2e_stalkMap_to_base_morphism_data, s2e_stalkMap_to_base_morphism_data] at he
  have hh := (Sigma.mk.inj_iff.mp he).2
  have hv := congrArg Subtype.val (eq_of_heq hh)
  exact congrArg CommRingCat.Hom.hom hv

end HodgeLean.Foundations.Program
