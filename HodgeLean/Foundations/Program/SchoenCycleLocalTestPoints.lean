import HodgeLean.Foundations.Program.SchoenCycleProductParameterReduction

/-! # Actual local test spectra and their scalar-compatible stalk maps -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual morphism from a local complex algebra spectrum induces the
specified complex scalar map on its image stalk, including nonreduced sources.
Source: Hartshorne, Algebraic Geometry, II.2, local spectra and base morphisms. -/
theorem s2e_base_morphism_stalk_constants
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (A : Type) [CommRing A] [Algebra ℂ A] [IsLocalRing A]
    (u : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) ⟶ X) (c : ℂ) :
    (Scheme.stalkClosedPointTo u.left).hom
      (HodgeLean.Foundations.Curves.stalkC (u.left (IsLocalRing.closedPoint A)) c) =
        algebraMap ℂ A c := by
  have he : CommRingCat.ofHom (HodgeLean.Foundations.Curves.stalkC
      (u.left (IsLocalRing.closedPoint A))) ≫ Scheme.stalkClosedPointTo u.left =
        CommRingCat.ofHom (algebraMap ℂ A) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← HodgeLean.Foundations.Curves.fromSpecStalk_comp_hom',
      ← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, Over.w u]
    rfl
  exact congrArg (fun k : CommRingCat.of ℂ ⟶ CommRingCat.of A => k.hom c) he

/-- Scalar reduction to a specified complex point identifies the image of
the local spectrum's distinguished point.
Source: Hartshorne, Algebraic Geometry, II.2, local spectra. -/
theorem s2e_base_morphism_point_of_scalar_reduction
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (A : Type) [CommRing A] [Algebra ℂ A] [IsLocalRing A]
    (ε : A →ₐ[ℂ] ℂ)
    (u : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) ⟶ X)
    (x : ComplexPoint X) (h : s2e_scalarResidue_morphism A ε ≫ u = x) :
    u.left (IsLocalRing.closedPoint A) = x.underlying := by
  have hsurj : Function.Surjective ε := by
    intro c
    refine ⟨algebraMap ℂ A c, ?_⟩
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using ε.commutes c
  letI : IsLocalHom ε.toRingHom := IsLocalHom.of_surjective ε.toRingHom hsurj
  have he := congrArg (fun z : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ X =>
    z.left (IsLocalRing.closedPoint ℂ)) h
  change u.left (Spec.map (CommRingCat.ofHom ε.toRingHom) (IsLocalRing.closedPoint ℂ)) =
    x.underlying at he
  rwa [Spec_closedPoint] at he

/-- A local test morphism whose distinguished point is specified comes from
a scalar-compatible local map on that exact stalk.
Source: Mathlib, AlgebraicGeometry.SpecToEquivOfLocalRing;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_base_morphism_stalk_map_at_point
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (A : Type) [CommRing A] [Algebra ℂ A] [IsLocalRing A]
    (u : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) ⟶ X)
    (p : X.left) (hp : u.left (IsLocalRing.closedPoint A) = p) :
    ∃ l : X.left.presheaf.stalk p →+* A, IsLocalHom l ∧
      ∃ hc : ∀ c, l (HodgeLean.Foundations.Curves.stalkC p c) = algebraMap ℂ A c,
        s2e_stalkMap_to_base_morphism X p A l hc = u := by
  subst p
  let v : Spec (CommRingCat.of A) ⟶ X.left := u.left
  refine ⟨(Scheme.stalkClosedPointTo v).hom, Scheme.isLocalHom_stalkClosedPointTo' v,
    s2e_base_morphism_stalk_constants X A u, ?_⟩
  apply Over.OverMorphism.ext
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk u.left

end HodgeLean.Foundations.Program
