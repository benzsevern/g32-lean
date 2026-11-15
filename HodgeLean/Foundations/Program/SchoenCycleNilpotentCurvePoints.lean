import HodgeLean.Foundations.Program.SchoenCycleParameterJetMaps
import HodgeLean.Foundations.Program.SchoenCycleCurveStalkJets
import Mathlib.RingTheory.Nilpotent.Lemmas
import HodgeLean.Foundations.Program.SchoenCycleParameterResidue

/-! # Nilpotent parameter values and actual curve morphisms -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An algebra map sending a local parameter to a nilpotent is a local map.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 1 and 3. -/
theorem s2e_nilpotent_parameter_map_isLocalHom
    (R A : Type*) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (f : R →+* A) (hf : IsNilpotent (f t)) : IsLocalHom f := by
  apply ((IsLocalRing.local_hom_TFAE f).out 3 1).mp
  rw [ht, Ideal.map_span, Set.image_singleton]
  apply Ideal.span_le.mpr
  intro x hx
  have hx' : x = f t := Set.mem_singleton_iff.mp hx
  rw [hx']
  exact nilpotent_iff_mem_prime.mp hf (IsLocalRing.maximalIdeal A) inferInstance

/-- A scalar-compatible map from an actual stalk defines an actual morphism
over the complex base.
Source: Hartshorne, Algebraic Geometry, II.2, the spectrum of a local ring. -/
def s2e_stalkMap_to_base_morphism (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (p : X.left) (A : Type) [CommRing A] [Algebra ℂ A]
    (f : X.left.presheaf.stalk p →+* A)
    (hf : ∀ c, f (HodgeLean.Foundations.Curves.stalkC p c) = algebraMap ℂ A c) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) ⟶ X :=
  Over.homMk (Spec.map (CommRingCat.ofHom f) ≫ X.left.fromSpecStalk p) (by
    rw [Category.assoc, HodgeLean.Foundations.Curves.fromSpecStalk_comp_hom',
      ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext hf)

/-- The morphism constructed from a local stalk map retains exactly that
point and local map in the spectrum–stalk correspondence.
Source: Mathlib, AlgebraicGeometry.SpecToEquivOfLocalRing;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_stalkMap_to_base_morphism_data
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (p : X.left) (A : Type) [CommRing A] [Algebra ℂ A] [IsLocalRing A]
    (f : X.left.presheaf.stalk p →+* A) [IsLocalHom f]
    (hf : ∀ c, f (HodgeLean.Foundations.Curves.stalkC p c) = algebraMap ℂ A c) :
    SpecToEquivOfLocalRing X.left (CommRingCat.of A)
      (s2e_stalkMap_to_base_morphism X p A f hf).left =
        ⟨p, ⟨CommRingCat.ofHom f, inferInstance⟩⟩ := by
  exact (SpecToEquivOfLocalRing X.left (CommRingCat.of A)).apply_symm_apply
    ⟨p, ⟨CommRingCat.ofHom f, inferInstance⟩⟩

/-- A prescribed scalar-compatible local stalk map specifies a unique actual
morphism over the complex base.
Source: Mathlib, AlgebraicGeometry.SpecToEquivOfLocalRing;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_stalkMap_to_base_morphism_unique
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (p : X.left) (A : Type) [CommRing A] [Algebra ℂ A] [IsLocalRing A]
    (f : X.left.presheaf.stalk p →+* A) [IsLocalHom f]
    (hf : ∀ c, f (HodgeLean.Foundations.Curves.stalkC p c) = algebraMap ℂ A c) :
    ∃! u : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) ⟶ X,
      SpecToEquivOfLocalRing X.left (CommRingCat.of A) u.left =
        ⟨p, ⟨CommRingCat.ofHom f, inferInstance⟩⟩ := by
  refine ⟨s2e_stalkMap_to_base_morphism X p A f hf,
    s2e_stalkMap_to_base_morphism_data X p A f hf, ?_⟩
  intro u hu
  apply Over.OverMorphism.ext
  exact (SpecToEquivOfLocalRing X.left (CommRingCat.of A)).injective
    (hu.trans (s2e_stalkMap_to_base_morphism_data X p A f hf).symm)

/-- Reduction of a stalk-defined morphism agrees with the specified actual
complex point whenever their local maps agree after scalar residue.
Source: Hartshorne, Algebraic Geometry, II.2, functoriality of spectra;
Mathlib, AlgebraicGeometry.SpecToEquivOfLocalRing. -/
theorem s2e_stalkMap_to_base_morphism_reduction
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (p : ComplexPoint X)
    (A : Type) [CommRing A] [Algebra ℂ A]
    (f : X.left.presheaf.stalk p.underlying →+* A)
    (hf : ∀ c, f (HodgeLean.Foundations.Curves.stalkC p.underlying c) = algebraMap ℂ A c)
    (ε : A →ₐ[ℂ] ℂ) (hε : ε.toRingHom.comp f = p.stalkHom.hom) :
    Spec.map (CommRingCat.ofHom ε.toRingHom) ≫
      (s2e_stalkMap_to_base_morphism X p.underlying A f hf).left = p.left := by
  change Spec.map (CommRingCat.ofHom ε.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom f) ≫ X.left.fromSpecStalk p.underlying) = p.left
  rw [← Category.assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom f ≫ CommRingCat.ofHom ε.toRingHom = p.stalkHom := by
    apply CommRingCat.hom_ext
    exact hε
  rw [he]
  exact (SpecToEquivOfLocalRing X.left (CommRingCat.of ℂ)).symm_apply_apply p.left

/-- A nilpotent parameter value in an actual curve stalk reduces to the
specified complex point under every complex scalar residue.
Source: Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald,
Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_curve_nilpotent_stalkMap_reduction
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (p : ComplexPoint X)
    (t : X.left.presheaf.stalk p.underlying)
    (ht : IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) = Ideal.span {t})
    (A : Type) [CommRing A] [Algebra ℂ A] :
    letI : Algebra ℂ (X.left.presheaf.stalk p.underlying) :=
      (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
    ∀ (f : X.left.presheaf.stalk p.underlying →ₐ[ℂ] A), IsNilpotent (f t) →
    ∀ ε : A →ₐ[ℂ] ℂ,
      Spec.map (CommRingCat.ofHom ε.toRingHom) ≫
        (s2e_stalkMap_to_base_morphism X p.underlying A f.toRingHom (fun c => f.commutes c)).left =
          p.left := by
  let R := X.left.presheaf.stalk p.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  intro f hf ε
  let φ : R →ₐ[ℂ] ℂ :=
    { toRingHom := p.stalkHom.hom
      commutes' := s2e_complex_point_stalk_constants X p }
  have h0 : ε (f t) = 0 := isNilpotent_iff_eq_zero.mp (hf.map ε.toRingHom)
  have he := s2e_parameter_map_scalar_reduction R A φ t ht f ε h0
  apply s2e_stalkMap_to_base_morphism_reduction X p A f.toRingHom
    (fun c => f.commutes c) ε
  exact congrArg AlgHom.toRingHom he

end HodgeLean.Foundations.Program
