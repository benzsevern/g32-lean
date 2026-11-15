import HodgeLean.Foundations.Program.SchoenCycleNilpotentCurvePoints
import HodgeLean.Adapters.AbelianPower

/-! # Actual curve-power morphisms from local stalk data -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Prescribed local maps to all curve factors determine a unique actual
morphism to the retained curve power over the complex base.
Source: Hartshorne, Algebraic Geometry, II.2; Mac Lane, Categories for the
Working Mathematician, III.4, categorical products. -/
theorem s2e_product_stalk_maps_realization
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (n : ℕ)
    (A : Type) [CommRing A] [Algebra ℂ A] [IsLocalRing A]
    (p : Fin n → X.left) (f : ∀ i, X.left.presheaf.stalk (p i) →+* A)
    [∀ i, IsLocalHom (f i)]
    (hf : ∀ i c, f i (HodgeLean.Foundations.Curves.stalkC (p i) c) = algebraMap ℂ A c) :
    ∃! u : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) ⟶ g3_power X n,
      ∀ i, SpecToEquivOfLocalRing X.left (CommRingCat.of A) (u ≫ g3_proj X n i).left =
        ⟨p i, ⟨CommRingCat.ofHom (f i), inferInstance⟩⟩ := by
  let D := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  let v (i : Fin n) : D ⟶ X := s2e_stalkMap_to_base_morphism X (p i) A (f i) (hf i)
  let c := Fan.mk D v
  let t := (spec_g3_isLimit_fan X n).some
  let u := t.lift c
  have hu (i : Fin n) : u ≫ g3_proj X n i = v i := t.fac c (Discrete.mk i)
  refine ⟨u, ?_, ?_⟩
  · intro i
    rw [hu]
    exact s2e_stalkMap_to_base_morphism_data X (p i) A (f i) (hf i)
  · intro w hw
    apply t.hom_ext
    rintro ⟨i⟩
    change w ≫ g3_proj X n i = u ≫ g3_proj X n i
    rw [hu]
    apply Over.OverMorphism.ext
    exact (SpecToEquivOfLocalRing X.left (CommRingCat.of A)).injective
      ((hw i).trans (s2e_stalkMap_to_base_morphism_data X (p i) A (f i) (hf i)).symm)

/-- Nilpotent values of regular local parameters in every factor are realized
by an actual morphism to the curve power, with the specified local maps.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
Hartshorne, Algebraic Geometry, II.2, local spectra and products. -/
theorem s2e_curve_power_nilpotent_parameter_realization
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (n : ℕ)
    (p : Fin n → ComplexPoint X)
    (t : ∀ i, X.left.presheaf.stalk (p i).underlying)
    (ht : ∀ i, IsLocalRing.maximalIdeal (X.left.presheaf.stalk (p i).underlying) =
      Ideal.span {t i})
    (hreg : ∀ i, Function.Injective (fun x => t i * x))
    (A : Type) [CommRing A] [Algebra ℂ A] [IsLocalRing A]
    (a : Fin n → A) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ f : ∀ i, X.left.presheaf.stalk (p i).underlying →+* A,
      (∀ i, f i (t i) = a i) ∧
      ∃ hlocal : ∀ i, IsLocalHom (f i),
      ∃! u : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) ⟶ g3_power X n,
        ∀ i, SpecToEquivOfLocalRing X.left (CommRingCat.of A) (u ≫ g3_proj X n i).left =
          ⟨(p i).underlying, ⟨CommRingCat.ofHom (f i), hlocal i⟩⟩ := by
  classical
  let R (i : Fin n) := X.left.presheaf.stalk (p i).underlying
  letI (i : Fin n) : Algebra ℂ (R i) :=
    (HodgeLean.Foundations.Curves.stalkC (p i).underlying).toAlgebra
  let φ (i : Fin n) : R i →ₐ[ℂ] ℂ :=
    { toRingHom := (p i).stalkHom.hom
      commutes' := s2e_complex_point_stalk_constants X (p i) }
  have hmaps (i : Fin n) : ∃ f : R i →ₐ[ℂ] A, f (t i) = a i := by
    obtain ⟨N, hN⟩ := ha i
    exact (s2e_parameter_nilpotent_map_exists_unique (R i) A (φ i) (t i) (ht i)
      (hreg i) N (a i) hN).exists
  choose f hf using hmaps
  have hlocal (i : Fin n) : IsLocalHom (f i).toRingHom :=
    s2e_nilpotent_parameter_map_isLocalHom (R i) A (t i) (ht i) (f i).toRingHom
      ((hf i).symm ▸ ha i)
  letI (i : Fin n) : IsLocalHom (f i).toRingHom := hlocal i
  refine ⟨fun i => (f i).toRingHom, hf, hlocal, ?_⟩
  exact s2e_product_stalk_maps_realization X n A (fun i => (p i).underlying)
    (fun i => (f i).toRingHom) (fun i c => (f i).commutes c)

end HodgeLean.Foundations.Program
