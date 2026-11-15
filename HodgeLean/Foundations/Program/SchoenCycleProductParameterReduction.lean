import HodgeLean.Foundations.Program.SchoenCycleProductStalkPoints
import HodgeLean.Foundations.Program.SchoenCycleGeometryChecks

/-! # Scalar reduction of actual curve-power parameter morphisms -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A complex scalar residue gives the base-point morphism into its algebra spectrum.
Source: Hartshorne, Algebraic Geometry, II.2, functoriality of spectra. -/
def s2e_scalarResidue_morphism (A : Type) [CommRing A] [Algebra ℂ A]
    (ε : A →ₐ[ℂ] ℂ) :
    Over.mk (𝟙 (Spec ↧ℂ)) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom ε.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom ε.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) = 𝟙 (Spec ↧ℂ)
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    ext c
    exact ε.commutes c)

/-- A tuple of nilpotent curve parameter maps reduces to its exact tuple of
actual complex points in the retained scheme power.
Source: Hartshorne, Algebraic Geometry, II.2, local spectra and products;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_curve_power_nilpotent_parameter_reduction
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (n : ℕ)
    (p : Fin n → ComplexPoint X)
    (t : ∀ i, X.left.presheaf.stalk (p i).underlying)
    (ht : ∀ i, IsLocalRing.maximalIdeal (X.left.presheaf.stalk (p i).underlying) =
      Ideal.span {t i})
    (A : Type) [CommRing A] [Algebra ℂ A] :
    letI (i : Fin n) : Algebra ℂ (X.left.presheaf.stalk (p i).underlying) :=
      (HodgeLean.Foundations.Curves.stalkC (p i).underlying).toAlgebra
    ∀ (f : ∀ i, X.left.presheaf.stalk (p i).underlying →ₐ[ℂ] A),
      (∀ i, IsNilpotent (f i (t i))) → ∀ ε : A →ₐ[ℂ] ℂ,
      s2e_scalarResidue_morphism A ε ≫
        s2_lift n (fun i => s2e_stalkMap_to_base_morphism X (p i).underlying A
          (f i).toRingHom (fun c => (f i).commutes c)) = s2_lift n p := by
  letI (i : Fin n) : Algebra ℂ (X.left.presheaf.stalk (p i).underlying) :=
    (HodgeLean.Foundations.Curves.stalkC (p i).underlying).toAlgebra
  intro f hf ε
  apply (spec_g3_isLimit_fan X n).some.hom_ext
  rintro ⟨i⟩
  change (s2e_scalarResidue_morphism A ε ≫ _) ≫ g3_proj X n i =
    s2_lift n p ≫ g3_proj X n i
  rw [Category.assoc, s2_check_lift_proj, s2_check_lift_proj]
  apply Over.OverMorphism.ext
  exact s2e_curve_nilpotent_stalkMap_reduction X (p i) (t i) (ht i) A (f i) (hf i) ε

end HodgeLean.Foundations.Program
