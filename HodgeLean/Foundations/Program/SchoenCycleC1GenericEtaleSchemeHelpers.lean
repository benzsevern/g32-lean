import Mathlib.AlgebraicGeometry.Morphisms.Finite
import HodgeLean.Foundations.Program.SchoenCycleC1GenericEtaleHelpers
import HodgeLean.Foundations.Program.SchoenTowerEtaleSpecNeighborhood

/-! # Generic base neighbourhoods for actual finite affine projections -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A finite injective affine domain projection in characteristic zero
is etale on the entire inverse image of a nonempty base open. -/
theorem s2e_c1_finite_spec_exists_etale_base_open
    (R S : Type) [CommRing R] [IsDomain R] [CharZero R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S] :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
    ∃ U : (Spec (CommRingCat.of R)).Opens,
      (U : Set (Spec (CommRingCat.of R))).Nonempty ∧ IsFinite (f ∣_ U) ∧ Etale (f ∣_ U) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  haveI : IsFinite f := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  obtain ⟨r, hr, hEt⟩ := s2e_c1_finite_charZero_exists_base_etale_basicOpen R S
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen r
  have hpre : f ⁻¹ᵁ U = PrimeSpectrum.basicOpen (algebraMap R S r) := rfl
  let V : (Spec (CommRingCat.of S)).Opens := PrimeSpectrum.basicOpen (algebraMap R S r)
  haveI := hEt
  haveI : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away (algebraMap R S r))))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have hfac : V.ι ≫ f =
      (basicOpenIsoSpecAway (R := CommRingCat.of S) (algebraMap R S r)).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (algebraMap R S r)))) := by
    rw [← basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of S) (algebraMap R S r),
      Category.assoc, ← Spec.map_comp]
    congr 2
  haveI : Etale (V.ι ≫ f) := by rw [hfac]; infer_instance
  haveI : Etale ((f ⁻¹ᵁ U).ι ≫ f) := by rw [hpre]; exact inferInstanceAs (Etale (V.ι ≫ f))
  haveI : Etale ((f ∣_ U) ≫ U.ι) := by rw [morphismRestrict_ι]; infer_instance
  haveI : Etale (f ∣_ U) := Etale.of_comp (f ∣_ U) U.ι
  refine ⟨U, ⟨⟨⊥, inferInstance⟩, ?_⟩, inferInstance, inferInstance⟩
  exact hr

end HodgeLean.Foundations.Program
