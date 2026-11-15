import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Locus

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Foundations.Program

/-- Étaleness at a ring prime gives an actual open neighborhood for the spectrum map. -/
theorem s2t_etale_spec_neighborhood {R S : Type} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S]
    (q : PrimeSpectrum S) [Algebra.IsEtaleAt R q.asIdeal] :
    ∃ V : (Spec (CommRingCat.of S)).Opens, q ∈ V ∧
      Etale (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  obtain ⟨r, hr, hEt⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) q.asIdeal
  letI := hEt
  refine ⟨PrimeSpectrum.basicOpen r, hr, ?_⟩
  have hmap : Etale (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      ((RingHom.etale_algebraMap).mpr inferInstance)
  letI := hmap
  have heq : (show (Spec (CommRingCat.of S)).Opens from PrimeSpectrum.basicOpen r).ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      (basicOpenIsoSpecAway (R := CommRingCat.of S) r).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) := by
    rw [← basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of S) r, Category.assoc, ← Spec.map_comp]
    congr 2
  rw [heq]
  infer_instance

end HodgeLean.Foundations.Program
