import HodgeLean.Foundations.Program.SchoenSelectedGeometryAlgebraSmoothPoints
import HodgeLean.Foundations.Program.SchoenSelectedGeometrySmoothPoints

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
namespace HodgeLean.Foundations.Program

local instance s0_affine_spec_finite_presentation
    (S : Type) [CommRing S] [Algebra ℂ S] [Algebra.FinitePresentation ℂ S] :
    LocallyOfFinitePresentation (affineSpecStructureMap S) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

/-- Local algebraic smoothness places the corresponding prime in the scheme smooth locus. -/
theorem s0_spec_mem_smoothLocus
    (S : Type) [CommRing S] [Algebra ℂ S] [Algebra.FinitePresentation ℂ S]
    (p : PrimeSpectrum S) [Algebra.IsSmoothAt ℂ p.asIdeal] :
    p ∈ (affineSpecStructureMap S).smoothLocus := by
  obtain ⟨r, hr, hs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth ℂ p.asIdeal
  letI := hs
  let j : Spec ↧(Localization.Away r) ⟶ Spec ↧S :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))
  have hp : p ∈ Set.range j := by
    change p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away r)))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨q, rfl⟩ := hp
  have hj : j ≫ affineSpecStructureMap S = affineSpecStructureMap (Localization.Away r) := by
    rw [← Spec.map_comp]
    congr 1
  letI : Smooth (j ≫ affineSpecStructureMap S) := by
    rw [hj]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  have hq : q ∈ (j ≫ affineSpecStructureMap S).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at hq

#print axioms s0_spec_mem_smoothLocus
end HodgeLean.Foundations.Program
