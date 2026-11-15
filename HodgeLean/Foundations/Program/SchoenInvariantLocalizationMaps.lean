import HodgeLean.Foundations.Program.SchoenInvariantLocalization
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

section
variable (A B K L G : Type)
    [CommRing A] [CommRing B] [CommRing K] [CommRing L]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Group G] [MulSemiringAction G B] [MulSemiringAction G L]
    [SMulCommClass G A B] [SMulDistribClass G B L] [Algebra.IsInvariant A B G]
    (M : Submonoid A) [IsLocalization M K]
    [IsLocalization (Algebra.algebraMapSubmonoid B M) L]
    (hAB : Function.Injective (algebraMap A B))
    (hBL : Function.Injective (algebraMap B L))

/-- The map from the original invariant base to the fixed localized ring. -/
def s2_localizedFixedBaseMap : A →+* FixedPoints.subring L G :=
  (s2_invariantsLocalizationEquiv A B K L G M hAB hBL).toRingHom.comp (algebraMap A K)

/-- The fixed localized ring is a localization through its actual base map. -/
theorem s2_localizedFixedBaseMap_isLocalization :
    letI := (s2_localizedFixedBaseMap A B K L G M hAB hBL).toAlgebra
    IsLocalization M (FixedPoints.subring L G) := by
  exact (IsLocalization.isLocalization_iff_of_ringEquiv M
    (s2_invariantsLocalizationEquiv A B K L G M hAB hBL)).mp inferInstance

/-- The invariant localization map has the prescribed underlying scalar map. -/
theorem s2_localizedFixedBaseMap_coe_apply (a : A) :
    (s2_localizedFixedBaseMap A B K L G M hAB hBL a : L) = algebraMap A L a := by
  change algebraMap K L (algebraMap A K a) = algebraMap A L a
  exact (IsScalarTower.algebraMap_apply A K L a).symm

/-- A principal invariant localization gives an open immersion through its actual base map. -/
theorem s2_localizedFixedBaseMap_spec_openImmersion (a : A) (hM : M = Submonoid.powers a) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (s2_localizedFixedBaseMap A B K L G M hAB hBL))) := by
  letI := (s2_localizedFixedBaseMap A B K L G M hAB hBL).toAlgebra
  haveI : IsLocalization.Away a (FixedPoints.subring L G) := by
    change IsLocalization (Submonoid.powers a) (FixedPoints.subring L G)
    rw [← hM]
    exact s2_localizedFixedBaseMap_isLocalization A B K L G M hAB hBL
  exact IsOpenImmersion.of_isLocalization a

end
end HodgeLean.Foundations.Program
