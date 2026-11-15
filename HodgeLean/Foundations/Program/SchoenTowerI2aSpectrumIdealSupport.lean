import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual ideal sheaf on a coefficient spectrum has the zero locus of
its specified coefficient ideal as its support.
Source: Mathlib, `Scheme.IdealSheafData.coe_support_inter`, `Spec_zeroLocus`
and `Ideal.comap_map_of_bijective`. -/
theorem s2v_i2a_spectrum_ideal_support
    (R : Type) [CommRing R] (K : (Spec (CommRingCat.of R)).IdealSheafData) (I : Ideal R)
    (hK : K.ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :
    K.support.carrier = PrimeSpectrum.zeroLocus (I : Set R) := by
  have hs : K.support.carrier = (Spec (CommRingCat.of R)).zeroLocus
      (U := ⊤) (K.ideal ⟨⊤, isAffineOpen_top _⟩) := by
    change (K.support : Set (Spec (CommRingCat.of R))) = _
    simpa only [TopologicalSpace.Opens.coe_top, Set.inter_univ] using
      K.coe_support_inter ⟨⊤, isAffineOpen_top _⟩
  rw [hs, hK, Spec_zeroLocus]
  change PrimeSpectrum.zeroLocus
      (((I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).comap
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) : Set R) = _
  have hb : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  rw [Ideal.comap_map_of_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom hb]

end HodgeLean.Foundations.Program
