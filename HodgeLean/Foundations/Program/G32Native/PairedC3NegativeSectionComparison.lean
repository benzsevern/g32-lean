import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeSectionRestrictions

/-! # Coordinate-independent native negative-line section comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open ProjSpaceCech AlgebraicGeometry.ProjSpace Scheme.Modules
open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The chosen coordinate only supplies a frame; the actual section map
is independent of that choice. -/
def pairedC3NegativeFractionSectionEquiv (R : Type) [CommRing R] (n : ℕ)
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    GradedModule.sec (GradedModule.FD R n (-1)) I ≃ₗ[R]
      sectionModuleOverBase ((𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))) ≫ π R n)
        (twistingSheaf R n).dual (coordinateIntersection R n I) :=
  pairedC3NegativeFractionSectionEquivAt R n (I.min' hI) (Finset.min'_mem I hI)

/-- The coordinate-independent equivalence commutes with native restrictions
and the original structural base action. -/
theorem paired_c3_negative_section_restrict (R : Type) [CommRing R] (n : ℕ)
    {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) (hI : I.Nonempty) (hJ : J.Nonempty)
    (z : GradedModule.sec (GradedModule.FD R n (-1)) I) :
    sectionRestrictionOverBase ((𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))) ≫ π R n)
        (twistingSheaf R n).dual (coordinateIntersection_mono R n hIJ)
        (pairedC3NegativeFractionSectionEquiv R n I hI z) =
      pairedC3NegativeFractionSectionEquiv R n J hJ (GradedModule.secIncl _ hIJ z) := by
  exact (paired_c3_negative_section_at_restrict R n hIJ (I.min' hI) (Finset.min'_mem I hI) z).trans
    (paired_c3_negative_section_independent R n (I.min' hI) (hIJ (Finset.min'_mem I hI))
      (J.min' hJ) (Finset.min'_mem J hJ) (GradedModule.secIncl _ hIJ z))

#print axioms pairedC3NegativeFractionSectionEquiv
#print axioms paired_c3_negative_section_restrict
end HodgeLean.Foundations.Program.G32Native
