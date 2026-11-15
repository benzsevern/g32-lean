import HodgeLean.Foundations.Program.G32Native.PairedConormalCoordinateFractionSection

/-! # Actual twisting sections represented by the original coordinate monomials -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open ProjSpaceCech
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- Restricting a global section through an intermediate open retains its direct restriction. -/
theorem paired_module_restrict_top {X : Scheme} (M : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (s : Γ(M, ⊤)) :
    M.presheaf.map (homOfLE h).op
      (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) =
        M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s := by
  change (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
    M.presheaf.map (homOfLE h).op).hom s = _
  rw [← Functor.map_comp]
  rfl

/-- On every coordinate intersection the original monomial gives the original
coordinate twisting section, retaining the coordinate frame and its scale. -/
theorem paired_twist_coordinateFraction_sectionAt
    (R : Type) [CommRing R] (n : ℕ)
    (I : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ I)
    (j : Fin (n + 1)) :
    ProjSpace.twistingFractionSectionEquivAt R n 1 i hi
      (GradedModule.sec.mk _ I (paired_twist_coordinateFraction R n I j)) =
      ((ProjSpace.twistingSheaf R n).tensorPow 1).presheaf.map
        (homOfLE (le_top : ProjSpace.coordinateIntersection R n I ≤ ⊤)).op
        (tensorPowSection (ProjSpace.twistingCoordinateSection R n j) 1) := by
  rw [ProjSpace.twistingFractionSectionEquivAt_apply,
    paired_twist_coordinateFraction_coefficient_section]
  let L := (ProjSpace.twistingSheaf R n).tensorPow 1
  let hI := ProjSpace.coordinateIntersection_le_standardOpen R n hi
  have h := congrArg (fun s => L.presheaf.map (homOfLE hI).op s)
    (ProjSpace.coordinateRatioSection_pow_smul_twistingCoordinateSection R n 1 i j)
  change L.presheaf.map (homOfLE hI).op
    (ProjSpace.coordinateRatioSection R n i j ^ 1 • L.presheaf.map (homOfLE le_top).op
      (tensorPowSection (ProjSpace.twistingCoordinateSection R n i) 1)) =
    L.presheaf.map (homOfLE hI).op (L.presheaf.map (homOfLE le_top).op
      (tensorPowSection (ProjSpace.twistingCoordinateSection R n j) 1)) at h
  simp only [pow_one, L.map_smul, paired_module_restrict_top] at h
  exact h

/-- The same identity holds for the original frame-independent fraction map. -/
theorem paired_twist_coordinateFraction_section
    (R : Type) [CommRing R] (n : ℕ)
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty) (j : Fin (n + 1)) :
    ProjSpace.twistingFractionSectionEquiv R n 1 I hI
      (GradedModule.sec.mk _ I (paired_twist_coordinateFraction R n I j)) =
      ((ProjSpace.twistingSheaf R n).tensorPow 1).presheaf.map
        (homOfLE (le_top : ProjSpace.coordinateIntersection R n I ≤ ⊤)).op
        (tensorPowSection (ProjSpace.twistingCoordinateSection R n j) 1) :=
  paired_twist_coordinateFraction_sectionAt R n I (I.min' hI) (Finset.min'_mem I hI) j

end HodgeLean.Foundations.Program.G32Native
