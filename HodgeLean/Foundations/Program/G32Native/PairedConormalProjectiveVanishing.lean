import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafPositiveVanishing
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.FiniteFreeTensorVanishing
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.ModuleSheafCohomologyIso

/-! # Vanishing for the actual projective unit and finite free sheaves -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type) [CommRing R] (k : ℕ)
local notation "P" => Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R)
local notation "sP" => (𝟙 P) ≫ ProjSpace.π R k
local notation "K" => ProjSpace.stdCoverPullback (𝟙 P)

/-- The degree-zero twisting power gives vanishing for the actual structure module. -/
theorem conormal_projective_unit_vanishing (q : ℕ) :
    Subsingleton ((toOModulePresheaf sP
      (SheafOfModules.unit (P).ringCatSheaf)).HSucc K q) := by
  exact ProjSpace.twistingSectionPresheaf_subsingleton_HSucc R k 0 q

/-- Finite free projective sheaves inherit vanishing through the actual tensor unitor. -/
theorem conormal_projective_free_vanishing (J : Type) [Finite J] (q : ℕ) :
    Subsingleton ((toOModulePresheaf sP
      (SheafOfModules.free J : (P).Modules)).HSucc K q) := by
  let F : (P).Modules := SheafOfModules.free J
  let U : (P).Modules := SheafOfModules.unit (P).ringCatSheaf
  have : Subsingleton ((toOModulePresheaf sP U).HSucc K q) :=
    conormal_projective_unit_vanishing R k q
  letI hv : Subsingleton ((toOModulePresheaf sP (F ⊗ 𝟙_ (P).Modules)).HSucc K q) := by
    change Subsingleton ((toOModulePresheaf sP (tensor F U)).HSucc K q)
    exact finiteFreeTensor_subsingleton_HSucc sP U J K q
  exact subsingleton_HSucc_of_iso sP K (ρ_ F) q

end HodgeLean.Foundations.Program.G32Native
