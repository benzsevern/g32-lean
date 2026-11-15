import HodgeLean.Foundations.Program.G32Native.PairedConormalProjectiveVanishing
import HodgeLean.Foundations.Program.G32Native.PairedConormalUnitLift

/-! # Lifting structure-module arrows through projective free-kernel sequences -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra

/-- On polynomial projective space, a finite free kernel suffices for global unit lifting. -/
theorem conormal_polynomial_projective_unit_lift
    (R : Type) [CommRing R] (k : ℕ)
    (S : ShortComplex (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R)).Modules)
    (hs : S.ShortExact) [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (J : Type) [Finite J] (e : S.X₁ ≅ SheafOfModules.free J)
    (u : SheafOfModules.unit
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R)).ringCatSheaf ⟶ S.X₃) :
    ∃ l : SheafOfModules.unit
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R)).ringCatSheaf ⟶ S.X₂,
      l ≫ S.g = u := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R)
  let sP := (𝟙 P) ≫ ProjSpace.π R k
  let K := ProjSpace.stdCoverPullback (𝟙 P)
  have : Subsingleton ((toOModulePresheaf sP (SheafOfModules.free J)).HSucc K 0) :=
    conormal_projective_free_vanishing R k J 0
  have : Subsingleton ((toOModulePresheaf sP S.X₁).HSucc K 0) :=
    subsingleton_HSucc_of_iso sP K e.symm 0
  exact conormal_unit_lift_of_top_surjective S.g
    (conormal_global_surjective_of_cech_vanishing sP K S hs) u

end HodgeLean.Foundations.Program.G32Native
