import HodgeLean.Foundations.Program.G32Native.PairedConormalProjectiveIsoLift
import HodgeLean.Foundations.Program.G32Native.PairedConormalQuasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Unit lifting with quasicoherence of only the supplied middle object -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The quotient's quasicoherence follows from the actual elementary sequence. -/
theorem conormal_projective_unit_lift
    (R : Type) [CommRing R] (k : ℕ) {X : Scheme}
    (e : Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R) ≅ X)
    (S : ShortComplex X.Modules) (hs : S.ShortExact) [S.X₂.IsQuasicoherent]
    (J : Type) [Finite J] (ef : S.X₁ ≅ SheafOfModules.free J)
    (u : SheafOfModules.unit X.ringCatSheaf ⟶ S.X₃) :
    ∃ l : SheafOfModules.unit X.ringCatSheaf ⟶ S.X₂, l ≫ S.g = u := by
  have hfree : (SheafOfModules.free (R := X.ringCatSheaf) J).IsQuasicoherent := inferInstance
  letI : S.X₁.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((sheafOfModulesEquivalence X).functor.mapIso ef.symm) hfree
  letI : S.X₃.IsQuasicoherent := conormal_shortExact_last_quasicoherent S hs
  letI : ((pullback e.hom).obj S.X₂).IsQuasicoherent :=
    conormal_open_pullback_quasicoherent e.hom S.X₂
  letI : ((pullback e.hom).obj S.X₃).IsQuasicoherent :=
    conormal_open_pullback_quasicoherent e.hom S.X₃
  exact conormal_projective_iso_unit_lift R k e S hs J ef u

end HodgeLean.Foundations.Program.G32Native
