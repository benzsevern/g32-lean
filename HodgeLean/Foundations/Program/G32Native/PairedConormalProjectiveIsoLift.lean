import HodgeLean.Foundations.Program.G32Native.PairedConormalProjectiveLift
import HodgeLean.Foundations.Program.G32Native.PairedConormalPullbackEquivalence
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Invertible.Invertible
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Transporting projective unit lifts through the actual scheme isomorphism -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original unit arrow lifts after transporting the supplied sequence to polynomial Proj. -/
theorem conormal_projective_iso_unit_lift
    (R : Type) [CommRing R] (k : ℕ) {X : Scheme}
    (e : Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R) ≅ X)
    (S : ShortComplex X.Modules) (hs : S.ShortExact)
    [((pullback e.hom).obj S.X₂).IsQuasicoherent]
    [((pullback e.hom).obj S.X₃).IsQuasicoherent]
    (J : Type) [Finite J] (ef : S.X₁ ≅ SheafOfModules.free J)
    (u : SheafOfModules.unit X.ringCatSheaf ⟶ S.X₃) :
    ∃ l : SheafOfModules.unit X.ringCatSheaf ⟶ S.X₂, l ≫ S.g = u := by
  let F := pullback e.hom
  letI : F.IsEquivalence := conormal_pullback_isEquivalence e
  let T := S.map F
  have ht : T.ShortExact := hs.map_of_exact F
  letI : T.X₂.IsQuasicoherent := inferInstanceAs (((pullback e.hom).obj S.X₂).IsQuasicoherent)
  letI : T.X₃.IsQuasicoherent := inferInstanceAs (((pullback e.hom).obj S.X₃).IsQuasicoherent)
  let eu := pullbackUnitIso e.hom
  let et : T.X₁ ≅ SheafOfModules.free J :=
    F.mapIso ef ≪≫ (SheafOfModules.mapFreeIso F J eu.symm).symm
  obtain ⟨l', hl'⟩ := conormal_polynomial_projective_unit_lift R k T ht J et
    (eu.inv ≫ F.map u)
  refine ⟨F.preimage (eu.hom ≫ l'), ?_⟩
  apply F.map_injective
  rw [Functor.map_comp, Functor.map_preimage, Category.assoc]
  change eu.hom ≫ l' ≫ T.g = F.map u
  rw [hl', ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end HodgeLean.Foundations.Program.G32Native
