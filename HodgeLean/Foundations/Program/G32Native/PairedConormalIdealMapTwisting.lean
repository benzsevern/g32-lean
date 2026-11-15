import HodgeLean.Foundations.Program.G32Native.PairedConormalIdealSectionTransition
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheaf

/-! # Twisting sections from maps of the actual hyperplane ideal -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.GlueOfCocycle
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- A map to the structure module retains a scalar transition of its source sections. -/
theorem paired_unitMap_scalar_transition {Y : Scheme} (M : Y.Modules)
    (φ : M ⟶ SheafOfModules.unit Y.ringCatSheaf)
    {U V W : Y.Opens} (hU : W ≤ U) (hV : W ≤ V)
    (a : Γ(Y, W)) (s : Γ(M, U)) (t : Γ(M, V))
    (h : a • M.presheaf.map (homOfLE hV).op t =
      M.presheaf.map (homOfLE hU).op s) :
    a * Y.presheaf.map (homOfLE hV).op
      (show Γ(Y, V) from φ.val.app (Opposite.op V) t) =
        Y.presheaf.map (homOfLE hU).op
          (show Γ(Y, U) from φ.val.app (Opposite.op U) s) := by
  have hφ := congrArg (φ.val.app (Opposite.op W)) h
  have hs := (φ.val.app (Opposite.op W)).hom.map_smul a
    (M.presheaf.map (homOfLE hV).op t)
  have hU' := PresheafOfModules.naturality_apply φ.val (homOfLE hU).op s
  have hV' := PresheafOfModules.naturality_apply φ.val (homOfLE hV).op t
  exact (congrArg (fun z : Γ(Y, W) => a * z) hV').symm.trans
    (hs.symm.trans (hφ.trans hU'))

variable (k : ℕ)
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)
local notation "I" => Conormal.idealModule (Scheme.IdealSheafData.subschemeι (paired_nativeHyperplaneIdeal k))

/-- The local coefficient is the image of the original ideal generator. -/
def paired_nativeIdealMapCoefficient
    (φ : I ⟶ SheafOfModules.unit (X).ringCatSheaf) (i : Fin (k + 1)) :
    Γ(X, ProjSpace.standardOpen ℂ k i) :=
  φ.val.app (Opposite.op (ProjSpace.standardOpen ℂ k i))
    (paired_nativeHyperplaneStandardGenerator k i)

/-- The supplied ideal map retains the original coordinate transition. -/
theorem paired_nativeIdealMapCoefficient_transition
    (φ : I ⟶ SheafOfModules.unit (X).ringCatSheaf) (i j : Fin (k + 1))
    (U : (X).Opens) (hi : U ≤ ProjSpace.standardOpen ℂ k i)
    (hj : U ≤ ProjSpace.standardOpen ℂ k j) :
    rO hi (ProjSpace.coordinateRatioSection ℂ k i j) *
      rO hj (paired_nativeIdealMapCoefficient k φ j) =
      rO hi (paired_nativeIdealMapCoefficient k φ i) := by
  exact paired_unitMap_scalar_transition I φ hi hj _ _ _
    (paired_nativeHyperplaneStandardGenerator_transition k i j U hi hj)

/-- The original ideal map determines an actual global twisting section. -/
def paired_nativeIdealMapTwistingSection
    (φ : I ⟶ SheafOfModules.unit (X).ringCatSheaf) :
    Γ(ProjSpace.twistingSheaf ℂ k, ⊤) :=
  glueMk (ProjSpace.twistingCocycle ℂ k) ⊤
    (fun i => rO inf_le_right (paired_nativeIdealMapCoefficient k φ i.down)) (by
      intro i j
      change rO (leTi (U := ProjSpace.twistingCover ℂ k) ⊤ i j)
          (rO inf_le_right (paired_nativeIdealMapCoefficient k φ i.down)) =
        rO (leij (U := ProjSpace.twistingCover ℂ k) ⊤ i j)
          (rO inf_le_left (ProjSpace.coordinateRatioSection ℂ k i.down j.down)) *
        rO (leTj (U := ProjSpace.twistingCover ℂ k) ⊤ i j)
          (rO inf_le_right (paired_nativeIdealMapCoefficient k φ j.down))
      rw [rO_rO, rO_rO, rO_rO]
      exact (paired_nativeIdealMapCoefficient_transition k φ i.down j.down _ _ _).symm)

/-- Every component is the image of the supplied ideal generator. -/
theorem paired_nativeIdealMapTwistingSection_component
    (φ : I ⟶ SheafOfModules.unit (X).ringCatSheaf)
    (i : ULift (Fin (k + 1))) :
    glueComponent (ProjSpace.twistingCocycle ℂ k) ⊤ i
      (paired_nativeIdealMapTwistingSection k φ) =
        rO inf_le_right (paired_nativeIdealMapCoefficient k φ i.down) := by
  exact glueComponent_glueMk _ _ _ _ i

end HodgeLean.Foundations.Program.G32Native
