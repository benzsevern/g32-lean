import HodgeLean.Foundations.Program.SchoenCycleC2AffinePushforwardSectionsHelpers

/-! # Associated-module coordinates for affine pushforward -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native

/-- The global sections of an affine pushed associated sheaf are the
original module with scalars restricted along the affine map. -/
def unionAffinePushforwardTildeSectionsIso
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (M : ModuleCat S) :
    (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)) ≅
        (ModuleCat.restrictScalars φ.hom).obj M :=
  (s2e_affine_pushforward_sections_iso R S φ).app (tilde M) ≪≫
    (ModuleCat.restrictScalars φ.hom).mapIso (tilde.isoTop M).symm

/-- Affine pushforward of an associated sheaf is the associated sheaf of
the scalar-restricted module. -/
def unionAffinePushforwardTildeIso
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (M : ModuleCat S) :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.restrictScalars φ.hom).obj M) := by
  let P := (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)
  have : IsIso (tilde M).fromTildeΓ :=
    (isIso_fromTildeΓ_iff_isLocalizing (tilde M)).mpr (isLocalizing_tilde M)
  have : IsIso P.fromTildeΓ := isIso_fromTildeΓ_pushforward φ (tilde M)
  exact (asIso P.fromTildeΓ).symm ≪≫
    (tilde.functor R).mapIso (unionAffinePushforwardTildeSectionsIso R S φ M)

#print axioms unionAffinePushforwardTildeSectionsIso
#print axioms unionAffinePushforwardTildeIso

end HodgeLean.Foundations.Program.G32Native
