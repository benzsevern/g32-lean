import HodgeLean.Foundations.Program.G32Native.UnionConormalSquarePullback
import HodgeLean.Foundations.AlgebraicGeometry.ConormalBaseChangeTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Transporting the supplied conormal frames along comparison squares -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal HodgeLean.Foundations.Program

/-- Pullback retains the specified basis set of a free module sheaf. -/
def unionConormalPullbackFreeIso {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) :
    (Scheme.Modules.pullback f).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (Fin n) : Y.Modules) ≅
      (SheafOfModules.free (R := X.ringCatSheaf) (Fin n) : X.Modules) := by
  haveI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward f).IsRightAdjoint)
  exact SheafOfModules.pullbackObjFreeIso _ (Fin n)

/-- A frame pulls back along a scheme map with the same basis set. -/
def unionConormalPullbackFrame {X Y : Scheme.{0}} (f : X ⟶ Y)
    (M : Y.Modules) (n : ℕ)
    (e : M ≅ (SheafOfModules.free (R := Y.ringCatSheaf) (Fin n) : Y.Modules)) :
    (Scheme.Modules.pullback f).obj M ≅
      (SheafOfModules.free (R := X.ringCatSheaf) (Fin n) : X.Modules) :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ unionConormalPullbackFreeIso f n

/-- A frame on an open restricts to a pullback frame on any smaller open. -/
def unionConormalFrameOnSmallerOpen
    {X : Scheme.{0}} (M : X.Modules) (U V : X.Opens) (hVU : V ≤ U) (n : ℕ)
    (e : Scheme.Modules.restrict M U.ι ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin n) : U.toScheme.Modules)) :
    (Scheme.Modules.pullback V.ι).obj M ≅
      (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin n) : V.toScheme.Modules) :=
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι hVU)).symm.app M ≪≫
    (Scheme.Modules.pullbackComp (X.homOfLE hVU) U.ι).symm.app M ≪≫
      unionConormalPullbackFrame (X.homOfLE hVU) _ n
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e)

/-- Invertible natural comparisons transport the original first source frame. -/
def unionConormalSourceFrameTransport
    {Q₀ Q₁ W Q₀' Q₁' W' : Scheme.{0}}
    (i₀ : Q₀ ⟶ W) (a : Q₁ ⟶ Q₀) (i₀' : Q₀' ⟶ W') (a' : Q₁' ⟶ Q₀')
    (j : W' ⟶ W) (b₀ : Q₀' ⟶ Q₀) (b₁ : Q₁' ⟶ Q₁)
    (h₀ : b₀ ≫ i₀ = i₀' ≫ j) (hb : b₁ ≫ a = a' ≫ b₀)
    [IsIso (idealPullbackMap i₀ i₀' j b₀ h₀)] (n : ℕ)
    (e : (Scheme.Modules.pullback a).obj (s2c_conormal i₀) ≅
      (SheafOfModules.free (R := Q₁.ringCatSheaf) (Fin n) : Q₁.Modules)) :
    (Scheme.Modules.pullback a').obj (s2c_conormal i₀') ≅
      (SheafOfModules.free (R := Q₁'.ringCatSheaf) (Fin n) : Q₁'.Modules) := by
  haveI : IsIso (comparisonMap i₀ i₀' j b₀ h₀) :=
    comparisonMap_isIso_of_idealPullbackMap_isIso i₀ i₀' j b₀ h₀
  let c := asIso (comparisonMap i₀ i₀' j b₀ h₀)
  let s := (unionConormalSquarePullbackIso a a' b₀ b₁ hb).app (s2c_conormal i₀)
  exact ((Scheme.Modules.pullback a').mapIso c).symm ≪≫ s.symm ≪≫
    unionConormalPullbackFrame b₁ _ n e

/-- Invertible natural comparisons transport the original first target frame. -/
def unionConormalTargetFrameTransport
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (j : W' ⟶ W) (b : Q' ⟶ Q) (h : b ≫ i = i' ≫ j)
    [IsIso (idealPullbackMap i i' j b h)] (n : ℕ)
    (e : s2c_conormal i ≅
      (SheafOfModules.free (R := Q.ringCatSheaf) (Fin n) : Q.Modules)) :
    s2c_conormal i' ≅
      (SheafOfModules.free (R := Q'.ringCatSheaf) (Fin n) : Q'.Modules) := by
  haveI : IsIso (comparisonMap i i' j b h) :=
    comparisonMap_isIso_of_idealPullbackMap_isIso i i' j b h
  exact (asIso (comparisonMap i i' j b h)).symm ≪≫
    unionConormalPullbackFrame b _ n e

/-- A frame on the pulled original source transports to the new source. -/
def unionConormalSourcePulledFrameTransport
    {Q₀ Q₁ W Q₀' Q₁' W' : Scheme.{0}}
    (i₀ : Q₀ ⟶ W) (a : Q₁ ⟶ Q₀) (i₀' : Q₀' ⟶ W') (a' : Q₁' ⟶ Q₀')
    (j : W' ⟶ W) (b₀ : Q₀' ⟶ Q₀) (b₁ : Q₁' ⟶ Q₁)
    (h₀ : b₀ ≫ i₀ = i₀' ≫ j) (hb : b₁ ≫ a = a' ≫ b₀)
    [IsIso (idealPullbackMap i₀ i₀' j b₀ h₀)] (n : ℕ)
    (e : (Scheme.Modules.pullback b₁).obj
        ((Scheme.Modules.pullback a).obj (s2c_conormal i₀)) ≅
      (SheafOfModules.free (R := Q₁'.ringCatSheaf) (Fin n) : Q₁'.Modules)) :
    (Scheme.Modules.pullback a').obj (s2c_conormal i₀') ≅
      (SheafOfModules.free (R := Q₁'.ringCatSheaf) (Fin n) : Q₁'.Modules) := by
  haveI : IsIso (comparisonMap i₀ i₀' j b₀ h₀) :=
    comparisonMap_isIso_of_idealPullbackMap_isIso i₀ i₀' j b₀ h₀
  let c := asIso (comparisonMap i₀ i₀' j b₀ h₀)
  let s := (unionConormalSquarePullbackIso a a' b₀ b₁ hb).app (s2c_conormal i₀)
  exact ((Scheme.Modules.pullback a').mapIso c).symm ≪≫ s.symm ≪≫ e

/-- A frame on the pulled original target transports to the new target. -/
def unionConormalTargetPulledFrameTransport
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (j : W' ⟶ W) (b : Q' ⟶ Q) (h : b ≫ i = i' ≫ j)
    [IsIso (idealPullbackMap i i' j b h)] (n : ℕ)
    (e : (Scheme.Modules.pullback b).obj (s2c_conormal i) ≅
      (SheafOfModules.free (R := Q'.ringCatSheaf) (Fin n) : Q'.Modules)) :
    s2c_conormal i' ≅
      (SheafOfModules.free (R := Q'.ringCatSheaf) (Fin n) : Q'.Modules) := by
  haveI : IsIso (comparisonMap i i' j b h) :=
    comparisonMap_isIso_of_idealPullbackMap_isIso i i' j b h
  exact (asIso (comparisonMap i i' j b h)).symm ≪≫ e

#print axioms unionConormalSourceFrameTransport
#print axioms unionConormalTargetFrameTransport
end HodgeLean.Foundations.Program.G32Native
