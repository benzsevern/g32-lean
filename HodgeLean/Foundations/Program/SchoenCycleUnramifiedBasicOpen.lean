import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Actual basic-open section maps from unramified localizations -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Formal unramifiedness of a localization identifies the actual section map on its affine basic open.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.3 and II.8. -/
theorem s2e_formallyUnramified_appLE_basicOpen
    (X Y : Scheme) (f : X ⟶ Y) (U : Y.affineOpens) (W : X.affineOpens)
    (hWU : W.1 ≤ f ⁻¹ᵁ U.1) (a : Γ(X, W.1))
    (h : letI : Algebra Γ(Y, U.1) Γ(X, W.1) := (f.appLE U.1 W.1 hWU).hom.toAlgebra
      Algebra.FormallyUnramified Γ(Y, U.1) (Localization.Away a)) :
    (f.appLE U.1 (X.basicOpen a) ((X.basicOpen_le a).trans hWU)).hom.FormallyUnramified := by
  let R := Γ(Y, U.1)
  let B := Γ(X, W.1)
  let C := Γ(X, X.basicOpen a)
  let φ := (f.appLE U.1 W.1 hWU).hom
  let ρ := (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
  letI : Algebra R B := φ.toAlgebra
  letI : Algebra B C := ρ.toAlgebra
  letI : Algebra R C := (ρ.comp φ).toAlgebra
  letI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsLocalization.Away a C :=
    W.2.isLocalization_of_eq_basicOpen a (homOfLE (X.basicOpen_le a)) rfl
  let e : Localization.Away a ≃ₐ[B] C :=
    IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) C
  have he : e.toRingEquiv.toRingHom.comp (algebraMap R (Localization.Away a)) =
      (f.appLE U.1 (X.basicOpen a) ((X.basicOpen_le a).trans hWU)).hom := by
    ext r
    change e (algebraMap R (Localization.Away a) r) = _
    rw [IsScalarTower.algebraMap_apply R B (Localization.Away a), e.commutes]
    have hc := f.appLE_map hWU (homOfLE (X.basicOpen_le a)).op
    exact congrArg (fun F : Γ(Y, U.1) ⟶ Γ(X, X.basicOpen a) => F.hom r) hc
  have hl : (algebraMap R (Localization.Away a)).FormallyUnramified :=
    RingHom.formallyUnramified_algebraMap.mpr h
  have hx := RingHom.FormallyUnramified.respectsIso.1
    (algebraMap R (Localization.Away a)) e.toRingEquiv hl
  rwa [he] at hx

end HodgeLean.Foundations.Program
