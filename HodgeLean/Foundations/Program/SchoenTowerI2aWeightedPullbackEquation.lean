import HodgeLean.Foundations.Program.SchoenTowerI2aWeightedEquationRescaling
import HodgeLean.Foundations.Program.SchoenTowerI2aWeightedTransformGerm
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorStalkPullback

/-! Actual weighted pullback equations after rational rescaling.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A rational equation on the original base and the weighted ideal transform give a unit-weighted strict equation in the actual source stalk, preserving the generated field. -/
theorem s2v_i2a_weighted_pullback_equation
    {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (κX : X.functionField ⟶ CommRingCat.of K)
    (κY : Y.functionField ⟶ CommRingCat.of K)
    (hsq : Spec.map κX ≫ X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map κY ≫ Y.fromSpecStalk (genericPoint Y))
    (x : X) {J : Type} [Fintype J] (I : J → Y.IdealSheafData)
    (D : J → X.IdealSheafData) (E : X.IdealSheafData) (n : J → ℕ) (m : ℕ)
    (htransform : (∏ j, (I j) ^ n j).comap f = (∏ j, (D j) ^ n j) * E ^ m)
    (U : X.affineOpens) (V : Y.affineOpens) (hxU : x ∈ U.1) (hxV : f x ∈ V.1)
    (g : J → Γ(Y, V)) (z : J → Γ(X, U))
    (hg : ∀ j, (I j).ideal V = Ideal.span {g j})
    (hz : ∀ j, (D j).ideal U = Ideal.span {z j})
    (e : X.presheaf.stalk x) (he_ne : e ≠ 0)
    (he : (E.ideal U).map (X.presheaf.germ U.1 x hxU).hom = Ideal.span {e})
    (ε : (Y.presheaf.stalk (f x))ˣ) (A B : Y.presheaf.stalk (f x))
    (hA : A ≠ 0) (hB : B ≠ 0) (t : K)
    (heq : let ρ := s2v_l1b_kval_stalkMap Y (f x) κY
      t ^ m * (ρ B) ^ m = ρ (ε : Y.presheaf.stalk (f x)) *
        (∏ j, ρ ((Y.presheaf.germ V.1 (f x) hxV).hom (g j)) ^ n j) * (ρ A) ^ m)
    (hgen : Subfield.closure (Set.range (s2v_l1b_kval_stalkMap X x κX) ∪ {t}) = ⊤) :
    ∃ (w : K) (δ : (X.presheaf.stalk x)ˣ),
      Subfield.closure (Set.range (s2v_l1b_kval_stalkMap X x κX) ∪ {w}) = ⊤ ∧
      w ^ m = s2v_l1b_kval_stalkMap X x κX δ *
        ∏ j, s2v_l1b_kval_stalkMap X x κX
          ((X.presheaf.germ U.1 x hxU).hom (z j)) ^ n j := by
  let ρ := s2v_l1b_kval_stalkMap X x κX
  let φ := (f.stalkMap x).hom
  let F : J → X.presheaf.stalk x := fun j =>
    φ ((Y.presheaf.germ V.1 (f x) hxV).hom (g j))
  let G : J → X.presheaf.stalk x := fun j => (X.presheaf.germ U.1 x hxU).hom (z j)
  have hρ : Function.Injective ρ := κX.hom.injective.comp (IsFractionRing.injective _ _)
  have hcomp : ρ.comp φ = s2v_l1b_kval_stalkMap Y (f x) κY :=
    s2v_l1b_divisor_stalk_pullback f κX κY hsq x
  have hpoint (v : Y.presheaf.stalk (f x)) : ρ (φ v) =
      s2v_l1b_kval_stalkMap Y (f x) κY v := DFunLike.congr_fun hcomp v
  have hne (v : Y.presheaf.stalk (f x)) (hv : v ≠ 0) : ρ (φ v) ≠ 0 := by
    rw [hpoint]
    intro h
    exact hv ((κY.hom.injective.comp (IsFractionRing.injective _ _))
      (h.trans (map_zero (s2v_l1b_kval_stalkMap Y (f x) κY)).symm))
  apply s2v_i2a_weighted_equation_rescaling ρ F G n e (φ A) (φ B) m
    (by simpa only [map_zero] using hρ.ne he_ne) (hne A hA) (hne B hB)
    (s2v_i2a_weighted_transform_germ f I D E n m htransform x U V hxU hxV
      g z hg hz e he) (Units.map φ ε) t _ hgen
  change t ^ m * ρ (φ B) ^ m =
    ρ (φ (ε : Y.presheaf.stalk (f x))) * (∏ j, ρ (F j) ^ n j) * ρ (φ A) ^ m
  simpa only [F, hpoint] using heq

end HodgeLean.Foundations.Program
