import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIdealGerm
import HodgeLean.Foundations.Program.SchoenTowerL1bPullbackProducts

/-! Weighted transform identities in the actual chart stalk.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A weighted ideal-sheaf transform gives the corresponding principal ideal identity in the actual stalk, using the supplied equations on both charts. -/
theorem s2v_i2a_weighted_transform_germ
    {X Y : Scheme} (f : X ⟶ Y) {J : Type*} [Fintype J]
    (I : J → Y.IdealSheafData) (D : J → X.IdealSheafData)
    (E : X.IdealSheafData) (n : J → ℕ) (m : ℕ)
    (htransform : (∏ j, (I j) ^ n j).comap f = (∏ j, (D j) ^ n j) * E ^ m)
    (x : X) (U : X.affineOpens) (V : Y.affineOpens)
    (hxU : x ∈ U.1) (hxV : f x ∈ V.1)
    (g : J → Γ(Y, V)) (z : J → Γ(X, U))
    (hg : ∀ j, (I j).ideal V = Ideal.span {g j})
    (hz : ∀ j, (D j).ideal U = Ideal.span {z j})
    (e : X.presheaf.stalk x)
    (he : (E.ideal U).map (X.presheaf.germ U.1 x hxU).hom = Ideal.span {e}) :
    (∏ j, Ideal.span {((f.stalkMap x).hom ((Y.presheaf.germ V.1 (f x) hxV).hom (g j)))} ^ n j) =
      (∏ j, Ideal.span {(X.presheaf.germ U.1 x hxU).hom (z j)} ^ n j) *
        Ideal.span {e} ^ m := by
  classical
  let germ : X.IdealSheafData →* Ideal (X.presheaf.stalk x) :=
    { toFun := fun Q => (Q.ideal U).map (X.presheaf.germ U.1 x hxU).hom
      map_one' := by
        simp only [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.ideal_top,
          Pi.top_apply, Ideal.map_top, Ideal.one_eq_top]
      map_mul' := fun Q R => Ideal.map_mul _ _ _ }
  have H := congrArg germ htransform
  rw [s2v_l1b_comap_prod] at H
  simp only [map_mul, map_pow, map_prod, s2v_l1b_comap_pow] at H
  have hsource (j : J) : germ ((I j).comap f) =
      Ideal.span {((f.stalkMap x).hom ((Y.presheaf.germ V.1 (f x) hxV).hom (g j)))} := by
    change (((I j).comap f).ideal U).map (X.presheaf.germ U.1 x hxU).hom = _
    rw [s2v_l1b_divisor_comap_ideal_germ f (I j) x V U hxV hxU,
      hg j, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  have htarget (j : J) : germ (D j) =
      Ideal.span {(X.presheaf.germ U.1 x hxU).hom (z j)} := by
    change ((D j).ideal U).map (X.presheaf.germ U.1 x hxU).hom = _
    rw [hz j, Ideal.map_span, Set.image_singleton]
  simpa only [hsource, htarget, show germ E = Ideal.span {e} from he] using H

end HodgeLean.Foundations.Program
