import HodgeLean.Foundations.Program.SchoenTransferQ3CartesianSlices

/-! Actual stalk maps of a cartesian scheme square. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s4_q3_closed_pullback_stalk_square
    {W Z C : Scheme} (t : W ⟶ Z) (i : C ⟶ Z) [IsClosedImmersion i]
    (d : (pullback t i : Scheme)) :
    let e := Z.presheaf.stalkCongr (Inseparable.of_eq
      (congrArg (fun k : pullback t i ⟶ Z => k d) (pullback.condition (f := t) (g := i))))
    t.stalkMap (pullback.fst t i d) ≫ (pullback.fst t i).stalkMap d =
      e.hom ≫ i.stalkMap (pullback.snd t i d) ≫ (pullback.snd t i).stalkMap d := by
  dsimp only
  rw [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp]
  exact Scheme.Hom.stalkMap_congr_hom _ _ (pullback.condition (f := t) (g := i)) d

theorem s4_q3_factor_fromSpecStalk_at_closedPoint
    {X : Scheme} (R : CommRingCat) [IsLocalRing R]
    (k : Spec R ⟶ X) (x : X) (hx : k (IsLocalRing.closedPoint R) = x) :
    ∃ r : X.presheaf.stalk x ⟶ R,
      Spec.map r ≫ X.fromSpecStalk x = k := by
  subst x
  exact ⟨Scheme.stalkClosedPointTo k, Scheme.Spec_stalkClosedPointTo_fromSpecStalk k⟩

end HodgeLean.Foundations.Program
