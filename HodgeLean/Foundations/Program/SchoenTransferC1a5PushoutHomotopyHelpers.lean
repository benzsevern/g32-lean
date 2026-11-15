import HodgeLean.Foundations.Program.SchoenTransferC1a5PushoutTopologyHelpers
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.TopCat.Basic

/-! Continuous homotopy gluing for actual attachment pushouts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- Compatible homotopies on the two pieces glue to a homotopy on the attachment pushout.
Source: Hatcher §2.1, homotopy gluing; Mathlib ContinuousMap.curry and ContinuousMap.uncurry. -/
def c1a5_pushout_homotopy {A B C D Z : TopCat.{0}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t l r b) {f g : D ⟶ Z}
    (HB : TopCat.Homotopy (r ≫ f) (r ≫ g))
    (HC : TopCat.Homotopy (b ≫ f) (b ≫ g))
    (hcompat : ∀ (s : unitInterval) (a : A), HB (s, t a) = HC (s, l a)) :
    TopCat.Homotopy f g := by
  let hB : B ⟶ TopCat.of C(unitInterval, Z) := TopCat.ofHom
    (ContinuousMap.curry ⟨fun p : B × unitInterval ↦ HB (p.2, p.1),
      HB.continuous.comp continuous_swap⟩)
  let hC : C ⟶ TopCat.of C(unitInterval, Z) := TopCat.ofHom
    (ContinuousMap.curry ⟨fun p : C × unitInterval ↦ HC (p.2, p.1),
      HC.continuous.comp continuous_swap⟩)
  have hw : t ≫ hB = l ≫ hC := by
    ext a s
    exact hcompat s a
  let hD : D ⟶ TopCat.of C(unitInterval, Z) := sq.desc hB hC hw
  have hleft (x : B) (s : unitInterval) : hD (r x) s = HB (s, x) :=
    congrArg (fun q : C(unitInterval, Z) ↦ q s)
      (ConcreteCategory.congr_hom (sq.inl_desc hB hC hw) x)
  have hright (x : C) (s : unitInterval) : hD (b x) s = HC (s, x) :=
    congrArg (fun q : C(unitInterval, Z) ↦ q s)
      (ConcreteCategory.congr_hom (sq.inr_desc hB hC hw) x)
  refine
    { toFun := fun q ↦ hD q.2 q.1
      continuous_toFun := (ContinuousMap.uncurry hD.hom).continuous.comp continuous_swap
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro x
    obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) x
    · exact (hleft x 0).trans (HB.map_zero_left x)
    · exact (hright x 0).trans (HC.map_zero_left x)
  · intro x
    obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) x
    · exact (hleft x 1).trans (HB.map_one_left x)
    · exact (hright x 1).trans (HC.map_one_left x)

example := @c1a5_pushout_homotopy

end HodgeLean.Foundations.Program
