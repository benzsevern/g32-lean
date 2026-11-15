import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedSupportSuspension

/-! # Original degree transports through actual support suspension
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual signed support suspension retains the original relative degree transport on source and target.
Source: properCycle_real_support_suspension_iso; AlgebraicTopology.Singular.relativeHomologyDegreeCast.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_suspension_degree_transport
    (Y : TopCat.{0}) (T : Set Y) (hT : IsClosed T) {i j : ℕ} (e : i = j)
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of (ℝ × Y))
      {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ) (i+1)) :
    relativeHomologyDegreeCast e
      ((properCycle_real_support_suspension_iso Y T hT i).hom.hom z) =
      (properCycle_real_support_suspension_iso Y T hT j).hom.hom
        (relativeHomologyDegreeCast (congrArg (fun k => k+1) e) z) := by
  subst j
  rfl

/-- The literal-degree composed suspension to zero is the general composed suspension through the original source degree equality.
Source: properCycle_real_support_suspension_degree_transport; properCycle_iterated_zero_support_suspension_iso.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_zero_support_degree_transport
    (Y : TopCat.{0}) (T : Set Y) (hT : IsClosed T) (n : ℕ)
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := properCycle_real_support_space Y n)
      (properCycle_real_point_support Y T n)ᶜ) (0+n)) :
    (properCycle_iterated_zero_support_suspension_iso Y T hT n).hom.hom
      (relativeHomologyDegreeCast (Nat.zero_add n) z) =
      (properCycle_iterated_support_suspension_iso Y T hT 0 n).hom.hom z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let X := properCycle_real_support_space Y n
    let U := properCycle_real_point_support Y T n
    let hU := properCycle_real_point_support_isClosed Y T hT n
    let sI := properCycle_real_support_suspension_iso X U hU (0+n)
    let sN := properCycle_real_support_suspension_iso X U hU n
    have hs := properCycle_real_support_suspension_degree_transport X U hU (Nat.zero_add n) z
    change relativeHomologyDegreeCast (Nat.zero_add n) (sI.hom.hom z) =
      sN.hom.hom (relativeHomologyDegreeCast (Nat.zero_add (n+1)) z) at hs
    change (properCycle_iterated_zero_support_suspension_iso Y T hT n).hom.hom
      (sN.hom.hom (relativeHomologyDegreeCast (Nat.zero_add (n+1)) z)) =
      (properCycle_iterated_support_suspension_iso Y T hT 0 n).hom.hom (sI.hom.hom z)
    rw [← hs]
    exact ih (sI.hom.hom z)

end HodgeLean.Foundations.QuotientDuality
