import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs

/-! Nonzero scalar changes of coherent local orientations. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

def scaledLocalOrientation (X : TopCat.{0}) (n : ℕ)
    (o : LocalRationalOrientation X n) (q : ℚ) (hq : q ≠ 0) :
    LocalRationalOrientation X n where
  generator x := q • o.generator x
  generates x := by
    let e := LinearEquiv.smulOfNeZero ℚ (orientationGroup X n x) q hq
    have he : (fun r : ℚ => r • (q • o.generator x)) =
        (fun r : ℚ => e (r • o.generator x)) := by
      funext r
      exact smul_comm r q (o.generator x)
    change Function.Bijective (fun r : ℚ => r • (q • o.generator x))
    rw [he]
    exact e.bijective.comp (o.generates x)
  vanishes := o.vanishes
  coherent x := by
    obtain ⟨U, hx, c, hc⟩ := o.coherent x
    refine ⟨U, hx, q • c, fun y hy => ?_⟩
    rw [map_smul, hc y hy]

#print axioms scaledLocalOrientation
end HodgeLean.Foundations.QuotientDuality
