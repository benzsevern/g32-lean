import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismCoordinates
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-! Projection is injective on the graph lift of one independent base simplex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_graph_simplex_fiber {E : Type*}
    [AddCommGroup E] [Module ℝ E] (s : Finset E)
    (hs : AffineIndependent ℝ (fun i : s => i.val)) (a : E → ℝ)
    (p q : E × ℝ)
    (hp : p ∈ convexHull ℝ (Set.range (fun i : s => (i.val, a i.val))))
    (hq : q ∈ convexHull ℝ (Set.range (fun i : s => (i.val, a i.val))))
    (hpq : p.1 = q.1) : p = q := by
  obtain ⟨w, hw⟩ := (s2v_hardt6rb_convexHull_range_weights _ p).mp hp
  obtain ⟨v, hv⟩ := (s2v_hardt6rb_convexHull_range_weights _ q).mp hq
  have hwb := congrArg Prod.fst hw
  have hvb := congrArg Prod.fst hv
  have hwh := congrArg Prod.snd hw
  have hvh := congrArg Prod.snd hv
  simp only [Prod.fst_sum] at hwb hvb
  simp only [Prod.snd_sum] at hwh hvh
  change (∑ i, w.val i • i.val) = p.1 at hwb
  change (∑ i, v.val i • i.val) = q.1 at hvb
  change (∑ i, w.val i * a i.val) = p.2 at hwh
  change (∑ i, v.val i * a i.val) = q.2 at hvh
  have he : w.val = v.val := by
    funext i
    exact hs.eq_of_sum_eq_sum (w.property.2.trans v.property.2.symm)
      (hwb.trans (hpq.trans hvb.symm)) i (Finset.mem_univ i)
  exact Prod.ext hpq (hwh.symm.trans (he ▸ hvh))

end HodgeLean.Foundations.Program
