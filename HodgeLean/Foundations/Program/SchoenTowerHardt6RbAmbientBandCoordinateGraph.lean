import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAmbientBandGraph
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandCoordinates

/-! Endpoint formulas give actual model graphs in full successor-dimensional coordinate blocks. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ambient_band_coordinate_graph {n N : ℕ}
    (F : s2v_t11b_Formula n) (l u c d : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin 4 → s2v_t11b_Formula (n + 1))
    (hg : ∀ i z, z ∈ (g i).realize ↔ ∃ x : F.realize,
      (∀ v, z v.succ = x.val v) ∧ z 0 = (![l, u, c, d] i) x.val)
    (C : Set (EuclideanSpace ℝ (Fin n) × ℝ))
    (hC : C = {p | p.1 ∈ F.realize ∧ l p.1 ≤ p.2 ∧ p.2 ≤ u p.1})
    (h : C ≃ₜ {p : EuclideanSpace ℝ (Fin n) × ℝ |
      p.1 ∈ F.realize ∧ c p.1 ≤ p.2 ∧ p.2 ≤ d p.1})
    (hh : ∀ p q, h p = q ↔ p.val.1 = q.val.1 ∧
      (p.val.2 - l p.val.1) * (d p.val.1 - c p.val.1) =
        (q.val.2 - c p.val.1) * (u p.val.1 - l p.val.1))
    (e : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (he0 : ∀ p, e p 0 = p.2) (hes : ∀ p i, e p i.succ = p.1 i)
    (idx outIdx : Fin (n + 1) → Fin N) :
    ∃ G : s2v_t11b_Formula N, ∀ z, z ∈ G.realize ↔ ∃ p : C,
      (∀ i, z (idx i) = e p.val i) ∧ (∀ i, z (outIdx i) = e (h p).val i) := by
  obtain ⟨G, hG⟩ := s2v_hardt6rb_ambient_band_graph F l u c d g hg C hC h hh
    (fun i => idx i.succ) (fun i => outIdx i.succ) (idx 0) (outIdx 0)
  have hcoord (j : Fin (n + 1) → Fin N) (z : EuclideanSpace ℝ (Fin N))
      (p : EuclideanSpace ℝ (Fin n) × ℝ) :
      (∀ i, z (j i) = e p i) ↔ (∀ i, z (j i.succ) = p.1 i) ∧ z (j 0) = p.2 := by
    constructor
    · intro hz
      exact ⟨fun i => (hz i.succ).trans (hes p i), (hz 0).trans (he0 p)⟩
    · rintro ⟨hb, ht⟩ i
      exact Fin.cases (ht.trans (he0 p).symm) (fun a => (hb a).trans (hes p a).symm) i
  refine ⟨G, ?_⟩
  intro z
  rw [hG]
  apply exists_congr
  intro p
  rw [hcoord, hcoord]
  exact and_assoc.symm

end HodgeLean.Foundations.Program
