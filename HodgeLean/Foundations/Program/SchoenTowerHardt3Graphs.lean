import HodgeLean.Foundations.Program.SchoenTowerHardt3RootFormula
import Mathlib.Order.Hom.Set

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Ordered full root enumerations have Boolean graphs, without an additional regularity premise.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, cylindrical sections, pp. 6–7. -/
theorem s2v_hardt3_enumeration_graph {n r : ℕ}
    (c : s2v_t11b_Formula n) (R : s2v_t11b_Formula (n + 1))
    (ψ : Fin r → c.realize → ℝ)
    (hmono : ∀ a, StrictMono (fun v => ψ v a))
    (hroots : ∀ a : c.realize, ∀ x : ℝ,
      WithLp.toLp 2 (Fin.cons x (fun j => a.val j)) ∈ R.realize ↔ ∃ v, x = ψ v a)
    (v : Fin r) :
    ∃ g : s2v_t11b_Formula (n + 1), ∀ a : EuclideanSpace ℝ (Fin n), ∀ x : ℝ,
      WithLp.toLp 2 (Fin.cons x (fun j => a j)) ∈ g.realize ↔
        ∃ ha : a ∈ c.realize, x = ψ v ⟨a, ha⟩ := by
  classical
  let b := s2v_hardt2_boundIndex (n + 1) r
  let u := s2v_hardt2_freeIndex (n + 1) r
  let root := fun i : Fin r => s2v_hardt1_rename
    (Fin.cases (b i) (fun j => u j.succ)) R
  let order := fun ij : Fin r × Fin r =>
    if ij.1 < ij.2 then s2v_t11b_Formula.compl (.nonneg
      (MvPolynomial.X (b ij.1) - MvPolynomial.X (b ij.2))) else .nonneg 0
  let roots := s2v_t11b_Formula.conjunction (Finset.univ.toList.map root)
  let orders := s2v_t11b_Formula.conjunction (Finset.univ.toList.map order)
  let p : MvPolynomial (Fin ((n + 1) + r)) ℝ :=
    MvPolynomial.X (u 0) - MvPolynomial.X (b v)
  let F := s2v_t11b_Formula.inter
    (s2v_hardt1_rename (fun j => u j.succ) c)
    (.inter roots (.inter orders (.inter (.nonneg p) (.nonneg (-p)))))
  have hF (y : Fin r → ℝ) (a : EuclideanSpace ℝ (Fin n)) (x : ℝ) :
      s2v_hardt2_insert r y (WithLp.toLp 2 (Fin.cons x (fun j => a j))) ∈ F.realize ↔
      a ∈ c.realize ∧ (∀ i, WithLp.toLp 2 (Fin.cons (y i) (fun j => a j)) ∈ R.realize) ∧
        StrictMono y ∧ x = y v := by
    let z := s2v_hardt2_insert r y (WithLp.toLp 2 (Fin.cons x (fun j => a j)))
    have hu (i : Fin (n + 1)) : z (u i) = (Fin.cons x (fun j : Fin n => a j) : Fin (n + 1) → ℝ) i := by
      simpa only [z, u] using s2v_hardt2_insert_free y (WithLp.toLp 2 (Fin.cons x (fun j => a j))) i
    have hb (i : Fin r) : z (b i) = y i := s2v_hardt2_insert_bound y (WithLp.toLp 2 (Fin.cons x (fun j => a j))) i
    have hc : WithLp.toLp 2 (fun j => z (u j.succ)) = a := by ext j; exact hu j.succ
    have hr (i : Fin r) : WithLp.toLp 2
        (fun j => z (Fin.cases (b i) (fun j => u j.succ) j)) =
        WithLp.toLp 2 (Fin.cons (y i) (fun j => a j)) := by
      ext j
      refine Fin.cases (hb i) (fun j => hu j.succ) j
    change (_ ∈ (s2v_hardt1_rename _ c).realize ∧ _) ↔ _
    rw [s2v_hardt1_realize_rename, hc]
    simp only [roots, orders, s2v_t11b_Formula.realize, Set.mem_inter_iff,
      s2v_t11b_realize_conjunction, List.forall_mem_map, Finset.mem_toList,
      Finset.mem_univ, forall_true_left]
    have hr' : (∀ i, z ∈ (root i).realize) ↔
        ∀ i, WithLp.toLp 2 (Fin.cons (y i) (fun j => a j)) ∈ R.realize := by
      apply forall_congr'; intro i
      rw [s2v_hardt1_realize_rename, hr]
    have ho : (∀ ij, z ∈ (order ij).realize) ↔ StrictMono y := by
      constructor
      · intro h i j hij
        have hh := h (i, j)
        simpa [order, hij, s2v_t11b_Formula.realize, hb, sub_neg] using hh
      · intro h ij
        by_cases hij : ij.1 < ij.2
        · simpa [order, hij, s2v_t11b_Formula.realize, hb, sub_neg] using h hij
        · simp [order, hij, s2v_t11b_Formula.realize]
    rw [hr', ho]
    simp only [p, Set.mem_setOf_eq, map_sub, map_neg, MvPolynomial.eval_X, u, b, s2v_hardt2_insert_free, s2v_hardt2_insert_bound,
      Fin.cons_zero, neg_nonneg]
    constructor
    · rintro ⟨ha, hr, hm, hle, hge⟩
      exact ⟨ha, hr, hm, by linarith⟩
    · rintro ⟨ha, hr, hm, he⟩
      exact ⟨ha, hr, hm, by linarith, by linarith⟩
  obtain ⟨g, hg⟩ := s2v_hardt2_repeated_projection F
  refine ⟨g, ?_⟩
  intro a x
  rw [hg]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨ha, hyr, hym, hxy⟩ := (hF y a x).mp hy
    choose j hj using fun i => (hroots ⟨a, ha⟩ (y i)).mp (hyr i)
    have hjmono : StrictMono j := by
      intro i l hil
      exact (hmono ⟨a, ha⟩).lt_iff_lt.mp (by rw [← hj i, ← hj l]; exact hym hil)
    have hsurj := Finite.surjective_of_injective hjmono.injective
    have he : y = fun i => ψ i ⟨a, ha⟩ := by
      apply hym.eq_of_range_eq (hmono ⟨a, ha⟩)
      ext t
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨j i, (hj i).symm⟩
      · rintro ⟨i, rfl⟩
        obtain ⟨l, hl⟩ := hsurj i
        exact ⟨l, (hj l).trans (congrArg (fun i => ψ i ⟨a, ha⟩) hl)⟩
    exact ⟨ha, hxy.trans (congrFun he v)⟩
  · rintro ⟨ha, hx⟩
    refine ⟨fun i => ψ i ⟨a, ha⟩, (hF _ a x).mpr ⟨ha, ?_, hmono _, hx⟩⟩
    intro i
    exact (hroots ⟨a, ha⟩ _).mpr ⟨i, rfl⟩

#print axioms s2v_hardt3_enumeration_graph
end HodgeLean.Foundations.Program
