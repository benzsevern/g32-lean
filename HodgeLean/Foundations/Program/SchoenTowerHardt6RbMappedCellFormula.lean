import HodgeLean.Foundations.Program.SchoenTowerHardt6RbActualImageFormula
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbHeightLiftGraph
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSectionCellFormula

/-! Endpoint, base and ambient graphs construct the actual Boolean formulas of mapped cells. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_mapped_cell_formula {n q : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n))) (U : s2v_t11b_Formula n) (hU : U.realize ⊆ A)
    (l u : U.realize → ℝ) (gl gu : s2v_t11b_Formula (n + 1))
    (hgl : ∀ z, z ∈ gl.realize ↔ ∃ x : U.realize,
      (∀ i, z i.succ = x.val i) ∧ z 0 = l x)
    (hgu : ∀ z, z ∈ gu.realize ↔ ∃ x : U.realize,
      (∀ i, z i.succ = x.val i) ∧ z 0 = u x)
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (G : s2v_t11b_Formula (n + q))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x ∈ A,
      (∀ i, z (Fin.castAdd q i) = x i) ∧ (∀ i, z (Fin.natAdd n i) = β x i))
    (e : EuclideanSpace ℝ (Fin (q + 1)) ≃ₜ EuclideanSpace ℝ (Fin (q + 1)))
    (J : s2v_t11b_Formula ((q + 1) + (q + 1)))
    (hJ : ∀ z, z ∈ J.realize ↔ ∃ x : EuclideanSpace ℝ (Fin (q + 1)),
      (∀ i, z (Fin.castAdd (q + 1) i) = x i) ∧
      (∀ i, z (Fin.natAdd (q + 1) i) = e x i))
    (graph : Bool) :
    ∃ c : s2v_t11b_Formula (q + 1),
      c.realize = e '' {z | ∃ x : U.realize, (∀ i, z i.succ = β x.val i) ∧
        (if graph then z 0 = l x else l x < z 0 ∧ z 0 < u x)} := by
  obtain ⟨V, hV⟩ := s2v_hardt6rb_section_cell_formula U l u gl gu hgl hgu graph
  obtain ⟨H, hH⟩ := s2v_hardt6rb_height_lift_graph A β G hG
  let T : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (q + 1)) :=
    fun x => WithLp.toLp 2 (Fin.cons (x 0)
      (fun i => β (WithLp.toLp 2 (fun j : Fin n => x j.succ)) i))
  let D := {x : EuclideanSpace ℝ (Fin (n + 1)) |
    WithLp.toLp 2 (fun j : Fin n => x j.succ) ∈ A}
  have hT : ∀ z, z ∈ H.realize ↔ ∃ x ∈ D,
      (∀ i, z (Fin.castAdd (q + 1) i) = x i) ∧
      (∀ i, z (Fin.natAdd (n + 1) i) = T x i) := by
    intro z
    rw [hH]
    constructor
    · rintro ⟨x, hx, hin, ht, hout⟩
      exact ⟨x, hx, hin, fun i => Fin.cases ht hout i⟩
    · rintro ⟨x, hx, hin, hout⟩
      exact ⟨x, hx, hin, hout 0, fun i => hout i.succ⟩
  have hVD : V.realize ⊆ D := by
    intro z hz
    obtain ⟨x, hx, ht⟩ := (hV z).mp hz
    have he : WithLp.toLp 2 (fun i : Fin n => z i.succ) = x.val := by
      ext i
      exact hx i
    change WithLp.toLp 2 (fun i : Fin n => z i.succ) ∈ A
    rw [he]
    exact hU x.property
  obtain ⟨W, hW⟩ := s2v_hardt6rb_actual_image_formula T D H hT V hVD
  have hWeq : W.realize = {z | ∃ x : U.realize, (∀ i, z i.succ = β x.val i) ∧
      (if graph then z 0 = l x else l x < z 0 ∧ z 0 < u x)} := by
    rw [hW]
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx, ht⟩ := (hV y).mp hy
      have he : WithLp.toLp 2 (fun i : Fin n => y i.succ) = x.val := by
        ext i
        exact hx i
      refine ⟨x, ?_, ht⟩
      intro i
      change β (WithLp.toLp 2 (fun j : Fin n => y j.succ)) i = β x.val i
      rw [he]
    · rintro ⟨x, hx, ht⟩
      let y : EuclideanSpace ℝ (Fin (n + 1)) :=
        WithLp.toLp 2 (Fin.cons (z 0) (fun i => x.val i))
      have he : WithLp.toLp 2 (fun i : Fin n => y i.succ) = x.val := by ext i; rfl
      refine ⟨y, (hV y).mpr ⟨x, fun _ => rfl, ht⟩, ?_⟩
      ext i
      refine Fin.cases rfl (fun j => ?_) i
      change β (WithLp.toLp 2 (fun i : Fin n => y i.succ)) j = z j.succ
      rw [he]
      exact (hx j).symm
  have hJ' : ∀ z, z ∈ J.realize ↔ ∃ x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin (q + 1)))),
      (∀ i, z (Fin.castAdd (q + 1) i) = x i) ∧
      (∀ i, z (Fin.natAdd (q + 1) i) = e x i) := by
    intro z
    simpa only [Set.mem_univ, true_and] using hJ z
  obtain ⟨c, hc⟩ := s2v_hardt6rb_actual_image_formula e Set.univ J hJ' W (Set.subset_univ _)
  exact ⟨c, hc.trans (congrArg (fun S => e '' S) hWeq)⟩

end HodgeLean.Foundations.Program
