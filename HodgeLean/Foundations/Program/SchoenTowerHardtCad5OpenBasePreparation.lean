import HodgeLean.Foundations.Program.SchoenTowerHardtCad5ConnectedCells
import HodgeLean.Foundations.Program.SchoenTowerHardtCad3

/-! Root preparation retaining openness of full-dimensional induction cells. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_prepare_open_base {n k b : ℕ}
    (ih : ∀ {h : ℕ} (B : Fin h → s2v_t11b_Formula n),
      ∃ Q : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin n))),
        (∀ i j, (Q.cell i).realize ⊆ (B j).realize ∨ Disjoint (Q.cell i).realize (B j).realize) ∧
        (∀ i, Q.dim i = n → IsOpen (Q.cell i).realize))
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (C : Fin b → s2v_t11b_Formula n) (hcover : (⋃ j, (C j).realize) = Set.univ)
    (r : Fin b → ℕ) (ψ : (j : Fin b) → Fin (r j) → (C j).realize → ℝ)
    (hψ : ∀ j l, Continuous (ψ j l)) (hm : ∀ j a, StrictMono (fun l => ψ j l a))
    (g : (j : Fin b) → Fin (r j) → s2v_t11b_Formula (n + 1))
    (hg : ∀ j l y, y ∈ (g j l).realize ↔ ∃ a : (C j).realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ j l a)
    (hz : ∀ j p, (∀ a : (C j).realize, (P p).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
      (∀ a : (C j).realize, (P p).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0))
    (hr : ∀ j a t, (∃ p, (P p).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
      (P p).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔ ∃ l, t = ψ j l a) :
    ∃ Q : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin n))),
    ∃ R : Fin Q.count → ℕ, ∃ roots : (i : Fin Q.count) → Fin (R i) → (Q.cell i).realize → ℝ,
      (∀ i, Q.dim i = n → IsOpen (Q.cell i).realize) ∧
      (∀ i, IsConnected (Q.cell i).realize) ∧
      (∀ i l, Continuous (roots i l)) ∧
      (∀ i a, StrictMono (fun l => roots i l a)) ∧
      (∀ i a t, (∃ p, (P p).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
        (P p).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔ ∃ l, t = roots i l a) ∧
      (∀ i p, (∀ a : (Q.cell i).realize, (P p).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
        (∀ a : (Q.cell i).realize, (P p).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0)) ∧
      (∀ i l p, (∀ a : (Q.cell i).realize,
          (P p).eval₂ (MvPolynomial.eval (fun v => a.val v)) (roots i l a) < 0) ∨
        (∀ a : (Q.cell i).realize,
          (P p).eval₂ (MvPolynomial.eval (fun v => a.val v)) (roots i l a) = 0) ∨
        (∀ a : (Q.cell i).realize,
          0 < (P p).eval₂ (MvPolynomial.eval (fun v => a.val v)) (roots i l a))) := by
  classical
  choose s D hDn hDd hDu hDs using fun j =>
    s2v_hardt_cad3_section_sign_refinement (C j) (ψ j) (hm j) (g j) (hg j) P
  let T := Fin b ⊕ ((j : Fin b) × Fin (s j))
  let enum := (Fintype.equivFin T).symm
  let marks : Fin (Fintype.card T) → s2v_t11b_Formula n := fun t =>
    match enum t with
    | .inl j => C j
    | .inr jl => D jl.1 jl.2
  obtain ⟨Q, ha, hopen⟩ := ih marks
  have haC (i : Fin Q.count) (j : Fin b) :
      (Q.cell i).realize ⊆ (C j).realize ∨ Disjoint (Q.cell i).realize (C j).realize := by
    simpa only [marks, enum, Equiv.symm_apply_apply] using ha i ((Fintype.equivFin T) (.inl j))
  have haD (i : Fin Q.count) (j : Fin b) (l : Fin (s j)) :
      (Q.cell i).realize ⊆ (D j l).realize ∨ Disjoint (Q.cell i).realize (D j l).realize := by
    simpa only [marks, enum, Equiv.symm_apply_apply] using ha i ((Fintype.equivFin T) (.inr ⟨j, l⟩))
  have parentExists (i : Fin Q.count) : ∃ j, (Q.cell i).realize ⊆ (C j).realize := by
    obtain ⟨x, hx⟩ := Q.nonempty i
    have hc : x ∈ ⋃ j, (C j).realize := by rw [hcover]; exact Set.mem_univ x
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hc
    rcases haC i j with h | h
    · exact ⟨j, h⟩
    · exact (Set.disjoint_left.mp h hx hj).elim
  choose parent hp using parentExists
  let into (i : Fin Q.count) (a : (Q.cell i).realize) : (C (parent i)).realize :=
    ⟨a.val, hp i a.property⟩
  let roots (i : Fin Q.count) (l : Fin (r (parent i))) (a : (Q.cell i).realize) :=
    ψ (parent i) l (into i a)
  refine ⟨Q, fun i => r (parent i), roots, hopen, s2v_hardt_cad5_cell_connected Q,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i l
    exact (hψ (parent i) l).comp (continuous_subtype_val.subtype_mk _)
  · intro i a
    exact hm (parent i) (into i a)
  · intro i a t
    exact hr (parent i) (into i a) t
  · intro i p
    exact (hz (parent i) p).imp (fun h a => h (into i a)) (fun h a => h (into i a))
  · intro i l p
    obtain ⟨x, hx⟩ := Q.nonempty i
    have hxC := hp i hx
    have hxD : x ∈ ⋃ j, (D (parent i) j).realize := by rw [hDu]; exact hxC
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxD
    have hsub : (Q.cell i).realize ⊆ (D (parent i) j).realize := by
      rcases haD i (parent i) j with h | h
      · exact h
      · exact (Set.disjoint_left.mp h hx hj).elim
    rcases hDs (parent i) j l p with h | h | h
    · exact Or.inl (fun a => h (into i a) (hsub a.property))
    · exact Or.inr (Or.inl (fun a => h (into i a) (hsub a.property)))
    · exact Or.inr (Or.inr (fun a => h (into i a) (hsub a.property)))

end HodgeLean.Foundations.Program
