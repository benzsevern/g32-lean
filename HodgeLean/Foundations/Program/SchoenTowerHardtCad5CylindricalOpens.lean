import HodgeLean.Foundations.Program.SchoenTowerT11bDefs

/-! Open cylindrical lifts over open Euclidean base cells. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_first_coordinate_homeomorph (n : ℕ) :
    ∃ e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ (ℝ × EuclideanSpace ℝ (Fin n)),
      (∀ y, e y = (y 0, WithLp.toLp 2 (fun i => y i.succ))) ∧
      (∀ t a, e.symm (t, a) = WithLp.toLp 2 (Fin.cons t (fun i => a i))) := by
  let e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ (ℝ × EuclideanSpace ℝ (Fin n)) :=
    { toFun := fun y => (y 0, WithLp.toLp 2 (fun i => y i.succ))
      invFun := fun p => WithLp.toLp 2 (Fin.cons p.1 (fun i => p.2 i))
      left_inv := by
        intro y
        ext i
        exact Fin.cases rfl (fun _ => rfl) i
      right_inv := by
        rintro ⟨t, a⟩
        apply Prod.ext
        · rfl
        · ext i; rfl
      continuous_toFun :=
        ((continuous_apply 0).comp (PiLp.continuous_ofLp 2 _)).prodMk
          ((PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i =>
            (continuous_apply i.succ).comp (PiLp.continuous_ofLp 2 _))))
      continuous_invFun := (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i =>
        Fin.cases continuous_fst (fun j =>
          (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp continuous_snd)) i)) }
  exact ⟨e, fun _ => rfl, fun _ _ => rfl⟩

theorem s2v_hardt_cad5_band_isOpen {n r : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsOpen C)
    (ψ : Fin r → C → ℝ) (hψ : ∀ j, Continuous (ψ j)) (i : Fin (r + 1)) :
    IsOpen {y : EuclideanSpace ℝ (Fin (n + 1)) | ∃ a : C,
      (∀ v, y v.succ = a.val v) ∧
      (∀ j : Fin r, j.val < i.val → ψ j a < y 0) ∧
      (∀ j : Fin r, i.val ≤ j.val → y 0 < ψ j a)} := by
  obtain ⟨e, he, hInv⟩ := s2v_hardt_cad5_first_coordinate_homeomorph n
  let ins : ℝ × C → EuclideanSpace ℝ (Fin (n + 1)) := fun p => e.symm (p.1, p.2.val)
  have hIns : IsOpenMap ins := e.symm.isOpenMap.comp
    (IsOpenMap.id.prodMap hC.isOpenMap_subtype_val)
  let W : Set (ℝ × C) := {p | (∀ j : Fin r, j.val < i.val → ψ j p.2 < p.1) ∧
      (∀ j : Fin r, i.val ≤ j.val → p.1 < ψ j p.2)}
  have hLo (j : Fin r) : IsOpen {p : ℝ × C | j.val < i.val → ψ j p.2 < p.1} := by
    by_cases hj : j.val < i.val
    · simpa only [hj, true_implies, Function.comp_apply] using isOpen_lt ((hψ j).comp continuous_snd) continuous_fst
    · simpa only [hj, false_implies, Set.ofPred_true] using (isOpen_univ : IsOpen (Set.univ : Set (ℝ × C)))
  have hHi (j : Fin r) : IsOpen {p : ℝ × C | i.val ≤ j.val → p.1 < ψ j p.2} := by
    by_cases hj : i.val ≤ j.val
    · simpa only [hj, true_implies, Function.comp_apply] using isOpen_lt continuous_fst ((hψ j).comp continuous_snd)
    · simpa only [hj, false_implies, Set.ofPred_true] using (isOpen_univ : IsOpen (Set.univ : Set (ℝ × C)))
  have hLow : IsOpen {p : ℝ × C | ∀ j : Fin r, j.val < i.val → ψ j p.2 < p.1} := by
    simpa only [Set.ofPred_forall] using isOpen_iInter_of_finite hLo
  have hHigh : IsOpen {p : ℝ × C | ∀ j : Fin r, i.val ≤ j.val → p.1 < ψ j p.2} := by
    simpa only [Set.ofPred_forall] using isOpen_iInter_of_finite hHi
  have hW : IsOpen W := hLow.inter hHigh
  have hImage : ins '' W = {y : EuclideanSpace ℝ (Fin (n + 1)) | ∃ a : C,
      (∀ v, y v.succ = a.val v) ∧
      (∀ j : Fin r, j.val < i.val → ψ j a < y 0) ∧
      (∀ j : Fin r, i.val ≤ j.val → y 0 < ψ j a)} := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.2, ?_, ?_, ?_⟩
      · intro v
        change (e.symm (p.1, p.2.val)) v.succ = p.2.val v
        rw [hInv]
        rfl
      · intro j hj
        change ψ j p.2 < (e.symm (p.1, p.2.val)) 0
        rw [hInv]
        exact hp.1 j hj
      · intro j hj
        change (e.symm (p.1, p.2.val)) 0 < ψ j p.2
        rw [hInv]
        exact hp.2 j hj
    · rintro ⟨a, ha, hlo, hhi⟩
      refine ⟨(y 0, a), ⟨hlo, hhi⟩, ?_⟩
      change e.symm (y 0, a.val) = y
      rw [hInv]
      ext v
      exact Fin.cases rfl (fun j => (ha j).symm) v
  rw [← hImage]
  exact hIns W hW

end HodgeLean.Foundations.Program
