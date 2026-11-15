import HodgeLean.Foundations.Program.SchoenTowerHardtCad3FormulaTools

/-! Actual Boolean graphs of finite tuples of supplied CAD root sections. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_section_tuple_formula {n q r : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ j y, y ∈ (g j).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ j a)
    (f : Fin q → Fin r) :
    ∃ H : s2v_t11b_Formula (q + n),
      ∀ (t : EuclideanSpace ℝ (Fin q)) (a : EuclideanSpace ℝ (Fin n)),
        WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a i)) ∈ H.realize ↔
          ∃ ha : a ∈ C.realize, ∀ i, t i = ψ (f i) ⟨a, ha⟩ := by
  let ρ (i : Fin q) : Fin (n + 1) → Fin (q + n) :=
    Fin.cases (i.castAdd n) (fun v => v.natAdd q)
  obtain ⟨H₀, hH₀⟩ := s2v_hardt_cad3_finite_inter
    (fun i : Fin q => s2v_hardt1_rename (ρ i) (g (f i)))
  refine ⟨.inter (s2v_hardt1_rename (Fin.natAdd q) C) H₀, ?_⟩
  intro t a
  change (_ ∧ _) ↔ _
  rw [s2v_hardt1_realize_rename, hH₀]
  have hbase : WithLp.toLp 2 (fun i =>
      Fin.append (fun j => t j) (fun j => a j) (Fin.natAdd q i)) = a := by
    ext i
    simp only [Fin.append_right]
  rw [hbase]
  have hcoords (i : Fin q) : WithLp.toLp 2 (fun v =>
      Fin.append (fun j => t j) (fun j => a j) (ρ i v)) =
        WithLp.toLp 2 (Fin.cons (t i) (fun v => a v)) := by
    ext v
    refine Fin.cases ?_ (fun j => ?_) v <;> simp [ρ]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    intro i
    have hi := h i
    rw [s2v_hardt1_realize_rename, hcoords, hg] at hi
    obtain ⟨b, hb, ht⟩ := hi
    have hba : b = (⟨a, ha⟩ : C.realize) := by
      apply Subtype.ext
      ext v
      exact (hb v).symm
    simpa only [hba, Fin.cons_zero] using ht
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    intro i
    rw [s2v_hardt1_realize_rename, hcoords, hg]
    exact ⟨⟨a, ha⟩, fun _ => rfl, h i⟩

end HodgeLean.Foundations.Program
