import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSectionBandFormula

/-! Actual Boolean graphs of band rescaling maps from their endpoint graphs. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ambient_band_graph {n N : ℕ}
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
    (idx outIdx : Fin n → Fin N) (iy iv : Fin N) :
    ∃ G : s2v_t11b_Formula N, ∀ z, z ∈ G.realize ↔ ∃ p : C,
      (∀ i, z (idx i) = p.val.1 i) ∧ z iy = p.val.2 ∧
      (∀ i, z (outIdx i) = (h p).val.1 i) ∧ z iv = (h p).val.2 := by
  obtain ⟨R, hR₀⟩ := s2v_hardt6rb_section_band_relation F
    (fun i x => (![l, u, c, d] i) x.val) g hg idx iy iv
  have hR : ∀ z, z ∈ R.realize ↔ ∃ x : F.realize, (∀ i, z (idx i) = x.val i) ∧
      l x.val ≤ z iy ∧ z iy ≤ u x.val ∧ c x.val ≤ z iv ∧ z iv ≤ d x.val ∧
      (z iy - l x.val) * (d x.val - c x.val) = (z iv - c x.val) * (u x.val - l x.val) := by
    intro z
    exact hR₀ z
  let P : Fin n → MvPolynomial (Fin N) ℝ := fun i =>
    .X (outIdx i) - .X (idx i)
  obtain ⟨B, hBraw⟩ := s2v_hardt_cad3_finite_inter
    (fun i => s2v_t11b_Formula.inter (.nonneg (P i)) (.nonneg (-P i)))
  have hB : ∀ z, z ∈ B.realize ↔ ∀ i, z (outIdx i) = z (idx i) := by
    intro z
    rw [hBraw]
    simp only [s2v_t11b_Formula.realize, Set.mem_inter_iff, Set.mem_setOf_eq,
      P, map_neg, map_sub, MvPolynomial.eval_X]
    constructor
    · intro hz i
      have hi := hz i
      linarith
    · intro hz i
      rw [hz i]
      exact ⟨by simp, by simp⟩
  refine ⟨.inter R B, ?_⟩
  intro z
  change (z ∈ R.realize ∧ z ∈ B.realize) ↔ _
  rw [hR, hB]
  constructor
  · rintro ⟨⟨x, hx, hylo, hyhi, hvlo, hvhi, hrel⟩, hout⟩
    let p : C := ⟨(x.val, z iy), by rw [hC]; exact ⟨x.property, hylo, hyhi⟩⟩
    let q : {p : EuclideanSpace ℝ (Fin n) × ℝ |
        p.1 ∈ F.realize ∧ c p.1 ≤ p.2 ∧ p.2 ≤ d p.1} :=
      ⟨(x.val, z iv), x.property, hvlo, hvhi⟩
    have he : h p = q := (hh p q).mpr ⟨rfl, hrel⟩
    refine ⟨p, hx, rfl, ?_, ?_⟩
    · intro i
      rw [he]
      exact (hout i).trans (hx i)
    · rw [he]
  · rintro ⟨p, hx, hy, hout, hv⟩
    have hps : p.val.1 ∈ F.realize ∧ l p.val.1 ≤ p.val.2 ∧ p.val.2 ≤ u p.val.1 :=
      (Set.ext_iff.mp hC p.val).mp p.property
    have hbase := ((hh p (h p)).mp rfl).1
    have hrel := ((hh p (h p)).mp rfl).2
    refine ⟨⟨⟨p.val.1, hps.1⟩, hx, ?_⟩, ?_⟩
    · rw [hy, hv]
      refine ⟨hps.2.1, hps.2.2, ?_, ?_, hrel⟩
      · change c p.val.1 ≤ (h p).val.2
        rw [hbase]
        exact (h p).property.2.1
      · change (h p).val.2 ≤ d p.val.1
        rw [hbase]
        exact (h p).property.2.2
    · intro i
      exact (hout i).trans ((congrArg (fun x => x i) hbase).symm.trans (hx i).symm)

end HodgeLean.Foundations.Program
