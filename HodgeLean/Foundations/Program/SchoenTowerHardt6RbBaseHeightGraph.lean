import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Relations

/-! Actual base-map relations with an unchanged height coordinate. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_base_height_graph {n q N : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n))) (B : Set (EuclideanSpace ℝ (Fin q)))
    (k : A → B) (G : s2v_t11b_Formula (n + q))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : A,
      (∀ i, z (Fin.castAdd q i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (k x).val i))
    (idx : Fin n → Fin N) (outIdx : Fin q → Fin N) (iy iv : Fin N) :
    ∃ H : s2v_t11b_Formula N, ∀ z, z ∈ H.realize ↔ ∃ x : A,
      (∀ i, z (idx i) = x.val i) ∧ (∀ i, z (outIdx i) = (k x).val i) ∧ z iv = z iy := by
  let ρ : Fin (n + q) → Fin N := Fin.addCases idx outIdx
  let p : MvPolynomial (Fin N) ℝ := .X iv - .X iy
  let E : s2v_t11b_Formula N := .inter (.nonneg p) (.nonneg (-p))
  have hE : ∀ z, z ∈ E.realize ↔ z iv = z iy := by
    intro z
    change (0 ≤ MvPolynomial.eval (fun i => z i) p ∧
      0 ≤ MvPolynomial.eval (fun i => z i) (-p)) ↔ _
    simp only [p, map_sub, map_neg, MvPolynomial.eval_X]
    constructor
    · rintro ⟨h1, h2⟩
      linarith
    · intro he
      rw [he]
      exact ⟨by norm_num, by norm_num⟩
  refine ⟨.inter (s2v_hardt1_rename ρ G) E, ?_⟩
  intro z
  change (z ∈ (s2v_hardt1_rename ρ G).realize ∧ z ∈ E.realize) ↔ _
  rw [s2v_hardt1_realize_rename, hG, hE]
  simp only [ρ, Fin.addCases_left, Fin.addCases_right]
  constructor
  · rintro ⟨⟨x, hx, hkx⟩, he⟩
    exact ⟨x, hx, hkx, he⟩
  · rintro ⟨x, hx, hkx, he⟩
    exact ⟨⟨x, hx, hkx⟩, he⟩

end HodgeLean.Foundations.Program
