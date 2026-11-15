import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Relations

/-! Boolean graphs of compositions retain the actual maps and full coordinate equations. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_actual_graph_compose {n q r : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n))) (B : Set (EuclideanSpace ℝ (Fin q)))
    (C : Set (EuclideanSpace ℝ (Fin r))) (f : A → B) (g : B → C)
    (G : s2v_t11b_Formula (n + q)) (H : s2v_t11b_Formula (q + r))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : A,
      (∀ i, z (Fin.castAdd q i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (f x).val i))
    (hH : ∀ z, z ∈ H.realize ↔ ∃ y : B,
      (∀ i, z (Fin.castAdd r i) = y.val i) ∧
      (∀ i, z (Fin.natAdd q i) = (g y).val i)) :
    ∃ R : s2v_t11b_Formula (n + r), ∀ z, z ∈ R.realize ↔ ∃ x : A,
      (∀ i, z (Fin.castAdd r i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (g (f x)).val i) := by
  obtain ⟨R, hR⟩ := s2v_hardt_cad5_relation_compose G H
  refine ⟨R, ?_⟩
  intro z
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => z (Fin.castAdd r i))
  let y : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i => z (Fin.natAdd n i))
  have hpaste : WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => y i)) = z := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [x, y]
  have hr := hR x y
  rw [hpaste] at hr
  rw [hr]
  constructor
  · rintro ⟨v, hfv, hgv⟩
    obtain ⟨a, ha, hva⟩ := (hG _).mp hfv
    obtain ⟨b, hvb, hb⟩ := (hH _).mp hgv
    simp only [PiLp.toLp_apply, Fin.append_left, Fin.append_right] at ha hva hvb hb
    have he : f a = b := by
      apply Subtype.ext
      ext i
      exact (hva i).symm.trans (hvb i)
    refine ⟨a, ha, ?_⟩
    intro i
    rw [he]
    exact hb i
  · rintro ⟨a, ha, hb⟩
    refine ⟨(f a).val, (hG _).mpr ⟨a, ?_, ?_⟩, (hH _).mpr ⟨f a, ?_, ?_⟩⟩
    · simpa only [PiLp.toLp_apply, Fin.append_left] using ha
    · intro i
      simp only [PiLp.toLp_apply, Fin.append_right]
    · intro i
      simp only [PiLp.toLp_apply, Fin.append_left]
    · simpa only [PiLp.toLp_apply, Fin.append_right] using hb

end HodgeLean.Foundations.Program
