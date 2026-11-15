import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Relations

/-! Actual Boolean section graphs pulled back along an actual Boolean base map. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_section_graph_pullback {n q : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n))) (B : Set (EuclideanSpace ℝ (Fin q)))
    (k : A → B) (c : B → ℝ)
    (G : s2v_t11b_Formula (n + q)) (C : s2v_t11b_Formula (q + 1))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : A,
      (∀ i, z (Fin.castAdd q i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (k x).val i))
    (hC : ∀ z, z ∈ C.realize ↔ ∃ y : B,
      (∀ i, z i.succ = y.val i) ∧ z 0 = c y) :
    ∃ F : s2v_t11b_Formula (n + 1), ∀ z, z ∈ F.realize ↔ ∃ x : A,
      (∀ i, z i.succ = x.val i) ∧ z 0 = c (k x) := by
  let u := s2v_hardt2_boundIndex (n + 1) q
  let v := s2v_hardt2_freeIndex (n + 1) q
  let ρ : Fin (n + q) → Fin ((n + 1) + q) :=
    Fin.addCases (fun i => v i.succ) u
  let τ : Fin (q + 1) → Fin ((n + 1) + q) := Fin.cases (v 0) u
  let R : s2v_t11b_Formula ((n + 1) + q) :=
    .inter (s2v_hardt1_rename ρ G) (s2v_hardt1_rename τ C)
  obtain ⟨F, hF⟩ := s2v_hardt2_repeated_projection R
  have hρ (z : EuclideanSpace ℝ (Fin (n + 1))) (a : Fin q → ℝ) :
      WithLp.toLp 2 (fun i => s2v_hardt2_insert q a z (ρ i)) =
        WithLp.toLp 2 (Fin.append (fun i : Fin n => z i.succ) a) := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [ρ, u, v, s2v_hardt2_insert_bound, s2v_hardt2_insert_free]
  have hτ (z : EuclideanSpace ℝ (Fin (n + 1))) (a : Fin q → ℝ) :
      WithLp.toLp 2 (fun i => s2v_hardt2_insert q a z (τ i)) =
        WithLp.toLp 2 (Fin.cons (z 0) a) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [τ, u, v, s2v_hardt2_insert_bound, s2v_hardt2_insert_free]
  refine ⟨F, ?_⟩
  intro z
  rw [hF]
  constructor
  · rintro ⟨a, ha⟩
    change _ ∧ _ at ha
    rw [s2v_hardt1_realize_rename, hρ, s2v_hardt1_realize_rename, hτ] at ha
    obtain ⟨x, hx, hax⟩ := (hG _).mp ha.1
    obtain ⟨y, hay, hcy⟩ := (hC _).mp ha.2
    simp only [Fin.append_left, Fin.append_right] at hx hax
    simp only [Fin.cons_succ, Fin.cons_zero] at hay hcy
    have he : k x = y := by
      apply Subtype.ext
      ext i
      exact (hax i).symm.trans (hay i)
    exact ⟨x, hx, he.symm ▸ hcy⟩
  · rintro ⟨x, hx, hc⟩
    refine ⟨fun i => (k x).val i, ?_⟩
    change _ ∧ _
    rw [s2v_hardt1_realize_rename, hρ, s2v_hardt1_realize_rename, hτ]
    refine ⟨(hG _).mpr ⟨x, ?_, ?_⟩, (hC _).mpr ⟨k x, ?_, ?_⟩⟩
    · simpa only [Fin.append_left] using hx
    · intro i
      simp only [Fin.append_right]
    · intro i
      simp only [Fin.cons_succ]
    · exact hc

end HodgeLean.Foundations.Program
