import HodgeLean.Foundations.Program.SchoenTowerHardt2

/-! Actual coordinate formulas for reversal and composition of Boolean relations. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_relation_reverse {n q : ℕ}
    (G : s2v_t11b_Formula (n + q)) :
    ∃ J : s2v_t11b_Formula (q + n),
      ∀ (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin q)),
        WithLp.toLp 2 (Fin.append (fun i => y i) (fun i => x i)) ∈ J.realize ↔
          WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => y i)) ∈ G.realize := by
  let ρ : Fin (n + q) → Fin (q + n) :=
    Fin.addCases (Fin.natAdd q) (Fin.castAdd n)
  refine ⟨s2v_hardt1_rename ρ G, ?_⟩
  intro x y
  rw [s2v_hardt1_realize_rename]
  have heq : WithLp.toLp 2 (fun i =>
      Fin.append (fun j => y j) (fun j => x j) (ρ i)) =
      WithLp.toLp 2 (Fin.append (fun j => x j) (fun j => y j)) := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [ρ]
  rw [heq]

theorem s2v_hardt_cad5_relation_compose {n q r : ℕ}
    (G : s2v_t11b_Formula (n + q)) (H : s2v_t11b_Formula (q + r)) :
    ∃ F : s2v_t11b_Formula (n + r),
      ∀ (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin r)),
        WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => z i)) ∈ F.realize ↔
          ∃ y : EuclideanSpace ℝ (Fin q),
            WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => y i)) ∈ G.realize ∧
            WithLp.toLp 2 (Fin.append (fun i => y i) (fun i => z i)) ∈ H.realize := by
  let u := s2v_hardt2_boundIndex (n + r) q
  let v := s2v_hardt2_freeIndex (n + r) q
  let ρ : Fin (n + q) → Fin ((n + r) + q) :=
    Fin.addCases (fun i => v (i.castAdd r)) u
  let τ : Fin (q + r) → Fin ((n + r) + q) :=
    Fin.addCases u (fun i => v (i.natAdd n))
  let R : s2v_t11b_Formula ((n + r) + q) :=
    .inter (s2v_hardt1_rename ρ G) (s2v_hardt1_rename τ H)
  obtain ⟨F, hF⟩ := s2v_hardt2_repeated_projection R
  refine ⟨F, ?_⟩
  intro x z
  rw [hF]
  let w : EuclideanSpace ℝ (Fin (n + r)) :=
    WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => z i))
  have hρ (y : Fin q → ℝ) : WithLp.toLp 2
      (fun i => s2v_hardt2_insert q y w (ρ i)) =
      WithLp.toLp 2 (Fin.append (fun i => x i) y) := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [ρ, u, v, w, s2v_hardt2_insert_bound, s2v_hardt2_insert_free]
  have hτ (y : Fin q → ℝ) : WithLp.toLp 2
      (fun i => s2v_hardt2_insert q y w (τ i)) =
      WithLp.toLp 2 (Fin.append y (fun i => z i)) := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [τ, u, v, w, s2v_hardt2_insert_bound, s2v_hardt2_insert_free]
  constructor
  · rintro ⟨y, hy⟩
    change _ ∧ _ at hy
    rw [s2v_hardt1_realize_rename, hρ, s2v_hardt1_realize_rename, hτ] at hy
    exact ⟨WithLp.toLp 2 y, hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨fun i => y i, ?_⟩
    change _ ∧ _
    rw [s2v_hardt1_realize_rename, hρ, s2v_hardt1_realize_rename, hτ]
    exact hy

theorem s2v_hardt_cad5_relation_restricted_reverse {n q : ℕ}
    (C : s2v_t11b_Formula n) (G : s2v_t11b_Formula (n + q)) :
    ∃ J : s2v_t11b_Formula (q + n),
      ∀ (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin q)),
        WithLp.toLp 2 (Fin.append (fun i => y i) (fun i => x i)) ∈ J.realize ↔
          x ∈ C.realize ∧
          WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => y i)) ∈ G.realize := by
  obtain ⟨J, hJ⟩ := s2v_hardt_cad5_relation_reverse
    (.inter (s2v_hardt1_rename (Fin.castAdd q) C) G)
  refine ⟨J, ?_⟩
  intro x y
  rw [hJ]
  change (_ ∧ _) ↔ _
  rw [s2v_hardt1_realize_rename]
  have hx : WithLp.toLp 2 (fun i =>
      Fin.append (fun j => x j) (fun j => y j) (Fin.castAdd q i)) = x := by
    ext i
    simp
  rw [hx]

theorem s2v_hardt_cad5_block_projection_formula {q n : ℕ}
    (S : s2v_t11b_Formula (q + n)) :
    ∃ F : s2v_t11b_Formula n, ∀ a : EuclideanSpace ℝ (Fin n),
      a ∈ F.realize ↔ ∃ t : EuclideanSpace ℝ (Fin q),
        WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a i)) ∈ S.realize := by
  let u := s2v_hardt2_boundIndex n q
  let v := s2v_hardt2_freeIndex n q
  let ρ : Fin (q + n) → Fin (n + q) := Fin.addCases u v
  obtain ⟨F, hF⟩ := s2v_hardt2_repeated_projection (s2v_hardt1_rename ρ S)
  refine ⟨F, ?_⟩
  intro a
  rw [hF]
  have hcoords (t : Fin q → ℝ) : WithLp.toLp 2
      (fun i => s2v_hardt2_insert q t a (ρ i)) =
        WithLp.toLp 2 (Fin.append t (fun i => a i)) := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [ρ, u, v, s2v_hardt2_insert_bound, s2v_hardt2_insert_free]
  constructor
  · rintro ⟨t, ht⟩
    rw [s2v_hardt1_realize_rename, hcoords] at ht
    exact ⟨WithLp.toLp 2 t, ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨fun i => t i, ?_⟩
    rw [s2v_hardt1_realize_rename, hcoords]
    exact ht

end HodgeLean.Foundations.Program
