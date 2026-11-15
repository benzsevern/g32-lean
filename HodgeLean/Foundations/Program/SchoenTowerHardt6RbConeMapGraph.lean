import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBooleanConeFormula

/-! The cone over an actual boundary graph is the actual graph of its radial map. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_cone_map_graph {n m : ℕ}
    (A X : Set (EuclideanSpace ℝ (Fin n))) (B : Set (EuclideanSpace ℝ (Fin m)))
    (a : EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin m))
    (h : X → EuclideanSpace ℝ (Fin m)) (H : A → B)
    (p : X × Set.Icc (0 : ℝ) 1 → A) (hp : Function.Surjective p)
    (hpx : ∀ z, (p z).val = AffineMap.lineMap a z.1.val z.2.val)
    (hHx : ∀ z, (H (p z)).val = AffineMap.lineMap b (h z.1) z.2.val)
    (G : s2v_t11b_Formula (n + m))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : X,
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = h x i)) :
    ∃ R : s2v_t11b_Formula (n + m), ∀ z, z ∈ R.realize ↔ ∃ x : A,
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (H x).val i) := by
  let c : EuclideanSpace ℝ (Fin (n + m)) := WithLp.toLp 2 (Fin.append (fun i => a i) (fun i => b i))
  obtain ⟨R, hR⟩ := s2v_hardt6rb_boolean_cone_formula c G
  refine ⟨R, ?_⟩
  intro z
  rw [hR]
  constructor
  · rintro ⟨w, hw, t, ht, hz⟩
    obtain ⟨x, hx, hy⟩ := (hG w).mp hw
    refine ⟨p (x, ⟨t, ht⟩), ?_, ?_⟩
    · intro i
      rw [hpx]
      simpa only [c, PiLp.toLp_apply, Fin.append_left, hx,
        AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using hz (Fin.castAdd m i)
    · intro i
      rw [hHx]
      simpa only [c, PiLp.toLp_apply, Fin.append_right, hy,
        AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using hz (Fin.natAdd n i)
  · rintro ⟨y, hy, hHy⟩
    obtain ⟨v, rfl⟩ := hp y
    let w : EuclideanSpace ℝ (Fin (n + m)) :=
      WithLp.toLp 2 (Fin.append (fun i => v.1.val i) (fun i => h v.1 i))
    refine ⟨w, (hG w).mpr ⟨v.1, ?_, ?_⟩, v.2.val, v.2.property, ?_⟩
    · intro i; simp only [w, PiLp.toLp_apply, Fin.append_left]
    · intro i; simp only [w, PiLp.toLp_apply, Fin.append_right]
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [hy j, hpx]
        simp only [c, w, PiLp.toLp_apply, Fin.append_left,
          AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      · rw [hHy j, hHx]
        simp only [c, w, PiLp.toLp_apply, Fin.append_right,
          AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

end HodgeLean.Foundations.Program
