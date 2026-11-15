import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBaseHeightGraph

/-! A Boolean base map has an actual height-preserving graph in full height-first coordinate blocks. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_height_lift_graph {n q : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (G : s2v_t11b_Formula (n + q))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x ∈ A,
      (∀ i, z (Fin.castAdd q i) = x i) ∧
      (∀ i, z (Fin.natAdd n i) = β x i)) :
    ∃ H : s2v_t11b_Formula ((n + 1) + (q + 1)), ∀ z, z ∈ H.realize ↔
      ∃ x : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (fun i : Fin n => x i.succ) ∈ A ∧
        (∀ i, z (Fin.castAdd (q + 1) i) = x i) ∧
        z (Fin.natAdd (n + 1) 0) = x 0 ∧
        (∀ i, z (Fin.natAdd (n + 1) i.succ) =
          β (WithLp.toLp 2 (fun j : Fin n => x j.succ)) i) := by
  let k : A → (Set.univ : Set (EuclideanSpace ℝ (Fin q))) := fun x => ⟨β x.val, trivial⟩
  have hk : ∀ z, z ∈ G.realize ↔ ∃ x : A,
      (∀ i, z (Fin.castAdd q i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (k x).val i) := by
    intro z
    rw [hG]
    exact ⟨fun ⟨x, hx, ha, hb⟩ => ⟨⟨x, hx⟩, ha, hb⟩,
      fun ⟨x, ha, hb⟩ => ⟨x.val, x.property, ha, hb⟩⟩
  obtain ⟨H, hH⟩ := s2v_hardt6rb_base_height_graph A Set.univ k G hk
    (fun i => Fin.castAdd (q + 1) i.succ)
    (fun i => Fin.natAdd (n + 1) i.succ)
    (Fin.castAdd (q + 1) 0) (Fin.natAdd (n + 1) 0)
  refine ⟨H, ?_⟩
  intro z
  rw [hH]
  constructor
  · rintro ⟨a, ha, hb, ht⟩
    let x : EuclideanSpace ℝ (Fin (n + 1)) :=
      WithLp.toLp 2 (fun i => z (Fin.castAdd (q + 1) i))
    have he : WithLp.toLp 2 (fun i : Fin n => x i.succ) = a.val := by
      ext i
      exact ha i
    exact ⟨x, he.symm ▸ a.property, fun _ => rfl, ht, by simpa only [he] using hb⟩
  · rintro ⟨x, hx, hin, ht, hout⟩
    refine ⟨⟨WithLp.toLp 2 (fun i : Fin n => x i.succ), hx⟩,
      (fun i => hin i.succ), hout, ht.trans (hin 0).symm⟩

end HodgeLean.Foundations.Program
