import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceCellConstruction

/-! Ordered face-root data construct all graph cells and adjacent-root band cells simultaneously. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_cell_family {n : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hβ : ContinuousOn β L.space)
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
    (G : s2v_t11b_Formula (n + n))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x ∈ L.space,
      (∀ i, z (Fin.castAdd n i) = x i) ∧ (∀ i, z (Fin.natAdd n i) = β x i))
    (J : s2v_t11b_Formula ((n + 1) + (n + 1)))
    (hJ : ∀ z, z ∈ J.realize ↔ ∃ x : EuclideanSpace ℝ (Fin (n + 1)),
      (∀ i, z (Fin.castAdd (n + 1) i) = x i) ∧
      (∀ i, z (Fin.natAdd (n + 1) i) = e x i))
    (r : L.faces → ℕ)
    (f : (s : L.faces) → Fin (r s) → EuclideanSpace ℝ (Fin n) → ℝ)
    (H : (s : L.faces) → Fin (r s) → s2v_t11b_Formula (n + 1))
    (hf : ∀ s i, ContinuousOn (f s i) (convexHull ℝ (↑s.val : Set _)))
    (hm : ∀ s x, x ∈ convexHull ℝ (↑s.val : Set _) → Monotone (fun i => f s i x))
    (hs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s.val : Set _)) →
      StrictMono (fun i => f s i x))
    (hH : ∀ s i z, z ∈ (H s i).realize ↔ ∃ x ∈ convexHull ℝ (↑s.val : Set _),
      z 0 = f s i x ∧ (∀ j, z j.succ = x j)) :
    ∃ cg : (s : L.faces) → Fin (r s) → s2v_t11b_Formula (n + 1),
    ∃ cb : (s : L.faces) → (i j : Fin (r s)) → i.val + 1 = j.val → s2v_t11b_Formula (n + 1),
      (∀ s i, (cg s i).realize.Nonempty ∧
        (cg s i).realize = e '' {z | ∃ x ∈ intrinsicInterior ℝ
          (convexHull ℝ (↑s.val : Set _)), (∀ a, z a.succ = β x a) ∧ z 0 = f s i x} ∧
        closure (cg s i).realize = e '' {z | ∃ x ∈ convexHull ℝ (↑s.val : Set _),
          (∀ a, z a.succ = β x a) ∧ f s i x ≤ z 0 ∧ z 0 ≤ f s i x}) ∧
      (∀ s i j (hij : i.val + 1 = j.val), (cb s i j hij).realize.Nonempty ∧
        (cb s i j hij).realize = e '' {z | ∃ x ∈ intrinsicInterior ℝ
          (convexHull ℝ (↑s.val : Set _)), (∀ a, z a.succ = β x a) ∧
          f s i x < z 0 ∧ z 0 < f s j x} ∧
        closure (cb s i j hij).realize = e '' {z | ∃ x ∈ convexHull ℝ (↑s.val : Set _),
          (∀ a, z a.succ = β x a) ∧ f s i x ≤ z 0 ∧ z 0 ≤ f s j x}) := by
  classical
  have graphs (s : L.faces) (i : Fin (r s)) :=
    s2v_hardt6rb_face_cell_construction L β hβ e s true (f s i) (f s i) (hf s i) (hf s i)
      (fun _ _ => le_rfl) (fun _ _ _ => rfl) (fun h => Bool.noConfusion h)
      G hG J hJ (H s i) (H s i) (hH s i) (hH s i)
  have bands (s : L.faces) (i j : Fin (r s)) (hij : i.val + 1 = j.val) :=
    s2v_hardt6rb_face_cell_construction L β hβ e s false (f s i) (f s j) (hf s i) (hf s j)
      (fun x hx => hm s x hx (by change i.val ≤ j.val; omega))
      (fun h => Bool.noConfusion h)
      (fun _ x hx => hs s x hx (by change i.val < j.val; omega))
      G hG J hJ (H s i) (H s j) (hH s i) (hH s j)
  choose cg hcg using graphs
  choose cb hcb using bands
  exact ⟨cg, cb, hcg, hcb⟩

end HodgeLean.Foundations.Program
