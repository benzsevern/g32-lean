import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRefinementSelection
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRefinedCellClosure
import HodgeLean.Foundations.Program.SchoenTowerT11bDefs

/-! Finite model selection carries every geometric witness into the refinement interface. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_refinement_of_finite_models {n m q : ℕ} {ι : Type*} [Fintype ι]
    (f : s2v_t11b_Formula (n + 1))
    (b : Fin m → s2v_t11b_Formula (n + 1))
    (a : Fin q → s2v_t11b_Formula (n + 1))
    (ha : (⋃ j, (a j).realize) = f.realize)
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
    (G : s2v_t11b_Formula (n + n))
    (J : s2v_t11b_Formula ((n + 1) + (n + 1)))
    (hL : L.faces.Finite) (hβ : ContinuousOn β L.space) (hβinj : Set.InjOn β L.space)
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x ∈ L.space,
      (∀ i, z (Fin.castAdd n i) = x i) ∧ (∀ i, z (Fin.natAdd n i) = β x i))
    (hJ : ∀ z, z ∈ J.realize ↔ ∃ x : EuclideanSpace ℝ (Fin (n + 1)),
      (∀ i, z (Fin.castAdd (n + 1) i) = x i) ∧
      (∀ i, z (Fin.natAdd (n + 1) i) = e x i))
    (cells : ι → s2v_t11b_Formula (n + 1))
    (face : ι → L.faces) (kind : ι → Bool)
    (lower upper : ι → EuclideanSpace ℝ (Fin n) → ℝ)
    (gLower gUpper : ι → s2v_t11b_Formula (n + 1))
    (hne : ∀ i, (cells i).realize.Nonempty)
    (hdis : ∀ i j, i ≠ j → Disjoint (cells i).realize (cells j).realize)
    (hcover : f.realize ⊆ ⋃ i, (cells i).realize)
    (hF : ∀ i, (cells i).realize ⊆ f.realize ∨ Disjoint (cells i).realize f.realize)
    (hA : ∀ i j, (cells i).realize ⊆ (a j).realize ∨ Disjoint (cells i).realize (a j).realize)
    (hB : ∀ i j, (cells i).realize ⊆ (b j).realize ∨ Disjoint (cells i).realize (b j).realize)
    (hl : ∀ i, ContinuousOn (lower i) (convexHull ℝ ((face i).val : Set (EuclideanSpace ℝ (Fin n)))))
    (hu : ∀ i, ContinuousOn (upper i) (convexHull ℝ ((face i).val : Set (EuclideanSpace ℝ (Fin n)))))
    (hlu : ∀ i x, x ∈ convexHull ℝ ((face i).val : Set (EuclideanSpace ℝ (Fin n))) → lower i x ≤ upper i x)
    (hgraph : ∀ i, kind i = true → ∀ x ∈ convexHull ℝ ((face i).val : Set (EuclideanSpace ℝ (Fin n))), lower i x = upper i x)
    (hband : ∀ i, kind i = false → ∀ x ∈ intrinsicInterior ℝ
      (convexHull ℝ ((face i).val : Set (EuclideanSpace ℝ (Fin n)))), lower i x < upper i x)
    (hgl : ∀ i z, z ∈ (gLower i).realize ↔ ∃ x ∈ convexHull ℝ ((face i).val : Set (EuclideanSpace ℝ (Fin n))),
      z 0 = lower i x ∧ (∀ j, z j.succ = x j))
    (hgu : ∀ i z, z ∈ (gUpper i).realize ↔ ∃ x ∈ convexHull ℝ ((face i).val : Set (EuclideanSpace ℝ (Fin n))),
      z 0 = upper i x ∧ (∀ j, z j.succ = x j))
    (hcell : ∀ i, (cells i).realize = e '' {z | ∃ x ∈ intrinsicInterior ℝ
      (convexHull ℝ ((face i).val : Set (EuclideanSpace ℝ (Fin n)))),
      (∀ j, z j.succ = β x j) ∧
      (if kind i then z 0 = lower i x else lower i x < z 0 ∧ z 0 < upper i x)}) :
    ∃ k : ℕ,
    ∃ c : Fin k → s2v_t11b_Formula (n + 1),
    ∃ L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
    ∃ β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
    ∃ e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)),
    ∃ s : Fin k → L.faces,
    ∃ graph : Fin k → Bool,
    ∃ l : Fin k → EuclideanSpace ℝ (Fin n) → ℝ,
    ∃ u : Fin k → EuclideanSpace ℝ (Fin n) → ℝ,
    ∃ G : s2v_t11b_Formula (n + n),
    ∃ J : s2v_t11b_Formula ((n + 1) + (n + 1)),
    ∃ gl : Fin k → s2v_t11b_Formula (n + 1),
    ∃ gu : Fin k → s2v_t11b_Formula (n + 1),
    (L.faces.Finite) ∧
      (ContinuousOn β L.space) ∧
      (Set.InjOn β L.space) ∧
      (∀ z, z ∈ G.realize ↔ ∃ x ∈ L.space,
        (∀ i, z (Fin.castAdd n i) = x i) ∧
        (∀ i, z (Fin.natAdd n i) = β x i)) ∧
      (∀ z, z ∈ J.realize ↔ ∃ x : EuclideanSpace ℝ (Fin (n + 1)),
        (∀ i, z (Fin.castAdd (n + 1) i) = x i) ∧
        (∀ i, z (Fin.natAdd (n + 1) i) = e x i)) ∧
      (∀ i, (c i).realize.Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (c i).realize (c j).realize) ∧
      ((⋃ i, (c i).realize) = f.realize) ∧
      (∀ i j, (c i).realize ⊆ (b j).realize ∨ Disjoint (c i).realize (b j).realize) ∧
      (∀ i, ∃ j, (c i).realize ⊆ (a j).realize) ∧
      (∀ i, ContinuousOn (l i) (convexHull ℝ (↑(s i).val : Set _))) ∧
      (∀ i, ContinuousOn (u i) (convexHull ℝ (↑(s i).val : Set _))) ∧
      (∀ i x, x ∈ convexHull ℝ (↑(s i).val : Set _) → l i x ≤ u i x) ∧
      (∀ i, graph i = true → ∀ x ∈ convexHull ℝ (↑(s i).val : Set _), l i x = u i x) ∧
      (∀ i, graph i = false → ∀ x ∈ intrinsicInterior ℝ
        (convexHull ℝ (↑(s i).val : Set _)), l i x < u i x) ∧
      (∀ i z, z ∈ (gl i).realize ↔ ∃ x ∈ convexHull ℝ (↑(s i).val : Set _),
        z 0 = l i x ∧ (∀ j, z j.succ = x j)) ∧
      (∀ i z, z ∈ (gu i).realize ↔ ∃ x ∈ convexHull ℝ (↑(s i).val : Set _),
        z 0 = u i x ∧ (∀ j, z j.succ = x j)) ∧
      (∀ i, (c i).realize = e '' {z | ∃ x ∈ intrinsicInterior ℝ
        (convexHull ℝ (↑(s i).val : Set _)),
        (∀ j, z j.succ = β x j) ∧
        (if graph i then z 0 = l i x else l i x < z 0 ∧ z 0 < u i x)}) ∧
      (∀ i, closure (c i).realize = e '' {z | ∃ x ∈ convexHull ℝ (↑(s i).val : Set _),
        (∀ j, z j.succ = β x j) ∧ l i x ≤ z 0 ∧ z 0 ≤ u i x}) := by
  classical
  obtain ⟨k, idx, hinj, hcne, hcdis, hcu, hcb, hca⟩ :=
    s2v_hardt6rb_refinement_selection (fun i => (cells i).realize)
      (⋃ i, (cells i).realize) f.realize hcover hne hdis rfl hF
      (fun j => (a j).realize) ha hA (fun j => (b j).realize) hB
  refine ⟨k, (fun i => cells (idx i)), L, β, e, (fun i => face (idx i)),
    (fun i => kind (idx i)), (fun i => lower (idx i)), (fun i => upper (idx i)),
    G, J, (fun i => gLower (idx i)), (fun i => gUpper (idx i)),
    hL, hβ, hβinj, hG, hJ, hcne, hcdis, hcu, hcb, hca,
    (fun i => hl (idx i)), (fun i => hu (idx i)), (fun i => hlu (idx i)),
    (fun i => hgraph (idx i)), (fun i => hband (idx i)),
    (fun i => hgl (idx i)), (fun i => hgu (idx i)), (fun i => hcell (idx i)), ?_⟩
  intro i
  exact s2v_hardt6rb_refined_cell_closure L β hβ e (face (idx i)) (kind (idx i))
    (lower (idx i)) (upper (idx i)) (hl (idx i)) (hu (idx i)) (hlu (idx i))
    (hgraph (idx i)) (hband (idx i)) (cells (idx i)).realize (hcell (idx i))

end HodgeLean.Foundations.Program
