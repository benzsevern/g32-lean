import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPreparedBaseRefinement
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbMarkedRootPresentation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAdaptedBaseMap
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceRootFamily
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactBase

/-! Lower-dimensional compact base triangulations construct the successor-dimensional boundary refinement. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_refinement_induction_step {n m q : ℕ}
    (ih : ∀ {v : ℕ} (P : s2v_t11b_Formula n), IsCompact P.realize →
      ∀ D : Fin v → s2v_t11b_Formula n,
      ∃ L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
        L.faces.Finite ∧ ∃ h : L.space ≃ₜ P.realize,
          (∀ j, ∃ S : Finset (Finset (EuclideanSpace ℝ (Fin n))),
            (↑S : Set _) ⊆ L.faces ∧
            P.realize ∩ (D j).realize = (fun x : L.space => (h x).val) ''
              {x : L.space | ∃ s ∈ S, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
          ∃ G : s2v_t11b_Formula (n + n), ∀ z, z ∈ G.realize ↔ ∃ x : L.space,
            (∀ i, z (Fin.castAdd n i) = x.val i) ∧
            (∀ i, z (Fin.natAdd n i) = (h x).val i))
    (f : s2v_t11b_Formula (n + 1)) (hf : IsCompact f.realize)
    (b : Fin m → s2v_t11b_Formula (n + 1))
    (a : Fin q → s2v_t11b_Formula (n + 1))
    (ha : (⋃ j, (a j).realize) = f.realize) :
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
  obtain ⟨e, F, J, hF, hJ, Q, hQ, t, C, hC, hd, hu, r, ψ, hψ, hm, hr, hrootCover,
    g, band, hg, hb, hGF, hBF, hGA, hBA, hGB, hBB⟩ :=
    s2v_hardt6rb_marked_root_presentation f b a
  have hFc : IsCompact F.realize := by
    rw [hF]
    exact e.isCompact_preimage.mpr hf
  obtain ⟨P, hPc, hPimage, hP⟩ := s2v_hardt6rb_compact_base F hFc
  obtain ⟨L, hL, h, hmarks, G, hG⟩ := ih P hPc C
  obtain ⟨β, hβ, hβinj, himage, he, hG', parent, hp⟩ :=
    s2v_hardt6rb_adapted_base_map L P.realize h (fun j => (C j).realize) hu hmarks G hG
  obtain ⟨w, H, hw, hwm, hws, hagree, hroots, hH⟩ :=
    s2v_hardt6rb_face_root_family L β hβ G hG' (fun j => (C j).realize) r ψ hψ hm
      Q hQ hr g hg parent hp
  have hbase : ∀ z ∈ e ⁻¹' f.realize, ∃ x ∈ L.space, ∀ i, z i.succ = β x i := by
    intro z hz
    have hzF : z ∈ F.realize := hF.symm ▸ hz
    let base : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i : Fin n => z i.succ)
    have hbaseP : base ∈ P.realize := by
      apply (hP base).mpr
      refine ⟨z 0, ?_⟩
      convert hzF using 1
      ext i
      exact Fin.cases rfl (fun _ => rfl) i
    obtain ⟨x, hx, heq⟩ := himage.symm ▸ hbaseP
    refine ⟨x, hx, ?_⟩
    intro i
    exact (congrArg (fun y : EuclideanSpace ℝ (Fin n) => y i) heq).symm
  exact s2v_hardt6rb_refinement_from_prepared_base f hf b a ha L β e G J hL hβ hβinj
    hG' hJ hbase C (fun j => (hC j).nonempty) r ψ hm g band hg hb hGF hBF hGA hBA hGB hBB
    parent hp w H hw hwm hws hagree hH

end HodgeLean.Foundations.Program
