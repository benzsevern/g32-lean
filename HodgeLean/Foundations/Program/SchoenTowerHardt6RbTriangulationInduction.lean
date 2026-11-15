import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPreparedRootTriangulation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbMappedRootCellTriangulation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactCarrierFromCells
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRefinementInduction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCoherentRootRestrictions
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceRootEnumeration
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceCellMarks
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceCellCover

/-! Lower-dimensional compatible compact triangulations construct the successor-dimensional marked triangulation. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_triangulation_induction_step {n m : ℕ}
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
    (b : Fin m → s2v_t11b_Formula (n + 1)) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))),
      K.faces.Finite ∧ ∃ h : K.space ≃ₜ f.realize,
        (∀ j, ∃ S : Finset (Finset (EuclideanSpace ℝ (Fin (n + 1)))),
          (↑S : Set _) ⊆ K.faces ∧ f.realize ∩ (b j).realize = (fun x : K.space => (h x).val) ''
            {x : K.space | ∃ s ∈ S, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
        ∃ G : s2v_t11b_Formula ((n + 1) + (n + 1)), ∀ z, z ∈ G.realize ↔ ∃ x : K.space,
          (∀ i, z (Fin.castAdd (n + 1) i) = x.val i) ∧
          (∀ i, z (Fin.natAdd (n + 1) i) = (h x).val i) := by
  classical
  obtain ⟨e, F, J, hF, hJ, Q, hQ, t, C, hC, hd, hu, r, ψ, hψ, hm, hr, hrootCover,
    g, band, hg, hb, hGF, hBF, _, _, hGB, hBB⟩ :=
    s2v_hardt6rb_marked_root_presentation f b (fun i : Fin 0 => Fin.elim0 i)
  have hFc : IsCompact F.realize := by rw [hF]; exact e.isCompact_preimage.mpr hf
  obtain ⟨P, hPc, hPimage, hP⟩ := s2v_hardt6rb_compact_base F hFc
  obtain ⟨B, hB, h, hmarks, Gb, hGb⟩ := ih P hPc C
  obtain ⟨β, hβ, hβinj, himage, he, hGb', parent, hp⟩ :=
    s2v_hardt6rb_adapted_base_map B P.realize h (fun j => (C j).realize) hu hmarks Gb hGb
  obtain ⟨w, Hw, hw, hwm, hws, hagree, hroots, hHw⟩ :=
    s2v_hardt6rb_face_root_family B β hβ Gb hGb' (fun j => (C j).realize) r ψ hψ hm
      Q hQ hr g hg parent hp
  have hrootEnum := s2v_hardt6rb_face_root_enumeration B β (fun j => (C j).realize) r ψ Q hrootCover parent hp w hagree
  obtain ⟨ρ, _, hρ, _, _⟩ := s2v_hardt6rb_coherent_face_root_restrictions B β (fun s => r (parent s)) w hw hwm hws Q hroots hrootEnum
  have hbase : ∀ z ∈ e ⁻¹' f.realize, ∃ x ∈ B.space, ∀ i, z i.succ = β x i := by
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
  exact s2v_hardt6rb_triangulation_from_prepared_roots f hf b B β e Gb J hB hβ hβinj hGb' hJ hbase
    C (fun j => (hC j).nonempty) r ψ hm g band hg hb hGF hBF hGB hBB parent hp w Hw hw hwm hws hagree hHw ρ hρ

end HodgeLean.Foundations.Program
