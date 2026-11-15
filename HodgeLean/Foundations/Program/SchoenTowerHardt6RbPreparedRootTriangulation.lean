import HodgeLean.Foundations.Program.SchoenTowerHardt6RbMappedRootCellTriangulation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactCarrierFromCells
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceCellMarks
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceCellCover

/-! Prepared coherent root data supply compatible compact marked triangulations in the original coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_triangulation_from_prepared_roots {n m t : ℕ}
    (f : s2v_t11b_Formula (n + 1)) (hf : IsCompact f.realize)
    (b : Fin m → s2v_t11b_Formula (n + 1))
    (B : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
    (Gb : s2v_t11b_Formula (n + n))
    (J : s2v_t11b_Formula ((n + 1) + (n + 1)))
    (hB : B.faces.Finite) (hβ : ContinuousOn β B.space) (hβinj : Set.InjOn β B.space)
    (hGb' : ∀ z, z ∈ Gb.realize ↔ ∃ x ∈ B.space,
      (∀ i, z (Fin.castAdd n i) = x i) ∧ (∀ i, z (Fin.natAdd n i) = β x i))
    (hJ : ∀ z, z ∈ J.realize ↔ ∃ x : EuclideanSpace ℝ (Fin (n + 1)),
      (∀ i, z (Fin.castAdd (n + 1) i) = x i) ∧
      (∀ i, z (Fin.natAdd (n + 1) i) = e x i))
    (hbase : ∀ z ∈ e ⁻¹' f.realize, ∃ x ∈ B.space, ∀ i, z i.succ = β x i)
    (C : Fin t → s2v_t11b_Formula n) (hC : ∀ j, (C j).realize.Nonempty)
    (r : Fin t → ℕ) (ψ : (j : Fin t) → Fin (r j) → (C j).realize → ℝ)
    (hm : ∀ j x, StrictMono (fun i => ψ j i x))
    (g : (j : Fin t) → Fin (r j) → s2v_t11b_Formula (n + 1))
    (band : (j : Fin t) → Fin (r j + 1) → s2v_t11b_Formula (n + 1))
    (hg : ∀ j i z, z ∈ (g j i).realize ↔ ∃ x : (C j).realize,
      (∀ k, z k.succ = x.val k) ∧ z 0 = ψ j i x)
    (hb : ∀ j i z, z ∈ (band j i).realize ↔ ∃ x : (C j).realize,
      (∀ k, z k.succ = x.val k) ∧
      (∀ k : Fin (r j), k.val < i.val → ψ j k x < z 0) ∧
      (∀ k : Fin (r j), i.val ≤ k.val → z 0 < ψ j k x))
    (hGF : ∀ j i, (g j i).realize ⊆ e ⁻¹' f.realize ∨ Disjoint (g j i).realize (e ⁻¹' f.realize))
    (hBF : ∀ j i, (band j i).realize ⊆ e ⁻¹' f.realize ∨ Disjoint (band j i).realize (e ⁻¹' f.realize))
    (hGB : ∀ j i k, (g j i).realize ⊆ e ⁻¹' (b k).realize ∨ Disjoint (g j i).realize (e ⁻¹' (b k).realize))
    (hBB : ∀ j i k, (band j i).realize ⊆ e ⁻¹' (b k).realize ∨ Disjoint (band j i).realize (e ⁻¹' (b k).realize))
    (parent : B.faces → Fin t)
    (hp : ∀ (s : B.faces) (x : EuclideanSpace ℝ (Fin n)),
      x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
        β x ∈ (C (parent s)).realize)
    (w : (s : B.faces) → Fin (r (parent s)) → EuclideanSpace ℝ (Fin n) → ℝ)
    (Hw : (s : B.faces) → Fin (r (parent s)) → s2v_t11b_Formula (n + 1))
    (hw : ∀ s i, ContinuousOn (w s i) (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))))
    (hwm : ∀ s x, x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) → Monotone (fun i => w s i x))
    (hws : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
      StrictMono (fun i => w s i x))
    (hagree : ∀ (s : B.faces) (i : Fin (r (parent s))) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))))),
      w s i x = ψ (parent s) i ⟨β x, hp s x hx⟩)
    (hHw : ∀ s i z, z ∈ (Hw s i).realize ↔ ∃ x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))),
      z 0 = w s i x ∧ (∀ k, z k.succ = x k)) 
    (ρ : ∀ s t : B.faces, t.val ⊆ s.val → Fin (r (parent s)) → Fin (r (parent t)))
    (hρ : ∀ s t hts a x, x ∈ convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) →
      w s a x = w t (ρ s t hts a) x) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))),
      K.faces.Finite ∧ ∃ h : K.space ≃ₜ f.realize,
        (∀ j, ∃ S : Finset (Finset (EuclideanSpace ℝ (Fin (n + 1)))),
          (↑S : Set _) ⊆ K.faces ∧ f.realize ∩ (b j).realize = (fun x : K.space => (h x).val) ''
            {x : K.space | ∃ s ∈ S, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
        ∃ G : s2v_t11b_Formula ((n + 1) + (n + 1)), ∀ z, z ∈ G.realize ↔ ∃ x : K.space,
          (∀ i, z (Fin.castAdd (n + 1) i) = x.val i) ∧
          (∀ i, z (Fin.natAdd (n + 1) i) = (h x).val i) := by
  classical
  have hHw' (s : B.faces) (a) (z) : z ∈ (Hw s a).realize ↔ ∃ x ∈ convexHull ℝ (s.val : Set _),
      (∀ i, z i.succ = x i) ∧ z 0 = w s a x := by
    rw [hHw]
    exact exists_congr fun x => and_congr_right fun _ => and_comm
  obtain ⟨L, hL, hLB, p, hInt, c, hc, K, hK, H, hcell, G, hG⟩ :=
    s2v_hardt6rb_mapped_root_cell_triangulation B hB (fun s => r (parent s)) w hw hwm hws ρ hρ Hw hHw'
      β hβ hβinj Gb hGb' e J hJ
  let parent' : L.faces → Fin t := fun s => parent (p s)
  have hp' (s : L.faces) (x) (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set _))) :
      β x ∈ (C (parent' s)).realize := hp (p s) x (hInt s hx)
  have hagree' (s : L.faces) (a : Fin (r (parent' s))) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))))) :
      w (p s) a x = ψ (parent' s) a ⟨β x, hp' s x hx⟩ := hagree (p s) a x (hInt s hx)
  have hbaseL : ∀ z ∈ e ⁻¹' f.realize, ∃ x ∈ L.space, ∀ i, z i.succ = β x i := by
    intro z hz
    obtain ⟨x, hx, heq⟩ := hbase z hz
    exact ⟨x, hLB.symm ▸ hx, heq⟩
  have hcover := s2v_hardt6rb_face_cell_cover L β e (e ⁻¹' f.realize) (e.isCompact_preimage.mpr hf)
    hbaseL C hC r ψ hm g band hg hb hBF parent' hp' (fun s => w (p s)) hagree' c (fun s a => by cases a <;> exact hc s _)
  have hcompatF := s2v_hardt6rb_face_cell_marks L β e C r ψ hm g band hg hb
    (fun _ : Fin 1 => e ⁻¹' f.realize) (fun j a _ => hGF j a) (fun j a _ => hBF j a)
    parent' hp' (fun s => w (p s)) hagree' c (fun s a => by cases a <;> exact hc s _)
  have hcompatB := s2v_hardt6rb_face_cell_marks L β e C r ψ hm g band hg hb
    (fun j => e ⁻¹' (b j).realize) hGB hBB parent' hp' (fun s => w (p s)) hagree' c (fun s a => by cases a <;> exact hc s _)
  let I := (s : L.faces) × s2v_hardt6rb_RootLabel (r (parent' s))
  letI : Fintype L.faces := hL.fintype
  letI (s : L.faces) : Fintype (s2v_hardt6rb_RootLabel (r (parent' s))) := Fintype.ofFinite _
  letI : Fintype I := inferInstance
  exact s2v_hardt6rb_compact_carrier_from_cells K hK (⋃ i : I, c i.1 i.2) H (fun i : I => c i.1 i.2) rfl
    (fun i => hcell i.1 i.2) f hf (by simpa only [e.image_preimage] using hcover) b
    (fun i => by simpa only [e.image_preimage] using hcompatF i.1 i.2 0)
    (fun i j => by simpa only [e.image_preimage] using hcompatB i.1 i.2 j) G hG


end HodgeLean.Foundations.Program
