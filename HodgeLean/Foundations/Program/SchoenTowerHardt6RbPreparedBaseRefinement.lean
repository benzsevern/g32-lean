import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRefinementModelSelection
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceCellFamily
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceCellDisjoint
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceCellCover
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceCellMarks

/-! Prepared base and root data construct every witness of the marked boundary refinement. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_refinement_from_prepared_base {n m q t : ℕ}
    (f : s2v_t11b_Formula (n + 1)) (hf : IsCompact f.realize)
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
    (hbase : ∀ z ∈ e ⁻¹' f.realize, ∃ x ∈ L.space, ∀ i, z i.succ = β x i)
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
    (hGA : ∀ j i k, (g j i).realize ⊆ e ⁻¹' (a k).realize ∨ Disjoint (g j i).realize (e ⁻¹' (a k).realize))
    (hBA : ∀ j i k, (band j i).realize ⊆ e ⁻¹' (a k).realize ∨ Disjoint (band j i).realize (e ⁻¹' (a k).realize))
    (hGB : ∀ j i k, (g j i).realize ⊆ e ⁻¹' (b k).realize ∨ Disjoint (g j i).realize (e ⁻¹' (b k).realize))
    (hBB : ∀ j i k, (band j i).realize ⊆ e ⁻¹' (b k).realize ∨ Disjoint (band j i).realize (e ⁻¹' (b k).realize))
    (parent : L.faces → Fin t)
    (hp : ∀ (s : L.faces) (x : EuclideanSpace ℝ (Fin n)),
      x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
        β x ∈ (C (parent s)).realize)
    (w : (s : L.faces) → Fin (r (parent s)) → EuclideanSpace ℝ (Fin n) → ℝ)
    (H : (s : L.faces) → Fin (r (parent s)) → s2v_t11b_Formula (n + 1))
    (hw : ∀ s i, ContinuousOn (w s i) (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))))
    (hwm : ∀ s x, x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) → Monotone (fun i => w s i x))
    (hws : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
      StrictMono (fun i => w s i x))
    (hagree : ∀ (s : L.faces) (i : Fin (r (parent s))) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))))),
      w s i x = ψ (parent s) i ⟨β x, hp s x hx⟩)
    (hH : ∀ s i z, z ∈ (H s i).realize ↔ ∃ x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))),
      z 0 = w s i x ∧ (∀ k, z k.succ = x k)) :
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
  letI : Fintype L.faces := hL.fintype
  let I := (s : L.faces) ×
    (Fin (r (parent s)) ⊕ {p : Fin (r (parent s)) × Fin (r (parent s)) // p.1.val + 1 = p.2.val})
  letI : Fintype I := Fintype.ofFinite I
  obtain ⟨cg, cb, hcg, hcb⟩ := s2v_hardt6rb_face_cell_family L β hβ e G hG J hJ
    (fun s => r (parent s)) w H hw hwm hws hH
  let cells (i : I) := match i.2 with
    | .inl j => cg i.1 j
    | .inr p => cb i.1 p.val.1 p.val.2 p.property
  let lo (i : I) : Fin (r (parent i.1)) := match i.2 with
    | .inl j => j
    | .inr p => p.val.1
  let hi (i : I) : Fin (r (parent i.1)) := match i.2 with
    | .inl j => j
    | .inr p => p.val.2
  let kind (i : I) : Bool := match i.2 with | .inl _ => true | .inr _ => false
  let lower (i : I) := w i.1 (lo i)
  let upper (i : I) := w i.1 (hi i)
  let gLower (i : I) := H i.1 (lo i)
  let gUpper (i : I) := H i.1 (hi i)
  have hmodel : ∀ s a, (cells ⟨s, a⟩).realize = e '' {z | ∃ x ∈ intrinsicInterior ℝ
      (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))), (∀ k, z k.succ = β x k) ∧
      match a with
      | .inl j => z 0 = w s j x
      | .inr p => w s p.val.1 x < z 0 ∧ z 0 < w s p.val.2 x} := by
    intro s a
    cases a with
    | inl j => exact (hcg s j).2.1
    | inr p => exact (hcb s p.val.1 p.val.2 p.property).2.1
  have hne (i : I) : (cells i).realize.Nonempty := by
    rcases i with ⟨s, a⟩
    cases a with
    | inl j => exact (hcg s j).1
    | inr p => exact (hcb s p.val.1 p.val.2 p.property).1
  have hdis : ∀ i j : I, i ≠ j → Disjoint (cells i).realize (cells j).realize :=
    s2v_hardt6rb_face_cell_disjoint L β hβinj e (fun s => r (parent s)) w hws
      (fun s a => (cells ⟨s, a⟩).realize) (by
        intro s a
        cases a with
        | inl j => exact (hcg s j).2.1
        | inr p => exact (hcb s p.val.1 p.val.2 p.property).2.1)
  have hcover : f.realize ⊆ ⋃ i : I, (cells i).realize := by
    have hcov := s2v_hardt6rb_face_cell_cover L β e (e ⁻¹' f.realize)
      (e.isCompact_preimage.mpr hf) hbase C hC r ψ hm g band hg hb hBF parent hp w hagree
      (fun s a => (cells ⟨s, a⟩).realize) hmodel
    simpa only [Set.image_preimage_eq _ e.surjective] using hcov
  have marks {v : ℕ} (M : Fin v → Set (EuclideanSpace ℝ (Fin (n + 1))))
      (hgm : ∀ j i k, (g j i).realize ⊆ e ⁻¹' M k ∨ Disjoint (g j i).realize (e ⁻¹' M k))
      (hbm : ∀ j i k, (band j i).realize ⊆ e ⁻¹' M k ∨ Disjoint (band j i).realize (e ⁻¹' M k)) :
      ∀ i : I, ∀ k, (cells i).realize ⊆ M k ∨ Disjoint (cells i).realize (M k) := by
    have hmarks := s2v_hardt6rb_face_cell_marks L β e C r ψ hm g band hg hb
      (fun k => e ⁻¹' M k) hgm hbm parent hp w hagree
      (fun s a => (cells ⟨s, a⟩).realize) hmodel
    intro i k
    simpa only [Set.image_preimage_eq _ e.surjective] using hmarks i.1 i.2 k
  have hF := marks (fun _ : Fin 1 => f.realize) (fun j i _ => hGF j i) (fun j i _ => hBF j i)
  have hA := marks (fun k => (a k).realize) hGA hBA
  have hB := marks (fun k => (b k).realize) hGB hBB
  apply s2v_hardt6rb_refinement_of_finite_models f b a ha L β e G J hL hβ hβinj hG hJ
    cells (fun i => i.1) kind lower upper gLower gUpper hne hdis hcover
    (fun i => hF i 0) hA hB
  · rintro ⟨s, a⟩
    exact hw s _
  · rintro ⟨s, a⟩
    exact hw s _
  · rintro ⟨s, a⟩ x hx
    cases a with
    | inl j => exact le_rfl
    | inr p => exact hwm s x hx (by
        change p.val.1.val ≤ p.val.2.val
        have h := p.property
        omega)
  · rintro ⟨s, a⟩ hkind x hx
    cases a with
    | inl j => rfl
    | inr p => cases hkind
  · rintro ⟨s, a⟩ hkind x hx
    cases a with
    | inl j => cases hkind
    | inr p => exact hws s x hx (by
        change p.val.1.val < p.val.2.val
        have h := p.property
        omega)
  · rintro ⟨s, a⟩ z
    exact hH s _ z
  · rintro ⟨s, a⟩ z
    exact hH s _ z
  · rintro ⟨s, a⟩
    cases a with
    | inl j => exact (hcg s j).2.1
    | inr p => exact (hcb s p.val.1 p.val.2 p.property).2.1

end HodgeLean.Foundations.Program
