import HodgeLean.Foundations.Program.SchoenTowerHardtCad4Sub
import HodgeLean.Foundations.Program.SchoenTowerHardt2
import HodgeLean.Foundations.Program.SchoenTowerHardt3
import HodgeLean.Foundations.Program.SchoenTowerHardtCad1
import HodgeLean.Foundations.Program.SchoenTowerHardtCad2
import HodgeLean.Foundations.Program.SchoenTowerHardtCad3

/-! Ambient induction inputs and chart transport over checked construction units. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad4_pre_root_lift_aux {n k b : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (B : Fin b → s2v_t11b_Formula n) :
    ∃ m : ℕ, ∃ C : Fin m → s2v_t11b_Formula n,
      (∀ i, IsConnected (C i).realize) ∧
      Pairwise (fun i j => Disjoint (C i).realize (C j).realize) ∧
      (⋃ i, (C i).realize) = Set.univ ∧
      (∀ i j, (C i).realize ⊆ (B j).realize ∨
        Disjoint (C i).realize (B j).realize) ∧
      (∀ i j, (∀ a : (C i).realize,
        (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
        (∀ a : (C i).realize,
        (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0)) ∧
      ∀ i, ∃ r : ℕ, ∃ ψ : Fin r → (C i).realize → ℝ,
        (∀ q, Continuous (ψ q)) ∧ (∀ a, StrictMono (fun q => ψ q a)) ∧
        (∀ a t, (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
          (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔
          ∃ q, t = ψ q a) ∧
        ∃ g : Fin r → s2v_t11b_Formula (n + 1),
        ∃ band : Fin (r + 1) → s2v_t11b_Formula (n + 1),
          (∀ q y, y ∈ (g q).realize ↔ ∃ a : (C i).realize,
            (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a) ∧
          (∀ q y, y ∈ (band q).realize ↔ ∃ a : (C i).realize,
            (∀ v, y v.succ = a.val v) ∧
            (∀ j : Fin r, j.val < q.val → ψ j a < y 0) ∧
            (∀ j : Fin r, q.val ≤ j.val → y 0 < ψ j a)) ∧
          (∀ q, (band q).realize.Nonempty) ∧
          (∀ q, (g q).realize.Nonempty) := by
  obtain ⟨m, C, hc, hd, hu, hB, hz, hr⟩ := s2v_hardt_cad2_root_partition P B
  refine ⟨m, C, hc, hd, hu, hB, hz, ?_⟩
  intro i
  obtain ⟨r, ψ, hψ, hm, hr⟩ := hr i
  obtain ⟨g, hg⟩ := s2v_hardt_cad2_section_formulas P (C i) (hc i) ψ hψ hm hr
    (C i) (fun _ h => h)
  obtain ⟨band, hb⟩ := s2v_hardt_cad3_band_formulas (C i) ψ hm g hg
  obtain ⟨hn, hgn, rest⟩ := s2v_hardt_cad3_cylinder_partition
    (C i) ψ hm (hc i).nonempty g hg band hb
  exact ⟨r, ψ, hψ, hm, hr, g, band, hg, hb, hn, hgn⟩

theorem s2v_hardt_cad4_pre_zero_aux {k : ℕ}
    (B : Fin k → s2v_t11b_Formula 0) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula (0),
    ∃ dim : Fin m → ℕ,
    ∃ e : (i : Fin m) → (c i).realize ≃ₜ {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : (i : Fin m) → s2v_t11b_Formula ((0) + dim i),
    ∃ I : (i : Fin m) → s2v_t11b_Formula (dim i + (0)),
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = Set.univ ∧
      (∀ i, dim i ≤ 0) ∧
      (∀ i (x : (c i).realize) (z : EuclideanSpace ℝ (Fin (dim i))),
        WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ (F i).realize ↔
          z = (e i x).val) ∧
      (∀ i (z : {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1}) (x : EuclideanSpace ℝ (Fin (0))),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ (I i).realize ↔
          x = ((e i).symm z).val) ∧
      (∀ i j, (c i).realize ⊆ (B j).realize ∨
        Disjoint (c i).realize (B j).realize) := by
  classical
  let C : s2v_t11b_Formula 0 := .nonneg 0
  have hC : C.realize = Set.univ := by
    ext x
    simp [C, s2v_t11b_Formula.realize]
  letI : Unique C.realize := ⟨⟨0, by rw [hC]; trivial⟩, fun _ => Subsingleton.elim _ _⟩
  letI : Unique {z : EuclideanSpace ℝ (Fin 0) | ∀ v, -1 < z v ∧ z v < 1} :=
    ⟨⟨0, fun v => Fin.elim0 v⟩, fun _ => Subsingleton.elim _ _⟩
  let e := Homeomorph.homeomorphOfUnique C.realize
    {z : EuclideanSpace ℝ (Fin 0) | ∀ v, -1 < z v ∧ z v < 1}
  refine ⟨1, fun _ => C, fun _ => 0, fun _ => e,
    fun _ => .nonneg 0, fun _ => .nonneg 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact ⟨0, by rw [hC]; trivial⟩
  · intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
  · simp only [hC, Set.iUnion_const]
  · intro i; exact le_rfl
  · intro i x z
    simp only [s2v_t11b_Formula.realize, map_zero, Set.mem_setOf_eq, le_refl, true_iff]
    exact Subsingleton.elim _ _
  · intro i z x
    simp only [s2v_t11b_Formula.realize, map_zero, Set.mem_setOf_eq, le_refl, true_iff]
    exact Subsingleton.elim _ _
  · intro i j
    by_cases h : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (B j).realize
    · left; intro x hx; simpa only [Subsingleton.elim x 0] using h
    · right; rw [Set.disjoint_left]; intro x hx hb
      exact h (by simpa only [Subsingleton.elim x 0] using hb)

theorem s2v_hardt_cad4_pre_successor_aux {n k : ℕ}
    (ih : ∀ {k : ℕ} (B : Fin k → s2v_t11b_Formula n),
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula (n),
    ∃ dim : Fin m → ℕ,
    ∃ e : (i : Fin m) → (c i).realize ≃ₜ {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : (i : Fin m) → s2v_t11b_Formula ((n) + dim i),
    ∃ I : (i : Fin m) → s2v_t11b_Formula (dim i + (n)),
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = Set.univ ∧
      (∀ i, dim i ≤ n) ∧
      (∀ i (x : (c i).realize) (z : EuclideanSpace ℝ (Fin (dim i))),
        WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ (F i).realize ↔
          z = (e i x).val) ∧
      (∀ i (z : {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1}) (x : EuclideanSpace ℝ (Fin (n))),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ (I i).realize ↔
          x = ((e i).symm z).val) ∧
      (∀ i j, (c i).realize ⊆ (B j).realize ∨
        Disjoint (c i).realize (B j).realize))
    (B : Fin k → s2v_t11b_Formula (n + 1)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula (n + 1),
    ∃ dim : Fin m → ℕ,
    ∃ e : (i : Fin m) → (c i).realize ≃ₜ {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : (i : Fin m) → s2v_t11b_Formula ((n + 1) + dim i),
    ∃ I : (i : Fin m) → s2v_t11b_Formula (dim i + (n + 1)),
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = Set.univ ∧
      (∀ i, dim i ≤ n + 1) ∧
      (∀ i (x : (c i).realize) (z : EuclideanSpace ℝ (Fin (dim i))),
        WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ (F i).realize ↔
          z = (e i x).val) ∧
      (∀ i (z : {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1}) (x : EuclideanSpace ℝ (Fin (n + 1))),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ (I i).realize ↔
          x = ((e i).symm z).val) ∧
      (∀ i j, (c i).realize ⊆ (B j).realize ∨
        Disjoint (c i).realize (B j).realize) ∧
      ∃ b : ℕ, ∃ C : Fin b → s2v_t11b_Formula n,
      ∃ d : Fin b → ℕ,
      ∃ baseChart : (j : Fin b) → (C j).realize ≃ₜ
        {z : EuclideanSpace ℝ (Fin (d j)) | ∀ v, -1 < z v ∧ z v < 1},
      ∃ baseForward : (j : Fin b) → s2v_t11b_Formula (n + d j),
      ∃ baseInverse : (j : Fin b) → s2v_t11b_Formula (d j + n),
      ∃ parent : Fin m → Fin b,
        (∀ j (a : (C j).realize) (z : EuclideanSpace ℝ (Fin (d j))),
          WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈
            (baseForward j).realize ↔ z = (baseChart j a).val) ∧
        (∀ j (z : {z : EuclideanSpace ℝ (Fin (d j)) | ∀ v, -1 < z v ∧ z v < 1})
            (a : EuclideanSpace ℝ (Fin n)),
          WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => a v)) ∈
            (baseInverse j).realize ↔ a = ((baseChart j).symm z).val) ∧
        (∀ j, (C j).realize.Nonempty) ∧
        Pairwise (fun i j => Disjoint (C i).realize (C j).realize) ∧
        (⋃ j, (C j).realize) = Set.univ ∧
        (∀ j, d j ≤ n) ∧
        (∀ i, (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
          WithLp.toLp 2 (fun v : Fin n => y v.succ)) '' (c i).realize =
            (C (parent i)).realize) ∧
        (∀ i, (dim i = d (parent i) ∧
            ∃ s : (C (parent i)).realize → ℝ, Continuous s ∧
              ∀ y, y ∈ (c i).realize ↔ ∃ a : (C (parent i)).realize,
                (∀ v, y v.succ = a.val v) ∧ y 0 = s a) ∨
          (dim i = d (parent i) + 1 ∧
            ∀ a : (C (parent i)).realize,
              let fiber := {t : ℝ | WithLp.toLp 2
                (Fin.cons t (fun v => a.val v)) ∈ (c i).realize}
              fiber.Nonempty ∧ IsOpen fiber ∧ Set.OrdConnected fiber)) := by
  classical
  let atoms := Finset.univ.biUnion (fun j : Fin k => (B j).atoms)
  let enum := (Fintype.equivFin {q // q ∈ atoms}).symm
  let P : Fin (Fintype.card {q // q ∈ atoms}) →
      Polynomial (MvPolynomial (Fin n) ℝ) := fun j =>
    MvPolynomial.finSuccEquiv ℝ n (enum j).val
  obtain ⟨b, C, hC, hdisj, hcover, hmarks, hzero, hlift⟩ :=
    s2v_hardt_cad4_pre_root_lift_aux P (fun j : Fin 0 => Fin.elim0 j)
  choose r ψ hψ hm hr g band hg hb hbn hgn using hlift
  obtain ⟨s, D, hDu, hDd, hDn, hDs, l, base, d, chart, forward, inverse,
    hn, hd, hu, hc, hdim, hF, hI, hrespect, hsignRespect,
    parent, into, roots, hinto, hroots, hcont, hmono, hroot, hz, hs⟩ :=
    s2v_hardt_cad4_sub_prepare ih P C hC hdisj hcover r ψ hψ hm g hg hzero hr
  apply s2v_hardt_cad4_sub_assemble B base d chart forward inverse hn hd hu hdim hF hI
  intro j
  obtain ⟨graphs, hgraphs⟩ := s2v_hardt_cad2_section_formulas P (base j) (hc j)
    (roots j) (hcont j) (hmono j) (hroot j) (base j) (fun _ h => h)
  have hatoms : ∀ j q, q ∈ (B j).atoms → ∃ p, MvPolynomial.finSuccEquiv ℝ n q = P p := by
    intro j q hq
    have hmem : q ∈ atoms := Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hq⟩
    refine ⟨(Fintype.equivFin {q // q ∈ atoms}) ⟨q, hmem⟩, ?_⟩
    simp only [P, enum, Equiv.symm_apply_apply]
  obtain ⟨m, c, dim, e, F, I, hcn, hcd, hcu, hcf, hci, hcb, hsign,
    kind, hkind, hkindDim, hproj, hfiber⟩ :=
    s2v_hardt_cad4_sub_lift P (base j) (hc j) (chart j) (forward j) (hF j)
      (roots j) (hcont j) (hmono j) graphs hgraphs (hz j) (hroot j) (hs j) B hatoms
  exact ⟨m, c, dim, e, F, I, hcn, hcd, hcu, hcf, hci, hcb, hproj, hfiber⟩

theorem s2v_hardt_cad4_pre_images_aux {n d k : ℕ}
    (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ x : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ G.realize ↔
        z = (e x).val)
    (B : Fin k → s2v_t11b_Formula n) :
    ∃ A : Fin k → s2v_t11b_Formula d, ∀ j z,
      z ∈ (A j).realize ↔ ∃ x : C.realize,
        x.val ∈ (B j).realize ∧ z = (e x).val := by
  classical
  let u := s2v_hardt2_boundIndex d n
  let v := s2v_hardt2_freeIndex d n
  let ρ : Fin (n + d) → Fin (d + n) := Fin.addCases u v
  let Q : Fin k → s2v_t11b_Formula (d + n) := fun j =>
    .inter (s2v_hardt1_rename u C)
      (.inter (s2v_hardt1_rename u (B j)) (s2v_hardt1_rename ρ G))
  choose A hA using fun j => s2v_hardt2_repeated_projection (Q j)
  refine ⟨A, ?_⟩
  intro j z
  rw [hA]
  have hcoords (y : Fin n → ℝ) :
      WithLp.toLp 2 (fun i => s2v_hardt2_insert n y z (ρ i)) =
        WithLp.toLp 2 (Fin.append y (fun i => z i)) := by
    ext i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simp only [ρ, Fin.addCases_left, u, s2v_hardt2_insert_bound, Fin.append_left]
    · simp only [ρ, Fin.addCases_right, v, s2v_hardt2_insert_free, Fin.append_right]
  have hbase (y : Fin n → ℝ) :
      WithLp.toLp 2 (fun i => s2v_hardt2_insert n y z (u i)) =
        WithLp.toLp 2 y := by
    ext i
    exact s2v_hardt2_insert_bound y z i
  constructor
  · rintro ⟨y, hy⟩
    change (_ ∧ _ ∧ _) at hy
    rw [s2v_hardt1_realize_rename, hbase] at hy
    rw [s2v_hardt1_realize_rename, hbase,
      s2v_hardt1_realize_rename, hcoords] at hy
    exact ⟨⟨WithLp.toLp 2 y, hy.1⟩, hy.2.1,
      (hG ⟨WithLp.toLp 2 y, hy.1⟩ z).mp hy.2.2⟩
  · rintro ⟨x, hx, hz⟩
    refine ⟨fun i => x.val i, ?_⟩
    change (_ ∧ _ ∧ _)
    rw [s2v_hardt1_realize_rename, hbase]
    rw [s2v_hardt1_realize_rename, hbase,
      s2v_hardt1_realize_rename, hcoords]
    exact ⟨x.property, hx, (hG x z).mpr hz⟩

theorem s2v_hardt_cad4_pre_transport_aux {n d k : ℕ}
    (ih : ∀ {k : ℕ} (B : Fin k → s2v_t11b_Formula d),
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula (d),
    ∃ dim : Fin m → ℕ,
    ∃ e : (i : Fin m) → (c i).realize ≃ₜ {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : (i : Fin m) → s2v_t11b_Formula ((d) + dim i),
    ∃ I : (i : Fin m) → s2v_t11b_Formula (dim i + (d)),
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = Set.univ ∧
      (∀ i, dim i ≤ d) ∧
      (∀ i (x : (c i).realize) (z : EuclideanSpace ℝ (Fin (dim i))),
        WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ (F i).realize ↔
          z = (e i x).val) ∧
      (∀ i (z : {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1}) (x : EuclideanSpace ℝ (Fin (d))),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ (I i).realize ↔
          x = ((e i).symm z).val) ∧
      (∀ i j, (c i).realize ⊆ (B j).realize ∨
        Disjoint (c i).realize (B j).realize))
    (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ {z : EuclideanSpace ℝ (Fin (d)) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ x : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ G.realize ↔
        z = (e x).val)
    (J : s2v_t11b_Formula (d + n))
    (hJ : ∀ z : {z : EuclideanSpace ℝ (Fin (d)) | ∀ v, -1 < z v ∧ z v < 1}, ∀ x : EuclideanSpace ℝ (Fin n),
      WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ J.realize ↔
        x = (e.symm z).val)
    (B : Fin k → s2v_t11b_Formula n) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula (n),
    ∃ dim : Fin m → ℕ,
    ∃ E : (i : Fin m) → (c i).realize ≃ₜ {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : (i : Fin m) → s2v_t11b_Formula ((n) + dim i),
    ∃ I : (i : Fin m) → s2v_t11b_Formula (dim i + (n)),
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = C.realize ∧
      (∀ i, dim i ≤ d) ∧
      (∀ i (x : (c i).realize) (z : EuclideanSpace ℝ (Fin (dim i))),
        WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ (F i).realize ↔
          z = (E i x).val) ∧
      (∀ i (z : {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1}) (x : EuclideanSpace ℝ (Fin (n))),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ (I i).realize ↔
          x = ((E i).symm z).val) ∧
      (∀ i j, (c i).realize ⊆ (B j).realize ∨
        Disjoint (c i).realize (B j).realize) ∧
      ∃ H : Fin m → s2v_t11b_Formula d,
      ∃ chart : (i : Fin m) → (H i).realize ≃ₜ
        {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1},
      ∃ toC : ∀ i, (c i).realize → C.realize,
      ∃ toH : ∀ i, (c i).realize → (H i).realize,
      ∃ intoBox : ∀ i, (H i).realize →
        {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1},
        (∀ i z, (intoBox i z).val = z.val) ∧
        (∀ i x, (toC i x).val = x.val) ∧
        (∀ i x, (toH i x).val = (e (toC i x)).val) ∧
        (∀ i, (H i).realize = {z | ∃ x : (c i).realize,
          z = (e (toC i x)).val}) ∧
        (∀ i z, e (toC i ((E i).symm z)) = intoBox i ((chart i).symm z)) ∧
        (∀ i z, ((E i).symm z).val =
          (e.symm (intoBox i ((chart i).symm z))).val) ∧
        (∀ i x, E i x = chart i (toH i x)) := by
  obtain ⟨A, hA⟩ := s2v_hardt_cad4_pre_images_aux C e G hG B
  classical
  obtain ⟨box, hbox, m, H, dim, chart, forward, inverse,
    hn, hd, hu, hF, hI, hdim, hmarks, hboxMarks,
    l, keep, c, toC, intoBox, pull, hkeep, hselection, htoC, hinto,
    hpull, hpullInv, hmembership, hcn, hcd, hcu, hcb, himage⟩ :=
    s2v_hardt_cad4_sub_pullback ih C e G hG J hJ B A hA
  have composites := fun i : Fin l =>
    s2v_hardt_cad4_sub_compose C e G hG J hJ (c i) (H (keep i))
      (toC i) (htoC i) (intoBox i) (hinto i) (pull i) (hpull i) (hpullInv i)
      (chart (keep i)) (forward (keep i)) (hF (keep i))
      (inverse (keep i)) (hI (keep i))
  choose E F I hEF hEI hE hEinv hEval using composites
  refine ⟨l, c, fun i => dim (keep i), E, F, I, hcn, hcd, hcu,
    (fun i => hdim (keep i)), hEF, hEI, hcb,
    (fun i => H (keep i)), (fun i => chart (keep i)), toC,
    (fun i => pull i), intoBox, hinto, htoC, hpull, himage, hEinv, hEval, hE⟩

#print axioms s2v_hardt_cad4_pre_zero_aux
#print axioms s2v_hardt_cad4_pre_root_lift_aux
#print axioms s2v_hardt_cad4_pre_images_aux
end HodgeLean.Foundations.Program
