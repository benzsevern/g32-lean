import HodgeLean.Foundations.Program.SchoenTowerHardt2
import HodgeLean.Foundations.Program.SchoenTowerHardt3
import HodgeLean.Foundations.Program.SchoenTowerHardtCad1
import HodgeLean.Foundations.Program.SchoenTowerHardtCad2
import HodgeLean.Foundations.Program.SchoenTowerHardtCad3

/-! Implication from explicit lower-dimensional partitions and checked root geometry.
The five construction interfaces separate base signs, local lifts, finite indexing,
box pullbacks and graph composition. HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad4_sub_prepare_aux {n k b : ℕ}
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
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (C : Fin b → s2v_t11b_Formula n)
    (hC : ∀ i, IsConnected (C i).realize)
    (hdisj : Pairwise (fun i j => Disjoint (C i).realize (C j).realize))
    (hcover : (⋃ i, (C i).realize) = Set.univ)
    (r : Fin b → ℕ) (ψ : (i : Fin b) → Fin (r i) → (C i).realize → ℝ)
    (hψ : ∀ i q, Continuous (ψ i q))
    (hm : ∀ i a, StrictMono (fun q => ψ i q a))
    (g : (i : Fin b) → Fin (r i) → s2v_t11b_Formula (n + 1))
    (hg : ∀ i q y, y ∈ (g i q).realize ↔ ∃ a : (C i).realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ i q a)
    (hz : ∀ i j, (∀ a : (C i).realize,
      (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
      (∀ a : (C i).realize,
      (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0))
    (hr : ∀ i a t, (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
      (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔
        ∃ q, t = ψ i q a)
    : ∃ s : Fin b → ℕ, ∃ D : (i : Fin b) → Fin (s i) → s2v_t11b_Formula n,
      (∀ i, (⋃ j, (D i j).realize) = (C i).realize) ∧
      (∀ i, Pairwise (fun j l => Disjoint (D i j).realize (D i l).realize)) ∧
      (∀ i j, (D i j).realize.Nonempty) ∧
      (∀ i j q p, (∀ a : (C i).realize, a.val ∈ (D i j).realize → (P p).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ i q a) < 0) ∨
        (∀ a : (C i).realize, a.val ∈ (D i j).realize → (P p).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ i q a) = 0) ∨
        (∀ a : (C i).realize, a.val ∈ (D i j).realize → 0 < (P p).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ i q a))) ∧
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula (n),
    ∃ dim : Fin m → ℕ,
    ∃ e : (i : Fin m) → (c i).realize ≃ₜ {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : (i : Fin m) → s2v_t11b_Formula ((n) + dim i),
    ∃ I : (i : Fin m) → s2v_t11b_Formula (dim i + (n)),
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = Set.univ ∧
      (∀ i, IsConnected (c i).realize) ∧
      (∀ i, dim i ≤ n) ∧
      (∀ i (x : (c i).realize) (z : EuclideanSpace ℝ (Fin (dim i))),
        WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ (F i).realize ↔
          z = (e i x).val) ∧
      (∀ i (z : {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1}) (x : EuclideanSpace ℝ (Fin (n))),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ (I i).realize ↔
          x = ((e i).symm z).val) ∧
      (∀ i j, (c i).realize ⊆ (C j).realize ∨ Disjoint (c i).realize (C j).realize) ∧
      (∀ i j l, (c i).realize ⊆ (D j l).realize ∨ Disjoint (c i).realize (D j l).realize) ∧
      ∃ parent : Fin m → Fin b,
      ∃ into : (i : Fin m) → (c i).realize → (C (parent i)).realize,
      ∃ roots : (i : Fin m) → Fin (r (parent i)) → (c i).realize → ℝ,
        (∀ i a, (into i a).val = a.val) ∧
        (∀ i q a, roots i q a = ψ (parent i) q (into i a)) ∧
        (∀ i q, Continuous (roots i q)) ∧
        (∀ i a, StrictMono (fun q => roots i q a)) ∧
        (∀ i a t, (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
          (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔
          ∃ q, t = roots i q a) ∧
        (∀ i j, (∀ a : (c i).realize,
          (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
          (∀ a : (c i).realize,
          (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0)) ∧
        (∀ i q j, (∀ a : (c i).realize, (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (roots i q a) < 0) ∨
        (∀ a : (c i).realize, (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (roots i q a) = 0) ∨
        (∀ a : (c i).realize, 0 < (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (roots i q a))) := by
  classical
  have refineSigns (i : Fin b) :=
    s2v_hardt_cad3_section_sign_refinement (C i) (ψ i) (hm i) (g i) (hg i) P
  choose s D hDn hDd hDu hDs using refineSigns
  let T := Fin b ⊕ ((i : Fin b) × Fin (s i))
  let enum := (Fintype.equivFin T).symm
  let marks : Fin (Fintype.card T) → s2v_t11b_Formula n := fun t =>
    match enum t with
    | .inl i => C i
    | .inr ij => D ij.1 ij.2
  obtain ⟨m, c, dim, e, F, I, hn, hd, hu, hdim, hF, hI, ha⟩ := ih marks
  have haC (i : Fin m) (j : Fin b) :
      (c i).realize ⊆ (C j).realize ∨ Disjoint (c i).realize (C j).realize := by
    simpa only [marks, enum, Equiv.symm_apply_apply] using
      ha i ((Fintype.equivFin T) (.inl j))
  have haD (i : Fin m) (j : Fin b) (l : Fin (s j)) :
      (c i).realize ⊆ (D j l).realize ∨ Disjoint (c i).realize (D j l).realize := by
    simpa only [marks, enum, Equiv.symm_apply_apply] using
      ha i ((Fintype.equivFin T) (.inr ⟨j,l⟩))
  have parentExists (i : Fin m) : ∃ j, (c i).realize ⊆ (C j).realize := by
    obtain ⟨x, hx⟩ := hn i
    have : x ∈ ⋃ j, (C j).realize := by rw [hcover]; trivial
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp this
    rcases haC i j with h | h
    · exact ⟨j, h⟩
    · exact False.elim (Set.disjoint_left.mp h hx hj)
  choose parent hp using parentExists
  let into (i : Fin m) (a : (c i).realize) : (C (parent i)).realize := ⟨a.val, hp i a.property⟩
  let roots (i : Fin m) (q : Fin (r (parent i))) (a : (c i).realize) :=
    ψ (parent i) q (into i a)
  have hcconn (i : Fin m) : IsConnected (c i).realize := by
    have hconv : Convex ℝ {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1} := by
      apply convex_iff_forall_pos.mpr
      intro x hx y hy a b ha hb hab v
      change -1 < a * x v + b * y v ∧ a * x v + b * y v < 1
      constructor
      · nlinarith [mul_pos ha (sub_pos.mpr (hx v).1), mul_pos hb (sub_pos.mpr (hy v).1)]
      · nlinarith [mul_pos ha (sub_pos.mpr (hx v).2), mul_pos hb (sub_pos.mpr (hy v).2)]
    have hb := hconv.isConnected ⟨0, by intro v; simp⟩
    exact isConnected_iff_connectedSpace.mpr
      ((e i).connectedSpace_iff.mpr (Subtype.connectedSpace hb))
  refine ⟨s, D, hDu, hDd, hDn, hDs, m, c, dim, e, F, I,
    hn, hd, hu, hcconn, hdim, hF, hI, haC, haD, parent, into, roots,
    (fun _ _ => rfl), (fun _ _ _ => rfl), ?_, ?_, ?_, ?_, ?_⟩
  · intro i q
    exact (hψ (parent i) q).comp (continuous_subtype_val.subtype_mk _)
  · intro i a
    exact hm (parent i) (into i a)
  · intro i a t
    exact hr (parent i) (into i a) t
  · intro i j
    exact hz (parent i) j |>.imp (fun h a => h (into i a)) (fun h a => h (into i a))
  · intro i q j
    obtain ⟨x, hx⟩ := hn i
    have hxC := hp i hx
    have hxD : x ∈ ⋃ l, (D (parent i) l).realize := by rw [hDu]; exact hxC
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hxD
    have hsub : (c i).realize ⊆ (D (parent i) l).realize := by
      rcases haD i (parent i) l with h | h
      · exact h
      · exact False.elim (Set.disjoint_left.mp h hx hl)
    rcases hDs (parent i) l q j with h | h | h
    · exact Or.inl (fun a => h (into i a) (hsub a.property))
    · exact Or.inr (Or.inl (fun a => h (into i a) (hsub a.property)))
    · exact Or.inr (Or.inr (fun a => h (into i a) (hsub a.property)))


theorem s2v_hardt_cad4_sub_lower {X : Type*} {r : ℕ}
    (ψ : Fin r → X → ℝ) (hm : ∀ a, StrictMono (fun q => ψ q a))
    (i : Fin (r + 1)) (hi : 0 < i.val) (a : X) (t : ℝ) :
    (∀ j : Fin r, j.val < i.val → ψ j a < t) ↔
      ψ ⟨i.val - 1, by omega⟩ a < t := by
  constructor
  · intro h
    exact h _ (by simp only; omega)
  · intro h j hj
    exact lt_of_le_of_lt ((hm a).monotone (show j ≤ ⟨i.val - 1, by omega⟩ by
      change j.val ≤ i.val - 1; omega)) h

theorem s2v_hardt_cad4_sub_upper {X : Type*} {r : ℕ}
    (ψ : Fin r → X → ℝ) (hm : ∀ a, StrictMono (fun q => ψ q a))
    (i : Fin (r + 1)) (hi : i.val < r) (a : X) (t : ℝ) :
    (∀ j : Fin r, i.val ≤ j.val → t < ψ j a) ↔
      t < ψ ⟨i.val, hi⟩ a := by
  constructor
  · intro h
    exact h _ (by rfl)
  · intro h j hj
    exact lt_of_lt_of_le h ((hm a).monotone (show (⟨i.val, hi⟩ : Fin r) ≤ j from hj))

theorem s2v_hardt_cad4_sub_band_chart {n d r : ℕ}
    (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔ z = (e a).val)
    (ψ : Fin r → C.realize → ℝ) (hψ : ∀ q, Continuous (ψ q))
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ q y, y ∈ (g q).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a)
    (i : Fin (r + 1)) (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧
      (∀ j : Fin r, j.val < i.val → ψ j a < y 0) ∧
      (∀ j : Fin r, i.val ≤ j.val → y 0 < ψ j a)) :
    ∃ E : b.realize ≃ₜ {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula ((n + 1) + (d + 1)),
    ∃ I : s2v_t11b_Formula ((d + 1) + (n + 1)),
      (∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin (d + 1)),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔ z = (E y).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
        ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔ y = (E.symm z).val) := by
  by_cases hr : r = 0
  · subst r
    have hb' : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
        (∀ v, y v.succ = a.val v) ∧ True := by
      intro y
      simpa only [Fin.forall_fin_zero, true_and] using hb y
    obtain ⟨E, F, I, _, hF, hI⟩ := s2v_hardt_cad3_whole_chart C e G hG b hb'
    exact ⟨E, F, I, hF, hI⟩
  · by_cases hi : i.val = 0
    · let q : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
      have hb' : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
          (∀ v, y v.succ = a.val v) ∧ (if false then ψ q a < y 0 else y 0 < ψ q a) := by
        intro y
        rw [hb]
        apply exists_congr
        intro a
        apply and_congr_right
        intro _
        have hlo : (∀ j : Fin r, j.val < i.val → ψ j a < y 0) := by
          intro j hj; omega
        simp only [Bool.false_eq_true, ite_false, and_iff_right hlo]
        simpa only [hi] using s2v_hardt_cad4_sub_upper ψ hm i (by omega) a (y 0)
      obtain ⟨E, F, I, _, hF, hI⟩ := s2v_hardt_cad3_ray_chart C e G hG
        (ψ q) (hψ q) false (g q) (hg q) b hb'
      exact ⟨E, F, I, hF, hI⟩
    · by_cases hir : i.val < r
      · let l : Fin r := ⟨i.val - 1, by omega⟩
        let u : Fin r := ⟨i.val, hir⟩
        have hb' : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
            (∀ v, y v.succ = a.val v) ∧ ψ l a < y 0 ∧ y 0 < ψ u a := by
          intro y
          rw [hb]
          apply exists_congr
          intro a
          exact and_congr Iff.rfl (and_congr
            (s2v_hardt_cad4_sub_lower ψ hm i (by omega) a (y 0))
            (s2v_hardt_cad4_sub_upper ψ hm i hir a (y 0)))
        obtain ⟨E, F, I, _, hF, hI⟩ := s2v_hardt_cad3_bounded_chart C e G hG
          (ψ l) (ψ u) (hψ l) (hψ u) (fun a => hm a (by change i.val - 1 < i.val; omega))
          (g l) (g u) (hg l) (hg u) b hb'
        exact ⟨E, F, I, hF, hI⟩
      · let q : Fin r := ⟨i.val - 1, by omega⟩
        have hb' : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
            (∀ v, y v.succ = a.val v) ∧ (if true then ψ q a < y 0 else y 0 < ψ q a) := by
          intro y
          rw [hb]
          apply exists_congr
          intro a
          apply and_congr_right
          intro _
          have hhi : (∀ j : Fin r, i.val ≤ j.val → y 0 < ψ j a) := by
            intro j hj; omega
          simp only [ite_true, and_iff_left hhi]
          exact s2v_hardt_cad4_sub_lower ψ hm i (by omega) a (y 0)
        obtain ⟨E, F, I, _, hF, hI⟩ := s2v_hardt_cad3_ray_chart C e G hG
          (ψ q) (hψ q) true (g q) (hg q) b hb'
        exact ⟨E, F, I, hF, hI⟩

theorem s2v_hardt_cad4_sub_lift_aux {n d r k h : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (C : s2v_t11b_Formula n) (hC : IsConnected C.realize)
    (e : C.realize ≃ₜ {z : EuclideanSpace ℝ (Fin (d)) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔
        z = (e a).val)
    (ψ : Fin r → C.realize → ℝ) (hψ : ∀ q, Continuous (ψ q))
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ q y, y ∈ (g q).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a)
    (hz : ∀ j, (∀ a : C.realize,
      (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
      (∀ a : C.realize,
      (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0))
    (hr : ∀ a : C.realize, ∀ t, (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
      (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔
        ∃ q, t = ψ q a)
    (hs : ∀ q j, (∀ a : C.realize, (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) < 0) ∨
        (∀ a : C.realize, (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) = 0) ∨
        (∀ a : C.realize, 0 < (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a)))
    (B : Fin h → s2v_t11b_Formula (n + 1))
    (hB : ∀ j q, q ∈ (B j).atoms → ∃ p, MvPolynomial.finSuccEquiv ℝ n q = P p) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula (n + 1),
    ∃ dim : Fin m → ℕ,
    ∃ e : (i : Fin m) → (c i).realize ≃ₜ {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : (i : Fin m) → s2v_t11b_Formula ((n + 1) + dim i),
    ∃ I : (i : Fin m) → s2v_t11b_Formula (dim i + (n + 1)),
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = {y | ∃ a : C.realize, ∀ v, y v.succ = a.val v} ∧
      (∀ i (x : (c i).realize) (z : EuclideanSpace ℝ (Fin (dim i))),
        WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ (F i).realize ↔
          z = (e i x).val) ∧
      (∀ i (z : {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1}) (x : EuclideanSpace ℝ (Fin (n + 1))),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ (I i).realize ↔
          x = ((e i).symm z).val) ∧
      (∀ i j, (c i).realize ⊆ (B j).realize ∨ Disjoint (c i).realize (B j).realize) ∧
      (∀ i j, (∀ y ∈ (c i).realize, (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0) < 0) ∨
        (∀ y ∈ (c i).realize, (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0) = 0) ∨
        (∀ y ∈ (c i).realize, 0 < (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0))) ∧
      ∃ kind : Fin m ≃ (Fin r ⊕ Fin (r + 1)),
        (∀ i y, y ∈ (c i).realize ↔ ∃ a : C.realize,
          (∀ v, y v.succ = a.val v) ∧
          match kind i with
          | .inl q => y 0 = ψ q a
          | .inr q => (∀ j : Fin r, j.val < q.val → ψ j a < y 0) ∧
              (∀ j : Fin r, q.val ≤ j.val → y 0 < ψ j a)) ∧
        (∀ i, dim i = match kind i with | .inl _ => d | .inr _ => d + 1) ∧
        (∀ i, (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
          WithLp.toLp 2 (fun v : Fin n => y v.succ)) '' (c i).realize = C.realize) ∧
        (∀ i, (dim i = d ∧ ∃ s : C.realize → ℝ, Continuous s ∧
          ∀ y, y ∈ (c i).realize ↔ ∃ a : C.realize,
            (∀ v, y v.succ = a.val v) ∧ y 0 = s a) ∨
          (dim i = d + 1 ∧ ∀ a : C.realize,
            let fiber := {t : ℝ | WithLp.toLp 2 (Fin.cons t (fun v => a.val v)) ∈ (c i).realize}
            fiber.Nonempty ∧ IsOpen fiber ∧ Set.OrdConnected fiber)) := by
  classical
  obtain ⟨b, hb⟩ := s2v_hardt_cad3_band_formulas C ψ hm g hg
  obtain ⟨hbn, hgn, hbd, hgd, hbg, hcover, _⟩ :=
    s2v_hardt_cad3_cylinder_partition C ψ hm hC.nonempty g hg b hb
  have hbs := s2v_hardt_cad3_band_signs C ψ hm hC hψ P hz (fun a t => (hr a t).symm) b hb
  let J := Fin r ⊕ Fin (r + 1)
  let cells : J → s2v_t11b_Formula (n + 1) := Sum.elim g b
  let dims : J → ℕ := Sum.elim (fun _ => d) (fun _ => d + 1)
  have charts (j : J) :
      ∃ E : (cells j).realize ≃ₜ {z : EuclideanSpace ℝ (Fin (dims j)) | ∀ v, -1 < z v ∧ z v < 1},
      ∃ F : s2v_t11b_Formula ((n + 1) + dims j),
      ∃ I : s2v_t11b_Formula (dims j + (n + 1)),
        (∀ x : (cells j).realize, ∀ z : EuclideanSpace ℝ (Fin (dims j)),
          WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ F.realize ↔ z = (E x).val) ∧
        (∀ z : {z : EuclideanSpace ℝ (Fin (dims j)) | ∀ v, -1 < z v ∧ z v < 1},
          ∀ x : EuclideanSpace ℝ (Fin (n + 1)),
          WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ I.realize ↔ x = (E.symm z).val) := by
    cases j with
    | inl q =>
      obtain ⟨E, F, I, _, hF, hI⟩ := s2v_hardt_cad2_graph_chart_formulas C e (ψ q) (hψ q) (g q) (hg q) G hG
      exact ⟨E, F, I, hF, hI⟩
    | inr q => exact s2v_hardt_cad4_sub_band_chart C e G hG ψ hψ hm g hg q (b q) (hb q)
  choose E F I hF hI using charts
  have hsign (i : J) (j : Fin k) :
      (∀ y ∈ (cells i).realize, (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0) < 0) ∨
      (∀ y ∈ (cells i).realize, (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0) = 0) ∨
      (∀ y ∈ (cells i).realize, 0 < (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0)) := by
    cases i with
    | inr q => exact hbs q j
    | inl q =>
      have transfer (y : EuclideanSpace ℝ (Fin (n + 1))) (hy : y ∈ (g q).realize) :
          ∃ a : C.realize, (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0) =
            (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) := by
        obtain ⟨a, ha, ht⟩ := (hg q y).mp hy
        exact ⟨a, by rw [ht, show (fun v => y v.succ) = (fun v => a.val v) from funext ha]⟩
      rcases hs q j with h | h | h
      · exact Or.inl (fun y hy => by obtain ⟨a, he⟩ := transfer y hy; rw [he]; exact h a)
      · exact Or.inr (Or.inl (fun y hy => by obtain ⟨a, he⟩ := transfer y hy; rw [he]; exact h a))
      · exact Or.inr (Or.inr (fun y hy => by obtain ⟨a, he⟩ := transfer y hy; rw [he]; exact h a))
  have hadapt (i : J) (j : Fin h) :
      (cells i).realize ⊆ (B j).realize ∨ Disjoint (cells i).realize (B j).realize := by
    have hn : (cells i).realize.Nonempty := by cases i with | inl q => exact hgn q | inr q => exact hbn q
    obtain ⟨x, hx⟩ := hn
    have constant (y : EuclideanSpace ℝ (Fin (n + 1))) (hy : y ∈ (cells i).realize) :
        y ∈ (B j).realize ↔ x ∈ (B j).realize := by
      apply s2v_t11b_formula_membership_of_atom_signs
      intro Q hQ
      obtain ⟨p, hp⟩ := hB j Q hQ
      have evaleq (z : EuclideanSpace ℝ (Fin (n + 1))) :
          MvPolynomial.eval (fun v => z v) Q =
            (P p).eval₂ (MvPolynomial.eval (fun v => z v.succ)) (z 0) := by
        rw [← hp, s2v_t11b_finSucc_family_eval Q (WithLp.toLp 2 (fun v => z v.succ)) (z 0)]
        exact congrArg (fun f => MvPolynomial.eval f Q)
          (funext (fun v => Fin.cases rfl (fun _ => rfl) v))
      rw [evaleq y, evaleq x]
      rcases hsign i p with h | h | h
      · exact iff_of_false (not_le.mpr (h y hy)) (not_le.mpr (h x hx))
      · rw [h y hy, h x hx]
      · exact iff_of_true (le_of_lt (h y hy)) (le_of_lt (h x hx))
    by_cases hxB : x ∈ (B j).realize
    · exact Or.inl (fun y hy => (constant y hy).mpr hxB)
    · exact Or.inr (Set.disjoint_left.mpr (fun y hy hB => hxB ((constant y hy).mp hB)))
  have hprojection (i : J) :
      (fun y : EuclideanSpace ℝ (Fin (n + 1)) => WithLp.toLp 2 (fun v : Fin n => y v.succ)) ''
        (cells i).realize = C.realize := by
    ext a
    constructor
    · rintro ⟨y, hy, rfl⟩
      cases i with
      | inl q =>
        obtain ⟨a, ha, _⟩ := (hg q y).mp hy
        have he : WithLp.toLp 2 (fun v => y v.succ) = a.val := by ext v; exact ha v
        change WithLp.toLp 2 (fun v => y v.succ) ∈ C.realize
        rw [he]
        exact a.property
      | inr q =>
        obtain ⟨a, ha, _, _⟩ := (hb q y).mp hy
        have he : WithLp.toLp 2 (fun v => y v.succ) = a.val := by ext v; exact ha v
        change WithLp.toLp 2 (fun v => y v.succ) ∈ C.realize
        rw [he]
        exact a.property
    · intro ha
      cases i with
      | inl q =>
        refine ⟨WithLp.toLp 2 (Fin.cons (ψ q ⟨a, ha⟩) (fun v => a v)),
          (hg q _).mpr ⟨⟨a, ha⟩, (fun _ => rfl), rfl⟩, ?_⟩
        ext v; rfl
      | inr q =>
        obtain ⟨f, _, hf⟩ := s2v_hardt_cad3_continuous_height ψ hm hψ q
        refine ⟨WithLp.toLp 2 (Fin.cons (f ⟨a, ha⟩) (fun v => a v)),
          (hb q _).mpr ⟨⟨a, ha⟩, (fun _ => rfl), hf ⟨a, ha⟩⟩, ?_⟩
        ext v; rfl
  have hfib (i : Fin (r + 1)) (a : C.realize) :
      let fiber := {t : ℝ | WithLp.toLp 2 (Fin.cons t (fun v => a.val v)) ∈ (b i).realize}
      fiber.Nonempty ∧ IsOpen fiber ∧ Set.OrdConnected fiber := by
    have he : {t : ℝ | WithLp.toLp 2 (Fin.cons t (fun v => a.val v)) ∈ (b i).realize} =
        {t | (∀ j : Fin r, j.val < i.val → ψ j a < t) ∧
          (∀ j : Fin r, i.val ≤ j.val → t < ψ j a)} := by
      ext t
      rw [Set.mem_setOf_eq, hb]
      constructor
      · rintro ⟨a', ha', ht⟩
        have haa : a' = a := by apply Subtype.ext; ext v; exact (ha' v).symm
        simpa only [haa, Fin.cons_zero, Set.mem_setOf_eq] using ht
      · intro ht
        exact ⟨a, (fun _ => rfl), ht⟩
    dsimp only
    rw [he]
    obtain ⟨f, _, hf⟩ := s2v_hardt_cad3_continuous_height ψ hm hψ i
    refine ⟨⟨f a, hf a⟩, ?_, ?_⟩
    · have hlo : IsOpen {t : ℝ | ∀ j : Fin r, j.val < i.val → ψ j a < t} := by
        simp only [Set.setOf_forall]
        exact isOpen_iInter_of_finite (fun j => isOpen_iInter_of_finite (fun _ => isOpen_Ioi))
      have hhi : IsOpen {t : ℝ | ∀ j : Fin r, i.val ≤ j.val → t < ψ j a} := by
        simp only [Set.setOf_forall]
        exact isOpen_iInter_of_finite (fun j => isOpen_iInter_of_finite (fun _ => isOpen_Iio))
      exact hlo.inter hhi
    · constructor
      intro x hx y hy z hz
      exact ⟨fun j hj => lt_of_lt_of_le (hx.1 j hj) hz.1,
        fun j hj => lt_of_le_of_lt hz.2 (hy.2 j hj)⟩
  let enum := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, (fun i => cells (enum i)), (fun i => dims (enum i)),
    (fun i => E (enum i)), (fun i => F (enum i)), (fun i => I (enum i)), ?_, ?_, ?_,
    (fun i => hF (enum i)), (fun i => hI (enum i)),
    (fun i => hadapt (enum i)), (fun i => hsign (enum i)), enum, ?_, ?_,
    (fun i => hprojection (enum i)), ?_⟩
  · intro i
    cases hi : enum i with
    | inl q => simpa only [hi, cells, Sum.elim_inl] using hgn q
    | inr q => simpa only [hi, cells, Sum.elim_inr] using hbn q
  · intro i j hij
    have hne := fun he => hij (enum.injective he)
    cases hi : enum i with
    | inl q =>
      cases hj : enum j with
      | inl p =>
        simp only [hi, hj, cells, Sum.elim_inl]
        exact hgd (show q ≠ p by intro he; apply hne; rw [hi, hj, he])
      | inr p => simpa only [hi, hj, cells, Sum.elim_inl, Sum.elim_inr] using (hbg p q).symm
    | inr q =>
      cases hj : enum j with
      | inl p => simpa only [hi, hj, cells, Sum.elim_inl, Sum.elim_inr] using hbg q p
      | inr p =>
        simp only [hi, hj, cells, Sum.elim_inr]
        exact hbd (show q ≠ p by intro he; apply hne; rw [hi, hj, he])
  · ext y
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi⟩
      apply (hcover y).mp
      cases h : enum i with
      | inl q => exact Or.inr ⟨q, by simpa only [h, cells, Sum.elim_inl] using hi⟩
      | inr q => exact Or.inl ⟨q, by simpa only [h, cells, Sum.elim_inr] using hi⟩
    · intro hy
      rcases (hcover y).mpr hy with ⟨q, hq⟩ | ⟨q, hq⟩
      · exact ⟨enum.symm (.inr q), by simpa only [Equiv.apply_symm_apply, cells, Sum.elim_inr] using hq⟩
      · exact ⟨enum.symm (.inl q), by simpa only [Equiv.apply_symm_apply, cells, Sum.elim_inl] using hq⟩
  · intro i y
    cases hi : enum i with
    | inl q => simpa only [hi, cells, Sum.elim_inl] using hg q y
    | inr q => simpa only [hi, cells, Sum.elim_inr] using hb q y
  · intro i
    cases hi : enum i <;> simp only [hi, dims, Sum.elim_inl, Sum.elim_inr]
  · intro i
    cases hi : enum i with
    | inl q =>
      simp only [hi, cells, dims, Sum.elim_inl]
      exact Or.inl ⟨True.intro, ψ q, hψ q, hg q⟩
    | inr q =>
      simp only [hi, cells, dims, Sum.elim_inr]
      exact Or.inr ⟨True.intro, hfib q⟩


theorem s2v_hardt_cad4_sub_assemble_aux {n k b : ℕ}
    (B : Fin k → s2v_t11b_Formula (n + 1))
    (C : Fin b → s2v_t11b_Formula n) (d : Fin b → ℕ)
    (baseChart : (j : Fin b) → (C j).realize ≃ₜ {z : EuclideanSpace ℝ (Fin (d j)) | ∀ v, -1 < z v ∧ z v < 1})
    (baseForward : (j : Fin b) → s2v_t11b_Formula (n + d j))
    (baseInverse : (j : Fin b) → s2v_t11b_Formula (d j + n))
    (hn : ∀ j, (C j).realize.Nonempty)
    (hd : Pairwise (fun i j => Disjoint (C i).realize (C j).realize))
    (hu : (⋃ j, (C j).realize) = Set.univ)
    (hdim : ∀ j, d j ≤ n)
    (hF : ∀ j (a : (C j).realize) (z : EuclideanSpace ℝ (Fin (d j))),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈
        (baseForward j).realize ↔ z = (baseChart j a).val)
    (hI : ∀ j (z : {z : EuclideanSpace ℝ (Fin (d j)) | ∀ v, -1 < z v ∧ z v < 1}) (a : EuclideanSpace ℝ (Fin n)),
      WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => a v)) ∈
        (baseInverse j).realize ↔ a = ((baseChart j).symm z).val)
    (localCells : ∀ j : Fin b,
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula (n + 1),
    ∃ dim : Fin m → ℕ,
    ∃ e : (i : Fin m) → (c i).realize ≃ₜ {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : (i : Fin m) → s2v_t11b_Formula ((n + 1) + dim i),
    ∃ I : (i : Fin m) → s2v_t11b_Formula (dim i + (n + 1)),
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = {y | ∃ a : (C j).realize, ∀ v, y v.succ = a.val v} ∧
      (∀ i (x : (c i).realize) (z : EuclideanSpace ℝ (Fin (dim i))),
        WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ (F i).realize ↔
          z = (e i x).val) ∧
      (∀ i (z : {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1}) (x : EuclideanSpace ℝ (Fin (n + 1))),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ (I i).realize ↔
          x = ((e i).symm z).val) ∧
      (∀ i p, (c i).realize ⊆ (B p).realize ∨ Disjoint (c i).realize (B p).realize) ∧
      (∀ i, (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
        WithLp.toLp 2 (fun v : Fin n => y v.succ)) '' (c i).realize = (C j).realize) ∧
      (∀ i, (dim i = d j ∧ ∃ s : (C j).realize → ℝ, Continuous s ∧
        ∀ y, y ∈ (c i).realize ↔ ∃ a : (C j).realize,
          (∀ v, y v.succ = a.val v) ∧ y 0 = s a) ∨
        (dim i = d j + 1 ∧ ∀ a : (C j).realize,
          let fiber := {t : ℝ | WithLp.toLp 2 (Fin.cons t (fun v => a.val v)) ∈ (c i).realize}
          fiber.Nonempty ∧ IsOpen fiber ∧ Set.OrdConnected fiber))) :
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
  choose count cells dims charts forwards inverses hln hld hlu hlF hlI hla hlproj hlfib using localCells
  let T := (j : Fin b) × Fin (count j)
  let enum := (Fintype.equivFin T).symm
  have hbase (j : Fin b) (i : Fin (count j)) (y : EuclideanSpace ℝ (Fin (n + 1)))
      (hy : y ∈ (cells j i).realize) :
      WithLp.toLp 2 (fun v : Fin n => y v.succ) ∈ (C j).realize := by
    rw [← hlproj j i]
    exact ⟨y, hy, rfl⟩
  refine ⟨Fintype.card T, (fun i => cells (enum i).1 (enum i).2),
    (fun i => dims (enum i).1 (enum i).2),
    (fun i => charts (enum i).1 (enum i).2),
    (fun i => forwards (enum i).1 (enum i).2),
    (fun i => inverses (enum i).1 (enum i).2),
    (fun i => hln (enum i).1 (enum i).2), ?_, ?_, ?_,
    (fun i => hlF (enum i).1 (enum i).2),
    (fun i => hlI (enum i).1 (enum i).2),
    (fun i => hla (enum i).1 (enum i).2),
    b, C, d, baseChart, baseForward, baseInverse, (fun i => (enum i).1),
    hF, hI, hn, hd, hu, hdim,
    (fun i => hlproj (enum i).1 (enum i).2),
    (fun i => hlfib (enum i).1 (enum i).2)⟩
  · intro i j hij
    by_cases hp : (enum i).1 = (enum j).1
    · obtain ⟨a, ai, hei⟩ : ∃ a ai, enum i = (⟨a, ai⟩ : T) := ⟨_, _, rfl⟩
      obtain ⟨a', aj, hej⟩ : ∃ a' aj, enum j = (⟨a', aj⟩ : T) := ⟨_, _, rfl⟩
      simp only [hei, hej] at hp
      subst a'
      have hne : ai ≠ aj := by
        intro he
        apply hij
        apply enum.injective
        simpa only [hei, hej, he]
      change Disjoint (cells (enum i).1 (enum i).2).realize (cells (enum j).1 (enum j).2).realize
      rw [hei, hej]
      exact hld a hne
    · apply Set.disjoint_left.mpr
      intro y hyi hyj
      exact Set.disjoint_left.mp (hd hp)
        (hbase _ _ y hyi) (hbase _ _ y hyj)
  · apply Set.eq_univ_of_forall
    intro y
    have hy : WithLp.toLp 2 (fun v : Fin n => y v.succ) ∈ ⋃ j, (C j).realize := by rw [hu]; trivial
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    have hyc : y ∈ ⋃ i, (cells j i).realize := by
      rw [hlu j]
      exact ⟨⟨_, hj⟩, (fun _ => rfl)⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyc
    apply Set.mem_iUnion.mpr
    refine ⟨enum.symm ⟨j, i⟩, ?_⟩
    change y ∈ (cells (enum (enum.symm ⟨j, i⟩)).1 (enum (enum.symm ⟨j, i⟩)).2).realize
    rw [enum.apply_symm_apply]
    exact hi
  · intro i
    change dims (enum i).1 (enum i).2 ≤ n + 1
    rcases hlfib (enum i).1 (enum i).2 with h | h
    · rw [h.1]
      exact (hdim _).trans (Nat.le_succ _)
    · rw [h.1]
      exact Nat.add_le_add_right (hdim _) 1


theorem s2v_hardt_cad4_sub_pullback_aux {n d k : ℕ}
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
    (B : Fin k → s2v_t11b_Formula n)
    (A : Fin k → s2v_t11b_Formula d)
    (hA : ∀ j z, z ∈ (A j).realize ↔ ∃ x : C.realize,
      x.val ∈ (B j).realize ∧ z = (e x).val) :
    ∃ box : s2v_t11b_Formula d,
      (∀ z, z ∈ box.realize ↔ ∀ v, -1 < z v ∧ z v < 1) ∧
    ∃ m : ℕ, ∃ H : Fin m → s2v_t11b_Formula (d),
    ∃ dim : Fin m → ℕ,
    ∃ chart : (i : Fin m) → (H i).realize ≃ₜ {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ forward : (i : Fin m) → s2v_t11b_Formula ((d) + dim i),
    ∃ inverse : (i : Fin m) → s2v_t11b_Formula (dim i + (d)),
      (∀ i, (H i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (H i).realize (H j).realize) ∧
      (⋃ i, (H i).realize) = Set.univ ∧
      (∀ i (x : (H i).realize) (z : EuclideanSpace ℝ (Fin (dim i))),
        WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ (forward i).realize ↔
          z = (chart i x).val) ∧
      (∀ i (z : {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1}) (x : EuclideanSpace ℝ (Fin (d))),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ (inverse i).realize ↔
          x = ((chart i).symm z).val) ∧
      (∀ i, dim i ≤ d) ∧
      (∀ i j, (H i).realize ⊆ (A j).realize ∨ Disjoint (H i).realize (A j).realize) ∧
      (∀ i, (H i).realize ⊆ box.realize ∨ Disjoint (H i).realize box.realize) ∧
      ∃ l : ℕ, ∃ keep : Fin l → Fin m,
      ∃ c : Fin l → s2v_t11b_Formula n,
      ∃ toC : (i : Fin l) → (c i).realize → C.realize,
      ∃ intoBox : (i : Fin l) → (H (keep i)).realize → {z : EuclideanSpace ℝ (Fin (d)) | ∀ v, -1 < z v ∧ z v < 1},
      ∃ pull : (i : Fin l) → (c i).realize ≃ₜ (H (keep i)).realize,
        Function.Injective keep ∧
        (∀ j, (∃ i, keep i = j) ↔ (H j).realize ⊆ box.realize) ∧
        (∀ i x, (toC i x).val = x.val) ∧
        (∀ i z, (intoBox i z).val = z.val) ∧
        (∀ i x, (pull i x).val = (e (toC i x)).val) ∧
        (∀ i z, ((pull i).symm z).val = (e.symm (intoBox i z)).val) ∧
        (∀ i x, x ∈ (c i).realize ↔ ∃ a : C.realize,
          x = a.val ∧ (e a).val ∈ (H (keep i)).realize) ∧
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = C.realize ∧
        (∀ i j, (c i).realize ⊆ (B j).realize ∨ Disjoint (c i).realize (B j).realize) ∧
        (∀ i, (H (keep i)).realize = {z | ∃ x : (c i).realize,
          z = (e (toC i x)).val}) := by
  classical
  obtain ⟨box, hbox₀⟩ := s2v_hardt_cad3_finite_inter (fun v : Fin d =>
    s2v_t11b_Formula.inter (.compl (.nonneg (-MvPolynomial.X v - 1)))
      (.compl (.nonneg (MvPolynomial.X v - 1))))
  have hbox (z : EuclideanSpace ℝ (Fin d)) :
      z ∈ box.realize ↔ ∀ v, -1 < z v ∧ z v < 1 := by
    rw [hbox₀]
    apply forall_congr'
    intro v
    change (¬ 0 ≤ MvPolynomial.eval (fun v => z v) (-MvPolynomial.X v - 1)) ∧
      (¬ 0 ≤ MvPolynomial.eval (fun v => z v) (MvPolynomial.X v - 1)) ↔ _
    simp only [map_sub, map_neg, MvPolynomial.eval_X, map_one, not_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  obtain ⟨m, H, dim, chart, forward, inverse, hn, hd, hu, hdim, hF, hI, ha⟩ :=
    ih (Fin.cases box A)
  have haA (i : Fin m) (j : Fin k) :
      (H i).realize ⊆ (A j).realize ∨ Disjoint (H i).realize (A j).realize := ha i j.succ
  have habox (i : Fin m) :
      (H i).realize ⊆ box.realize ∨ Disjoint (H i).realize box.realize := ha i 0
  have formula (j : Fin m) : ∃ c : s2v_t11b_Formula n,
      ∀ x, x ∈ c.realize ↔ ∃ a : C.realize, x = a.val ∧ (e a).val ∈ (H j).realize := by
    let u := s2v_hardt2_boundIndex n d
    let v := s2v_hardt2_freeIndex n d
    let ρ : Fin (n + d) → Fin (n + d) := Fin.addCases v u
    let Q : s2v_t11b_Formula (n + d) := .inter (s2v_hardt1_rename v C)
      (.inter (s2v_hardt1_rename u (H j)) (s2v_hardt1_rename ρ G))
    obtain ⟨c, hc⟩ := s2v_hardt2_repeated_projection Q
    refine ⟨c, ?_⟩
    intro x
    rw [hc]
    have hfree (y : Fin d → ℝ) : WithLp.toLp 2 (fun i => s2v_hardt2_insert d y x (v i)) = x := by
      ext i
      exact s2v_hardt2_insert_free y x i
    have hbound (y : Fin d → ℝ) : WithLp.toLp 2 (fun i => s2v_hardt2_insert d y x (u i)) = WithLp.toLp 2 y := by
      ext i
      exact s2v_hardt2_insert_bound y x i
    have hcoords (y : Fin d → ℝ) : WithLp.toLp 2 (fun i => s2v_hardt2_insert d y x (ρ i)) =
        WithLp.toLp 2 (Fin.append (fun i => x i) y) := by
      ext i
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i
      · simp only [ρ, Fin.addCases_left, v, s2v_hardt2_insert_free, Fin.append_left]
      · simp only [ρ, Fin.addCases_right, u, s2v_hardt2_insert_bound, Fin.append_right]
    constructor
    · rintro ⟨y, hy⟩
      change (_ ∧ _ ∧ _) at hy
      rw [s2v_hardt1_realize_rename, hfree,
        s2v_hardt1_realize_rename, hbound,
        s2v_hardt1_realize_rename, hcoords] at hy
      refine ⟨⟨x, hy.1⟩, rfl, ?_⟩
      have he := (hG ⟨x, hy.1⟩ (WithLp.toLp 2 y)).mp hy.2.2
      exact he ▸ hy.2.1
    · rintro ⟨a, rfl, ha⟩
      refine ⟨fun i => (e a).val i, ?_⟩
      change (_ ∧ _ ∧ _)
      rw [s2v_hardt1_realize_rename, hfree,
        s2v_hardt1_realize_rename, hbound,
        s2v_hardt1_realize_rename, hcoords]
      exact ⟨a.property, ha, (hG a (e a).val).mpr rfl⟩
  choose cells hc using formula
  let S := {j : Fin m // (H j).realize ⊆ box.realize}
  let enum := (Fintype.equivFin S).symm
  let keep (i : Fin (Fintype.card S)) : Fin m := (enum i).val
  let c (i : Fin (Fintype.card S)) := cells (keep i)
  let toC (i : Fin (Fintype.card S)) (x : (c i).realize) : C.realize :=
    ⟨x.val, by obtain ⟨a, he, _⟩ := (hc (keep i) x.val).mp x.property; rw [he]; exact a.property⟩
  let intoBox (i : Fin (Fintype.card S)) (z : (H (keep i)).realize) :
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1} :=
    ⟨z.val, (hbox z.val).mp ((enum i).property z.property)⟩
  have hmem (i : Fin (Fintype.card S)) (x : (c i).realize) :
      (e (toC i x)).val ∈ (H (keep i)).realize := by
    obtain ⟨a, he, ha⟩ := (hc (keep i) x.val).mp x.property
    have hea : toC i x = a := Subtype.ext he
    rw [hea]
    exact ha
  have hinvmem (i : Fin (Fintype.card S)) (z : (H (keep i)).realize) :
      (e.symm (intoBox i z)).val ∈ (c i).realize := by
    apply (hc (keep i) _).mpr
    exact ⟨e.symm (intoBox i z), rfl, by simpa only [e.apply_symm_apply] using z.property⟩
  let pull (i : Fin (Fintype.card S)) : (c i).realize ≃ₜ (H (keep i)).realize :=
    { toFun := fun x => ⟨(e (toC i x)).val, hmem i x⟩
      invFun := fun z => ⟨(e.symm (intoBox i z)).val, hinvmem i z⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change (e.symm (intoBox i ⟨(e (toC i x)).val, hmem i x⟩)).val = x.val
        have he : intoBox i ⟨(e (toC i x)).val, hmem i x⟩ = e (toC i x) := Subtype.ext rfl
        rw [he, e.symm_apply_apply]
      right_inv := by
        intro z
        apply Subtype.ext
        change (e (toC i ⟨(e.symm (intoBox i z)).val, hinvmem i z⟩)).val = z.val
        have he : toC i ⟨(e.symm (intoBox i z)).val, hinvmem i z⟩ = e.symm (intoBox i z) := Subtype.ext rfl
        rw [he, e.apply_symm_apply]
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (e.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_val }
  have hkeep : Function.Injective keep := fun i j h => enum.injective (Subtype.ext h)
  have hselect (j : Fin m) : (∃ i, keep i = j) ↔ (H j).realize ⊆ box.realize := by
    constructor
    · rintro ⟨i, rfl⟩
      exact (enum i).property
    · intro hj
      exact ⟨enum.symm ⟨j, hj⟩, congrArg Subtype.val (enum.apply_symm_apply _)⟩
  refine ⟨box, hbox, m, H, dim, chart, forward, inverse,
    hn, hd, hu, hF, hI, hdim, haA, habox,
    Fintype.card S, keep, c, toC, intoBox, pull, hkeep, hselect,
    (fun _ _ => rfl), (fun _ _ => rfl), (fun _ _ => rfl), (fun _ _ => rfl),
    (fun i => hc (keep i)), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨z, hz⟩ := hn (keep i)
    exact ⟨(e.symm (intoBox i ⟨z, hz⟩)).val, hinvmem i ⟨z, hz⟩⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨a, ha, hai⟩ := (hc (keep i) x).mp hxi
    obtain ⟨a', ha', haj⟩ := (hc (keep j) x).mp hxj
    have he : a = a' := Subtype.ext (ha.symm.trans ha')
    subst a'
    exact Set.disjoint_left.mp (hd (fun h => hij (hkeep h))) hai haj
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a, rfl, _⟩ := (hc (keep i) x).mp hi
      exact a.property
    · intro hx
      let a : C.realize := ⟨x, hx⟩
      have he : (e a).val ∈ ⋃ j, (H j).realize := by rw [hu]; trivial
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp he
      have hjbox : (H j).realize ⊆ box.realize := by
        rcases habox j with h | h
        · exact h
        · exact False.elim (Set.disjoint_left.mp h hj ((hbox _).mpr (e a).property))
      obtain ⟨i, hi⟩ := (hselect j).mpr hjbox
      apply Set.mem_iUnion.mpr
      refine ⟨i, (hc (keep i) x).mpr ⟨a, rfl, ?_⟩⟩
      rw [hi]
      exact hj
  · intro i j
    rcases haA (keep i) j with h | h
    · apply Or.inl
      intro x hx
      obtain ⟨a, rfl, ha⟩ := (hc (keep i) x).mp hx
      obtain ⟨a', ha', he⟩ := (hA j (e a).val).mp (h ha)
      have haa : a = a' := e.injective (Subtype.ext he)
      simpa only [haa] using ha'
    · apply Or.inr
      apply Set.disjoint_left.mpr
      intro x hx hxB
      obtain ⟨a, rfl, ha⟩ := (hc (keep i) x).mp hx
      exact Set.disjoint_left.mp h ha ((hA j (e a).val).mpr ⟨a, hxB, rfl⟩)
  · intro i
    ext z
    constructor
    · intro hz
      let y : (H (keep i)).realize := ⟨z, hz⟩
      refine ⟨(pull i).symm y, ?_⟩
      exact (congrArg Subtype.val ((pull i).apply_symm_apply y)).symm
    · rintro ⟨x, rfl⟩
      exact hmem i x


theorem s2v_hardt_cad4_sub_compose_aux {n d q : ℕ}
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
    (c : s2v_t11b_Formula n) (H : s2v_t11b_Formula d)
    (toC : c.realize → C.realize)
    (htoC : ∀ x, (toC x).val = x.val)
    (intoBox : H.realize → {z : EuclideanSpace ℝ (Fin (d)) | ∀ v, -1 < z v ∧ z v < 1})
    (hinto : ∀ z, (intoBox z).val = z.val)
    (pull : c.realize ≃ₜ H.realize)
    (hpull : ∀ x, (pull x).val = (e (toC x)).val)
    (hpullInv : ∀ z, (pull.symm z).val = (e.symm (intoBox z)).val)
    (chart : H.realize ≃ₜ {z : EuclideanSpace ℝ (Fin (q)) | ∀ v, -1 < z v ∧ z v < 1})
    (K : s2v_t11b_Formula (d + q))
    (hK : ∀ y : H.realize, ∀ z : EuclideanSpace ℝ (Fin q),
      WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ K.realize ↔
        z = (chart y).val)
    (L : s2v_t11b_Formula (q + d))
    (hL : ∀ z : {z : EuclideanSpace ℝ (Fin (q)) | ∀ v, -1 < z v ∧ z v < 1}, ∀ y : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ L.realize ↔
        y = (chart.symm z).val) :
    ∃ E : c.realize ≃ₜ {z : EuclideanSpace ℝ (Fin (q)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula (n + q), ∃ I : s2v_t11b_Formula (q + n),
      (∀ x : c.realize, ∀ z : EuclideanSpace ℝ (Fin q),
        WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E x).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin (q)) | ∀ v, -1 < z v ∧ z v < 1}, ∀ x : EuclideanSpace ℝ (Fin n),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ I.realize ↔
          x = (E.symm z).val) ∧
      (∀ x, E x = chart (pull x)) ∧
      (∀ z, e (toC (E.symm z)) = intoBox (chart.symm z)) ∧
      (∀ z, (E.symm z).val = (e.symm (intoBox (chart.symm z))).val) := by
  let E := pull.trans chart
  let u := s2v_hardt2_boundIndex (n + q) d
  let v := s2v_hardt2_freeIndex (n + q) d
  let ix : Fin n → Fin ((n + q) + d) := fun i => v (Fin.castAdd q i)
  let iz : Fin q → Fin ((n + q) + d) := fun i => v (Fin.natAdd n i)
  let ρG : Fin (n + d) → Fin ((n + q) + d) := Fin.addCases ix u
  let ρK : Fin (d + q) → Fin ((n + q) + d) := Fin.addCases u iz
  let Q : s2v_t11b_Formula ((n + q) + d) :=
    .inter (s2v_hardt1_rename u H)
      (.inter (s2v_hardt1_rename ρG G) (s2v_hardt1_rename ρK K))
  obtain ⟨F₀, hF₀⟩ := s2v_hardt2_repeated_projection Q
  have hF (x : c.realize) (z : EuclideanSpace ℝ (Fin q)) :
      WithLp.toLp 2 (Fin.append (fun i => x.val i) (fun i => z i)) ∈ F₀.realize ↔ z = (E x).val := by
    rw [hF₀]
    let w := WithLp.toLp 2 (Fin.append (fun i => x.val i) (fun i => z i))
    have hbound (y : Fin d → ℝ) : WithLp.toLp 2 (fun i => s2v_hardt2_insert d y w (u i)) =
        WithLp.toLp 2 y := by
      ext i
      exact s2v_hardt2_insert_bound y w i
    have hcoordsG (y : Fin d → ℝ) : WithLp.toLp 2 (fun i => s2v_hardt2_insert d y w (ρG i)) =
        WithLp.toLp 2 (Fin.append (fun i => x.val i) y) := by
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [ρG, Fin.addCases_left, ix, v, s2v_hardt2_insert_free, w,
          WithLp.ofLp_toLp, Fin.append_left]
      · simp only [ρG, Fin.addCases_right, u, s2v_hardt2_insert_bound, Fin.append_right]
    have hcoordsK (y : Fin d → ℝ) : WithLp.toLp 2 (fun i => s2v_hardt2_insert d y w (ρK i)) =
        WithLp.toLp 2 (Fin.append y (fun i => z i)) := by
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [ρK, Fin.addCases_left, u, s2v_hardt2_insert_bound, Fin.append_left]
      · simp only [ρK, Fin.addCases_right, iz, v, s2v_hardt2_insert_free, w,
          WithLp.ofLp_toLp, Fin.append_right]
    have hG' (y : EuclideanSpace ℝ (Fin d)) :
        WithLp.toLp 2 (Fin.append (fun i => x.val i) (fun i => y i)) ∈ G.realize ↔
          y = (e (toC x)).val := by
      simpa only [htoC x] using hG (toC x) y
    constructor
    · rintro ⟨y, hy⟩
      change (_ ∧ _ ∧ _) at hy
      rw [s2v_hardt1_realize_rename, hbound,
        s2v_hardt1_realize_rename, hcoordsG,
        s2v_hardt1_realize_rename, hcoordsK] at hy
      let a : H.realize := ⟨WithLp.toLp 2 y, hy.1⟩
      have ha : a = pull x := Subtype.ext (((hG' a.val).mp hy.2.1).trans (hpull x).symm)
      have hz := (hK a z).mp hy.2.2
      change z = (chart (pull x)).val
      simpa only [ha] using hz
    · intro hz
      refine ⟨fun i => (pull x).val i, ?_⟩
      change (_ ∧ _ ∧ _)
      rw [s2v_hardt1_realize_rename, hbound,
        s2v_hardt1_realize_rename, hcoordsG,
        s2v_hardt1_realize_rename, hcoordsK]
      exact ⟨(pull x).property, (hG' (pull x).val).mpr (hpull x), (hK (pull x) z).mpr hz⟩
  obtain ⟨F, I, hforward, hinverse⟩ := s2v_hardt_cad3_inverse_graph c _ E F₀ hF
  refine ⟨E, F, I, hforward, hinverse, (fun _ => rfl), ?_, ?_⟩
  · intro z
    apply Subtype.ext
    calc
      (e (toC (E.symm z))).val = (pull (E.symm z)).val := (hpull _).symm
      _ = (chart.symm z).val := congrArg Subtype.val (pull.apply_symm_apply _)
      _ = (intoBox (chart.symm z)).val := (hinto _).symm
  · intro z
    exact hpullInv (chart.symm z)


end HodgeLean.Foundations.Program
