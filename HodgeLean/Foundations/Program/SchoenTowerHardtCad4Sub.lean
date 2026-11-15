import HodgeLean.Foundations.Program.SchoenTowerHardtCad4SubProofs

/-! Implication from explicit lower-dimensional partitions and checked root geometry.
The five construction interfaces separate base signs, local lifts, finite indexing,
box pullbacks and graph composition. HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Prepared section signs and charted base restrictions.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3, printed pp. 6–7. -/
theorem s2v_hardt_cad4_sub_prepare {n k b : ℕ}
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
        (∀ a : (c i).realize, 0 < (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (roots i q a))) :=
  s2v_hardt_cad4_sub_prepare_aux ih P C hC hdisj hcover r ψ hψ hm g hg hz hr

example {n k b : ℕ}
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
        (∀ a : (c i).realize, 0 < (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (roots i q a))) :=
  s2v_hardt_cad4_sub_prepare ih P C hC hdisj hcover r ψ hψ hm g hg hz hr

/-- One prepared base lifts to its sections and all bands.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3, printed pp. 6–7. -/
theorem s2v_hardt_cad4_sub_lift {n d r k h : ℕ}
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
            fiber.Nonempty ∧ IsOpen fiber ∧ Set.OrdConnected fiber)) :=
  s2v_hardt_cad4_sub_lift_aux P C hC e G hG ψ hψ hm g hg hz hr hs B hB

example {n d r k h : ℕ}
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
            fiber.Nonempty ∧ IsOpen fiber ∧ Set.OrdConnected fiber)) :=
  s2v_hardt_cad4_sub_lift P C hC e G hG ψ hψ hm g hg hz hr hs B hB

/-- Finite local cylinder partitions give the ambient successor output.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, printed pp. 6–7. -/
theorem s2v_hardt_cad4_sub_assemble {n k b : ℕ}
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
              fiber.Nonempty ∧ IsOpen fiber ∧ Set.OrdConnected fiber)) :=
  s2v_hardt_cad4_sub_assemble_aux B C d baseChart baseForward baseInverse hn hd hu hdim hF hI localCells

example {n k b : ℕ}
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
              fiber.Nonempty ∧ IsOpen fiber ∧ Set.OrdConnected fiber)) :=
  s2v_hardt_cad4_sub_assemble B C d baseChart baseForward baseInverse hn hd hu hdim hF hI localCells

/-- The actual open box selects exactly the cells transported to the carrier.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3, printed pp. 6–7. -/
theorem s2v_hardt_cad4_sub_pullback {n d k : ℕ}
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
          z = (e (toC i x)).val}) :=
  s2v_hardt_cad4_sub_pullback_aux ih C e G hG J hJ B A hA

example {n d k : ℕ}
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
          z = (e (toC i x)).val}) :=
  s2v_hardt_cad4_sub_pullback ih C e G hG J hJ B A hA

/-- Both graphs describe the actual composite chart and its inverse.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, printed pp. 6–7. -/
theorem s2v_hardt_cad4_sub_compose {n d q : ℕ}
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
      (∀ z, (E.symm z).val = (e.symm (intoBox (chart.symm z))).val) :=
  s2v_hardt_cad4_sub_compose_aux C e G hG J hJ c H toC htoC intoBox hinto pull hpull hpullInv chart K hK L hL

example {n d q : ℕ}
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
      (∀ z, (E.symm z).val = (e.symm (intoBox (chart.symm z))).val) :=
  s2v_hardt_cad4_sub_compose C e G hG J hJ c H toC htoC intoBox hinto pull hpull hpullInv chart K hK L hL

end HodgeLean.Foundations.Program
