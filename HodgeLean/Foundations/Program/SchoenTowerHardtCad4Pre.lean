import HodgeLean.Foundations.Program.SchoenTowerHardtCad4PreProofs

/-! Implication from lower-dimensional adapted partitions to successor assembly
and transport through a supplied graph-described chart. HC no distance;
AV milestone no distance. Frontier and intrinsic dimension are deferred. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The zero-dimensional starting partition has one cell.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3, pp. 6–7. -/
theorem s2v_hardt_cad4_pre_zero {k : ℕ}
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
        Disjoint (c i).realize (B j).realize) :=
  s2v_hardt_cad4_pre_zero_aux B

/-- Successor assembly uses adaptation for every finite base family.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3, pp. 6–7. -/
theorem s2v_hardt_cad4_pre_successor {n k : ℕ}
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
              fiber.Nonempty ∧ IsOpen fiber ∧ Set.OrdConnected fiber)) :=
  s2v_hardt_cad4_pre_successor_aux ih B

/-- Chart transport uses an adapted partition in the supplied chart dimension.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3, pp. 6–7. -/
theorem s2v_hardt_cad4_pre_transport {n d k : ℕ}
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
        (∀ i x, E i x = chart i (toH i x)) :=
  s2v_hardt_cad4_pre_transport_aux ih C e G hG J hJ B

/-- Ambient induction projects the successor output to its ambient partition.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3, pp. 6–7. -/
theorem s2v_hardt_cad4_pre_ambient {n k : ℕ}
    (B : Fin k → s2v_t11b_Formula n) :
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
        Disjoint (c i).realize (B j).realize) := by
  induction n generalizing k with
  | zero => exact s2v_hardt_cad4_pre_zero B
  | succ n ih =>
    obtain ⟨m, c, dim, e, F, I, hn, hd, hc, hdim, hF, hI, hB, rest⟩ :=
      s2v_hardt_cad4_pre_successor (fun {k} B => ih B) B
    exact ⟨m, c, dim, e, F, I, hn, hd, hc, hdim, hF, hI, hB⟩

/-- Root preparation supplies actual section and band formulas on every base piece.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3, pp. 6–7. -/
theorem s2v_hardt_cad4_pre_root_lift {n k b : ℕ}
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
          (∀ q, (g q).realize.Nonempty) :=
  s2v_hardt_cad4_pre_root_lift_aux P B

/-- Actual chart images of marked sets have Boolean descriptions.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, graph projection. -/
theorem s2v_hardt_cad4_pre_images {n d k : ℕ}
    (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ x : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ G.realize ↔
        z = (e x).val)
    (B : Fin k → s2v_t11b_Formula n) :
    ∃ A : Fin k → s2v_t11b_Formula d, ∀ j z,
      z ∈ (A j).realize ↔ ∃ x : C.realize,
        x.val ∈ (B j).realize ∧ z = (e x).val :=
  s2v_hardt_cad4_pre_images_aux C e G hG B


example {k : ℕ}
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
        Disjoint (c i).realize (B j).realize) :=
  s2v_hardt_cad4_pre_zero B

example {n k : ℕ}
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
              fiber.Nonempty ∧ IsOpen fiber ∧ Set.OrdConnected fiber)) :=
  s2v_hardt_cad4_pre_successor ih B

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
        (∀ i x, E i x = chart i (toH i x)) :=
  s2v_hardt_cad4_pre_transport ih C e G hG J hJ B

example {n k : ℕ}
    (B : Fin k → s2v_t11b_Formula n) :
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
        Disjoint (c i).realize (B j).realize) :=
  s2v_hardt_cad4_pre_ambient B

example {n k b : ℕ}
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
          (∀ q, (g q).realize.Nonempty) :=
  s2v_hardt_cad4_pre_root_lift P B

example {n d k : ℕ}
    (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ x : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ G.realize ↔
        z = (e x).val)
    (B : Fin k → s2v_t11b_Formula n) :
    ∃ A : Fin k → s2v_t11b_Formula d, ∀ j z,
      z ∈ (A j).realize ↔ ∃ x : C.realize,
        x.val ∈ (B j).realize ∧ z = (e x).val :=
  s2v_hardt_cad4_pre_images C e G hG B

end HodgeLean.Foundations.Program
