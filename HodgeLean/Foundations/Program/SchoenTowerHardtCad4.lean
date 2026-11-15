import HodgeLean.Foundations.Program.SchoenTowerHardtCad4Proofs

/-! Implication from Boolean descriptions to adapted cell partitions with chart graphs.
The successor interface records actual coordinate projections and fiber dimensions.
Chartwise transport retains the supplied homeomorphism. Frontier and intrinsic
dimension comparisons are deferred. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Finite Boolean families have adapted box-chart partitions.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3,
printed pp. 6–7, cylindrical construction and graph composition. -/
theorem s2v_hardt_cad4_adapted {n k : ℕ}
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
  s2v_hardt_cad4_adapted_aux B

example {n k : ℕ} (B : Fin k → s2v_t11b_Formula n) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (⋃ i, (c i).realize) = Set.univ := by
  obtain ⟨m, c, dim, e, F, I, hn, hd, hc, rest⟩ := s2v_hardt_cad4_adapted B
  exact ⟨m, c, hc⟩

/-- Successor cells project onto actual base cells with graph or interval fibers.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3,
printed pp. 6–7, cylindrical construction and graph composition. -/
theorem s2v_hardt_cad4_successor {n k : ℕ}
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
  s2v_hardt_cad4_successor_aux B

example {n k : ℕ}
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
  s2v_hardt_cad4_successor B

/-- Chartwise refinement retains the supplied chart by composition.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3,
printed pp. 6–7, cylindrical construction and graph composition. -/
theorem s2v_hardt_cad4_chart_refinement {n d k : ℕ}
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
  s2v_hardt_cad4_chart_refinement_aux C e G hG J hJ B

example {n d k : ℕ}
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
  s2v_hardt_cad4_chart_refinement C e G hG J hJ B

/-- Marking both polynomial inequalities separates the three real signs.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, sign-adapted CAD. -/
theorem s2v_hardt_cad4_polynomial_signs {n k : ℕ}
    (P : Fin k → MvPolynomial (Fin n) ℝ) :
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
      (∀ i j, ((c i).realize ⊆ (s2v_t11b_Formula.nonneg (P j)).realize ∨
        Disjoint (c i).realize (s2v_t11b_Formula.nonneg (P j)).realize) ∧
        ((c i).realize ⊆ (s2v_t11b_Formula.nonneg (-P j)).realize ∨
        Disjoint (c i).realize (s2v_t11b_Formula.nonneg (-P j)).realize)) ∧
      (∀ i j,
        (∀ x ∈ (c i).realize, MvPolynomial.eval (fun v => x v) (P j) < 0) ∨
        (∀ x ∈ (c i).realize, MvPolynomial.eval (fun v => x v) (P j) = 0) ∨
        (∀ x ∈ (c i).realize, 0 < MvPolynomial.eval (fun v => x v) (P j))) :=
  s2v_hardt_cad4_polynomial_signs_aux P

example {n k : ℕ} (P : Fin k → MvPolynomial (Fin n) ℝ) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (⋃ i, (c i).realize) = Set.univ := by
  obtain ⟨m, c, dim, e, F, I, hn, hd, hc, rest⟩ :=
    s2v_hardt_cad4_polynomial_signs P
  exact ⟨m, c, hc⟩

end HodgeLean.Foundations.Program
