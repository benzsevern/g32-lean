import HodgeLean.Foundations.Program.SchoenTowerHardtCad3Proofs

/-! Implication from ordered graph-described sections to band geometry and sign refinement.
Chart transport requires a supplied graph-described base chart and continuous sections.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Ordered section graphs give formulas for all bands, including exterior regions.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3,
printed pp. 6–7, cylindrical lifting construction. -/
theorem s2v_hardt_cad3_band_formulas {n r : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ q y, y ∈ (g q).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a) :
    ∃ b : Fin (r + 1) → s2v_t11b_Formula (n + 1), ∀ i y, y ∈ (b i).realize ↔ ∃ a : C.realize,
        (∀ v, y v.succ = a.val v) ∧
        (∀ q : Fin r, q.val < i.val → ψ q a < y 0) ∧
        (∀ q : Fin r, i.val ≤ q.val → y 0 < ψ q a) :=
  s2v_hardt_cad3_band_formulas_aux C ψ hm g hg

example {n r : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ q y, y ∈ (g q).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a) :
    ∃ b : Fin (r + 1) → s2v_t11b_Formula (n + 1), ∀ i y, y ∈ (b i).realize ↔ ∃ a : C.realize,
        (∀ v, y v.succ = a.val v) ∧
        (∀ q : Fin r, q.val < i.val → ψ q a < y 0) ∧
        (∀ q : Fin r, i.val ≤ q.val → y 0 < ψ q a) :=
  s2v_hardt_cad3_band_formulas C ψ hm g hg

/-- Bands and sections partition the actual cylinder over a nonempty base.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3,
printed pp. 6–7, cylindrical lifting construction. -/
theorem s2v_hardt_cad3_cylinder_partition {n r : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (hC : C.realize.Nonempty)
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ q y, y ∈ (g q).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a)
    (b : Fin (r + 1) → s2v_t11b_Formula (n + 1))
    (hb : ∀ i y, y ∈ (b i).realize ↔ ∃ a : C.realize,
        (∀ v, y v.succ = a.val v) ∧
        (∀ q : Fin r, q.val < i.val → ψ q a < y 0) ∧
        (∀ q : Fin r, i.val ≤ q.val → y 0 < ψ q a)) :
    (∀ i, (b i).realize.Nonempty) ∧ (∀ q, (g q).realize.Nonempty) ∧
    Pairwise (fun i j => Disjoint (b i).realize (b j).realize) ∧
    Pairwise (fun i j => Disjoint (g i).realize (g j).realize) ∧
    (∀ i q, Disjoint (b i).realize (g q).realize) ∧
    (∀ y : EuclideanSpace ℝ (Fin (n + 1)),
      ((∃ i, y ∈ (b i).realize) ∨ (∃ q, y ∈ (g q).realize)) ↔
      ∃ a : C.realize, ∀ v, y v.succ = a.val v) ∧
    (∀ i y, y ∈ (b i).realize →
      WithLp.toLp 2 (fun v => y v.succ) ∈ C.realize) :=
  s2v_hardt_cad3_cylinder_partition_aux C ψ hm hC g hg b hb

example {n r : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (hC : C.realize.Nonempty)
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ q y, y ∈ (g q).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a)
    (b : Fin (r + 1) → s2v_t11b_Formula (n + 1))
    (hb : ∀ i y, y ∈ (b i).realize ↔ ∃ a : C.realize,
        (∀ v, y v.succ = a.val v) ∧
        (∀ q : Fin r, q.val < i.val → ψ q a < y 0) ∧
        (∀ q : Fin r, i.val ≤ q.val → y 0 < ψ q a)) :
    (∀ i, (b i).realize.Nonempty) ∧ (∀ q, (g q).realize.Nonempty) ∧
    Pairwise (fun i j => Disjoint (b i).realize (b j).realize) ∧
    Pairwise (fun i j => Disjoint (g i).realize (g j).realize) ∧
    (∀ i q, Disjoint (b i).realize (g q).realize) ∧
    (∀ y : EuclideanSpace ℝ (Fin (n + 1)),
      ((∃ i, y ∈ (b i).realize) ∨ (∃ q, y ∈ (g q).realize)) ↔
      ∃ a : C.realize, ∀ v, y v.succ = a.val v) ∧
    (∀ i y, y ∈ (b i).realize →
      WithLp.toLp 2 (fun v => y v.succ) ∈ C.realize) :=
  s2v_hardt_cad3_cylinder_partition C ψ hm hC g hg b hb

/-- Bounded bands retain the supplied base chart and have actual map graphs.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3,
printed pp. 6–7, cylindrical lifting construction. -/
theorem s2v_hardt_cad3_bounded_chart {n d : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔
      z = (e a).val)
    (l u : C.realize → ℝ) (hl : Continuous l) (hu : Continuous u)
    (hlu : ∀ a, l a < u a)
    (L U : s2v_t11b_Formula (n + 1))
    (hL : ∀ y, y ∈ L.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = l a)
    (hU : ∀ y, y ∈ U.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = u a)
    (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ l a < y 0 ∧ y 0 < u a) :
    ∃ E : b.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula ((n + 1) + (d + 1)),
    ∃ I : s2v_t11b_Formula ((d + 1) + (n + 1)),
      (∀ y : b.realize, ∀ a : C.realize,
        (∀ v, y.val v.succ = a.val v) →
        (∀ v, (E y).val v.succ = (e a).val v) ∧ (E y).val 0 = 2 * ((y.val 0 - l a) / (u a - l a)) - 1) ∧
      (∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin (d + 1)),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E y).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
        ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔
          y = (E.symm z).val) :=
  s2v_hardt_cad3_bounded_chart_aux C e G hG l u hl hu hlu L U hL hU b hb

example {n d : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔
      z = (e a).val)
    (l u : C.realize → ℝ) (hl : Continuous l) (hu : Continuous u)
    (hlu : ∀ a, l a < u a)
    (L U : s2v_t11b_Formula (n + 1))
    (hL : ∀ y, y ∈ L.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = l a)
    (hU : ∀ y, y ∈ U.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = u a)
    (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ l a < y 0 ∧ y 0 < u a) :
    ∃ E : b.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula ((n + 1) + (d + 1)),
    ∃ I : s2v_t11b_Formula ((d + 1) + (n + 1)),
      (∀ y : b.realize, ∀ a : C.realize,
        (∀ v, y.val v.succ = a.val v) →
        (∀ v, (E y).val v.succ = (e a).val v) ∧ (E y).val 0 = 2 * ((y.val 0 - l a) / (u a - l a)) - 1) ∧
      (∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin (d + 1)),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E y).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
        ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔
          y = (E.symm z).val) :=
  s2v_hardt_cad3_bounded_chart C e G hG l u hl hu hlu L U hL hU b hb

/-- Ray bands retain the supplied base chart and have actual map graphs.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3,
printed pp. 6–7, cylindrical lifting construction. -/
theorem s2v_hardt_cad3_ray_chart {n d : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔
      z = (e a).val)
    (s : C.realize → ℝ) (hs : Continuous s) (upper : Bool)
    (S : s2v_t11b_Formula (n + 1))
    (hS : ∀ y, y ∈ S.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = s a)
    (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ (if upper then s a < y 0 else y 0 < s a)) :
    ∃ E : b.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula ((n + 1) + (d + 1)),
    ∃ I : s2v_t11b_Formula ((d + 1) + (n + 1)),
      (∀ y : b.realize, ∀ a : C.realize,
        (∀ v, y.val v.succ = a.val v) →
        (∀ v, (E y).val v.succ = (e a).val v) ∧ (E y).val 0 = ((if upper then y.val 0 - s a else s a - y.val 0) - 1) /
          ((if upper then y.val 0 - s a else s a - y.val 0) + 1)) ∧
      (∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin (d + 1)),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E y).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
        ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔
          y = (E.symm z).val) :=
  s2v_hardt_cad3_ray_chart_aux C e G hG s hs upper S hS b hb

example {n d : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔
      z = (e a).val)
    (s : C.realize → ℝ) (hs : Continuous s) (upper : Bool)
    (S : s2v_t11b_Formula (n + 1))
    (hS : ∀ y, y ∈ S.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = s a)
    (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ (if upper then s a < y 0 else y 0 < s a)) :
    ∃ E : b.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula ((n + 1) + (d + 1)),
    ∃ I : s2v_t11b_Formula ((d + 1) + (n + 1)),
      (∀ y : b.realize, ∀ a : C.realize,
        (∀ v, y.val v.succ = a.val v) →
        (∀ v, (E y).val v.succ = (e a).val v) ∧ (E y).val 0 = ((if upper then y.val 0 - s a else s a - y.val 0) - 1) /
          ((if upper then y.val 0 - s a else s a - y.val 0) + 1)) ∧
      (∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin (d + 1)),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E y).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
        ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔
          y = (E.symm z).val) :=
  s2v_hardt_cad3_ray_chart C e G hG s hs upper S hS b hb

/-- Whole bands retain the supplied base chart and have actual map graphs.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3,
printed pp. 6–7, cylindrical lifting construction. -/
theorem s2v_hardt_cad3_whole_chart {n d : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔
      z = (e a).val)

    (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ True) :
    ∃ E : b.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula ((n + 1) + (d + 1)),
    ∃ I : s2v_t11b_Formula ((d + 1) + (n + 1)),
      (∀ y : b.realize, ∀ a : C.realize,
        (∀ v, y.val v.succ = a.val v) →
        (∀ v, (E y).val v.succ = (e a).val v) ∧ (E y).val 0 = y.val 0 / (1 + |y.val 0|)) ∧
      (∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin (d + 1)),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E y).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
        ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔
          y = (E.symm z).val) :=
  s2v_hardt_cad3_whole_chart_aux C e G hG  b hb

example {n d : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔
      z = (e a).val)

    (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ True) :
    ∃ E : b.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula ((n + 1) + (d + 1)),
    ∃ I : s2v_t11b_Formula ((d + 1) + (n + 1)),
      (∀ y : b.realize, ∀ a : C.realize,
        (∀ v, y.val v.succ = a.val v) →
        (∀ v, (E y).val v.succ = (e a).val v) ∧ (E y).val 0 = y.val 0 / (1 + |y.val 0|)) ∧
      (∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin (d + 1)),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E y).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
        ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔
          y = (E.symm z).val) :=
  s2v_hardt_cad3_whole_chart C e G hG  b hb

/-- Connected root-free bands have one exact polynomial sign.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3,
printed pp. 6–7, cylindrical lifting construction. -/
theorem s2v_hardt_cad3_band_signs {n r k : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (hC : IsConnected C.realize) (hψ : ∀ q, Continuous (ψ q))
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (hz : ∀ j, (∀ a : C.realize,
      (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
      (∀ a : C.realize, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0))
    (hr : ∀ a : C.realize, ∀ t : ℝ, (∃ q, t = ψ q a) ↔
      ∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
        (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0)
    (b : Fin (r + 1) → s2v_t11b_Formula (n + 1))
    (hb : ∀ i y, y ∈ (b i).realize ↔ ∃ a : C.realize,
        (∀ v, y v.succ = a.val v) ∧
        (∀ q : Fin r, q.val < i.val → ψ q a < y 0) ∧
        (∀ q : Fin r, i.val ≤ q.val → y 0 < ψ q a)) :
    ∀ i j, (∀ y ∈ (b i).realize,
      (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0) < 0) ∨
      (∀ y ∈ (b i).realize,
      (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0) = 0) ∨
      (∀ y ∈ (b i).realize,
      0 < (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0)) :=
  s2v_hardt_cad3_band_signs_aux C ψ hm hC hψ P hz hr b hb

example {n r k : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (hC : IsConnected C.realize) (hψ : ∀ q, Continuous (ψ q))
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (hz : ∀ j, (∀ a : C.realize,
      (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
      (∀ a : C.realize, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0))
    (hr : ∀ a : C.realize, ∀ t : ℝ, (∃ q, t = ψ q a) ↔
      ∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
        (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0)
    (b : Fin (r + 1) → s2v_t11b_Formula (n + 1))
    (hb : ∀ i y, y ∈ (b i).realize ↔ ∃ a : C.realize,
        (∀ v, y v.succ = a.val v) ∧
        (∀ q : Fin r, q.val < i.val → ψ q a < y 0) ∧
        (∀ q : Fin r, i.val ≤ q.val → y 0 < ψ q a)) :
    ∀ i j, (∀ y ∈ (b i).realize,
      (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0) < 0) ∨
      (∀ y ∈ (b i).realize,
      (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0) = 0) ∨
      (∀ y ∈ (b i).realize,
      0 < (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0)) :=
  s2v_hardt_cad3_band_signs C ψ hm hC hψ P hz hr b hb

/-- Section evaluation sign loci have a finite Boolean refinement.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3,
printed pp. 6–7, cylindrical lifting construction. -/
theorem s2v_hardt_cad3_section_sign_refinement {n r k : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ q y, y ∈ (g q).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a)
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = C.realize ∧
      ∀ i q j, (∀ a : C.realize, a.val ∈ (c i).realize →
        (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) < 0) ∨
        (∀ a : C.realize, a.val ∈ (c i).realize →
        (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) = 0) ∨
        (∀ a : C.realize, a.val ∈ (c i).realize →
        0 < (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a)) :=
  s2v_hardt_cad3_section_sign_refinement_aux C ψ hm g hg P

example {n r k : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ q y, y ∈ (g q).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a)
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = C.realize ∧
      ∀ i q j, (∀ a : C.realize, a.val ∈ (c i).realize →
        (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) < 0) ∨
        (∀ a : C.realize, a.val ∈ (c i).realize →
        (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) = 0) ∨
        (∀ a : C.realize, a.val ∈ (c i).realize →
        0 < (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a)) :=
  s2v_hardt_cad3_section_sign_refinement C ψ hm g hg P

end HodgeLean.Foundations.Program
