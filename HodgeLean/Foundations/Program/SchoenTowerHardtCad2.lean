import HodgeLean.Foundations.Program.SchoenTowerHardtCad2Proofs

/-! Implication from polynomial root preparation to restricted section and chart graphs.
Base pieces are connected sets; cell charts are supplied separately.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Connected Boolean root preparation respects every supplied base set.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3,
printed pp. 6–7, root preparation in the CAD construction. -/
theorem s2v_hardt_cad2_root_partition {n k b : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (B : Fin b → s2v_t11b_Formula n) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ i, IsConnected (c i).realize) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = Set.univ ∧
      (∀ i j, (c i).realize ⊆ (B j).realize ∨
        Disjoint (c i).realize (B j).realize) ∧
      (∀ i j, (∀ a : (c i).realize,
        (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
        (∀ a : (c i).realize,
        (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0)) ∧
      ∀ i, ∃ r : ℕ, ∃ ψ : Fin r → (c i).realize → ℝ,
        (∀ q, Continuous (ψ q)) ∧ (∀ a, StrictMono (fun q => ψ q a)) ∧
        ∀ a t, (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
          (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔
          ∃ q, t = ψ q a :=
  s2v_hardt_cad2_root_partition_aux P B

example {n k b : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (B : Fin b → s2v_t11b_Formula n) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ i, IsConnected (c i).realize) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = Set.univ ∧
      (∀ i j, (c i).realize ⊆ (B j).realize ∨
        Disjoint (c i).realize (B j).realize) ∧
      (∀ i j, (∀ a : (c i).realize,
        (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
        (∀ a : (c i).realize,
        (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0)) ∧
      ∀ i, ∃ r : ℕ, ∃ ψ : Fin r → (c i).realize → ℝ,
        (∀ q, Continuous (ψ q)) ∧ (∀ a, StrictMono (fun q => ψ q a)) ∧
        ∀ a t, (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
          (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔
          ∃ q, t = ψ q a :=
  s2v_hardt_cad2_root_partition P B

/-- Ordered active roots have Boolean graphs on the actual restricted base.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3,
printed pp. 6–7, restricted graph construction step. -/
theorem s2v_hardt_cad2_section_formulas {n k r : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (C : s2v_t11b_Formula n) (hC : IsConnected C.realize)
    (ψ : Fin r → C.realize → ℝ) (hψ : ∀ q, Continuous (ψ q))
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (hr : ∀ a t, (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
      (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔
      ∃ q, t = ψ q a)
    (D : s2v_t11b_Formula n) (hD : D.realize ⊆ C.realize) :
    ∃ g : Fin r → s2v_t11b_Formula (n + 1), ∀ q y,
      y ∈ (g q).realize ↔ ∃ a : D.realize,
        (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q ⟨a.val, hD a.property⟩ :=
  s2v_hardt_cad2_section_formulas_aux P C hC ψ hψ hm hr D hD

example {n k r : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (C : s2v_t11b_Formula n) (hC : IsConnected C.realize)
    (ψ : Fin r → C.realize → ℝ) (hψ : ∀ q, Continuous (ψ q))
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (hr : ∀ a t, (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
      (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔
      ∃ q, t = ψ q a)
    (D : s2v_t11b_Formula n) (hD : D.realize ⊆ C.realize) :
    ∃ g : Fin r → s2v_t11b_Formula (n + 1), ∀ q y,
      y ∈ (g q).realize ↔ ∃ a : D.realize,
        (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q ⟨a.val, hD a.property⟩ :=
  s2v_hardt_cad2_section_formulas P C hC ψ hψ hm hr D hD

/-- A section graph retains its supplied base chart with actual graph formulas.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.3,
printed pp. 6–7, restricted graph construction step. -/
theorem s2v_hardt_cad2_graph_chart_formulas {n d : ℕ}
    (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (s : C.realize → ℝ) (hs : Continuous s)
    (g : s2v_t11b_Formula (n + 1))
    (hg : ∀ y, y ∈ g.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = s a)
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔
        z = (e a).val) :
    ∃ E : g.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula ((n + 1) + d),
    ∃ I : s2v_t11b_Formula (d + (n + 1)),
      (∀ a : C.realize, ∀ y : g.realize,
        (∀ v, y.val v.succ = a.val v) → E y = e a) ∧
      (∀ y : g.realize, ∀ z : EuclideanSpace ℝ (Fin d),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E y).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1},
        ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔
          y = (E.symm z).val) :=
  s2v_hardt_cad2_graph_chart_formulas_aux C e s hs g hg G hG

example {n d : ℕ}
    (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (s : C.realize → ℝ) (hs : Continuous s)
    (g : s2v_t11b_Formula (n + 1))
    (hg : ∀ y, y ∈ g.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = s a)
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔
        z = (e a).val) :
    ∃ E : g.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula ((n + 1) + d),
    ∃ I : s2v_t11b_Formula (d + (n + 1)),
      (∀ a : C.realize, ∀ y : g.realize,
        (∀ v, y.val v.succ = a.val v) → E y = e a) ∧
      (∀ y : g.realize, ∀ z : EuclideanSpace ℝ (Fin d),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E y).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1},
        ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔
          y = (E.symm z).val) :=
  s2v_hardt_cad2_graph_chart_formulas C e s hs g hg G hG

end HodgeLean.Foundations.Program
