import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Proofs

/-! Implication from finite Boolean chart partitions to dimension comparisons,
Boolean boundary operations and top-cell extraction. Dimension arguments precede
extraction; frontier refinement and continuous extensions at limits are deferred.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Partition maxima agree, also under Boolean-graph bijections.
Source: Coste, Real Algebraic Sets (2005), Propositions 1.7–1.8. -/
theorem s2v_hardt_cad5_invariance {n q : ℕ} (S : s2v_t11b_Formula n) (T : s2v_t11b_Formula q)
    (P : s2v_hardt_cad5_Partition S.realize)
    (Q : s2v_hardt_cad5_Partition S.realize)
    (R : s2v_hardt_cad5_Partition T.realize) :
    P.dimension = Q.dimension ∧
    ∀ (f : S.realize ≃ T.realize) (G : s2v_t11b_Formula (n + q)),
      (∀ (x : S.realize) (y : EuclideanSpace ℝ (Fin q)),
        WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => y v)) ∈ G.realize ↔
          y = (f x).val) → P.dimension = R.dimension :=
  s2v_hardt_cad5_invariance_aux S T P Q R

example {n q : ℕ} (S : s2v_t11b_Formula n) (T : s2v_t11b_Formula q)
    (P : s2v_hardt_cad5_Partition S.realize)
    (Q : s2v_hardt_cad5_Partition S.realize)
    (R : s2v_hardt_cad5_Partition T.realize) :
    P.dimension = Q.dimension ∧
    ∀ (f : S.realize ≃ T.realize) (G : s2v_t11b_Formula (n + q)),
      (∀ (x : S.realize) (y : EuclideanSpace ℝ (Fin q)),
        WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => y v)) ∈ G.realize ↔
          y = (f x).val) → P.dimension = R.dimension :=
  s2v_hardt_cad5_invariance S T P Q R

/-- Finite unions take maxima and inclusion preserves the dimension order.
Source: Coste, Real Algebraic Sets (2005), Proposition 1.7. -/
theorem s2v_hardt_cad5_unions {n k : ℕ} (B : Fin k → s2v_t11b_Formula n)
    (P : (i : Fin k) → s2v_hardt_cad5_Partition (B i).realize)
    (U : s2v_hardt_cad5_Partition (⋃ i, (B i).realize))
    (S T : s2v_t11b_Formula n)
    (Q : s2v_hardt_cad5_Partition S.realize)
    (R : s2v_hardt_cad5_Partition T.realize) :
    U.dimension =
      (Finset.univ.image (fun i => (P i).dimension) ∪ {-1}).max' (by simp) ∧
    (S.realize ⊆ T.realize → Q.dimension ≤ R.dimension) :=
  s2v_hardt_cad5_unions_aux B P U S T Q R

example {n k : ℕ} (B : Fin k → s2v_t11b_Formula n)
    (P : (i : Fin k) → s2v_hardt_cad5_Partition (B i).realize)
    (U : s2v_hardt_cad5_Partition (⋃ i, (B i).realize))
    (S T : s2v_t11b_Formula n)
    (Q : s2v_hardt_cad5_Partition S.realize)
    (R : s2v_hardt_cad5_Partition T.realize) :
    U.dimension =
      (Finset.univ.image (fun i => (P i).dimension) ∪ {-1}).max' (by simp) ∧
    (S.realize ⊆ T.realize → Q.dimension ≤ R.dimension) :=
  s2v_hardt_cad5_unions B P U S T Q R

/-- An ambient closure has a Boolean description and the same dimension.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1 and Proposition 1.9 (dimension equality consequence). -/
theorem s2v_hardt_cad5_closure {n : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) :
    ∃ C : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition C.realize,
      C.realize = closure S.realize ∧ Q.dimension = P.dimension :=
  s2v_hardt_cad5_closure_aux S P

example {n : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) :
    ∃ C : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition C.realize,
      C.realize = closure S.realize ∧ Q.dimension = P.dimension :=
  s2v_hardt_cad5_closure S P

/-- The ambient closure minus the set has strictly smaller dimension when inhabited.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1 and Proposition 1.9. -/
theorem s2v_hardt_cad5_boundary {n : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) :
    ∃ B : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition B.realize,
      B.realize = closure S.realize \ S.realize ∧
      (S.realize.Nonempty → Q.dimension < P.dimension) ∧
      (S.realize = ∅ → B.realize = ∅ ∧ Q.dimension = -1 ∧ P.dimension = -1) :=
  s2v_hardt_cad5_boundary_aux S P

example {n : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) :
    ∃ B : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition B.realize,
      B.realize = closure S.realize \ S.realize ∧
      (S.realize.Nonempty → Q.dimension < P.dimension) ∧
      (S.realize = ∅ → B.realize = ∅ ∧ Q.dimension = -1 ∧ P.dimension = -1) :=
  s2v_hardt_cad5_boundary S P

/-- Chartwise extraction returns relatively open top cells and a Boolean smaller remainder.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3 and Propositions 1.7–1.8. -/
theorem s2v_hardt_cad5_chart_top {n d k : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ (x : C.realize) (z : EuclideanSpace ℝ (Fin d)),
      WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ G.realize ↔
        z = (e x).val)
    (J : s2v_t11b_Formula (d + n))
    (hJ : ∀ (z : {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
      (x : EuclideanSpace ℝ (Fin n)),
      WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ J.realize ↔
        x = (e.symm z).val)
    (Z : Fin k → s2v_t11b_Formula n)
    (PZ : s2v_hardt_cad5_Partition (⋃ j, (Z j).realize))
    (hZ : PZ.dimension < (d : ℤ)) :
    ∃ P : s2v_hardt_cad5_Partition (C.realize \ ⋃ j, (Z j).realize),
    ∃ R : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition R.realize,
      (∀ i, P.dim i ≤ d) ∧
      (∀ i, P.dim i = d →
        IsOpen {x : C.realize | x.val ∈ (P.cell i).realize}) ∧
      R.realize = C.realize \ (⋃ i : {i : Fin P.count // P.dim i = d},
        (P.cell i.val).realize) ∧
      Q.dimension < (d : ℤ) :=
  s2v_hardt_cad5_chart_top_aux C e G hG J hJ Z PZ hZ

example {n d k : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ (x : C.realize) (z : EuclideanSpace ℝ (Fin d)),
      WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ G.realize ↔
        z = (e x).val)
    (J : s2v_t11b_Formula (d + n))
    (hJ : ∀ (z : {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
      (x : EuclideanSpace ℝ (Fin n)),
      WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ J.realize ↔
        x = (e.symm z).val)
    (Z : Fin k → s2v_t11b_Formula n)
    (PZ : s2v_hardt_cad5_Partition (⋃ j, (Z j).realize))
    (hZ : PZ.dimension < (d : ℤ)) :
    ∃ P : s2v_hardt_cad5_Partition (C.realize \ ⋃ j, (Z j).realize),
    ∃ R : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition R.realize,
      (∀ i, P.dim i ≤ d) ∧
      (∀ i, P.dim i = d →
        IsOpen {x : C.realize | x.val ∈ (P.cell i).realize}) ∧
      R.realize = C.realize \ (⋃ i : {i : Fin P.count // P.dim i = d},
        (P.cell i.val).realize) ∧
      Q.dimension < (d : ℤ) :=
  s2v_hardt_cad5_chart_top C e G hG J hJ Z PZ hZ

/-- Partition extraction separates top cells in the ambient incidence relation.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3 and Propositions 1.7–1.9. -/
theorem s2v_hardt_cad5_partition_top {n : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) :
    ∃ Z : s2v_t11b_Formula n, ∃ PZ : s2v_hardt_cad5_Partition Z.realize,
    ∃ U : s2v_t11b_Formula n, ∃ PU : s2v_hardt_cad5_Partition U.realize,
    ∃ R : s2v_t11b_Formula n, ∃ PR : s2v_hardt_cad5_Partition R.realize,
    ∃ parent : Fin PU.count → Fin P.count,
      Z.realize =
        (⋃ i, closure (P.cell i).realize \ (P.cell i).realize) ∪
        (⋃ i : {i : Fin P.count // (P.dim i : ℤ) < P.dimension},
          closure (P.cell i.val).realize) ∧
      (S.realize.Nonempty → PZ.dimension < P.dimension) ∧
      (∀ i, (PU.dim i : ℤ) = P.dimension ∧
        (P.dim (parent i) : ℤ) = P.dimension) ∧
      (∀ i, (PU.cell i).realize ⊆ (P.cell (parent i)).realize \ Z.realize) ∧
      (∀ i, IsOpen {x : S.realize | x.val ∈ (PU.cell i).realize}) ∧
      (∀ i, IsOpen {x : (P.cell (parent i)).realize | x.val ∈ (PU.cell i).realize}) ∧
      (∀ i j, i ≠ j → Disjoint (PU.cell j).realize (closure (PU.cell i).realize)) ∧
      R.realize = S.realize \ U.realize ∧
      (S.realize.Nonempty → PR.dimension < P.dimension) ∧
      (S.realize = ∅ → PU.count = 0 ∧ R.realize = ∅ ∧ PR.dimension = -1) :=
  s2v_hardt_cad5_partition_top_aux S P

example {n : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) :
    ∃ Z : s2v_t11b_Formula n, ∃ PZ : s2v_hardt_cad5_Partition Z.realize,
    ∃ U : s2v_t11b_Formula n, ∃ PU : s2v_hardt_cad5_Partition U.realize,
    ∃ R : s2v_t11b_Formula n, ∃ PR : s2v_hardt_cad5_Partition R.realize,
    ∃ parent : Fin PU.count → Fin P.count,
      Z.realize =
        (⋃ i, closure (P.cell i).realize \ (P.cell i).realize) ∪
        (⋃ i : {i : Fin P.count // (P.dim i : ℤ) < P.dimension},
          closure (P.cell i.val).realize) ∧
      (S.realize.Nonempty → PZ.dimension < P.dimension) ∧
      (∀ i, (PU.dim i : ℤ) = P.dimension ∧
        (P.dim (parent i) : ℤ) = P.dimension) ∧
      (∀ i, (PU.cell i).realize ⊆ (P.cell (parent i)).realize \ Z.realize) ∧
      (∀ i, IsOpen {x : S.realize | x.val ∈ (PU.cell i).realize}) ∧
      (∀ i, IsOpen {x : (P.cell (parent i)).realize | x.val ∈ (PU.cell i).realize}) ∧
      (∀ i j, i ≠ j → Disjoint (PU.cell j).realize (closure (PU.cell i).realize)) ∧
      R.realize = S.realize \ U.realize ∧
      (S.realize.Nonempty → PR.dimension < P.dimension) ∧
      (S.realize = ∅ → PU.count = 0 ∧ R.realize = ∅ ∧ PR.dimension = -1) :=
  s2v_hardt_cad5_partition_top S P

end HodgeLean.Foundations.Program
