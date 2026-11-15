import HodgeLean.Foundations.Program.SchoenTowerHardtCad6Proofs

/-! Implication from Boolean chart partitions and dimension extraction to descending
frontier refinement. Local triviality is outside this interface.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A top layer retains Boolean marks, ambient limit formulas and a smaller remainder.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3 and Propositions 1.7–1.9. -/
theorem s2v_hardt_cad6_layer {n d k l : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) (hP : ∀ i, P.dim i ≤ d)
    (B : Fin k → s2v_t11b_Formula n) (L : Fin l → s2v_t11b_Formula n) :
    ∃ U T : s2v_t11b_Formula n,
    ∃ PU : s2v_hardt_cad5_Partition U.realize,
    ∃ PT : s2v_hardt_cad5_Partition T.realize,
    ∃ boundary limits : Fin PU.count → s2v_t11b_Formula n,
    ∃ remainderMarks : Fin (k + l) → s2v_t11b_Formula n,
      U.realize ⊆ S.realize ∧ T.realize = S.realize \ U.realize ∧
      PT.dimension < (d : ℤ) ∧
      (∀ i, PU.dim i = d) ∧
      (∀ i, IsOpen {x : S.realize | x.val ∈ (PU.cell i).realize}) ∧
      (∀ i j, i ≠ j → Disjoint (PU.cell j).realize (closure (PU.cell i).realize)) ∧
      (∀ i, (boundary i).realize = closure (PU.cell i).realize \ (PU.cell i).realize) ∧
      (∀ i, (limits i).realize = closure (PU.cell i).realize) ∧
      (∀ i j, (PU.cell i).realize ⊆ (B j).realize ∨
        Disjoint (PU.cell i).realize (B j).realize) ∧
      (∀ i j, (PU.cell i).realize ⊆ (L j).realize ∨
        Disjoint (PU.cell i).realize (L j).realize) ∧
      (∀ j, (remainderMarks (Fin.castAdd l j)).realize = T.realize ∩ (B j).realize) ∧
      (∀ j, (remainderMarks (Fin.natAdd k j)).realize = T.realize ∩ (L j).realize) :=
  s2v_hardt_cad6_layer_aux S P hP B L

example {n d k l : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) (hP : ∀ i, P.dim i ≤ d)
    (B : Fin k → s2v_t11b_Formula n) (L : Fin l → s2v_t11b_Formula n) :
    ∃ U T : s2v_t11b_Formula n,
    ∃ PU : s2v_hardt_cad5_Partition U.realize,
    ∃ PT : s2v_hardt_cad5_Partition T.realize,
    ∃ boundary limits : Fin PU.count → s2v_t11b_Formula n,
    ∃ remainderMarks : Fin (k + l) → s2v_t11b_Formula n,
      U.realize ⊆ S.realize ∧ T.realize = S.realize \ U.realize ∧
      PT.dimension < (d : ℤ) ∧
      (∀ i, PU.dim i = d) ∧
      (∀ i, IsOpen {x : S.realize | x.val ∈ (PU.cell i).realize}) ∧
      (∀ i j, i ≠ j → Disjoint (PU.cell j).realize (closure (PU.cell i).realize)) ∧
      (∀ i, (boundary i).realize = closure (PU.cell i).realize \ (PU.cell i).realize) ∧
      (∀ i, (limits i).realize = closure (PU.cell i).realize) ∧
      (∀ i j, (PU.cell i).realize ⊆ (B j).realize ∨
        Disjoint (PU.cell i).realize (B j).realize) ∧
      (∀ i j, (PU.cell i).realize ⊆ (L j).realize ∨
        Disjoint (PU.cell i).realize (L j).realize) ∧
      (∀ j, (remainderMarks (Fin.castAdd l j)).realize = T.realize ∩ (B j).realize) ∧
      (∀ j, (remainderMarks (Fin.natAdd k j)).realize = T.realize ∩ (L j).realize) :=
  s2v_hardt_cad6_layer S P hP B L

/-- Descending dimension refinement gives ambient incidence compatible with every mark.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.5 (frontier assertion only). -/
theorem s2v_hardt_cad6_descending {n d k : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) (hP : ∀ i, P.dim i ≤ d)
    (B : Fin k → s2v_t11b_Formula n) :
    ∃ Q : s2v_hardt_cad5_Partition S.realize,
      (∀ i, Q.dim i ≤ d) ∧
      (∀ i j, (Q.cell i).realize ⊆ (B j).realize ∨
        Disjoint (Q.cell i).realize (B j).realize) ∧
      (∀ i j, ((Q.cell j).realize ∩ closure (Q.cell i).realize).Nonempty →
        (Q.cell j).realize ⊆ closure (Q.cell i).realize ∧
          (j = i ∨ Q.dim j < Q.dim i)) :=
  s2v_hardt_cad6_descending_aux S P hP B

example {n d k : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) (hP : ∀ i, P.dim i ≤ d)
    (B : Fin k → s2v_t11b_Formula n) :
    ∃ Q : s2v_hardt_cad5_Partition S.realize,
      (∀ i, Q.dim i ≤ d) ∧
      (∀ i j, (Q.cell i).realize ⊆ (B j).realize ∨
        Disjoint (Q.cell i).realize (B j).realize) ∧
      (∀ i j, ((Q.cell j).realize ∩ closure (Q.cell i).realize).Nonempty →
        (Q.cell j).realize ⊆ closure (Q.cell i).realize ∧
          (j = i ∨ Q.dim j < Q.dim i)) :=
  s2v_hardt_cad6_descending S P hP B

/-- Selecting exactly the ambient cells in a Boolean carrier preserves ambient incidence.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.5. -/
theorem s2v_hardt_cad6_carrier {n k : ℕ} (A : s2v_t11b_Formula n)
    (B : Fin k → s2v_t11b_Formula n) :
    ∃ P : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin n))),
    ∃ Q : s2v_hardt_cad5_Partition A.realize,
    ∃ select : Fin Q.count ↪ Fin P.count,
      (∀ i, Q.cell i = P.cell (select i) ∧ Q.dim i = P.dim (select i)) ∧
      (∀ j, (P.cell j).realize ⊆ A.realize ↔ ∃ i, select i = j) ∧
      (∀ i, (P.cell i).realize ⊆ A.realize ∨ Disjoint (P.cell i).realize A.realize) ∧
      (∀ i j, (P.cell i).realize ⊆ (B j).realize ∨
        Disjoint (P.cell i).realize (B j).realize) ∧
      (∀ i j, ((P.cell j).realize ∩ closure (P.cell i).realize).Nonempty →
        (P.cell j).realize ⊆ closure (P.cell i).realize ∧
          (j = i ∨ P.dim j < P.dim i)) ∧
      (∀ i j, (Q.cell i).realize ⊆ (B j).realize ∨
        Disjoint (Q.cell i).realize (B j).realize) ∧
      (∀ i j, ((Q.cell j).realize ∩ closure (Q.cell i).realize).Nonempty →
        (Q.cell j).realize ⊆ closure (Q.cell i).realize ∧
          (j = i ∨ Q.dim j < Q.dim i)) :=
  s2v_hardt_cad6_carrier_aux A B

example {n k : ℕ} (A : s2v_t11b_Formula n)
    (B : Fin k → s2v_t11b_Formula n) :
    ∃ P : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin n))),
    ∃ Q : s2v_hardt_cad5_Partition A.realize,
    ∃ select : Fin Q.count ↪ Fin P.count,
      (∀ i, Q.cell i = P.cell (select i) ∧ Q.dim i = P.dim (select i)) ∧
      (∀ j, (P.cell j).realize ⊆ A.realize ↔ ∃ i, select i = j) ∧
      (∀ i, (P.cell i).realize ⊆ A.realize ∨ Disjoint (P.cell i).realize A.realize) ∧
      (∀ i j, (P.cell i).realize ⊆ (B j).realize ∨
        Disjoint (P.cell i).realize (B j).realize) ∧
      (∀ i j, ((P.cell j).realize ∩ closure (P.cell i).realize).Nonempty →
        (P.cell j).realize ⊆ closure (P.cell i).realize ∧
          (j = i ∨ P.dim j < P.dim i)) ∧
      (∀ i j, (Q.cell i).realize ⊆ (B j).realize ∨
        Disjoint (Q.cell i).realize (B j).realize) ∧
      (∀ i j, ((Q.cell j).realize ∩ closure (Q.cell i).realize).Nonempty →
        (Q.cell j).realize ⊆ closure (Q.cell i).realize ∧
          (j = i ∨ Q.dim j < Q.dim i)) :=
  s2v_hardt_cad6_carrier A B

end HodgeLean.Foundations.Program
