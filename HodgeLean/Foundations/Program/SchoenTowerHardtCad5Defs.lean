import HodgeLean.Foundations.Program.SchoenTowerHardtCad4

/-! Concrete finite chart partitions and their integer maximum.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A finite list of nonempty Boolean chart cells partitioning a specified set.
Source: Coste, Real Algebraic Sets (2005), Definition 1.2 and Theorem 1.3. -/
structure s2v_hardt_cad5_Partition {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) where
  count : ℕ
  cell : Fin count → s2v_t11b_Formula n
  dim : Fin count → ℕ
  chart : (i : Fin count) → (cell i).realize ≃ₜ
    {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1}
  forward : (i : Fin count) → s2v_t11b_Formula (n + dim i)
  inverse : (i : Fin count) → s2v_t11b_Formula (dim i + n)
  nonempty : ∀ i, (cell i).realize.Nonempty
  disjoint : Pairwise (fun i j => Disjoint (cell i).realize (cell j).realize)
  cover : (⋃ i, (cell i).realize) = S
  bound : ∀ i, dim i ≤ n
  forward_eq : ∀ i (x : (cell i).realize) (z : EuclideanSpace ℝ (Fin (dim i))),
    WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈
      (forward i).realize ↔ z = (chart i x).val
  inverse_eq : ∀ i
    (z : {z : EuclideanSpace ℝ (Fin (dim i)) | ∀ v, -1 < z v ∧ z v < 1})
    (x : EuclideanSpace ℝ (Fin n)),
    WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈
      (inverse i).realize ↔ x = ((chart i).symm z).val

example {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (P : s2v_hardt_cad5_Partition S) : (⋃ i, (P.cell i).realize) = S := P.cover

/-- Integer maximum of natural dimensions with sentinel minus one.
Source: Coste, Real Algebraic Sets (2005), Proposition 1.7; empty-family convention. -/
def s2v_hardt_cad5_max {m : ℕ} (d : Fin m → ℕ) : ℤ :=
  (Finset.univ.image (fun i => (d i : ℤ)) ∪ {-1}).max' (by simp)

example : s2v_hardt_cad5_max (Fin.elim0 : Fin 0 → ℕ) = -1 := by
  simp [s2v_hardt_cad5_max]

/-- Dimension recorded by the concrete finite partition.
Source: Coste, Real Algebraic Sets (2005), Proposition 1.7. -/
def s2v_hardt_cad5_Partition.dimension {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S) : ℤ :=
  s2v_hardt_cad5_max P.dim

example {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (P : s2v_hardt_cad5_Partition S) : P.dimension = s2v_hardt_cad5_max P.dim := rfl

end HodgeLean.Foundations.Program
