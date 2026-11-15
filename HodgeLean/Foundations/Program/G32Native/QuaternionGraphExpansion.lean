import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section
set_option maxHeartbeats 200000

namespace HodgeLean.Foundations.Program.QuaternionGraph

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The exterior product of the graphs of one common scalar on two ordered frames. -/
def graphWedge {n : ℕ} (u v : Fin n → V) (t : K) : ⋀[K]^n V :=
  exteriorPower.ιMulti K n (fun i => u i + t • v i)

/-- An ordered mixed wedge, selecting the second frame at the indicated positions. -/
def mixedWedge {n : ℕ} (u v : Fin n → V) (s : Finset (Fin n)) : ⋀[K]^n V :=
  exteriorPower.ιMulti K n (fun i => if i ∈ s then v i else u i)

/-- The homogeneous graph coefficient obtained by collecting selections of equal size. -/
def graphCoeff {n : ℕ} (u v : Fin n → V) (k : Fin (n+1)) : ⋀[K]^n V :=
  ∑ s : Finset (Fin n), if s.card = k.val then mixedWedge (K := K) u v s else 0

/-- Scaling the selected positions scales a mixed wedge by the corresponding power. -/
theorem mixedWedge_smul {n : ℕ} (u v : Fin n → V) (s : Finset (Fin n)) (t : K) :
    mixedWedge (K := K) u (fun i => t • v i) s = t ^ s.card • mixedWedge (K := K) u v s := by
  classical
  have h := (exteriorPower.ιMulti K n (M := V)).toMultilinearMap.map_smul_univ
    (fun i => if i ∈ s then t else 1) (fun i => if i ∈ s then v i else u i)
  have hp : (∏ i : Fin n, if i ∈ s then t else 1) = t ^ s.card := by
    simp only [Finset.prod_ite, Finset.prod_const_one, mul_one]
    have hf : Finset.univ.filter (fun i : Fin n => i ∈ s) = s := by ext; simp
    rw [hf, Finset.prod_const]
  rw [hp] at h
  have he : (fun i => if i ∈ s then t • v i else u i) =
      (fun i => (if i ∈ s then t else 1) • (if i ∈ s then v i else u i)) := by
    funext i
    by_cases hi : i ∈ s <;> simp only [hi, ite_true, ite_false, one_smul]
  exact (congrArg (exteriorPower.ιMulti K n) he).trans h

/-- Multilinearity expands a graph wedge into its ordered mixed wedges. -/
theorem graphWedge_eq_sum_mixed {n : ℕ} (u v : Fin n → V) (t : K) :
    graphWedge u v t = ∑ s : Finset (Fin n), t ^ s.card • mixedWedge (K := K) u v s := by
  classical
  have h := (exteriorPower.ιMulti K n (M := V)).toMultilinearMap.map_add_univ
    (fun i => t • v i) u
  have he : (fun i => t • v i) + u = (fun i => u i + t • v i) := by
    funext i
    exact add_comm _ _
  rw [he] at h
  change graphWedge u v t = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro s hs
  exact mixedWedge_smul u v s t

/-- Grouping the mixed wedges by cardinality gives a vector polynomial of degree at most `n`. -/
theorem graphWedge_eq_sum_coeff {n : ℕ} (u v : Fin n → V) (t : K) :
    graphWedge u v t = ∑ k : Fin (n+1), t ^ k.val • graphCoeff u v k := by
  classical
  rw [graphWedge_eq_sum_mixed]
  let c : Finset (Fin n) → Fin (n+1) := fun s =>
    ⟨s.card, Nat.lt_succ_of_le (by simpa only [Finset.card_univ, Fintype.card_fin] using
      s.card_le_univ)⟩
  rw [← Finset.sum_fiberwise Finset.univ c (fun s => t ^ s.card • mixedWedge (K := K) u v s)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [graphCoeff, Finset.smul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  have hc : c s = k ↔ s.card = k.val := Fin.ext_iff
  by_cases h : s.card = k.val
  · simp only [hc, h, ite_true, smul_zero]
  · simp only [hc, h, ite_false, smul_zero]

#print axioms graphWedge_eq_sum_coeff
end HodgeLean.Foundations.Program.QuaternionGraph
