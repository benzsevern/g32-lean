import HodgeLean.Foundations.Program.PrymParabolicIntersectionReflection
import HodgeLean.Foundations.Program.PrymParabolicIntersectionDualTriangle

noncomputable section
open Convexity
namespace HodgeLean.Foundations.Program

/-- The point on the segment from the midpoint of face `k` to the triangle barycentre.
Source: Hatcher, *Algebraic Topology*, §3.3, barycentric dual cells. -/
def hga_dualPoint (k : Fin 3) (t : unitInterval) : StdSimplex ℝ (Fin 3) where
  weights := Finsupp.equivFunOnFinite.symm
    (fun i ↦ (1 - (t : ℝ)) * (if i = k then 0 else 1 / 2) + (t : ℝ) / 3)
  nonneg := by
    intro i
    change 0 ≤ (1 - (t : ℝ)) * (if i = k then 0 else 1 / 2) + (t : ℝ) / 3
    apply add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) _) (div_nonneg t.property.1 (by norm_num))
    split_ifs <;> norm_num
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    fin_cases k <;> norm_num [Fin.sum_univ_three] <;> ring

theorem hga_dualPoint_continuous (k : Fin 3) : Continuous (hga_dualPoint k) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).continuous_iff]
  apply continuous_pi
  intro i
  simp only [Function.comp_apply, hga_dualPoint, Finsupp.coe_equivFunOnFinite_symm]
  exact ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
    (continuous_subtype_val.div_const 3)

theorem hga_dualPoint_interior (k : Fin 3) (t : unitInterval) (ht : 0 < (t : ℝ))
    (i : Fin 3) : 0 < (hga_dualPoint k t).weights i := by
  change 0 < (1 - (t : ℝ)) * (if i = k then 0 else 1 / 2) + (t : ℝ) / 3
  apply add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr t.property.2) _)
    (div_pos ht (by norm_num))
  split_ifs <;> norm_num

theorem hga_dualPoint_barycentre (k : Fin 3) :
    hga_dualPoint k 1 = hga_triangleRetraction 0 := by
  apply StdSimplex.ext
  ext i
  rw [hga_triangleRetraction_zero_weights]
  change (1 - (1 : ℝ)) * (if i = k then 0 else 1 / 2) + (1 : ℝ) / 3 = 1 / 3
  ring

theorem hga_dualPoint_midpoint (k : Fin 3) :
    hga_dualPoint k 0 = StdSimplex.map k.succAbove
      (StdSimplex.homeomorphI.symm ⟨1 / 2, by constructor <;> norm_num⟩) := by
  apply StdSimplex.ext
  ext i
  rw [hg5_face_w]
  norm_num [hga_dualPoint]

theorem hga_dualPoint_injective (k : Fin 3) : Function.Injective (hga_dualPoint k) := by
  intro s t h
  have he := congrArg (fun a : StdSimplex ℝ (Fin 3) ↦ a.weights k) h
  simp [hga_dualPoint] at he
  exact Subtype.ext he

theorem hga_dualPoint_distinct_spokes (k l : Fin 3) (hkl : k ≠ l)
    (s t : unitInterval) (h : hga_dualPoint k s = hga_dualPoint l t) : s = 1 ∧ t = 1 := by
  have hk := congrArg (fun a : StdSimplex ℝ (Fin 3) ↦ a.weights k) h
  have hl := congrArg (fun a : StdSimplex ℝ (Fin 3) ↦ a.weights l) h
  simp [hga_dualPoint, hkl, Ne.symm hkl] at hk hl
  constructor <;> apply Subtype.ext <;> change (_ : ℝ) = 1 <;> linarith

theorem hga_dualPoint_zero_weight (k i : Fin 3) (t : unitInterval) :
    (hga_dualPoint k t).weights i = 0 ↔ t = 0 ∧ i = k := by
  constructor
  · intro hz
    have ht := t.property.2
    change (1 - (t : ℝ)) * (if i = k then 0 else 1 / 2) + (t : ℝ) / 3 = 0 at hz
    by_cases hik : i = k
    · rw [if_pos hik, mul_zero, zero_add] at hz
      refine ⟨?_, hik⟩
      apply Subtype.ext
      change (t : ℝ) = 0
      linarith
    · rw [if_neg hik] at hz
      linarith
  · rintro ⟨rfl, rfl⟩
    simp [hga_dualPoint]

#print axioms hga_dualPoint_zero_weight
#print axioms hga_dualPoint_distinct_spokes
#print axioms hga_dualPoint_injective
#print axioms hga_dualPoint_midpoint
#print axioms hga_dualPoint_barycentre
#print axioms hga_dualPoint_interior
#print axioms hga_dualPoint_continuous
#print axioms hga_dualPoint
end HodgeLean.Foundations.Program
