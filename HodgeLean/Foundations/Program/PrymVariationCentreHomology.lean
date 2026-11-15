import HodgeLean.Foundations.Program.PrymVariationCentreDefs

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b63d_scalar_commutes (z g : b4b_Group)
    (hz : b4b_toMatrix z = g32h_omega • (1 : Matrix (Fin 4) (Fin 4) ℂ)) :
    z * g = g * z := by
  apply Subtype.val_injective
  change b4b_toMatrix (z * g) = b4b_toMatrix (g * z)
  rw [map_mul, map_mul, hz]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, mul_comm]

theorem b63d_homology_deck_mul (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) (g h : b4b_Group) (x : b6m_H1 (b6m_Fibre b C t)) :
    homologyMap ℤ 1 (TopCat.ofHom (b6m_deck b b4b_Group C hC t g))
      (homologyMap ℤ 1 (TopCat.ofHom (b6m_deck b b4b_Group C hC t h)) x) =
    homologyMap ℤ 1 (TopCat.ofHom (b6m_deck b b4b_Group C hC t (g * h))) x := by
  rw [← LinearMap.comp_apply, ← homologyMap_comp]
  congr 3
  ext q
  apply Subtype.ext
  exact Prod.ext rfl (mul_smul g h q.val.2).symm

end HodgeLean.Foundations.Program
