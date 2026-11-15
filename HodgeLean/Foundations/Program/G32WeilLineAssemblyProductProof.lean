import HodgeLean.Foundations.Program.G32WeilLineAssemblyProjection
import HodgeLean.Foundations.Program.G32ContractionPullbackC
import HodgeLean.Foundations.Program.G32ContractionProductDegree
import HodgeLean.Foundations.Program.CycleFoundationsPullback
import HodgeLean.Foundations.Program.G32RepTransport
import HodgeLean.Foundations.Program.CycleFoundations
import HodgeLean.Foundations.Program.CyclotomicWeilLinear

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

theorem g32c_schoen_product_span_main (A : g32t_Sixfold) (X : g32p_Cover A) {r : ℕ}
    (S : Fin r → g32p_Supplier) (hS : ∀ j, g32p_Admissible X.aut (S j))
    (y : ∀ j, ⋀[ℚ]^(2 * (X.part (S j) (hS j)).k) (HQ (g32c_parts X S hS j) 1))
    (hy : ∀ j, (cupProductOf (g32c_parts X S hS j)).cupWedgeMap _ (y j) ∈
      algebraicCycleClassSpan (g32c_parts X S hS j) (X.part (S j) (hS j)).k)
    (p : ℕ) (hp : 2 * p = ∑ j, 2 * (X.part (S j) (hS j)).k) :
    g32c_classB X S hS (2 * p) (g32c_prodAbs fun j =>
      (HodgeBlocks.complexifyWedge _ (y j) :
        ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))) ∈
      (algebraicCycleClassSpan (g32c_B X S hS) p).baseChange ℂ := by
  classical
  letI := (torusCohomology_cupProductOf (g32c_B X S hS)).finite
  letI (j : Fin r) := (torusCohomology_cupProductOf (g32c_parts X S hS j)).finite
  let n : Fin r → ℕ := fun j => (X.part (S j) (hS j)).k
  let v := fun j => HodgeBlocks.complexifyWedge (2 * n j) (y j)
  let x := fun j => exteriorPower.map (2 * n j)
    ((homPullback (cfd_proj r (g32c_parts X S hS) j) 1).baseChange ℂ) (v j)
  have hx (j : Fin r) :
      f1575ExteriorCohomology (torusCohomology_cupProductOf (g32c_B X S hS)) _ (x j) ∈
        (algebraicCycleClassSpan (g32c_B X S hS) (n j)).baseChange ℂ := by
    letI := g32c_finite_projection_hom r (g32c_parts X S hS) j
    rw [f1575ExteriorCohomology_eq_baseChange]
    change ((cupProductOf (g32c_B X S hS)).cupWedgeMap _).baseChange ℂ
      ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv _).symm
        (exteriorPower.map _ ((homPullback (cfd_proj r (g32c_parts X S hS) j) 1).baseChange ℂ)
          (v j))) ∈ _
    rw [← g32c_cupC_pullback, ← f1575ExteriorCohomology_eq_baseChange
      (torusCohomology_cupProductOf (g32c_parts X S hS j))]
    apply g32c_pullbackC_span_aux
    rw [f1575ExteriorCohomology_complexify]
    exact Submodule.tmul_mem_baseChange_of_mem _ (hy j)
  have hmem : g32c_prodAbs (fun j => (v j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))) ∈
      ⋀[ℂ]^(2 * p) (∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1) := by
    rw [hp]
    exact g32c_orderedProduct_mem _ _ v
  let z := exteriorPower.map (2 * p) (g32c_oneB X S hS)
    ⟨g32c_prodAbs (fun j => (v j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))), hmem⟩
  have hz : (z : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_B X S hS) 1)) =
      (List.ofFn fun j => (x j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_B X S hS) 1))).prod := by
    simp only [z, exteriorPower.coe_map, g32c_prodAbs, map_list_prod, List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext j
    simp only [Function.comp_apply]
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, g32c_oneB_single]
    simp only [x, exteriorPower.coe_map]
  have hh := g32c_finite_wedge_span (g32c_B X S hS) r n x hx p hp z hz
  have hd : DirectSum.decompose
      (fun i : ℕ => ⋀[ℂ]^i (∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))
      (g32c_prodAbs (fun j => (v j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))))
      (2 * p) = ⟨_, hmem⟩ := Subtype.ext (DirectSum.decompose_of_mem_same _ hmem)
  unfold g32c_classB
  change ((cupProductOf (g32c_B X S hS)).cupWedgeMap (2 * p)).baseChange ℂ
    ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (2 * p)).symm
      (exteriorPower.map (2 * p) (g32c_oneB X S hS)
        (DirectSum.decompose
          (fun i : ℕ => ⋀[ℂ]^i (∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))
          (g32c_prodAbs (fun j => (v j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))))
          (2 * p)))) ∈ _
  rw [hd]
  simpa only [f1575ExteriorCohomology_eq_baseChange, z] using hh


end HodgeLean.Foundations.Program
