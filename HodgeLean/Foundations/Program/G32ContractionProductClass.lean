import HodgeLean.Foundations.Program.G32ContractionTwoDefs
import HodgeLean.Foundations.Program.G32ContractionPiBaseChange
import HodgeLean.Foundations.Program.G32ContractionProductDegree
import HodgeLean.Foundations.Program.CycleFoundations

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option Elab.async false
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program
variable {A : g32t_Sixfold}

theorem g32c_oneB_bijective (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) : Function.Bijective (g32c_oneB X S hS) := by
  obtain ⟨hπ⟩ := cfd_product_limit r (g32c_parts X S hS)
  have h := cfd_kunneth_one r (g32c_parts X S hS) (g32c_B X S hS)
    (cfd_proj r (g32c_parts X S hS)) hπ
  unfold cfd_oneMap at h
  exact g32c_piSum_baseChange_bijective
    (fun j => homPullback (cfd_proj r (g32c_parts X S hS) j) 1) h

theorem g32c_classB_prod_ne_zero_aux (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (d : ℕ)
    (I : HQ (g32c_B X S hS) (2 * d) ≃ₗ[ℚ] ℚ) (n : Fin r → ℕ) (hn : ∑ j, n j = 2 * d)
    (x : ∀ j, ⋀[ℂ]^(n j) (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1)) (hx : ∀ j, x j ≠ 0) :
    I.toLinearMap.baseChange ℂ (g32c_classB X S hS (2 * d)
      (g32c_prodAbs fun j => (x j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1)))) ≠
      0 := by
  letI := (torusCohomology_cupProductOf (g32c_B X S hS)).finite
  let z := g32c_prodAbs fun j => (x j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))
  have hz : z ≠ 0 := by
    apply g32c_orderedProduct_ne_zero
    intro j h
    apply hx j
    apply Subtype.ext
    exact h
  have hm : z ∈ ⋀[ℂ]^(2 * d) (∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1) := by
    rw [← hn]
    exact g32c_orderedProduct_mem _ n x
  have hI := g32c_baseChange_bijective I.toLinearMap I.bijective
  have hcup := g32c_baseChange_bijective ((cupProductOf (g32c_B X S hS)).cupWedgeMap (2 * d))
    ((torusCohomology_cupProductOf (g32c_B X S hS)).bijective (2 * d))
  have hone := g32c_oneB_bijective X S hS
  intro hzero
  have hclass : g32c_classB X S hS (2 * d) z = 0 :=
    hI.1 (by simpa only [map_zero] using hzero)
  unfold g32c_classB at hclass
  let D := DirectSum.decompose
    (fun i : ℕ => ⋀[ℂ]^i (∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1)) z (2 * d)
  let E := exteriorPower.map (2 * d) (g32c_oneB X S hS)
  let e := HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv
    (V := HQ (g32c_B X S hS) 1) (2 * d)
  have hw : e.symm (E D) = 0 := hcup.1 (by simpa only [map_zero] using hclass)
  have hv : E D = 0 := e.symm.injective (by simpa only [map_zero] using hw)
  have hd : D = 0 := (exteriorPower.map_injective_field (n := 2 * d) hone.1)
    (by simpa only [map_zero] using hv)
  have hid := DirectSum.decompose_of_mem_same
    (fun i : ℕ => ⋀[ℂ]^i (∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1)) hm
  change (D : ExteriorAlgebra ℂ (∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1)) = z at hid
  rw [hd, ZeroMemClass.coe_zero] at hid
  exact hz hid.symm

end HodgeLean.Foundations.Program
