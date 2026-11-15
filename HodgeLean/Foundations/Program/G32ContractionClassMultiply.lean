import HodgeLean.Foundations.Program.G32ContractionCupExterior

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


theorem g32c_classB_mul (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (i j k : ℕ) (h : i + j = k)
    (x : ⋀[ℂ]^i (∀ l, ℂ ⊗[ℚ] HQ (g32c_parts X S hS l) 1))
    (y : ⋀[ℂ]^j (∀ l, ℂ ⊗[ℚ] HQ (g32c_parts X S hS l) 1)) :
    g32c_classB X S hS k ((x : ExteriorAlgebra ℂ _) * (y : ExteriorAlgebra ℂ _)) =
      (cupProductOf (g32c_B X S hS)).cupC h
        (g32c_classB X S hS i x) (g32c_classB X S hS j y) := by
  subst k
  letI := (torusCohomology_cupProductOf (g32c_B X S hS)).finite
  unfold g32c_classB
  rw [g32c_decompose_mul_map]
  have hx : DirectSum.decompose (fun n : ℕ => ⋀[ℂ]^n _) (x : ExteriorAlgebra ℂ _) i = x :=
    Subtype.ext (DirectSum.decompose_of_mem_same _ x.property)
  have hy : DirectSum.decompose (fun n : ℕ => ⋀[ℂ]^n _) (y : ExteriorAlgebra ℂ _) j = y :=
    Subtype.ext (DirectSum.decompose_of_mem_same _ y.property)
  rw [hx, hy]
  simpa only [f1575ExteriorCohomology_eq_baseChange] using
    f1575ExteriorCohomology_wedge (torusCohomology_cupProductOf (g32c_B X S hS)) i j
      (exteriorPower.map i (g32c_oneB X S hS) x)
      (exteriorPower.map j (g32c_oneB X S hS) y)

theorem g32c_class_cross (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (i j k : ℕ) (h : i + j = k) :
    letI := (torusCohomology_cupProductOf A.X).finite
    ∀ (w : ⋀[ℂ]^i (ℂ ⊗[ℚ] HQ A.X 1))
      (z : ⋀[ℂ]^j (∀ l, ℂ ⊗[ℚ] HQ (g32c_parts X S hS l) 1)),
    g32c_class X S hS k
      (ExteriorAlgebra.map (LinearMap.inl ℂ _ _) (w : ExteriorAlgebra ℂ _) *
        ExteriorAlgebra.map (LinearMap.inr ℂ _ _) (z : ExteriorAlgebra ℂ _)) =
      (cupProductOf (A.X ⊗ g32c_B X S hS)).cupC h
        ((homPullback (fst A.X (g32c_B X S hS)) i).baseChange ℂ
          (((cupProductOf A.X).cupWedgeMap i).baseChange ℂ
            ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv i).symm w)))
        ((homPullback (snd A.X (g32c_B X S hS)) j).baseChange ℂ
          (g32c_classB X S hS j z)) := by
  subst k
  intro w z
  letI := (torusCohomology_cupProductOf (A.X ⊗ g32c_B X S hS)).finite
  letI := (torusCohomology_cupProductOf (g32c_B X S hS)).finite
  have hd := g32c_decompose_mul_map (g32c_oneC X S hS) i j
    (exteriorPower.map i (LinearMap.inl ℂ _ _) w)
    (exteriorPower.map j (LinearMap.inr ℂ _ _) z)
  simp only [exteriorPower.coe_map] at hd
  unfold g32c_class
  rw [hd]
  have hm := f1575ExteriorCohomology_wedge
    (torusCohomology_cupProductOf (A.X ⊗ g32c_B X S hS)) i j
    (exteriorPower.map i (g32c_oneC X S hS)
      (exteriorPower.map i (LinearMap.inl ℂ _ _) w))
    (exteriorPower.map j (g32c_oneC X S hS)
      (exteriorPower.map j (LinearMap.inr ℂ _ _) z))
  simp only [f1575ExteriorCohomology_eq_baseChange] at hm
  rw [hm]
  have hleft : exteriorPower.map i (g32c_oneC X S hS)
      (exteriorPower.map i (LinearMap.inl ℂ _ _) w) =
      exteriorPower.map i ((homPullback (fst A.X (g32c_B X S hS)) 1).baseChange ℂ) w := by
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, g32c_oneC_inl]
  have hright : exteriorPower.map j (g32c_oneC X S hS)
      (exteriorPower.map j (LinearMap.inr ℂ _ _) z) =
      exteriorPower.map j ((homPullback (snd A.X (g32c_B X S hS)) 1).baseChange ℂ ∘ₗ
        g32c_oneB X S hS) z := by
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, g32c_oneC_inr]
  rw [hleft, hright, ← g32c_cupC_pullback]
  congr 1
  rw [exteriorPower.map_comp, LinearMap.comp_apply, ← g32c_cupC_pullback]
  unfold g32c_classB
  congr 4
  apply Subtype.ext
  exact (DirectSum.decompose_of_mem_same (fun n : ℕ => ⋀[ℂ]^n _) z.property).symm

end HodgeLean.Foundations.Program
