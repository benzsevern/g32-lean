import HodgeLean.Foundations.Program.G32ContractionProjection
import HodgeLean.Adapters.F1575Products

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option Elab.async false
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

theorem g32c_cupExterior_wedge (Y : Over (Spec ↧ℂ)) [GrpObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (i j k : ℕ) (h : i + j = k) :
    letI := (torusCohomology_cupProductOf Y).finite
    ∀ (v : ⋀[ℂ]^i (ℂ ⊗[ℚ] HQ Y 1)) (w : ⋀[ℂ]^j (ℂ ⊗[ℚ] HQ Y 1)),
      ((cupProductOf Y).cupWedgeMap k).baseChange ℂ
        ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv k).symm
          ⟨(v : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ Y 1)) *
              (w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ Y 1)), h ▸ SetLike.mul_mem_graded v.property w.property⟩) =
      (cupProductOf Y).cupC h
        (((cupProductOf Y).cupWedgeMap i).baseChange ℂ
          ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv i).symm v))
        (((cupProductOf Y).cupWedgeMap j).baseChange ℂ
          ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv j).symm w)) := by
  subst k
  intro v w
  have hw : exteriorPower.wedge ℂ (ℂ ⊗[ℚ] HQ Y 1) i j v w =
      ⟨(v : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ Y 1)) *
        (w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ Y 1)),
        SetLike.mul_mem_graded v.property w.property⟩ :=
    Subtype.ext (Symplectic.coe_wedge v w)
  simpa only [f1575ExteriorCohomology_eq_baseChange, hw] using
    f1575ExteriorCohomology_wedge (torusCohomology_cupProductOf Y) i j v w


theorem g32c_decompose_mul_map {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (f : V →ₗ[ℂ] W)
    (i j : ℕ) (x : ⋀[ℂ]^i V) (y : ⋀[ℂ]^j V) :
    exteriorPower.map (i + j) f
      (DirectSum.decompose (fun n : ℕ => ⋀[ℂ]^n V)
        ((x : ExteriorAlgebra ℂ V) * (y : ExteriorAlgebra ℂ V)) (i + j)) =
      exteriorPower.wedge ℂ W i j (exteriorPower.map i f x) (exteriorPower.map j f y) := by
  apply Subtype.ext
  rw [exteriorPower.coe_map, DirectSum.decompose_of_mem_same
    (fun n : ℕ => ⋀[ℂ]^n V) (SetLike.mul_mem_graded x.property y.property),
    Symplectic.coe_wedge, exteriorPower.coe_map, exteriorPower.coe_map]
  exact map_mul (ExteriorAlgebra.map f) _ _

variable {A : g32t_Sixfold}

theorem g32c_oneC_inl (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    g32c_oneC X S hS ∘ₗ LinearMap.inl ℂ _ _ =
      (homPullback (fst A.X (g32c_B X S hS)) 1).baseChange ℂ := by
  apply LinearMap.ext
  intro v
  simp only [g32c_oneC, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.inl_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.proj_apply,
    map_zero, Finset.sum_const_zero, add_zero]

theorem g32c_oneC_inr (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    g32c_oneC X S hS ∘ₗ LinearMap.inr ℂ _ _ =
      (homPullback (snd A.X (g32c_B X S hS)) 1).baseChange ℂ ∘ₗ g32c_oneB X S hS := by
  apply LinearMap.ext
  intro v
  simp only [g32c_oneC, g32c_oneB, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    LinearMap.proj_apply, map_zero, zero_add, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [spec_homPullback_comp, LinearMap.baseChange_comp, LinearMap.comp_apply]


end HodgeLean.Foundations.Program
