import HodgeLean.Foundations.Program.CompensationAssemblyExteriorExt
import HodgeLean.Foundations.Program.CompensationAssemblyCrossComparison

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

variable (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem cq_cross_exterior_forward
    (e : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1)
    (heA : ∀ a, e (a, 0) = homPullback (fst A Y) 1 a)
    (heY : ∀ b, e (0, b) = homPullback (snd A Y) 1 b)
    (i j : ℕ) (a : ⋀[ℚ]^i (HQ A 1)) (b : ⋀[ℚ]^j (HQ Y 1)) :
    ExteriorAlgebra.map e.toLinearMap
      (ExteriorAlgebra.map (LinearMap.inl ℚ (HQ A 1) (HQ Y 1)) a *
        ExteriorAlgebra.map (LinearMap.inr ℚ (HQ A 1) (HQ Y 1)) b) =
      (((torusCohomology_cupProductOf (A ⊗ Y)).cupWedgeEquiv (i + j)).symm
        (cq_cross A Y i j
          ((torusCohomology_cupProductOf A).cupWedgeEquiv i a)
          ((torusCohomology_cupProductOf Y).cupWedgeEquiv j b)) :
            ExteriorAlgebra ℚ (HQ (A ⊗ Y) 1)) := by
  have h := cq_cross_exterior_product A Y e heA heY i j
    ((torusCohomology_cupProductOf A).cupWedgeEquiv i a)
    ((torusCohomology_cupProductOf Y).cupWedgeEquiv j b)
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h
  have hm := congrArg (ExteriorAlgebra.map e.toLinearMap) h
  rw [cq_exterior_map_symm_apply] at hm
  exact hm.symm

def cq_productExteriorRealization
    (e : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1) (n : ℕ) :
    ExteriorAlgebra ℚ (HQ A 1 × HQ Y 1) →ₗ[ℚ] HQ (A ⊗ Y) n :=
  ((torusCohomology_cupProductOf (A ⊗ Y)).cupWedgeEquiv n).toLinearMap ∘ₗ
    cq_exteriorDegree ℚ (HQ (A ⊗ Y) 1) n ∘ₗ
    (ExteriorAlgebra.map e.toLinearMap).toLinearMap

theorem cq_productExteriorRealization_surjective
    (e : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1) (n : ℕ) :
    Function.Surjective (cq_productExteriorRealization A Y e n) := by
  intro v
  refine ⟨ExteriorAlgebra.map e.symm.toLinearMap
    (((torusCohomology_cupProductOf (A ⊗ Y)).cupWedgeEquiv n).symm v), ?_⟩
  change (torusCohomology_cupProductOf (A ⊗ Y)).cupWedgeEquiv n
    (cq_exteriorDegree ℚ (HQ (A ⊗ Y) 1) n
      (ExteriorAlgebra.map e.toLinearMap
        (ExteriorAlgebra.map e.symm.toLinearMap
          (((torusCohomology_cupProductOf (A ⊗ Y)).cupWedgeEquiv n).symm v)))) = v
  rw [cq_exterior_map_symm_apply, cq_exteriorDegree_same, LinearEquiv.apply_symm_apply]

theorem cq_productExteriorRealization_product
    (e : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1)
    (heA : ∀ a, e (a, 0) = homPullback (fst A Y) 1 a)
    (heY : ∀ b, e (0, b) = homPullback (snd A Y) 1 b)
    (i j n : ℕ) (h : i + j = n)
    (a : ⋀[ℚ]^i (HQ A 1)) (b : ⋀[ℚ]^j (HQ Y 1)) :
    cq_productExteriorRealization A Y e n
      (ExteriorAlgebra.map (LinearMap.inl ℚ (HQ A 1) (HQ Y 1)) a *
        ExteriorAlgebra.map (LinearMap.inr ℚ (HQ A 1) (HQ Y 1)) b) =
      HQ.castEquiv (A ⊗ Y) h (cq_cross A Y i j
        ((torusCohomology_cupProductOf A).cupWedgeEquiv i a)
        ((torusCohomology_cupProductOf Y).cupWedgeEquiv j b)) := by
  subst n
  simp only [cq_productExteriorRealization, LinearMap.comp_apply,
    LinearEquiv.coe_coe, AlgHom.toLinearMap_apply]
  rw [cq_cross_exterior_forward A Y e heA heY, cq_exteriorDegree_same,
    LinearEquiv.apply_symm_apply, HQ.castEquiv_apply_self]

theorem cq_productExteriorRealization_product_ne
    (e : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1)
    (heA : ∀ a, e (a, 0) = homPullback (fst A Y) 1 a)
    (heY : ∀ b, e (0, b) = homPullback (snd A Y) 1 b)
    (i j n : ℕ) (h : i + j ≠ n)
    (a : ⋀[ℚ]^i (HQ A 1)) (b : ⋀[ℚ]^j (HQ Y 1)) :
    cq_productExteriorRealization A Y e n
      (ExteriorAlgebra.map (LinearMap.inl ℚ (HQ A 1) (HQ Y 1)) a *
        ExteriorAlgebra.map (LinearMap.inr ℚ (HQ A 1) (HQ Y 1)) b) = 0 := by
  simp only [cq_productExteriorRealization, LinearMap.comp_apply,
    LinearEquiv.coe_coe, AlgHom.toLinearMap_apply]
  rw [cq_cross_exterior_forward A Y e heA heY,
    cq_exteriorDegree_ne ℚ (HQ (A ⊗ Y) 1) n (i + j) h]
  exact ((torusCohomology_cupProductOf (A ⊗ Y)).cupWedgeEquiv n).toLinearMap.map_zero

theorem cq_cross_linear_ext {N : Type*} [AddCommGroup N] [Module ℚ N]
    (n : ℕ) (L S : HQ (A ⊗ Y) n →ₗ[ℚ] N)
    (h : ∀ (i j : ℕ) (hij : i + j = n) (a : HQ A i) (b : HQ Y j),
      L (HQ.castEquiv (A ⊗ Y) hij (cq_cross A Y i j a b)) =
      S (HQ.castEquiv (A ⊗ Y) hij (cq_cross A Y i j a b))) : L = S := by
  obtain ⟨e, heA, heY⟩ := cq_degree_one_product_equiv A Y
  have hE : L.comp (cq_productExteriorRealization A Y e n) =
      S.comp (cq_productExteriorRealization A Y e n) := by
    apply cq_exterior_product_linear_ext ℚ (HQ A 1) (HQ Y 1) N
    intro i j a b
    change L (cq_productExteriorRealization A Y e n
      (ExteriorAlgebra.map (LinearMap.inl ℚ (HQ A 1) (HQ Y 1)) a *
        ExteriorAlgebra.map (LinearMap.inr ℚ (HQ A 1) (HQ Y 1)) b)) =
      S (cq_productExteriorRealization A Y e n
        (ExteriorAlgebra.map (LinearMap.inl ℚ (HQ A 1) (HQ Y 1)) a *
          ExteriorAlgebra.map (LinearMap.inr ℚ (HQ A 1) (HQ Y 1)) b))
    by_cases hij : i + j = n
    · rw [cq_productExteriorRealization_product A Y e heA heY i j n hij]
      exact h i j hij _ _
    · rw [cq_productExteriorRealization_product_ne A Y e heA heY i j n hij]
      exact L.map_zero.trans S.map_zero.symm
  apply LinearMap.ext
  intro v
  obtain ⟨x, rfl⟩ := cq_productExteriorRealization_surjective A Y e n v
  exact LinearMap.congr_fun hE x

end HodgeLean.Foundations.Program
