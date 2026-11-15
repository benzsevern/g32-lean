import HodgeLean.Foundations.Program.CompensationAssemblyIntegration
import HodgeLean.Foundations.Program.CompensationAssemblyProduct
import HodgeLean.Foundations.Program.CompensationAssemblyExterior

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 10000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

theorem cq_exteriorPower_map_coe {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (n : ℕ) (f : M →ₗ[R] N) (a : ⋀[R]^n M) :
    (exteriorPower.map n f a : ExteriorAlgebra R N) = ExteriorAlgebra.map f a := by
  have hm : (⋀[R]^n N).subtype ∘ₗ exteriorPower.map n f =
      (ExteriorAlgebra.map f).toLinearMap ∘ₗ (⋀[R]^n M).subtype := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change (exteriorPower.map n f (exteriorPower.ιMulti R n v) : ExteriorAlgebra R N) =
      ExteriorAlgebra.map f (exteriorPower.ιMulti R n v)
    rw [exteriorPower.map_apply_ιMulti]
    exact (ExteriorAlgebra.map_apply_ιMulti f v).symm
  exact LinearMap.congr_fun hm a

variable (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem cq_cross_exterior (i j : ℕ) (a : HQ A i) (b : HQ Y j) :
    (((torusCohomology_cupProductOf (A ⊗ Y)).cupWedgeEquiv (i+j)).symm
      (cq_cross A Y i j a b) : ExteriorAlgebra ℚ (HQ (A ⊗ Y) 1)) =
      ExteriorAlgebra.map (homPullback (fst A Y) 1)
        (((torusCohomology_cupProductOf A).cupWedgeEquiv i).symm a) *
      ExteriorAlgebra.map (homPullback (snd A Y) 1)
        (((torusCohomology_cupProductOf Y).cupWedgeEquiv j).symm b) := by
  let TA := torusCohomology_cupProductOf A
  let TY := torusCohomology_cupProductOf Y
  let TP := torusCohomology_cupProductOf (A ⊗ Y)
  let u := exteriorPower.map i (homPullback (fst A Y) 1) ((TA.cupWedgeEquiv i).symm a)
  let v := exteriorPower.map j (homPullback (snd A Y) 1) ((TY.cupWedgeEquiv j).symm b)
  have hc : cq_cross A Y i j a b = TP.cupWedgeEquiv (i+j) (exteriorPower.wedge ℚ _ i j u v) := by
    change (cupProductOf (A ⊗ Y)).cup rfl (homPullback (fst A Y) i a)
      (homPullback (snd A Y) j b) = _
    rw [TorusCohomology.cupWedgeEquiv_apply, CupProduct.cupWedgeMap_wedge]
    congr 1
    · rw [spec_homPullback_eq_cupWedgeEquiv]
      rfl
    · rw [spec_homPullback_eq_cupWedgeEquiv]
      rfl
  change ((TP.cupWedgeEquiv (i+j)).symm (cq_cross A Y i j a b) :
    ExteriorAlgebra ℚ (HQ (A ⊗ Y) 1)) = _
  rw [hc, LinearEquiv.symm_apply_apply]
  change (u : ExteriorAlgebra ℚ (HQ (A ⊗ Y) 1)) * v = _
  rw [cq_exteriorPower_map_coe, cq_exteriorPower_map_coe]

theorem cq_cross_exterior_product
    (e : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1)
    (heA : ∀ a, e (a, 0) = homPullback (fst A Y) 1 a)
    (heY : ∀ b, e (0, b) = homPullback (snd A Y) 1 b)
    (i j : ℕ) (a : HQ A i) (b : HQ Y j) :
    ExteriorAlgebra.map e.symm.toLinearMap
      (((torusCohomology_cupProductOf (A ⊗ Y)).cupWedgeEquiv (i+j)).symm
        (cq_cross A Y i j a b)) =
      ExteriorAlgebra.map (LinearMap.inl ℚ (HQ A 1) (HQ Y 1))
        (((torusCohomology_cupProductOf A).cupWedgeEquiv i).symm a) *
      ExteriorAlgebra.map (LinearMap.inr ℚ (HQ A 1) (HQ Y 1))
        (((torusCohomology_cupProductOf Y).cupWedgeEquiv j).symm b) := by
  have hU : e.symm.toLinearMap ∘ₗ homPullback (fst A Y) 1 =
      LinearMap.inl ℚ (HQ A 1) (HQ Y 1) := by
    apply LinearMap.ext
    intro x
    change e.symm (homPullback (fst A Y) 1 x) = (x, 0)
    have h := congrArg e.symm (heA x)
    simpa only [LinearEquiv.symm_apply_apply] using h.symm
  have hV : e.symm.toLinearMap ∘ₗ homPullback (snd A Y) 1 =
      LinearMap.inr ℚ (HQ A 1) (HQ Y 1) := by
    apply LinearMap.ext
    intro x
    change e.symm (homPullback (snd A Y) 1 x) = (0, x)
    have h := congrArg e.symm (heY x)
    simpa only [LinearEquiv.symm_apply_apply] using h.symm
  rw [cq_cross_exterior, map_mul]
  change
    ((ExteriorAlgebra.map e.symm.toLinearMap).comp (ExteriorAlgebra.map (homPullback (fst A Y) 1))) _ *
    ((ExteriorAlgebra.map e.symm.toLinearMap).comp (ExteriorAlgebra.map (homPullback (snd A Y) 1))) _ = _
  rw [ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map, hU, hV]

def cq_projectionMap (I : HQ Y 4 ≃ₗ[ℚ] ℚ)
    (e : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1) : HQ (A ⊗ Y) 10 →ₗ[ℚ] HQ A 6 :=
  (TensorProduct.rid ℚ (HQ A 6)).toLinearMap ∘ₗ
    TensorProduct.map ((torusCohomology_cupProductOf A).cupWedgeEquiv 6).toLinearMap
      (I.toLinearMap ∘ₗ ((torusCohomology_cupProductOf Y).cupWedgeEquiv 4).toLinearMap) ∘ₗ
    cq_exteriorTensorComponent ℚ (HQ A 1) (HQ Y 1) 6 4 ∘ₗ
    (ExteriorAlgebra.map e.symm.toLinearMap).toLinearMap ∘ₗ
    (⋀[ℚ]^10 (HQ (A ⊗ Y) 1)).subtype ∘ₗ
    ((torusCohomology_cupProductOf (A ⊗ Y)).cupWedgeEquiv 10).symm.toLinearMap

theorem cq_projectionMap_cross (I : HQ Y 4 ≃ₗ[ℚ] ℚ)
    (e : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1)
    (heA : ∀ a, e (a, 0) = homPullback (fst A Y) 1 a)
    (heY : ∀ b, e (0, b) = homPullback (snd A Y) 1 b)
    (a : HQ A 6) (b : HQ Y 4) :
    cq_projectionMap A Y I e (cq_cross A Y 6 4 a b) = I b • a := by
  simp only [cq_projectionMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.subtype_apply, AlgHom.toLinearMap_apply]
  rw [cq_cross_exterior_product A Y e heA heY 6 4,
    cq_exteriorTensorComponent_same, TensorProduct.map_tmul]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
    TensorProduct.rid_tmul]

theorem cq_projectionMap_cross_ne (I : HQ Y 4 ≃ₗ[ℚ] ℚ)
    (e : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1)
    (heA : ∀ a, e (a, 0) = homPullback (fst A Y) 1 a)
    (heY : ∀ b, e (0, b) = homPullback (snd A Y) 1 b)
    (i j : ℕ) (hij : i + j = 10) (hj : j ≠ 4) (a : HQ A i) (b : HQ Y j) :
    cq_projectionMap A Y I e (HQ.castEquiv (A ⊗ Y) hij (cq_cross A Y i j a b)) = 0 := by
  have hgeneral (n m : ℕ) (h : n = m) (z : HQ (A ⊗ Y) n) :
      (((torusCohomology_cupProductOf (A ⊗ Y)).cupWedgeEquiv m).symm
        (HQ.castEquiv (A ⊗ Y) h z) : ExteriorAlgebra ℚ (HQ (A ⊗ Y) 1)) =
      (((torusCohomology_cupProductOf (A ⊗ Y)).cupWedgeEquiv n).symm z :
        ExteriorAlgebra ℚ (HQ (A ⊗ Y) 1)) := by
    subst m
    rfl
  have hcast := hgeneral (i+j) 10 hij (cq_cross A Y i j a b)
  simp only [cq_projectionMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.subtype_apply, AlgHom.toLinearMap_apply]
  rw [hcast, cq_cross_exterior_product A Y e heA heY i j,
    cq_exteriorTensorComponent_ne ℚ (HQ A 1) (HQ Y 1) 6 4 i j hj,
    map_zero, map_zero]

theorem cq_projection_normalized_linear (hY : TopologicalSpace.dim Y.left = 2) :
    ∃ (I : HQ Y 4 ≃ₗ[ℚ] ℚ) (P : HQ (A ⊗ Y) 10 →ₗ[ℚ] HQ A 6),
      (∀ (c : AlgebraicCycle Y.left ℚ),
        (∀ x, c x ≠ 0 → Order.coheight x = 2) →
        I (ccm3_cycleClass Y 2 c) = AlgebraicCycle.degree Y.hom c) ∧
      (∀ (a : HQ A 6) (b : HQ Y 4), P (cq_cross A Y 6 4 a b) = I b • a) ∧
      (∀ (i j : ℕ) (hij : i + j = 10), j ≠ 4 →
        ∀ (a : HQ A i) (b : HQ Y j),
          P (HQ.castEquiv (A ⊗ Y) hij (cq_cross A Y i j a b)) = 0) := by
  obtain ⟨I, hI⟩ := cq_surface_integration Y hY
  obtain ⟨e, heA, heY⟩ := cq_degree_one_product_equiv A Y
  exact ⟨I, cq_projectionMap A Y I e, hI,
    cq_projectionMap_cross A Y I e heA heY,
    cq_projectionMap_cross_ne A Y I e heA heY⟩

end HodgeLean.Foundations.Program
