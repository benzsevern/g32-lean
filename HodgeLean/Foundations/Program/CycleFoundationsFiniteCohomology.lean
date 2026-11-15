import HodgeLean.Foundations.Program.CycleFoundationsFinite

/-! Degree-one cohomology of iterated products. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
attribute [local irreducible] HQ homPullback
namespace HodgeLean.Foundations.Program

theorem cfd_oneMap_product_succ (r : ℕ) (A : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, GrpObj (A i)] [∀ i, IsCommMonObj (A i)]
    [∀ i, IsIntegral (A i).left] [∀ i, Smooth (A i).hom]
    [∀ i, IsProjective (A i).hom] (x : ∀ i, HQ (A i) 1) :
    cfd_oneMap (r + 1) A (cfd_product (r + 1) A) (cfd_proj (r + 1) A) x =
      homPullback (fst (A 0) (cfd_product r (fun i => A i.succ))) 1 (x 0) +
      homPullback (snd (A 0) (cfd_product r (fun i => A i.succ))) 1
        (cfd_oneMap r (fun i => A i.succ) (cfd_product r (fun i => A i.succ))
          (cfd_proj r (fun i => A i.succ)) (fun i => x i.succ)) := by
  simp only [cfd_oneMap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Fin.sum_univ_succ, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact LinearMap.congr_fun (spec_homPullback_comp
    (snd (A 0) (cfd_product r (fun i => A i.succ)))
    (cfd_proj r (fun i => A i.succ) i) 1) (x i.succ)

theorem cfd_oneMap_product_bijective (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, GrpObj (A i)] [∀ i, IsCommMonObj (A i)]
    [∀ i, IsIntegral (A i).left] [∀ i, Smooth (A i).hom]
    [∀ i, IsProjective (A i).hom] :
    Function.Bijective (cfd_oneMap r A (cfd_product r A) (cfd_proj r A)) := by
  induction r with
  | zero =>
    have hm : (𝟙 (cfd_product 0 A) : cfd_product 0 A ⟶ cfd_product 0 A) = 1 :=
      SemiCartesianMonoidalCategory.toUnit_unique _ _
    have hz : (LinearMap.id : HQ (cfd_product 0 A) 1 →ₗ[ℚ] HQ (cfd_product 0 A) 1) = 0 := by
      rw [← spec_homPullback_id, hm, spec_homPullback_one]
    refine ⟨fun x y _ => Subsingleton.elim _ _, fun x => ⟨(fun i => i.elim0), ?_⟩⟩
    have hx := LinearMap.congr_fun hz x
    simpa only [cfd_oneMap, Fin.sum_univ_zero, LinearMap.zero_apply, LinearMap.id_apply] using hx.symm
  | succ r ih =>
    have hb := cp_kunneth_H1 (A 0) (cfd_product r (fun i => A i.succ))
    have ht := ih (fun i => A i.succ)
    constructor
    · intro x y h
      rw [cfd_oneMap_product_succ, cfd_oneMap_product_succ] at h
      have hh := hb.injective
        (a₁ := (x 0, cfd_oneMap r (fun i => A i.succ)
          (cfd_product r (fun i => A i.succ)) (cfd_proj r (fun i => A i.succ))
          (fun i => x i.succ)))
        (a₂ := (y 0, cfd_oneMap r (fun i => A i.succ)
          (cfd_product r (fun i => A i.succ)) (cfd_proj r (fun i => A i.succ))
          (fun i => y i.succ))) h
      have h0 := congrArg Prod.fst hh
      have hs := ht.injective (congrArg Prod.snd hh)
      funext i
      exact Fin.cases h0 (fun j => congrFun hs j) i
    · intro x
      obtain ⟨⟨a, b⟩, hab⟩ := hb.surjective x
      obtain ⟨v, hv⟩ := ht.surjective b
      refine ⟨Fin.cases a v, ?_⟩
      rw [cfd_oneMap_product_succ]
      simpa only [cfd_product, Fin.cases_zero, Fin.cases_succ, hv] using hab

end HodgeLean.Foundations.Program
