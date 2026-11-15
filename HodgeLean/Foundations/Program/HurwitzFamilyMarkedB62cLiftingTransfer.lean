import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cBoundaryLifting

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
theorem b6m_cycle_lifting_of_torsionFree_homology
    (R : Type) [CommRing R] [IsDomain R] (S : ShortComplex (ModuleCat.{0} R))
    [Module.IsTorsionFree R S.X₃] [Module.IsTorsionFree R S.homology]
    (n : R) (hn : n ≠ 0) (c : S.X₁) (z : S.X₂)
    (hc : S.f.hom c = n • z) :
    ∃ w q : S.X₁, S.f.hom w = 0 ∧ c - w = n • q := by
  have hz : S.g.hom z = 0 := by
    apply (smul_eq_zero.mp (show n • S.g.hom z = 0 from ?_)).resolve_left hn
    rw [← map_smul, ← hc]
    exact S.moduleCat_zero_apply c
  let Z : LinearMap.ker S.g.hom := ⟨z, hz⟩
  have hclass : S.moduleCatHomologyClass Z = 0 := by
    apply (smul_eq_zero.mp (show n • S.moduleCatHomologyClass Z = 0 from ?_)).resolve_left hn
    rw [← map_smul]
    exact (b6m_homologyClass_zero_iff R S (n • Z)).mpr ⟨c, hc⟩
  obtain ⟨q, hq⟩ := (b6m_homologyClass_zero_iff R S Z).mp hclass
  refine ⟨c - n • q, q, ?_, ?_⟩
  · rw [map_sub, map_smul, hq, hc, sub_self]
  · abel

set_option backward.isDefEq.respectTransparency false in
theorem b6m_cycle_lifting_of_incidence_homology_embedding
    (S T : ShortComplex (ModuleCat.{0} ℤ)) [Module.IsTorsionFree ℤ S.X₃]
    {F E : Type} (left right : E → F)
    (faces : T.X₁ ≃ₗ[ℤ] (F →₀ ℤ)) (edges : T.X₂ ≃ₗ[ℤ] (E →₀ ℤ))
    (hd : ∀ c e, edges (T.f.hom c) e = faces c (right e) - faces c (left e))
    (j : S.homology →ₗ[ℤ] T.homology) (hj : Function.Injective j)
    (n : ℤ) (hn : n ≠ 0) (c : S.X₁) (z : S.X₂)
    (hc : S.f.hom c = n • z) :
    ∃ w q : S.X₁, S.f.hom w = 0 ∧ c - w = n • q := by
  letI := b6m_incidence_model_homology_torsionFree T left right faces edges hd
  letI : Module.IsTorsionFree ℤ S.homology :=
    Function.Injective.moduleIsTorsionFree j hj (fun n x ↦ j.map_smul' n x)
  have hc' : S.f.hom c = S.X₂.isModule.smul n z :=
    hc.trans (int_smul_eq_zsmul S.X₂.isModule n z).symm
  obtain ⟨w, q, hw, hq⟩ := b6m_cycle_lifting_of_torsionFree_homology ℤ S n hn c z hc'
  exact ⟨w, q, hw, hq.trans (int_smul_eq_zsmul S.X₁.isModule n q)⟩

end HodgeLean.Foundations.Program
