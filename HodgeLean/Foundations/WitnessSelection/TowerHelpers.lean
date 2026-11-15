import HodgeLean.Foundations.Program.SchoenCycleC1UnmarkedNormalizationTower

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.WitnessSelection

theorem tower_restriction_isIso
    (r : ℕ) (X : Fin (r + 1) → Scheme)
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc)
    (J : Type*) (D : ∀ i, J → (X i).IdealSheafData) (p q : Fin r → J)
    (hD : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i) (D i.castSucc t)
      (D i.castSucc (p i) ⊔ D i.castSucc (q i)))
    (hblowup : ∀ i : Fin r, ∀ (T : Scheme) (j : T ⟶ X i.castSucc),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty ((((D i.castSucc (p i) ⊔ D i.castSucc (q i)).comap j).ideal V)
          ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ X i.succ, u ≫ b i = j)
    (U : (X 0).Opens) (havoid : ∀ t, ∀ x ∈ U, x ∉ (D 0 t).support) :
    ∀ i, IsIso (s2e_towerTotalMap X (𝟙 (X 0)) b i ∣_ U) := by
  let I := fun i : Fin r => D i.castSucc (p i) ⊔ D i.castSucc (q i)
  have hs := s2e_c1_strict_support_tower_subset r X b J D I hD
  intro i
  induction i using Fin.induction with
  | zero => rw [s2e_towerTotalMap_zero, morphismRestrict_id]; infer_instance
  | succ j ih =>
    let V := (s2e_towerTotalMap X (𝟙 (X 0)) b j.castSucc) ⁻¹ᵁ U
    have hI : (I j).comap V.ι = ⊤ := by
      apply s2e_comap_eq_top_of_disjoint
      rw [Scheme.Opens.range_ι]
      apply Set.disjoint_left.mpr
      intro x hx hm
      rw [Scheme.IdealSheafData.support_sup] at hm
      exact havoid (p j) _ hx (hs j.castSucc (p j) hm.1)
    haveI : IsIso (pullback.snd (b j) V.ι) :=
      s2e_blowup_scheme_isIso_off_centre (b j) (I j) (hblowup j) V.ι hI
    haveI : IsIso (b j ∣_ V) := by
      haveI : IsIso ((pullbackRestrictIsoRestrict (b j) V).hom ≫ (b j ∣_ V)) := by
        rw [pullbackRestrictIsoRestrict_hom_morphismRestrict]
        infer_instance
      exact IsIso.of_isIso_comp_left (pullbackRestrictIsoRestrict (b j) V).hom _
    rw [s2e_towerTotalMap_succ, morphismRestrict_comp]
    letI := ih
    infer_instance

end HodgeLean.WitnessSelection
