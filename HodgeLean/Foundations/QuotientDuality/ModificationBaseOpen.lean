import HodgeLean.Foundations.Program.SchoenCycleC1StrictSupportTower

/-! The actual total base map is an isomorphism over the unmarked open. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem base_tower_isIso_off_centres (r : ℕ) (X : Fin (r + 1) → Scheme)
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc)
    (I : ∀ i : Fin r, (X i.castSucc).IdealSheafData)
    (hblowup : ∀ i : Fin r, ∀ (T : Scheme) (j : T ⟶ X i.castSucc),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty ((((I i).comap j).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ X i.succ, u ≫ b i = j)
    (U : (X 0).Opens)
    (havoid : ∀ i : Fin r, ∀ x : X i.castSucc,
      s2e_towerTotalMap X (𝟙 (X 0)) b i.castSucc x ∈ U → x ∉ (I i).support) :
    ∀ i, IsIso (s2e_towerTotalMap X (𝟙 (X 0)) b i ∣_ U) := by
  intro i
  induction i using Fin.induction with
  | zero =>
    rw [s2e_towerTotalMap_zero]
    infer_instance
  | succ j ih =>
    let V := (s2e_towerTotalMap X (𝟙 (X 0)) b j.castSucc) ⁻¹ᵁ U
    have hI : (I j).comap V.ι = ⊤ := by
      apply s2e_comap_eq_top_of_disjoint
      rw [Scheme.Opens.range_ι]
      exact Set.disjoint_left.mpr (fun y hy hi => havoid j y hy hi)
    haveI : IsIso (pullback.snd (b j) V.ι) :=
      s2e_blowup_scheme_isIso_off_centre (b j) (I j) (hblowup j) V.ι hI
    let E := pullbackRestrictIsoRestrict (b j) V
    haveI : IsIso (E.hom ≫ (b j ∣_ V)) := by
      rw [pullbackRestrictIsoRestrict_hom_morphismRestrict]
      infer_instance
    haveI : IsIso (b j ∣_ V) := IsIso.of_isIso_comp_left E.hom (b j ∣_ V)
    letI := ih
    rw [s2e_towerTotalMap_succ, morphismRestrict_comp]
    infer_instance

theorem base_tower_isIso_off_initial_branches
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
  apply base_tower_isIso_off_centres r X b I hblowup U
  intro i x hx hmem
  change x ∈ (D i.castSucc (p i) ⊔ D i.castSucc (q i)).support at hmem
  rw [Scheme.IdealSheafData.support_sup] at hmem
  exact havoid (p i) _ hx (hs i.castSucc (p i) hmem.1)

#print axioms base_tower_isIso_off_initial_branches
end HodgeLean.Foundations.QuotientDuality
