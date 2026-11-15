import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationBlowupEtale
import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers

/-! # Actual normalization etaleness along a tower away from its centres -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An initial etale base open stays etale for the specified field-source
normalizations through a tower whose centres avoid its full inverse images. -/
theorem s2e_c1_normalization_etale_tower_off_centres
    {K : Type} [Field K] (r : ℕ) (X : Fin (r + 1) → Scheme)
    [∀ i, IsIntegral (X i)]
    (f : ∀ i, Spec (CommRingCat.of K) ⟶ X i)
    [∀ i, QuasiCompact (f i)] [∀ i, QuasiSeparated (f i)] [∀ i, IsDominant (f i)]
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc) [∀ i, Surjective (b i)]
    (hf : ∀ i : Fin r, f i.succ ≫ b i = f i.castSucc)
    (I : ∀ i : Fin r, (X i.castSucc).IdealSheafData)
    (hblowup : ∀ i : Fin r, ∀ (T : Scheme) (j : T ⟶ X i.castSucc),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty ((((I i).comap j).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ X i.succ, u ≫ b i = j)
    (U : (X 0).Opens) (hU : (U : Set (X 0)).Nonempty)
    (havoid : ∀ i : Fin r, ∀ x : X i.castSucc,
      s2e_towerTotalMap X (𝟙 (X 0)) b i.castSucc x ∈ U → x ∉ (I i).support)
    [Etale ((f 0).fromNormalization ∣_ U)] :
    ∀ i, Etale ((f i).fromNormalization ∣_
      ((s2e_towerTotalMap X (𝟙 (X 0)) b i) ⁻¹ᵁ U)) := by
  have hs : ∀ i, Surjective (s2e_towerTotalMap X (𝟙 (X 0)) b i) := by
    intro i
    induction i using Fin.induction with
    | zero => change Surjective (𝟙 (X 0)); infer_instance
    | succ j ih =>
      rw [s2e_towerTotalMap_succ]
      letI := ih
      infer_instance
  intro i
  induction i using Fin.induction with
  | zero =>
    rw [s2e_towerTotalMap_zero, Scheme.Hom.id_preimage]
    infer_instance
  | succ j ih =>
    let V := (s2e_towerTotalMap X (𝟙 (X 0)) b j.castSucc) ⁻¹ᵁ U
    have hV : (V : Set (X j.castSucc)).Nonempty := by
      obtain ⟨y, hy⟩ := hU
      letI := hs j.castSucc
      obtain ⟨x, hx⟩ := (s2e_towerTotalMap X (𝟙 (X 0)) b j.castSucc).surjective y
      exact ⟨x, by change s2e_towerTotalMap X (𝟙 (X 0)) b j.castSucc x ∈ U; rw [hx]; exact hy⟩
    letI := ih
    have he := s2e_c1_normalization_blowup_etale_off_centre (f j.succ) (f j.castSucc)
      (b j) (hf j) (I j) (hblowup j) V hV (havoid j)
    rw [s2e_towerTotalMap_succ, Scheme.Hom.comp_preimage]
    exact he

end HodgeLean.Foundations.Program
