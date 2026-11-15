import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationEtaleTower
import HodgeLean.Foundations.Program.SchoenCycleC1StrictSupportTower

/-! # Etaleness of the specified normalization tower over the initial unmarked locus -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Initial branch avoidance supplies every centre-avoidance condition in
an actual paired strict-transform normalization tower. -/
theorem s2e_c1_normalization_tower_etale_over_initial_unmarked_open
    {K : Type} [Field K] (r : ℕ) (X : Fin (r + 1) → Scheme)
    [∀ i, IsIntegral (X i)]
    (f : ∀ i, Spec (CommRingCat.of K) ⟶ X i)
    [∀ i, QuasiCompact (f i)] [∀ i, QuasiSeparated (f i)] [∀ i, IsDominant (f i)]
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc) [∀ i, Surjective (b i)]
    (hf : ∀ i : Fin r, f i.succ ≫ b i = f i.castSucc)
    (J : Type*) (D : ∀ i, J → (X i).IdealSheafData) (p q : Fin r → J)
    (hD : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i) (D i.castSucc t)
      (D i.castSucc (p i) ⊔ D i.castSucc (q i)))
    (hblowup : ∀ i : Fin r, ∀ (T : Scheme) (j : T ⟶ X i.castSucc),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty ((((D i.castSucc (p i) ⊔ D i.castSucc (q i)).comap j).ideal V)
          ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ X i.succ, u ≫ b i = j)
    (U : (X 0).Opens) (hU : (U : Set (X 0)).Nonempty)
    (havoid : ∀ t, ∀ x ∈ U, x ∉ (D 0 t).support)
    [Etale ((f 0).fromNormalization ∣_ U)] :
    ∀ i, Etale ((f i).fromNormalization ∣_
      ((s2e_towerTotalMap X (𝟙 (X 0)) b i) ⁻¹ᵁ U)) := by
  let I := fun i : Fin r => D i.castSucc (p i) ⊔ D i.castSucc (q i)
  have hsupport := s2e_c1_strict_support_tower_subset r X b J D I hD
  apply s2e_c1_normalization_etale_tower_off_centres r X f b hf I hblowup U hU
  intro i x hx hmem
  change x ∈ (D i.castSucc (p i) ⊔ D i.castSucc (q i)).support at hmem
  rw [Scheme.IdealSheafData.support_sup] at hmem
  exact havoid (p i) _ hx (hsupport i.castSucc (p i) hmem.1)

end HodgeLean.Foundations.Program
