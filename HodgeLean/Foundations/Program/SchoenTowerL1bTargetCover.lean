import HodgeLean.Foundations.Program.SchoenTowerL1bSourceDescent

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Uniqueness on affine source restrictions with target-chart factorizations gives uniqueness
for arbitrary maps to the covered target. -/
theorem s2v_l1b_target_cover_hom_ext {T M B : Scheme} (p : M ⟶ B) (f : T ⟶ B)
    (𝒰 : M.OpenCover)
    (hlocal : ∀ (V : Scheme) [IsAffine V] (h : V ⟶ T) [IsOpenImmersion h]
      (a b : 𝒰.I₀) (k : V ⟶ 𝒰.X a) (l : V ⟶ 𝒰.X b),
      k ≫ 𝒰.f a ≫ p = h ≫ f → l ≫ 𝒰.f b ≫ p = h ≫ f →
      k ≫ 𝒰.f a = l ≫ 𝒰.f b)
    (k l : T ⟶ M) (hk : k ≫ p = f) (hl : l ≫ p = f) : k = l := by
  apply Scheme.Cover.hom_ext (𝒰.pullback₁ k)
  intro a
  change 𝒰.I₀ at a
  let W := pullback k (𝒰.f a)
  let q : W ⟶ T := pullback.fst k (𝒰.f a)
  apply Scheme.Cover.hom_ext (𝒰.pullback₁ (q ≫ l))
  intro b
  change 𝒰.I₀ at b
  let Z := pullback (q ≫ l) (𝒰.f b)
  let r : Z ⟶ W := pullback.fst (q ≫ l) (𝒰.f b)
  apply Z.affineCover.hom_ext
  intro c
  let t := Z.affineCover.f c
  have h₁ : (t ≫ r ≫ pullback.snd k (𝒰.f a)) ≫ 𝒰.f a ≫ p =
      (t ≫ r ≫ q) ≫ f := by
    simp only [Category.assoc]
    rw [← pullback.condition_assoc, hk]
  have h₂ : (t ≫ pullback.snd (q ≫ l) (𝒰.f b)) ≫ 𝒰.f b ≫ p =
      (t ≫ r ≫ q) ≫ f := by
    simp only [Category.assoc]
    rw [← pullback.condition_assoc]
    simp only [Category.assoc, hl]
    rfl
  have he := hlocal (Z.affineCover.X c) (t ≫ r ≫ q) a b
    (t ≫ r ≫ pullback.snd k (𝒰.f a))
    (t ≫ pullback.snd (q ≫ l) (𝒰.f b)) h₁ h₂
  change t ≫ r ≫ q ≫ k = t ≫ r ≫ q ≫ l
  simp only [Category.assoc] at he
  rw [← pullback.condition, ← pullback.condition] at he
  exact he

end HodgeLean.Foundations.Program
