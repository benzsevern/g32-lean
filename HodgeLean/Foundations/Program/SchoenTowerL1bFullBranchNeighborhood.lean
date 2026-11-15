import HodgeLean.Foundations.Program.SchoenTowerL1bFullBranchChart
import HodgeLean.Foundations.Program.SchoenTowerL1bEtaleBlowupCover

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Both coordinate blowup charts retain an injective atlas for all branch transforms and the weighted identity. -/
theorem s2v_l1b_full_branch_neighborhood
    (B X : Over (Spec ↧ℂ)) (f : X ⟶ B) {J σ : Type}
    [Fintype J] [DecidableEq J] [DecidableEq σ]
    (D : J → B.left.IdealSheafData) (K : B.left.IdealSheafData)
    (hcartier : ∀ x : X.left, ∃ V : X.left.affineOpens, x ∈ V.1 ∧
      Nonempty (((K.comap f.left).ideal V) ≃ₗ[Γ(X.left, V)] Γ(X.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (g : T ⟶ B),
      (∀ x : T.left, ∃ V : T.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((K.comap g.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! k : T ⟶ X, k ≫ f = g)
    (U : B.left.affineOpens) (c : ℂ →+* Γ(B.left, U))
    (z : σ → Γ(B.left, U)) (het : (MvPolynomial.eval₂Hom c z).Etale)
    (A : Set J) (g : A ↪ σ)
    (hD : ∀ j : A, (D j).ideal U = Ideal.span {z (g j)})
    (hunit : ∀ j, j ∉ A → (D j).ideal U = ⊤)
    (p q : J) (hpq : p ≠ q) (hp : p ∈ A) (hq : q ∈ A)
    (hK : K.ideal U = Ideal.span {z (g ⟨p, hp⟩), z (g ⟨q, hq⟩)})
    (n : J → ℕ) (m : ℕ) (hn : n p + n q = m)
    (x : X.left) (hx : f.left x ∈ U.1) :
    ∃ (V : X.left.affineOpens) (c' : ℂ →+* Γ(X.left, V))
      (w : σ → Γ(X.left, V)) (A' : Set J) (g' : A' ↪ σ),
      x ∈ V.1 ∧ (MvPolynomial.eval₂Hom c' w).Etale ∧
      (∀ j : A', (s2c_strictTransform f.left (D j) K).ideal V = Ideal.span {w (g' j)}) ∧
      (∀ j, j ∉ A' → (s2c_strictTransform f.left (D j) K).ideal V = ⊤) ∧
      (∏ j, ((D j).comap f.left) ^ n j).ideal V =
        ((∏ j, (s2c_strictTransform f.left (D j) K) ^ n j) *
          (K.comap f.left) ^ m).ideal V := by
  classical
  have hab : g ⟨p, hp⟩ ≠ g ⟨q, hq⟩ := by
    intro H; exact hpq (congrArg Subtype.val (g.injective H))
  have hrest (j : J) (hjp : j ≠ p) (hjq : j ≠ q) :
      (D j).ideal U = ⊤ ∨ ∃ t, t ≠ g ⟨p, hp⟩ ∧ t ≠ g ⟨q, hq⟩ ∧
        (D j).ideal U = Ideal.span {z t} := by
    by_cases hj : j ∈ A
    · refine Or.inr ⟨g ⟨j, hj⟩, ?_, ?_, hD ⟨j, hj⟩⟩
      · intro H; exact hjp (congrArg Subtype.val (g.injective H))
      · intro H; exact hjq (congrArg Subtype.val (g.injective H))
    · exact Or.inl (hunit j hj)
  obtain ⟨V₁, V₂, h₁, h₂, w₁, w₂, hcover, hw₁, hw₂, hz₁, hz₂⟩ :=
    s2v_l1b_blowup_etale_coordinate_cover B X f K hcartier hblowup U c z het
      (g ⟨p, hp⟩) (g ⟨q, hq⟩) hab hK
  have hx' : x ∈ V₁.1 ⊔ V₂.1 := by rw [hcover]; exact hx
  rcases hx' with hx₁ | hx₂
  · obtain ⟨g', hD', ht'⟩ := s2v_l1b_full_branch_chart f.left D K U V₁ h₁
      _ z w₁ hw₁ A g hD hunit p q hpq hp hq hK hz₁
    refine ⟨V₁, _, w₁, {j | j ∈ A ∧ j ≠ q}, g', hx₁, hw₁, hD', ht', ?_⟩
    simp only [s2v_l1b_ideal_sections_prod, Scheme.IdealSheafData.ideal_pow,
      Scheme.IdealSheafData.ideal_mul, Pi.pow_apply, Pi.mul_apply]
    exact s2v_l1b_weighted_coordinate_pullback f.left D K U V₁ h₁ _ z w₁ hw₁
      (g ⟨p, hp⟩) (g ⟨q, hq⟩) hab p q hpq hz₁ (hD ⟨p, hp⟩)
      (hD ⟨q, hq⟩) hK hrest n m hn
  · have hK' : K.ideal U = Ideal.span {z (g ⟨q, hq⟩), z (g ⟨p, hp⟩)} := by
      rw [hK, Set.pair_comm]
    obtain ⟨g', hD', ht'⟩ := s2v_l1b_full_branch_chart f.left D K U V₂ h₂
      _ z w₂ hw₂ A g hD hunit q p hpq.symm hq hp hK' hz₂
    refine ⟨V₂, _, w₂, {j | j ∈ A ∧ j ≠ p}, g', hx₂, hw₂, hD', ht', ?_⟩
    simp only [s2v_l1b_ideal_sections_prod, Scheme.IdealSheafData.ideal_pow,
      Scheme.IdealSheafData.ideal_mul, Pi.pow_apply, Pi.mul_apply]
    apply s2v_l1b_weighted_coordinate_pullback f.left D K U V₂ h₂ _ z w₂ hw₂
      (g ⟨q, hq⟩) (g ⟨p, hp⟩) hab.symm q p hpq.symm hz₂ (hD ⟨q, hq⟩)
      (hD ⟨p, hp⟩) hK' _ n m (by omega)
    intro j hjq hjp
    rcases hrest j hjp hjq with hj | ⟨t, hta, htb, ht⟩
    · exact Or.inl hj
    · exact Or.inr ⟨t, htb, hta, ht⟩

end HodgeLean.Foundations.Program
