import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs

noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Branch ideals on a specified tower, retaining the initial quotient and pair order. -/
def g32t5_branchFamily (Z B₀ : Over (Spec ↧ℂ)) (h r : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B₀) (z : Fin (2 * r) → ComplexPoint Z)
    (B : Fin (r + 1) → Over (Spec ↧ℂ)) (e₀ : B 0 ≅ B₀)
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc) :
    ∀ i, Fin (2 * r) → (B i).left.IdealSheafData :=
  Fin.induction (fun j => (s2c_branchIdeal Z B₀ h γ (z j)).comap e₀.hom.left)
    (fun i D j => s2c_strictTransform (b i).left (D j)
      (D ⟨2 * i.val, by omega⟩ ⊔ D ⟨2 * i.val + 1, by omega⟩))

theorem g32t5_branchFamily_zero (Z B₀ : Over (Spec ↧ℂ)) (h r : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B₀) (z : Fin (2 * r) → ComplexPoint Z)
    (B : Fin (r + 1) → Over (Spec ↧ℂ)) (e₀ : B 0 ≅ B₀)
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc) (j : Fin (2 * r)) :
    g32t5_branchFamily Z B₀ h r γ z B e₀ b 0 j =
      (s2c_branchIdeal Z B₀ h γ (z j)).comap e₀.hom.left := rfl

theorem g32t5_branchFamily_succ (Z B₀ : Over (Spec ↧ℂ)) (h r : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B₀) (z : Fin (2 * r) → ComplexPoint Z)
    (B : Fin (r + 1) → Over (Spec ↧ℂ)) (e₀ : B 0 ≅ B₀)
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc) (i : Fin r) (j : Fin (2 * r)) :
    g32t5_branchFamily Z B₀ h r γ z B e₀ b i.succ j =
      s2c_strictTransform (b i).left (g32t5_branchFamily Z B₀ h r γ z B e₀ b i.castSucc j)
        (g32t5_branchFamily Z B₀ h r γ z B e₀ b i.castSucc ⟨2 * i.val, by omega⟩ ⊔
         g32t5_branchFamily Z B₀ h r γ z B e₀ b i.castSucc ⟨2 * i.val + 1, by omega⟩) := by
  unfold g32t5_branchFamily
  rw [Fin.induction_succ]

/-- The literal native initial and transition equations determine every branch ideal. -/
theorem g32t5_branchFamily_unique (Z B₀ : Over (Spec ↧ℂ)) (h r : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B₀) (z : Fin (2 * r) → ComplexPoint Z)
    (B : Fin (r + 1) → Over (Spec ↧ℂ)) (e₀ : B 0 ≅ B₀)
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (hD₀ : ∀ j, D 0 j = (s2c_branchIdeal Z B₀ h γ (z j)).comap e₀.hom.left)
    (htransform : ∀ (i : Fin r) j, D i.succ j = s2c_strictTransform (b i).left
      (D i.castSucc j) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩)) :
    D = g32t5_branchFamily Z B₀ h r γ z B e₀ b := by
  funext i
  induction i using Fin.induction with
  | zero => exact funext hD₀
  | succ i ih =>
    funext j
    rw [htransform, g32t5_branchFamily_succ, ih]

/-- The zero-pair tower is the retained base itself. -/
theorem g32t5_zero_pair_bases (Z B₀ : Over (Spec ↧ℂ)) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B₀) (z : Fin (2 * 0) → ComplexPoint Z) :
    ∃ (B : Fin (0 + 1) → Over (Spec ↧ℂ))
      (e₀ : B 0 ≅ B₀)
      (b : ∀ i : Fin 0, B i.succ ⟶ B i.castSucc)
      (D : ∀ i, Fin (2 * 0) → (B i).left.IdealSheafData),
      (∀ j, D 0 j = (s2c_branchIdeal Z B₀ h γ (z j)).comap e₀.hom.left) ∧
      ∀ i : Fin 0,
        let K := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
          D i.castSucc ⟨2 * i.val + 1, by omega⟩
        (∀ j, D i.succ j = s2c_strictTransform (b i).left (D i.castSucc j) K) ∧
        (∀ x : (B i.succ).left, ∃ U : (B i.succ).left.affineOpens,
          x ∈ U.1 ∧ Nonempty (((K.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
            Γ((B i.succ).left, U))) ∧
        (∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
          (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
            Nonempty (((K.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
          ∃! u : T ⟶ B i.succ, u ≫ b i = f) := by
  refine ⟨fun _ => B₀, Iso.refl B₀, (fun i => Fin.elim0 i),
    (fun _ j => Fin.elim0 j), ?_, ?_⟩
  · intro j
    exact Fin.elim0 j
  · intro i
    exact Fin.elim0 i

end HodgeLean.Foundations.Program
