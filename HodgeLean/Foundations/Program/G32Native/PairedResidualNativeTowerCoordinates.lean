import HodgeLean.Foundations.Program.SchoenTowerL1bFiniteBaseCoordinates
import HodgeLean.Foundations.Program.SchoenTowerL1bTowerStepLocal

/-! # Branch coordinates on the supplied paired blow-up tower -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native.FibreC
open HodgeLean.Foundations.Program

/-- The supplied quotient and universal blow-ups retain simultaneous coordinates for
all unprocessed branch ideals, including at exceptional points. -/
theorem residual_native_tower_branch_coordinates
    (Z B₀ : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (n r : ℕ)
    (γ : g3_power Z (n + 1) ⟶ B₀) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hinv : ∀ τ, s2_permute Z (n + 1) τ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (n + 1) ⟶ T),
      (∀ τ, s2_permute Z (n + 1) τ ≫ f = f) → ∃! u : B₀ ⟶ T, γ ≫ u = f)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (B : Fin (r + 1) → Over (Spec ↧ℂ)) (e₀ : B 0 ≅ B₀)
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (hD₀ : ∀ t, D 0 t = (s2c_branchIdeal Z B₀ n γ (y t)).comap e₀.hom.left)
    (htransform : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩))
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U)))
    (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f) :
    ∀ (i : Fin (r + 1)) (x : ComplexPoint (B i)),
      ∃ (U : (B i).left.affineOpens) (z : Fin (n + 1) → Γ((B i).left, U))
        (f : {t : Fin (2 * r) // 2 * i.val ≤ t.val ∧
          x.underlying ∈ (D i t).support} ↪ Fin (n + 1)),
        x.underlying ∈ U.1 ∧
        (MvPolynomial.eval₂Hom ((B i).hom.appLE ⊤ U.1 le_top).hom z).Etale ∧
        (∀ t, (D i t.val).ideal U = Ideal.span {z (f t)}) ∧
        (∀ t : Fin (2 * r), 2 * i.val ≤ t.val →
          x.underlying ∉ (D i t).support → (D i t).ideal U = ⊤) := by
  classical
  intro i
  induction i using Fin.induction with
  | zero =>
    intro x
    obtain ⟨U, z, f, hx, het, hD, htop⟩ :=
      s2v_l1b_finite_base_coordinates Z B₀ (B 0) hdim n γ hsurj hinv hquot
        (2 * r) y hy e₀ (D 0) hD₀ x
    let f' : {t : Fin (2 * r) // 2 * (0 : Fin (r + 1)).val ≤ t.val ∧
        x.underlying ∈ (D 0 t).support} ↪ Fin (n + 1) :=
      ⟨fun t => f ⟨t.val, t.property.2⟩, by
        intro t s h
        have hval : t.val = s.val := Subtype.mk.inj (f.injective h)
        exact Subtype.ext hval⟩
    exact ⟨U, z, f', hx, het, fun t => hD ⟨t.val, t.property.2⟩,
      fun t _ ht => htop t ht⟩
  | succ i ih =>
    intro x
    obtain ⟨U, z, f, hx, het, hD, habs⟩ := ih (Point.map (b i) x)
    let a : Fin (2 * r) := ⟨2 * i.val, by omega⟩
    let c : Fin (2 * r) := ⟨2 * i.val + 1, by omega⟩
    have H := s2v_l1b_tower_step_local (B i.castSucc) (B i.succ) (b i)
      (D i.castSucc) (fun t => 2 * i.val ≤ t.val) (fun t => 2 * (i.val + 1) ≤ t.val)
      (by intro t ht; omega) a c
      (by intro he; have hv := congrArg Fin.val he; dsimp [a, c] at hv; omega)
      (by dsimp [a]; omega) (by dsimp [c]; omega)
      (by dsimp [a]; omega) (by dsimp [c]; omega)
      (hcartier i) (hblowup i) x U z f hx het hD habs
    have hsucc : D i.succ = fun t => s2c_strictTransform (b i).left
        (D i.castSucc t) (D i.castSucc a ⊔ D i.castSucc c) := funext (htransform i)
    rw [hsucc]
    exact H

#print axioms residual_native_tower_branch_coordinates
end HodgeLean.Foundations.Program.G32Native.FibreC
