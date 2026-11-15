import HodgeLean.Foundations.Program.SchoenCycleC2BlowupDimensionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2PowerDimensionHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual finite curve-power quotient and paired Cartier tower have the
curve-power dimension at every retained level. -/
theorem s2e_retained_tower_dimension
    (Z B₀ : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsIntegral B₀.left] [LocallyOfFiniteType B₀.hom]
    (hdimZ : dim Z.left = 1) (N r : ℕ)
    (γ : g3_power Z N ⟶ B₀) [IsFinite γ.left]
    (hs : Function.Surjective (Point.map γ))
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, Smooth (B i).hom]
    (e₀ : B 0 ≅ B₀) (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
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
    ∀ i, dim (B i).left = N := by
  have hdim₀ := s2e_finite_curve_power_target_dimension Z B₀ hdimZ N γ hs
  have he₀ : dim (B 0).left = dim B₀.left := by
    unfold TopologicalSpace.dim
    rw [e₀.hom.left.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  intro i
  exact (s2e_cartier_tower_dimension r B b
    (fun i => D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      D i.castSucc ⟨2 * i.val + 1, by omega⟩) hcartier hblowup i).trans
    (he₀.trans hdim₀)

end HodgeLean.Foundations.Program
