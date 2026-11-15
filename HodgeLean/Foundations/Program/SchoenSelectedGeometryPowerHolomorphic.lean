import HodgeLean.Foundations.Program.SchoenSelectedGeometryProductAnalytic

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters MonoidalCategory
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Finite tuples of holomorphic curve maps give holomorphic maps into scheme powers.
Source: holomorphic pairing and induction on finite products. -/
theorem s0_power_point_tuple_holomorphic
    (A : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 A.hom]
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    (n : ℕ) (F : Fin n → C → ComplexPoint A)
    (hF : ∀ i, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω (F i)) :
    letI : SmoothOfRelativeDimension n (g3_power A n).hom := by
      simpa only [Nat.mul_one] using spec_g3_smoothOfRelativeDimension_power A 1 n
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin n → ℂ) ω
      (fun x ↦ (s0_power_point_homeomorph A n).symm (fun i ↦ F i x)) := by
  induction n with
  | zero =>
      letI : SmoothOfRelativeDimension 0 (g3_power A 0).hom := by
        simpa only [Nat.mul_one] using spec_g3_smoothOfRelativeDimension_power A 1 0
      let p := (s0_power_point_homeomorph A 0).symm (fun i ↦ Fin.elim0 i)
      have he : (fun x ↦ (s0_power_point_homeomorph A 0).symm (fun i ↦ F i x)) =
          fun _ : C ↦ p := by
        funext x
        congr 1
        funext i
        exact Fin.elim0 i
      rw [he]
      exact contMDiff_const
  | succ n ih =>
      letI : SmoothOfRelativeDimension n (g3_power A n).hom := by
        simpa only [Nat.mul_one] using spec_g3_smoothOfRelativeDimension_power A 1 n
      have ht := ih (fun i ↦ F i.succ) (fun i ↦ hF i.succ)
      letI : SmoothOfRelativeDimension (n + 1) (g3_power A (n + 1)).hom := by
        simpa only [Nat.mul_one] using spec_g3_smoothOfRelativeDimension_power A 1 (n + 1)
      letI : SmoothOfRelativeDimension (n + 1) (A ⊗ g3_power A n).hom :=
        inferInstanceAs (SmoothOfRelativeDimension (n + 1) (g3_power A (n + 1)).hom)
      have hp : ∀ (k : ℕ) (_ : k = 1 + n)
          (hs : SmoothOfRelativeDimension k (A ⊗ g3_power A n).hom),
          letI := hs
          ContMDiff (𝓘(ℂ, Fin 1 → ℂ).prod 𝓘(ℂ, Fin n → ℂ))
            𝓘(ℂ, Fin k → ℂ) ω (complexPointProdHomeomorph A (g3_power A n)).symm := by
        intro k hk hs
        subst k
        exact s0_product_point_pairing_holomorphic A (g3_power A n) 1 n
      have h := (hp (n + 1) (Nat.add_comm n 1) inferInstance).comp ((hF 0).prodMk ht)
      exact h

#print axioms s0_power_point_tuple_holomorphic
end HodgeLean.Foundations.Program
