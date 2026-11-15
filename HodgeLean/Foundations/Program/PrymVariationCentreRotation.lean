import HodgeLean.Foundations.Program.PrymVariationCentreChevalleyWeil

noncomputable section
open HodgeLean.Papers
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

section Surface
variable (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
  [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [MulAction b4b_Group C] [FaithfulSMul b4b_Group C]
  (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))

include hG

theorem b63d_der_mul_at (x : C) (g h : b4b_Group) :
    b4cov_der ℂ x (g * h) =
      (b4cov_der ℂ (h • x) g).comp (b4cov_der ℂ x h) := by
  have hf : (fun z : C ↦ (g * h) • z) =
      (fun z : C ↦ g • z) ∘ (fun z : C ↦ h • z) := funext (mul_smul g h)
  rw [b4cov_der, hf]
  exact mfderiv_comp x (((hG g) _).mdifferentiableAt (by simp))
    (((hG h) _).mdifferentiableAt (by simp))

theorem b63d_rotGen_conjugate (x : C) (h : b4b_Group)
    (hh : b4_IsRotGen ℂ x h) (g : b4b_Group) :
    b4_IsRotGen ℂ (g • x) (g * h * g⁻¹) := by
  have hord : orderOf (g * h * g⁻¹) = orderOf h := by
    simpa only [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq h
  have hcard : Nat.card (MulAction.stabilizer b4b_Group (g • x)) =
      Nat.card (MulAction.stabilizer b4b_Group x) :=
    Nat.card_congr (MulAction.stabilizerEquivStabilizer (g := g) rfl).toEquiv.symm
  refine ⟨?_, hord.trans (hh.2.1.trans hcard.symm), ?_⟩
  · simp only [mul_smul, inv_smul_smul, hh.1]
  · intro v
    rw [hord]
    let k := g * h * g⁻¹
    have hrel : k * g = g * h := by dsimp [k]; group
    have hchain : (b4cov_der ℂ (g • x) k).comp (b4cov_der ℂ x g) =
        (b4cov_der ℂ x g).comp (b4cov_der ℂ x h) := by
      rw [← b63d_der_mul_at C hG x k g, hrel, b63d_der_mul_at C hG x g h, hh.1]
    let c := b4cov_scal (by simp : Module.finrank ℂ ℂ = 1) g x
    have hc : c ≠ 0 := b4cov_scal_ne_zero (by simp) hG g x
    have hgv (u : ℂ) : b4cov_der ℂ x g u = c • u :=
      b4cov_mfderiv_smul_apply (by simp) g x u
    have he := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L v) hchain
    change b4cov_der ℂ (g • x) k (b4cov_der ℂ x g v) =
      b4cov_der ℂ x g (b4cov_der ℂ x h v) at he
    have he' : c • b4cov_der ℂ (g • x) k v =
        c • (Complex.exp (2 * Real.pi * Complex.I / (orderOf h : ℂ)) • v) := by
      calc
        c • b4cov_der ℂ (g • x) k v = b4cov_der ℂ (g • x) k (c • v) :=
          (map_smul _ c v).symm
        _ = b4cov_der ℂ (g • x) k (b4cov_der ℂ x g v) := by rw [hgv]
        _ = b4cov_der ℂ x g (b4cov_der ℂ x h v) := he
        _ = c • (Complex.exp (2 * Real.pi * Complex.I / (orderOf h : ℂ)) • v) := by
          rw [hgv]
          exact congrArg (fun u : ℂ ↦ c • u) (hh.2.2 v)
    exact (smul_right_injective _ hc) he'

theorem b63d_rotationGenerator_smul (x : C) (g : b4b_Group) :
    b63d_rotationGenerator C hG (g • x) =
      g * b63d_rotationGenerator C hG x * g⁻¹ := by
  exact b63d_rotationGenerator_eq C hG (g • x) _
    (b63d_rotGen_conjugate C hG x _ (b63d_rotationGenerator_isRotGen C hG x) g)

end Surface
end HodgeLean.Foundations.Program
