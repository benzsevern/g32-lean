import HodgeLean.Foundations.Program.G32Native.PELIntegralDualRealization

noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- An operator preserving the full integral dual has an integral transpose on
homology, with the exact evaluation equation and no scalar multiplier.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§1.2–1.3. -/
theorem integralDual_transpose {Λ : Type} [AddCommGroup Λ]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ Λ)
    (T : Module.End ℚ (b2b_dual Λ))
    (hT : ∀ f ∈ integralDual Λ, T f ∈ integralDual Λ) :
    ∃ φ : Λ →ₗ[ℤ] Λ, ∀ f x, (T f) x = f (φ x) := by
  let c : ι → b2b_dual Λ := fun i => integralDualInclusion Λ (b.coord i)
  have hc (i : ι) : c i ∈ integralDual Λ := fun x => ⟨b.coord i x, rfl⟩
  have hTc (i : ι) : T (c i) ∈ (integralDualInclusion Λ).range := by
    rw [integralDual_range]
    exact hT (c i) (hc i)
  let g : ι → (Λ →ₗ[ℤ] ℤ) := fun i => (hTc i).choose
  have hg (i : ι) (x : Λ) : (g i x : ℚ) = T (c i) x :=
    LinearMap.congr_fun (hTc i).choose_spec x
  let φ : Λ →ₗ[ℤ] Λ := ∑ i, (g i).smulRight (b i)
  have hdecomp (f : b2b_dual Λ) : f = ∑ i, f (b i) • c i := by
    ext x
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    change (b.repr x i : ℚ) * f (b i) = f (b i) * (b.repr x i : ℚ)
    ring
  refine ⟨φ, fun f x => ?_⟩
  conv_lhs => rw [hdecomp f]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  change (∑ i, f (b i) * T (c i) x) = f ((∑ i, (g i).smulRight (b i)) x)
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hg i x]
  change f (b i) * (g i x : ℚ) = (g i x : ℚ) * f (b i)
  ring

#print axioms integralDual_transpose
end HodgeLean.Foundations.Program.GeneralTypeIII
