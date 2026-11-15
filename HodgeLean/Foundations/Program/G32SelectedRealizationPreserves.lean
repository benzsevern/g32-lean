import HodgeLean.Foundations.Program.G32SelectedRealizationCyclotomic

noncomputable section
open HodgeLean.Foundations
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_aeval_preserves {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (T : Module.End K V) (W : Submodule K V)
    (hT : ∀ v ∈ W, T v ∈ W) (p : Polynomial K) :
    ∀ v ∈ W, Polynomial.aeval T p v ∈ W := by
  have hn (n : ℕ) : ∀ v ∈ W, (T ^ n) v ∈ W := by
    induction n with
    | zero => intro v hv; simpa only [pow_zero, Module.End.one_apply] using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih (T v) (hT v hv)
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (hp v hv) (hq v hv)
  | monomial n a =>
    intro v hv
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, LinearMap.smul_apply]
    exact W.smul_mem a (hn n v hv)

theorem g32y_cyclotomic_preserves {V : Type*} [AddCommGroup V] [Module ℚ V]
    {m d : ℕ} [NeZero m] (e : V ≃ₗ[ℚ] (Fin d → cyc_Field m))
    (W : Submodule ℂ (ℂ ⊗[ℚ] V))
    (hζ : ∀ v ∈ W, (cyc_scalar e (IsCyclotomicExtension.zeta m ℚ (cyc_Field m))).baseChange ℂ v ∈ W) :
    ∀ a v, v ∈ W → (cyc_scalar e a).baseChange ℂ v ∈ W := by
  intro a v hv
  let ζ := IsCyclotomicExtension.zeta m ℚ (cyc_Field m)
  let hz := IsCyclotomicExtension.zeta_spec m ℚ (cyc_Field m)
  let pb := hz.powerBasis ℚ
  obtain ⟨p, hp⟩ := pb.exists_eq_aeval' a
  have hgen : pb.gen = ζ := hz.powerBasis_gen ℚ
  rw [hgen] at hp
  let ρ : cyc_Field m →ₐ[ℚ] Module.End ℂ (ℂ ⊗[ℚ] V) :=
    (Module.End.baseChangeHom ℚ ℂ V).comp (cyc_rep e)
  have ha : (cyc_scalar e a).baseChange ℂ =
      Polynomial.aeval ((cyc_scalar e ζ).baseChange ℂ) (p.map (algebraMap ℚ ℂ)) := by
    change ρ a = _
    rw [hp, ← Polynomial.aeval_algHom_apply]
    exact Polynomial.aeval_eq_aeval_map
      (IsScalarTower.algebraMap_eq ℚ ℂ (Module.End ℂ (ℂ ⊗[ℚ] V))).symm p (ρ ζ)
  rw [ha]
  exact g32y_aeval_preserves _ W hζ _ v hv

end HodgeLean.Foundations.Program
