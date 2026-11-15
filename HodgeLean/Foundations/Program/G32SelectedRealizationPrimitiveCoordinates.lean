import HodgeLean.Foundations.Program.G32SelectedRealizationPrimitiveAction

noncomputable section
set_option maxRecDepth 2000
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

theorem g32y_relation_cyclotomic_coordinates {H V : Type*} [Group H]
    [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] {m : ℕ} [NeZero m]
    (R : Representation ℚ H V) (χ : H →* Multiplicative (ZMod m))
    (hχ : Function.Surjective χ) :
    let W : Submodule ℚ V :=
      (⨅ h, ⨅ (_ : χ h = 1), LinearMap.eqLocus (R h) LinearMap.id) ⊓
      ⨅ h, ⨅ (_ : χ h = Multiplicative.ofAdd 1),
        LinearMap.ker (Polynomial.aeval (R h) (Polynomial.cyclotomic m ℚ))
    ∃ d : ℕ, ∃ e : W ≃ₗ[ℚ] (Fin d → cyc_Field m),
      ∀ h, W.subtype ∘ₗ cyc_scalar e
        (IsCyclotomicExtension.zeta m ℚ (cyc_Field m) ^ (χ h).toAdd.val) =
          R h ∘ₗ W.subtype := by
  classical
  let W : Submodule ℚ V :=
    (⨅ h, ⨅ (_ : χ h = 1), LinearMap.eqLocus (R h) LinearMap.id) ⊓
    ⨅ h, ⨅ (_ : χ h = Multiplicative.ofAdd 1),
      LinearMap.ker (Polynomial.aeval (R h) (Polynomial.cyclotomic m ℚ))
  obtain ⟨a, ha⟩ := hχ (Multiplicative.ofAdd 1)
  have hstable : ∀ a v, v ∈ W → R a v ∈ W :=
    g32y_relation_space_stable R χ (Multiplicative.ofAdd 1) (Polynomial.cyclotomic m ℚ)
  let T : Module.End ℚ W := (R a).restrict (hstable a)
  have hT : Polynomial.aeval T (Polynomial.cyclotomic m ℚ) = 0 := by
    apply g32y_restrict_aeval_zero (R a) W (hstable a)
    intro v hv
    simp only [W, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_eqLocus,
      LinearMap.id_apply, LinearMap.mem_ker] at hv
    exact hv.2 a ha
  obtain ⟨ρ, hρ⟩ := g32y_cyclotomic_action T hT
  obtain ⟨d, e, he⟩ := g32y_cyclotomic_coordinates ρ
  refine ⟨d, e, ?_⟩
  intro h
  rw [he, map_pow, hρ]
  have hc : W.subtype ∘ₗ T = R a ∘ₗ W.subtype := rfl
  have hp := g32y_aeval_intertwine W.subtype T (R a) hc
    ((Polynomial.X : Polynomial ℚ) ^ (χ h).toAdd.val)
  simp only [Polynomial.aeval_X_pow] at hp
  rw [hp]
  apply LinearMap.ext
  intro v
  change (R a ^ (χ h).toAdd.val) (v : V) = R h (v : V)
  have hv := v.property
  simp only [W, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_eqLocus,
    LinearMap.id_apply, LinearMap.mem_ker] at hv
  exact (g32y_fixed_character_power R χ a ha v hv.1 h).symm

end HodgeLean.Foundations.Program
