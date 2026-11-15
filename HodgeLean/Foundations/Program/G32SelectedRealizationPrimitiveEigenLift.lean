import HodgeLean.Foundations.Program.G32SelectedRealizationRelationBaseChange

noncomputable section
open HodgeLean.Foundations
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_primitive_character_eigenvector_lift
    {H U : Type*} [Group H] [Finite H] [AddCommGroup U] [Module ℚ U]
    {m : ℕ} [NeZero m] (hm : 3 ≤ m) (χ : H →* Multiplicative (ZMod m))
    (T : H → Module.End ℚ U) (σ : cyc_Field m →ₐ[ℚ] ℂ)
    (v : ℂ ⊗[ℚ] U)
    (hv : ∀ h, (T h).baseChange ℂ v =
      σ (IsCyclotomicExtension.zeta m ℚ (cyc_Field m) ^ (Multiplicative.toAdd (χ h)).val) • v) :
    let W : Submodule ℚ U :=
      (⨅ (h : H) (_ : χ h = 1), LinearMap.eqLocus (T h) LinearMap.id) ⊓
        ⨅ (h : H) (_ : χ h = Multiplicative.ofAdd 1),
          LinearMap.ker (Polynomial.aeval (T h) (Polynomial.cyclotomic m ℚ))
    v ∈ LinearMap.range (W.subtype.baseChange ℂ) := by
  dsimp only
  classical
  let ζ := IsCyclotomicExtension.zeta m ℚ (cyc_Field m)
  have hz := IsCyclotomicExtension.zeta_spec m ℚ (cyc_Field m)
  have hσ : IsPrimitiveRoot (σ ζ) m := hz.map_of_injective σ.injective
  have hroot : (Polynomial.cyclotomic m ℂ).eval (σ ζ) = 0 :=
    Polynomial.isRoot_cyclotomic_iff.mpr hσ
  have hC := g32y_relation_baseChange T {h | χ h = 1}
    {h | χ h = Multiplicative.ofAdd 1} (Polynomial.cyclotomic m ℚ)
  dsimp only [Set.mem_setOf_eq] at hC
  change LinearMap.range (((⨅ (h : H) (_ : χ h = 1),
    LinearMap.eqLocus (T h) LinearMap.id) ⊓
      ⨅ (h : H) (_ : χ h = Multiplicative.ofAdd 1),
        LinearMap.ker (Polynomial.aeval (T h) (Polynomial.cyclotomic m ℚ))).subtype.baseChange ℂ) = _ at hC
  rw [hC]
  constructor
  · apply (Submodule.mem_iInf _).mpr
    intro h
    apply (Submodule.mem_iInf _).mpr
    intro hh
    change χ h = 1 at hh
    apply LinearMap.mem_eqLocus.mpr
    simpa only [hh, toAdd_one, ZMod.val_zero, pow_zero, map_one, one_smul,
      LinearMap.id_apply] using hv h
  · apply (Submodule.mem_iInf _).mpr
    intro h
    apply (Submodule.mem_iInf _).mpr
    intro hh
    change χ h = Multiplicative.ofAdd 1 at hh
    apply LinearMap.mem_ker.mpr
    have he : (T h).baseChange ℂ v = σ ζ • v := by
      simpa only [hh, toAdd_ofAdd, ZMod.val_one'' (n := m) (by omega), pow_one] using hv h
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul he, Polynomial.map_cyclotomic,
      hroot, zero_smul]

end HodgeLean.Foundations.Program
