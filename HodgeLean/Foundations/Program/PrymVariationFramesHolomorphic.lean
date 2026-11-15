import HodgeLean.Foundations.Program.PrymVariationFramesDefs
import HodgeLean.Foundations.Program.VariationHodgePeriod

noncomputable section
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem b63e_coordVector_equiv {ι : Type} [Fintype ι] {M : Type*} [AddCommGroup M]
    (B : Module.Basis ι ℤ M) (c : ι → ℂ) :
    b63e_coordVector B c = (B.baseChange ℂ).equivFun.symm c := by
  simp only [b63e_coordVector, Module.Basis.equivFun_symm_apply,
    Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
theorem b63e_const_subbundle_of_frames {k : ℕ} (V : TopologicalSpace.Opens (Fin k → ℂ))
    {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ M)
    (G : V → Submodule ℂ (ℂ ⊗[ℤ] M))
    (hframe : ∀ t₀ : V, ∃ W : Set (Fin k → ℂ), IsOpen W ∧ t₀.val ∈ W ∧
      ∃ r : ℕ, ∃ c : Fin r → (Fin k → ℂ) → (ι → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t : V, t.val ∈ W →
          Submodule.span ℂ (Set.range fun i ↦ b63e_coordVector B (c i t.val)) = G t) :
    (b2_constLocalSystem V M).IsHolomorphicSubbundle (Fin k → ℂ) G := by
  intro t₀
  obtain ⟨W, hW, ht₀, r, c, hc, hspan⟩ := hframe t₀
  obtain ⟨U, hUo, hU, htU, hUW⟩ := d1per_exists_simplyConnected_nhds (Fin k → ℂ)
    (hW.preimage continuous_subtype_val) ht₀
  let σ : Fin r → V → ℂ ⊗[ℤ] M := fun i t ↦ b63e_coordVector B (c i t.val)
  refine ⟨U, hU, htU, hUo, r, σ, ?_, fun t ht ↦ hspan t (hUW ht)⟩
  intro i
  let D : (ι → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ (ℂ ⊗[ℤ] M)) → ℂ) :=
    (b2_coord (ℂ ⊗[ℤ] M)).toLinearMap.comp (B.baseChange ℂ).equivFun.symm.toLinearMap
  have hD : AnalyticOnNhd ℂ (fun x ↦ D (c i x)) W := by
    intro x hx
    exact (D.toContinuousLinearMap.analyticAt _).comp (hc i x hx)
  have hh : ContMDiffOn 𝓘(ℂ, Fin k → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℂ (ℂ ⊗[ℤ] M)) → ℂ) ω
      (fun t : V ↦ D (c i t.val)) U :=
    hD.contDiffOn_of_completeSpace.contMDiffOn.comp
      contMDiff_subtype_val.contMDiffOn hUW
  show ContMDiffOn _ _ _ _ U
  apply hh.congr
  intro t ht
  simp only [Function.comp_apply, b2_LatticeLocalSystem.flatCoord, ht, dite_true]
  apply congrArg (b2_coord (ℂ ⊗[ℤ] M))
  exact (b2a_const_flatTransport M U hU ⟨t, ht⟩ ⟨t₀, htU⟩ (σ i t)).trans
    (b63e_coordVector_equiv B (c i t.val))

end HodgeLean.Foundations.Program
