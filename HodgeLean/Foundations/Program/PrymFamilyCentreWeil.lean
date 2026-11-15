import HodgeLean.Foundations.Program.PrymFamilyCentreDefs
import HodgeLean.Blocks.Weil.WeilClasses

/-! # B6-3g, parts 2 and 3: Hodge numbers of a Weil action from lattice data

Linear algebra for the statements `weil_h10` and `weil_h01`: through an injective pairing that
transposes `J` into `ψ` and carries `H^{1,0}` onto the annihilator of `F`, the `μ`-eigenpart of
`J` in `H^{1,0}` is the annihilator of `F + E_{-μ}(ψ)`; on a weight-one lattice with an integral
`φ` of square `-n`, both eigenspaces of `φ_ℂ` have half the rank.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

/-- **Eigenparts against an annihilator.** If `π` is injective, transposes `J` into `ψ`, and
carries `H10` onto the annihilator of `A`, then the `μ`-eigenpart of `J` in `H10` is carried onto
the annihilator of `A ⊔ E_{-μ}(ψ)`, when `ψ² = μ²` and `μ ≠ 0`.
Source: Bourbaki, *Algebra*, Ch. II, §2 (duality); Birkenhake–Lange, §1.2. -/
theorem b63g2_eigen_annihilator {W H : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [AddCommGroup H] [Module ℂ H]
    (π : H →ₗ[ℂ] Module.Dual ℂ W) (hπ : Function.Injective π)
    (J : H →ₗ[ℂ] H) (ψ : W →ₗ[ℂ] W) (hπJ : ∀ ξ v, π (J ξ) v = π ξ (ψ v))
    (H10 : Submodule ℂ H) (A : Submodule ℂ W)
    (hmem : ∀ ξ, ξ ∈ H10 ↔ ∀ a ∈ A, π ξ a = 0)
    (hsurj : ∀ f : Module.Dual ℂ W, (∀ a ∈ A, f a = 0) → ∃ ξ, π ξ = f)
    (μ : ℂ) (hμ : μ ≠ 0) (hψ : ∀ v, ψ (ψ v) = (μ * μ) • v) :
    Module.finrank ℂ ↥(Module.End.eigenspace J μ ⊓ H10) +
      Module.finrank ℂ ↥(A ⊔ Module.End.eigenspace ψ (-μ)) = Module.finrank ℂ W := by
  have hmap : (Module.End.eigenspace J μ ⊓ H10).map π =
      (A ⊔ Module.End.eigenspace ψ (-μ)).dualAnnihilator := by
    rw [Submodule.dualAnnihilator_sup_eq]
    ext f
    simp only [Submodule.mem_map, Submodule.mem_inf, Module.End.mem_eigenspace_iff,
      Submodule.mem_dualAnnihilator]
    constructor
    · rintro ⟨ξ, ⟨hJ, hH⟩, rfl⟩
      refine ⟨(hmem ξ).1 hH, fun w hw ↦ ?_⟩
      have h1 : π ξ (ψ w) = μ * π ξ w := by
        rw [← hπJ, hJ, map_smul, LinearMap.smul_apply, smul_eq_mul]
      have h2 : π ξ (ψ w) = -μ * π ξ w := by
        rw [hw, map_smul, smul_eq_mul]
      have h3 : (2 * μ) * π ξ w = 0 := by linear_combination h2 - h1
      exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero two_ne_zero hμ)
    · rintro ⟨hA, hE⟩
      obtain ⟨ξ, hξ⟩ := hsurj f hA
      refine ⟨ξ, ⟨?_, (hmem ξ).2 (hξ ▸ hA)⟩, hξ⟩
      apply hπ
      apply LinearMap.ext
      intro v
      have hv : ψ (ψ v - μ • v) = -μ • (ψ v - μ • v) := by
        rw [map_sub, map_smul, hψ]
        module
      have h0 := hE _ hv
      rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
      rw [hπJ, map_smul, LinearMap.smul_apply, smul_eq_mul, hξ, h0]
  have h1 : Module.finrank ℂ ↥((Module.End.eigenspace J μ ⊓ H10).map π) =
      Module.finrank ℂ ↥(Module.End.eigenspace J μ ⊓ H10) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective π hπ _)).symm
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (A ⊔ Module.End.eigenspace ψ (-μ))
  rw [← hmap, h1] at h2
  omega

/-- Conjugation carries the `ν`-eigenspace of a complexified integral map into its
`ν̄`-eigenspace.
Source: Birkenhake–Lange, §1.2 (the analytic and rational representations). -/
theorem b63g2_conj_eigenspace {L : Type*} [AddCommGroup L] (φ : L →+ L) (ν : ℂ) :
    b2_conjSubmodule L (Module.End.eigenspace (b2_cplxMap φ) ν) ≤
      Module.End.eigenspace (b2_cplxMap φ) (star ν) := by
  rw [b2a_conjSubmodule_eq_map]
  rintro _ ⟨v, hv, rfl⟩
  have hv : b2_cplxMap φ v = ν • v := Module.End.mem_eigenspace_iff.mp hv
  rw [Module.End.mem_eigenspace_iff]
  change b2_cplxMap φ (b2_conj L v) = star ν • b2_conj L v
  rw [← b63g_conj_cplxMap, hv]
  exact b2a_conj_smul ν v

/-- **Both eigenspaces have half the rank.** On a weight-one lattice, a complexified integral
map with `ψ² = μ²`, `μ ≠ 0` and `μ̄ = -μ` has eigenspaces for `μ` and `-μ` of the dimension of
`F`, and `ℂ ⊗ L` has twice that dimension.
Source: Birkenhake–Lange, §1.2 and §5.5. -/
theorem b63g2_eigen_half {L : Type*} [AddCommGroup L] [Module.Finite ℤ L] [Module.Free ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) (hF : b2_IsWeightOne L F) (φ : L →+ L) (μ : ℂ) (hμ : μ ≠ 0)
    (hψ : ∀ v, b2_cplxMap φ (b2_cplxMap φ v) = (μ * μ) • v) (hstar : star μ = -μ) :
    Module.finrank ℂ ↥(Module.End.eigenspace (b2_cplxMap φ) (-μ)) = Module.finrank ℂ F ∧
      Module.finrank ℂ (ℂ ⊗[ℤ] L) = Module.finrank ℂ F + Module.finrank ℂ F := by
  set ψ := b2_cplxMap φ
  have hW : Module.finrank ℂ F + Module.finrank ℂ F = Module.finrank ℂ (ℂ ⊗[ℤ] L) := by
    have h := Submodule.finrank_add_eq_of_isCompl hF
    rwa [b2a_finrank_conjSubmodule] at h
  have hcompl : IsCompl (Module.End.eigenspace ψ μ) (Module.End.eigenspace ψ (-μ)) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v h1 h2
      rw [Module.End.mem_eigenspace_iff] at h1 h2
      have h3 : (2 * μ) • v = 0 := by
        rw [mul_smul, two_smul]
        nth_rewrite 1 [← neg_neg μ]
        rw [neg_smul, ← h1, ← h2]
        simp
      exact (smul_eq_zero.mp h3).resolve_left (mul_ne_zero two_ne_zero hμ)
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have ha : (2 * μ)⁻¹ • (ψ v + μ • v) ∈ Module.End.eigenspace ψ μ := by
        rw [Module.End.mem_eigenspace_iff, map_smul, map_add, map_smul, hψ]
        module
      have hb : -(2 * μ)⁻¹ • (ψ v - μ • v) ∈ Module.End.eigenspace ψ (-μ) := by
        rw [Module.End.mem_eigenspace_iff, map_smul, map_sub, map_smul, hψ]
        module
      have hv : v = (2 * μ)⁻¹ • (ψ v + μ • v) + -(2 * μ)⁻¹ • (ψ v - μ • v) := by
        rw [neg_smul, ← sub_eq_add_neg, ← smul_sub, add_sub_sub_cancel, ← two_smul ℂ,
          smul_smul, smul_smul]
        rw [show (2 * μ)⁻¹ * 2 * μ = 1 by field_simp, one_smul]
      rw [hv]
      exact Submodule.add_mem_sup ha hb
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  have hle1 : Module.finrank ℂ ↥(Module.End.eigenspace ψ μ) ≤
      Module.finrank ℂ ↥(Module.End.eigenspace ψ (-μ)) := by
    rw [← b2a_finrank_conjSubmodule, ← hstar]
    exact Submodule.finrank_mono (b63g2_conj_eigenspace φ μ)
  have hle2 : Module.finrank ℂ ↥(Module.End.eigenspace ψ (-μ)) ≤
      Module.finrank ℂ ↥(Module.End.eigenspace ψ μ) := by
    rw [← b2a_finrank_conjSubmodule]
    have h := b63g2_conj_eigenspace φ (-μ)
    rw [star_neg, hstar, neg_neg] at h
    exact Submodule.finrank_mono h
  omega

/-- **Eigenparts of the dual operator in `H^{1,0}`.** For an abelian variety `X`, a marking
`e : Λ ≃ Λ_X` carrying `F` to the period filtration, and `φ_X` with `φ_X ∘ e = e ∘ φ`, the
`μ`-eigenpart of the dual operator in `H^{1,0}` has the dimension of `F ∩ E_{-μ}(φ_ℂ)`.
Source: Birkenhake–Lange, §1.2, Theorem 1.4.1 and §5.5; `b2_abelianHodgeF_eq`,
`b63g_pairing_dual`. -/
theorem b63g2_dual_eigen (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) (e : Λ ≃+ b2_abelianLattice X)
    (he : F.map (b2_cplxMap e.toAddMonoidHom) = b2_abelianF X)
    (φ : Λ →+ Λ) (φX : b2_abelianLattice X →+ b2_abelianLattice X)
    (hφX : φX.comp e.toAddMonoidHom = e.toAddMonoidHom.comp φ)
    (μ : ℂ) (hμ : μ ≠ 0) (hψ : ∀ v, b2_cplxMap φ (b2_cplxMap φ v) = (μ * μ) • v)
    (hstar : star μ = -μ) :
    letI := (torusCohomology_cupProductOf X).finite
    Module.finrank ℂ ↥(Module.End.eigenspace ((b63g_dualOperator X φX).baseChange ℂ) μ ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (1, 0)) =
      Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (b2_cplxMap φ) (-μ)) := by
  letI := (torusCohomology_cupProductOf X).finite
  letI := (finiteBetti_abelian X).finite 1
  change Module.finrank ℂ ↥(Module.End.eigenspace ((b63g_dualOperator X φX).baseChange ℂ) μ ⊓
    cohomologyHodgePiece X 1 (1, 0)) = _
  have hann : (cohomologyHodgePiece X 1 (1, 0)).map (b2_abelianPairing X) =
      (b2_abelianF X).dualAnnihilator := by
    rw [← b2_abelianHodgeF_eq X, b2_abelianHodgeF,
      Subspace.dualCoannihilator_dualAnnihilator_eq]
    rfl
  let eC : (ℂ ⊗[ℤ] Λ) ≃ₗ[ℂ] (ℂ ⊗[ℤ] b2_abelianLattice X) :=
    e.toIntLinearEquiv.baseChange ℤ ℂ Λ (b2_abelianLattice X)
  have heC : ∀ v, eC v = b2_cplxMap e.toAddMonoidHom v := fun _ ↦ rfl
  have hF' : ∀ w, w ∈ b2_abelianF X ↔ eC.symm w ∈ F := by
    intro w
    rw [← he]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [← heC, LinearEquiv.symm_apply_apply]
      exact ha
    · intro h
      exact ⟨eC.symm w, h, by rw [← heC, LinearEquiv.apply_symm_apply]⟩
  have hcomm : ∀ v, b2_cplxMap φX (eC v) = eC (b2_cplxMap φ v) := by
    intro v
    rw [heC, heC, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← b63g_cplxMap_comp,
      ← b63g_cplxMap_comp, hφX]
  let π : (ℂ ⊗[ℚ] HQ X 1) →ₗ[ℂ] Module.Dual ℂ (ℂ ⊗[ℤ] Λ) :=
    (eC : (ℂ ⊗[ℤ] Λ) →ₗ[ℂ] (ℂ ⊗[ℤ] b2_abelianLattice X)).dualMap ∘ₗ b2_abelianPairing X
  have hπ : ∀ ξ v, π ξ v = b2_abelianPairing X ξ (eC v) := fun _ _ ↦ rfl
  have hπinj : Function.Injective π := by
    intro a b h
    apply b63g_pairing_injective X
    apply LinearMap.ext
    intro w
    have := LinearMap.congr_fun h (eC.symm w)
    rwa [hπ, hπ, LinearEquiv.apply_symm_apply] at this
  have hπJ : ∀ ξ v, π ((b63g_dualOperator X φX).baseChange ℂ ξ) v =
      π ξ (b2_cplxMap φ v) := by
    intro ξ v
    rw [hπ, hπ, b63g_pairing_dual, hcomm]
  have hdual : ∀ ξ, b2_abelianPairing X ξ ∈ (b2_abelianF X).dualAnnihilator ↔
      ∀ a ∈ F, π ξ a = 0 := by
    intro ξ
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro h a ha
      rw [hπ]
      exact h _ ((hF' _).2 (by rwa [LinearEquiv.symm_apply_apply]))
    · intro h w hw
      have := h _ ((hF' w).1 hw)
      rwa [hπ, LinearEquiv.apply_symm_apply] at this
  have hmem : ∀ ξ, ξ ∈ cohomologyHodgePiece X 1 (1, 0) ↔ ∀ a ∈ F, π ξ a = 0 := by
    intro ξ
    rw [← hdual, ← hann]
    constructor
    · intro h
      exact Submodule.mem_map_of_mem h
    · rintro ⟨ξ', hξ', h⟩
      rwa [← b63g_pairing_injective X h]
  have hsurj : ∀ f : Module.Dual ℂ (ℂ ⊗[ℤ] Λ), (∀ a ∈ F, f a = 0) → ∃ ξ, π ξ = f := by
    intro f hf
    let g : Module.Dual ℂ (ℂ ⊗[ℤ] b2_abelianLattice X) :=
      f ∘ₗ (eC.symm : (ℂ ⊗[ℤ] b2_abelianLattice X) →ₗ[ℂ] (ℂ ⊗[ℤ] Λ))
    have hg : g ∈ (b2_abelianF X).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      exact hf _ ((hF' w).1 hw)
    rw [← hann] at hg
    obtain ⟨ξ, -, hξ⟩ := hg
    refine ⟨ξ, LinearMap.ext fun v ↦ ?_⟩
    rw [hπ, hξ]
    change f (eC.symm (eC v)) = f v
    rw [LinearEquiv.symm_apply_apply]
  have h1 := b63g2_eigen_annihilator π hπinj _ (b2_cplxMap φ) hπJ _ F hmem hsurj μ hμ hψ
  have h2 := b63g2_eigen_half F hF φ μ hμ hψ hstar
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq F
    (Module.End.eigenspace (b2_cplxMap φ) (-μ))
  omega

/-- `φ² = -n` on the lattice gives `φ_ℂ² = μ²` when `μ² = -n`.
Source: `LinearMap.baseChange` is functorial. -/
theorem b63g2_cplxMap_sq {L : Type*} [AddCommGroup L] (φ : L →+ L) (n : ℤ)
    (hsq : ∀ l, φ (φ l) = (-n) • l) (μ : ℂ) (hμ : μ * μ = -(n : ℂ)) :
    ∀ v, b2_cplxMap φ (b2_cplxMap φ v) = (μ * μ) • v := by
  intro v
  induction v using TensorProduct.inductionOn with
  | tmul c l =>
    change c ⊗ₜ[ℤ] φ (φ l) = (μ * μ) • (c ⊗ₜ[ℤ] l)
    rw [hsq, TensorProduct.tmul_smul, hμ, ← Int.cast_neg, Int.cast_smul_eq_zsmul]
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]

/-- `i√d` is purely imaginary.
Source: `HodgeBlocks.WeilAction.omegaC`. -/
theorem b63g2_omegaC_star (d : ℚ) :
    star (HodgeBlocks.WeilAction.omegaC d) = -HodgeBlocks.WeilAction.omegaC d := by
  simp [HodgeBlocks.WeilAction.omegaC, Complex.conj_ofReal]

end HodgeLean.Foundations.Program
