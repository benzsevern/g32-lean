import HodgeLean.Foundations.PositivePolarizationRosati
import HodgeLean.Foundations.PositivePolarizationLinear

noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

theorem m2_contract_ratio_injective {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] [AddCommGroup W] [Module ℚ W]
    (e : W ≃ₗ[ℚ] ⋀[ℚ]^2 V) {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω) :
    Function.Injective (fun d => contract (e d) ∘ₗ (contractEquiv hω).symm.toLinearMap) := by
  intro d f h
  apply e.injective
  apply contract_injective
  ext φ
  have ht := LinearMap.congr_fun h ((contractEquiv hω) φ)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply] using ht

theorem m2_contract_ratio_selfadjoint {V : Type*} [AddCommGroup V] [Module ℚ V]
    {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω) (d : ⋀[ℚ]^2 V) :
    p1_adjoint ω hω (contract d ∘ₗ (contractEquiv hω).symm.toLinearMap) =
      contract d ∘ₗ (contractEquiv hω).symm.toLinearMap := by
  apply p1r_adjoint_eq_of hω
  intro x y
  calc
    _ = -dualForm hω ((contract d ∘ₗ (contractEquiv hω).symm.toLinearMap) y) x := by
      simp only [dualForm_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      exact p1l_contract_skew _ _ _
    _ = _ := (isAlt_dualForm hω).neg_eq _ _

theorem m2_bivector_fixed_iff_commutes {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω)
    (d : ⋀[K]^2 V) (u : Module.End K V) (hu : IsUnit u)
    (hpol : exteriorPower.map 2 u ω = ω) :
    exteriorPower.map 2 u d = d ↔
      u ∘ₗ (contract d ∘ₗ (contractEquiv hω).symm.toLinearMap) =
        (contract d ∘ₗ (contractEquiv hω).symm.toLinearMap) ∘ₗ u := by
  have hb := congrArg contract hpol
  rw [contract_map] at hb
  have hb' (φ : Module.Dual K V) : u (contract ω (u.dualMap φ)) = contract ω φ :=
    LinearMap.congr_fun hb φ
  have hinj : Function.Injective u := by
    obtain ⟨a, rfl⟩ := hu
    intro x y h
    have hh := congrArg (fun z => (a.inv : Module.End K V) z) h
    simpa only [← Module.End.mul_apply, a.inv_val, Module.End.one_apply] using hh
  constructor
  · intro hd
    have ha := congrArg contract hd
    rw [contract_map] at ha
    ext x
    obtain ⟨φ, rfl⟩ := hω.2 x
    obtain ⟨ψ, rfl⟩ := LinearMap.dualMap_surjective_of_injective hinj φ
    change u (contract d ((contractEquiv hω).symm (contract ω (u.dualMap ψ)))) =
      contract d ((contractEquiv hω).symm (u (contract ω (u.dualMap ψ))))
    rw [contractEquiv_symm_contract, hb', contractEquiv_symm_contract]
    exact LinearMap.congr_fun ha ψ
  · intro hc
    apply contract_injective
    rw [contract_map]
    ext φ
    have hh := LinearMap.congr_fun hc (contract ω (u.dualMap φ))
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      contractEquiv_symm_contract, hb'] using hh

theorem m2_derivation_fixed_iff_commutes {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (d : ⋀[K]^2 V) (f : Module.End K V)
    (hpol : InvariantsExterior.exteriorDer 2 f ω = 0) :
    InvariantsExterior.exteriorDer 2 f d = 0 ↔
      f ∘ₗ (contract d ∘ₗ (contractEquiv hω).symm.toLinearMap) =
        (contract d ∘ₗ (contractEquiv hω).symm.toLinearMap) ∘ₗ f := by
  have hb := congrArg contract hpol
  rw [pol1_contract_exteriorDer, map_zero] at hb
  have hb' (φ : Module.Dual K V) : f (contract ω φ) = -contract ω (f.dualMap φ) := by
    have hh := LinearMap.congr_fun hb φ
    exact eq_neg_of_add_eq_zero_left hh
  rw [← contract_injective.eq_iff, map_zero, pol1_contract_exteriorDer]
  constructor
  · intro hd
    ext x
    obtain ⟨φ, rfl⟩ := hω.2 x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      contractEquiv_symm_contract, hb', map_neg]
    have hh := LinearMap.congr_fun hd φ
    exact eq_neg_of_add_eq_zero_left hh
  · intro hc
    ext φ
    have hh := LinearMap.congr_fun hc (contract ω φ)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      contractEquiv_symm_contract, hb', map_neg] at hh
    exact add_eq_zero_iff_eq_neg.mpr hh

theorem m2_eigenspace_of_split {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (P Q : Submodule K W) (C : Module.End K W) (a b : K) (hab : a ≠ b)
    (hsplit : P ⊔ Q = ⊤) (hP : ∀ x ∈ P, C x = a • x)
    (hQ : ∀ x ∈ Q, C x = b • x) : C.eigenspace a = P := by
  apply le_antisymm
  · intro x hx
    obtain ⟨p, hp, q, hq, heq⟩ := Submodule.mem_sup.mp (hsplit ▸ Submodule.mem_top : x ∈ P ⊔ Q)
    have h := Module.End.mem_eigenspace_iff.mp hx
    rw [← heq, map_add, hP _ hp, hQ _ hq, smul_add] at h
    have hq0 : q = 0 := by
      have hh : (b - a) • q = 0 := by
        rw [sub_smul, sub_eq_zero]
        exact add_left_cancel h
      exact (smul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hab.symm)
    rw [← heq, hq0, add_zero]
    exact hp
  · intro x hx
    exact Module.End.mem_eigenspace_iff.mpr (hP x hx)

end HodgeLean.Foundations.Program
