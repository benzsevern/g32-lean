import HodgeLean.Foundations.DualForm

/-! # Linear algebra for product polarizations -/

noncomputable section
set_option maxHeartbeats 400000
open Module
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]

/-- Evaluate functoriality of exterior powers on a vector.
Source: Mathlib `exteriorPower.map_comp`. -/
theorem cp_exterior_map_map {Z : Type*} [AddCommGroup Z] [Module K Z]
    (n : ℕ) (f : U →ₗ[K] V) (g : V →ₗ[K] Z) (x : ⋀[K]^n U) :
    exteriorPower.map n g (exteriorPower.map n f x) = exteriorPower.map n (g ∘ₗ f) x :=
  (LinearMap.congr_fun (exteriorPower.map_comp f g) x).symm

/-- Contraction is natural for linear maps between different spaces.
Source: Bourbaki, *Algebra*, Chapter III, §7 (contraction of exterior tensors). -/
theorem cp_contract_map (f : U →ₗ[K] V) (ω : ⋀[K]^2 U) :
    contract (exteriorPower.map 2 f ω) = f ∘ₗ contract ω ∘ₗ f.dualMap := by
  have h : contract ∘ₗ exteriorPower.map 2 f =
      (LinearMap.llcomp K (Module.Dual K V) U V f ∘ₗ
        (LinearMap.llcomp K (Module.Dual K V) (Module.Dual K U) U).flip f.dualMap) ∘ₗ contract := by
    ext v φ
    simp [LinearMap.dualMap_apply]
  exact LinearMap.congr_fun h ω

/-- The two-vector on a product formed from its two factors.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §5.2. -/
def cp_sumVec (ωU : ⋀[K]^2 U) (ωV : ⋀[K]^2 V) : ⋀[K]^2 (U × V) :=
  exteriorPower.map 2 (LinearMap.inl K U V) ωU +
    exteriorPower.map 2 (LinearMap.inr K U V) ωV

example (ωU : ⋀[K]^2 U) : cp_sumVec ωU (0 : ⋀[K]^2 V) =
    exteriorPower.map 2 (LinearMap.inl K U V) ωU := by
  simp only [cp_sumVec, map_zero, add_zero]

/-- Contraction of the sum restricts the covector to each factor.
Source: `cp_contract_map`, linearity of contraction. -/
theorem cp_contract_sumVec (ωU : ⋀[K]^2 U) (ωV : ⋀[K]^2 V) (φ : Module.Dual K (U × V)) :
    contract (cp_sumVec ωU ωV) φ =
      (contract ωU (φ ∘ₗ LinearMap.inl K U V), contract ωV (φ ∘ₗ LinearMap.inr K U V)) := by
  simp only [cp_sumVec, map_add, LinearMap.add_apply, cp_contract_map,
    LinearMap.comp_apply, LinearMap.dualMap_apply', LinearMap.inl_apply, LinearMap.inr_apply]
  ext <;> simp

/-- Nondegenerate two-vectors remain nondegenerate under direct sum.
Source: `cp_contract_sumVec`; the inverse covector is the sum of the inverse covectors. -/
theorem cp_sumVec_nondegenerate [Module.Finite K U] [Module.Finite K V]
    {ωU : ⋀[K]^2 U} {ωV : ⋀[K]^2 V}
    (hU : IsNondegenerate ωU) (hV : IsNondegenerate ωV) :
    IsNondegenerate (cp_sumVec ωU ωV) := by
  have hs : Function.Surjective (contract (cp_sumVec ωU ωV)) := by
    rintro ⟨x, y⟩
    obtain ⟨φ, hφ⟩ := hU.surjective x
    obtain ⟨ψ, hψ⟩ := hV.surjective y
    refine ⟨φ ∘ₗ LinearMap.fst K U V + ψ ∘ₗ LinearMap.snd K U V, ?_⟩
    rw [cp_contract_sumVec]
    have h₁ : (φ ∘ₗ LinearMap.fst K U V + ψ ∘ₗ LinearMap.snd K U V) ∘ₗ
        LinearMap.inl K U V = φ := by ext x; simp
    have h₂ : (φ ∘ₗ LinearMap.fst K U V + ψ ∘ₗ LinearMap.snd K U V) ∘ₗ
        LinearMap.inr K U V = ψ := by ext y; simp
    rw [h₁, h₂, hφ, hψ]
  refine ⟨?_, hs⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr hs
  exact Subspace.dual_finrank_eq

/-- The dual alternating form of a sum is the sum of the dual alternating forms.
Source: `cp_contract_sumVec`, the inverse definition of `dualForm`. -/
theorem cp_dualForm_sumVec [Module.Finite K U] [Module.Finite K V]
    {ωU : ⋀[K]^2 U} {ωV : ⋀[K]^2 V}
    (hU : IsNondegenerate ωU) (hV : IsNondegenerate ωV) (x y : U × V) :
    dualForm (cp_sumVec_nondegenerate hU hV) x y =
      dualForm hU x.1 y.1 + dualForm hV x.2 y.2 := by
  let hP := cp_sumVec_nondegenerate hU hV
  let φ := (contractEquiv hP).symm y
  have hc : contract (cp_sumVec ωU ωV) φ = y := (contractEquiv hP).apply_symm_apply y
  rw [cp_contract_sumVec] at hc
  have h₁ : φ ∘ₗ LinearMap.inl K U V = (contractEquiv hU).symm y.1 := by
    apply (contractEquiv hU).injective
    rw [(contractEquiv hU).apply_symm_apply]
    exact congrArg Prod.fst hc
  have h₂ : φ ∘ₗ LinearMap.inr K U V = (contractEquiv hV).symm y.2 := by
    apply (contractEquiv hV).injective
    rw [(contractEquiv hV).apply_symm_apply]
    exact congrArg Prod.snd hc
  change φ x = ((contractEquiv hU).symm y.1) x.1 + ((contractEquiv hV).symm y.2) x.2
  calc
    φ x = φ (LinearMap.inl K U V x.1 + LinearMap.inr K U V x.2) := by congr 1; ext <;> simp
    _ = φ (LinearMap.inl K U V x.1) + φ (LinearMap.inr K U V x.2) := map_add φ _ _
    _ = _ := by
      change (φ ∘ₗ LinearMap.inl K U V) x.1 + (φ ∘ₗ LinearMap.inr K U V) x.2 = _
      rw [h₁, h₂]


/-- Rosati skewness is preserved by direct sums.
Source: `isRosatiSkew_iff_dualForm`, `cp_dualForm_sumVec`. -/
theorem cp_sumVec_rosati [Module.Finite K U] [Module.Finite K V]
    {ωU : ⋀[K]^2 U} {ωV : ⋀[K]^2 V}
    (hU : IsNondegenerate ωU) (hV : IsNondegenerate ωV)
    (JU : Module.End K U) (JV : Module.End K V)
    (hJU : IsRosatiSkew ωU JU) (hJV : IsRosatiSkew ωV JV) :
    IsRosatiSkew (cp_sumVec ωU ωV) (JU.prodMap JV) := by
  apply (isRosatiSkew_iff_dualForm (cp_sumVec_nondegenerate hU hV) _).mpr
  intro x y
  rw [cp_dualForm_sumVec, cp_dualForm_sumVec]
  change dualForm hU (JU x.1) y.1 + dualForm hV (JV x.2) y.2 =
    -(dualForm hU x.1 (JU y.1) + dualForm hV x.2 (JV y.2))
  rw [(isRosatiSkew_iff_dualForm hU JU).mp hJU,
    (isRosatiSkew_iff_dualForm hV JV).mp hJV]
  ring

/-- Linear equivalences transport nondegenerate two-vectors.
Source: `cp_contract_map`. -/
theorem cp_map_nondegenerate [Module.Finite K U] [Module.Finite K V]
    (e : U ≃ₗ[K] V) {ω : ⋀[K]^2 U} (hω : IsNondegenerate ω) :
    IsNondegenerate (exteriorPower.map 2 e.toLinearMap ω) := by
  rw [IsNondegenerate, cp_contract_map]
  exact e.bijective.comp (hω.comp e.dualMap.bijective)

/-- Transport preserves the dual form on transported vectors.
Source: `cp_contract_map`, the inverse definition of `dualForm`. -/
theorem cp_dualForm_map [Module.Finite K U] [Module.Finite K V]
    (e : U ≃ₗ[K] V) {ω : ⋀[K]^2 U} (hω : IsNondegenerate ω) (x y : U) :
    dualForm (cp_map_nondegenerate e hω) (e x) (e y) = dualForm hω x y := by
  let φ := (contractEquiv hω).symm y
  let ψ := φ ∘ₗ e.symm.toLinearMap
  have hp : e.toLinearMap.dualMap ψ = φ := by
    ext v
    simp only [LinearMap.dualMap_apply, ψ, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hc : contract (exteriorPower.map 2 e.toLinearMap ω) ψ = e y := by
    rw [cp_contract_map, LinearMap.comp_apply, LinearMap.comp_apply, hp]
    exact congrArg e ((contractEquiv hω).apply_symm_apply y)
  have hi : (contractEquiv (cp_map_nondegenerate e hω)).symm (e y) = ψ := by
    apply (contractEquiv (cp_map_nondegenerate e hω)).injective
    rw [(contractEquiv (cp_map_nondegenerate e hω)).apply_symm_apply]
    exact hc.symm
  change ((contractEquiv (cp_map_nondegenerate e hω)).symm (e y)) (e x) = φ x
  rw [hi]
  exact congrArg φ (e.symm_apply_apply x)


/-- A specified equality of two-vectors identifies the transported dual forms.
Source: `cp_dualForm_map`. -/
theorem cp_dualForm_map_of_eq [Module.Finite K U] [Module.Finite K V]
    (e : U ≃ₗ[K] V) {ωU : ⋀[K]^2 U} {ωV : ⋀[K]^2 V}
    (hU : IsNondegenerate ωU) (hV : IsNondegenerate ωV)
    (hω : exteriorPower.map 2 e.toLinearMap ωU = ωV) (x y : U) :
    dualForm hV (e x) (e y) = dualForm hU x y := by
  subst ωV
  exact cp_dualForm_map e hU x y

/-- An intertwining linear equivalence transports Rosati skewness.
Source: `cp_dualForm_map`, `isRosatiSkew_iff_dualForm`. -/
theorem cp_map_rosati [Module.Finite K U] [Module.Finite K V]
    (e : U ≃ₗ[K] V) {ω : ⋀[K]^2 U} (hω : IsNondegenerate ω)
    (JU : Module.End K U) (JV : Module.End K V)
    (hJ : ∀ x, JV (e x) = e (JU x)) (hR : IsRosatiSkew ω JU) :
    IsRosatiSkew (exteriorPower.map 2 e.toLinearMap ω) JV := by
  apply (isRosatiSkew_iff_dualForm (cp_map_nondegenerate e hω) JV).mpr
  intro x y
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := e.surjective y
  rw [hJ, hJ, cp_dualForm_map, cp_dualForm_map]
  exact (isRosatiSkew_iff_dualForm hω JU).mp hR x y

/-- A nonzero scalar preserves nondegeneracy of a two-vector.
Source: linearity of contraction, bijectivity of nonzero scalar multiplication. -/
theorem cp_smul_nondegenerate [Module.Finite K U] {ω : ⋀[K]^2 U}
    (c : K) (hc : c ≠ 0) (hω : IsNondegenerate ω) : IsNondegenerate (c • ω) := by
  rw [IsNondegenerate, map_smul]
  exact (LinearEquiv.smulOfNeZero K U c hc).bijective.comp hω

/-- Scaling a two-vector scales its dual form by the reciprocal scalar.
Source: the inverse definition of `dualForm`, linearity of contraction. -/
theorem cp_dualForm_smul [Module.Finite K U] {ω : ⋀[K]^2 U}
    (c : K) (hc : c ≠ 0) (hω : IsNondegenerate ω)
    (hscaled : IsNondegenerate (c • ω)) (x y : U) :
    dualForm hscaled x y = c⁻¹ * dualForm hω x y := by
  let φ := (contractEquiv hω).symm y
  have hh : contract (c • ω) (c⁻¹ • φ) = y := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc, one_smul]
    exact (contractEquiv hω).apply_symm_apply y
  have hi : (contractEquiv hscaled).symm y = c⁻¹ • φ := by
    apply (contractEquiv hscaled).injective
    rw [(contractEquiv hscaled).apply_symm_apply]
    exact hh.symm
  rw [dualForm_apply, hi, LinearMap.smul_apply]
  rfl

/-- A specified scalar equality of two-vectors identifies their dual forms.
Source: `cp_dualForm_smul`. -/
theorem cp_dualForm_smul_of_eq [Module.Finite K U] {ω ωscaled : ⋀[K]^2 U}
    (c : K) (hc : c ≠ 0) (hω : IsNondegenerate ω) (hscaled : IsNondegenerate ωscaled)
    (hv : ωscaled = c • ω) (x y : U) : dualForm hscaled x y = c⁻¹ * dualForm hω x y := by
  subst ωscaled
  exact cp_dualForm_smul c hc hω hscaled x y

/-- Negating an operator preserves its Rosati skewness.
Source: bilinearity of the dual alternating form. -/
theorem cp_neg_rosati [Module.Finite K U] {ω : ⋀[K]^2 U}
    (hω : IsNondegenerate ω) (J : Module.End K U) (hR : IsRosatiSkew ω J) :
    IsRosatiSkew ω (-J) := by
  apply (isRosatiSkew_iff_dualForm hω (-J)).mpr
  intro x y
  simp only [LinearMap.neg_apply, map_neg, (isRosatiSkew_iff_dualForm hω J).mp hR,
    LinearMap.neg_apply, neg_neg]

/-- Scaling the vector preserves Rosati skewness of an operator.
Source: `cp_dualForm_smul`. -/
theorem cp_smul_rosati [Module.Finite K U] {ω : ⋀[K]^2 U}
    (c : K) (hc : c ≠ 0) (hω : IsNondegenerate ω) (hscaled : IsNondegenerate (c • ω))
    (J : Module.End K U) (hR : IsRosatiSkew ω J) : IsRosatiSkew (c • ω) J := by
  apply (isRosatiSkew_iff_dualForm hscaled J).mpr
  intro x y
  rw [cp_dualForm_smul c hc hω hscaled, cp_dualForm_smul c hc hω hscaled,
    (isRosatiSkew_iff_dualForm hω J).mp hR]
  ring


end HodgeLean.Foundations.Program
