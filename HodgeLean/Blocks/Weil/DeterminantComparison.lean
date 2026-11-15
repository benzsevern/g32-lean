import HodgeLean.Blocks.Weil.ExteriorQuotientDerivation
import HodgeLean.Blocks.Weil.KernelQuotient
import HodgeLean.Blocks.Weil.KernelSemisimple

/-! # The quadratic determinant and the rational Weil space -/

noncomputable section

namespace HodgeBlocks.WeilAction

open ExteriorRestriction

variable {K V : Type*} [Field K] [Algebra ℚ K] [Module.Finite ℚ K]
  [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
  [Module K V] [IsScalarTower ℚ K V] [Module.Finite K V]
  {M : QHodgeStructure 1 V} {d : ℚ}

/-- The exterior quotient annihilates the rational Weil operator for the compatible
quadratic-field action. -/
theorem quotient_derivationKernelOperatorQ (A : WeilAction M d) (ω : K)
    (hω : ω ^ 2 = algebraMap ℚ K (-d)) (hJ : A.J = scalarEnd (V := V) ω)
    (k : ℕ) (x : ⋀[ℚ]^(k + k) V) :
    quotient (K := K) (k + k) (derivationKernelOperatorQ A k x) = 0 := by
  change quotient (K := K) (k + k)
    (derivationExt A.J (k + k) (derivationExt A.J (k + k) x) +
      (4 * (k : ℚ) ^ 2 * d) • x) = 0
  rw [map_add, map_smul, hJ, quotient_derivationExt, quotient_derivationExt,
    smul_smul, ← IsScalarTower.algebraMap_smul K (4 * (k : ℚ) ^ 2 * d),
    ← add_smul]
  have hc : (((k + k : ℕ) : K) * ω) * (((k + k : ℕ) : K) * ω) +
      algebraMap ℚ K (4 * (k : ℚ) ^ 2 * d) = 0 := by
    calc
      _ = (((k + k : ℕ) : K) ^ 2) * ω ^ 2 +
          algebraMap ℚ K (4 * (k : ℚ) ^ 2 * d) := by ring
      _ = 0 := by rw [hω]; push_cast; norm_num; ring
  rw [hc, zero_smul]

/-- The K-exterior quotient restricts to an isomorphism on the rational Weil space. -/
theorem bijective_quotient_weilClasses (A : WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
    (hκ : 1 ≤ Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))
    (ω : K) (hω : ω ^ 2 = algebraMap ℚ K (-d))
    (hJ : A.J = scalarEnd (V := V) ω) (hK : Module.finrank ℚ K = 2)
    (hV : Module.finrank K V =
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
        Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) :
    Function.Bijective ((quotient (K := K) _).comp (A.weilClasses hH hW).subtype) := by
  let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  letI : Module.Finite ℚ (⋀[K]^(k + k) V) := Module.Finite.trans K _
  have hn : 0 < k + k := by dsimp [k]; omega
  have hdim : Module.finrank ℚ (⋀[K]^(k + k) V) = 2 := by
    rw [← Module.finrank_mul_finrank ℚ K (⋀[K]^(k + k) V), hK]
    rw [← hV, finrank_topExteriorPower K V]
  rw [A.weilClasses_eq_ker_derivationKernelOperatorQ hH hW hd]
  apply bijective_quotient_restrict_ker
  · exact quotient_surjective (k + k) hn
  · exact A.quotient_derivationKernelOperatorQ ω hω hJ k
  · exact A.derivationKernelOperatorQ_no_nilpotent hH hW hd
  · rw [← A.weilClasses_eq_ker_derivationKernelOperatorQ hH hW hd,
      A.finrank_weilClasses_eq_two hH hW hd hκ, hdim]

/-- Quadratic restriction of scalars gives the expected K-dimension of a Weil factor. -/
theorem finrank_over_quadratic (A : WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
    (hK : Module.finrank ℚ K = 2) :
    Module.finrank K V = Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) := by
  have hc := Submodule.finrank_add_eq_of_isCompl (A.isCompl_Vs_Vsbar hd)
  rw [A.finrank_Vsbar_eq_Vs, Module.finrank_baseChange] at hc
  have hVs := A.finrank_Vs_eq_twice_inf_H10 hH hW
  have hr := Module.finrank_mul_finrank ℚ K V
  rw [hK] at hr
  omega

section Inclusion

variable (A : WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
    (hκ : 1 ≤ Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))
    (ω : K) (hω : ω ^ 2 = algebraMap ℚ K (-d))
    (hJ : A.J = scalarEnd (V := V) ω) (hK : Module.finrank ℚ K = 2)

/-- The normalized quadratic determinant comparison: its forward map is the
universal exterior quotient restricted to the Weil space. -/
def determinantEquiv : ↥(A.weilClasses hH hW) ≃ₗ[ℚ]
    (⋀[K]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V) :=
  LinearEquiv.ofBijective ((quotient (K := K) _).comp (A.weilClasses hH hW).subtype)
    (A.bijective_quotient_weilClasses hH hW hd hκ ω hω hJ hK
      (A.finrank_over_quadratic hH hW hd hK))

/-- The rational inclusion of the K-determinant, normalized as a section of the
universal exterior quotient with image in the Weil space. -/
def determinantInclusion :
    (⋀[K]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V) →ₗ[ℚ]
    (⋀[ℚ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V) :=
  (A.weilClasses hH hW).subtype.comp
    (A.determinantEquiv hH hW hd hκ ω hω hJ hK).symm.toLinearMap

/-- The normalized K-determinant inclusion is injective. -/
theorem determinantInclusion_injective :
    Function.Injective (A.determinantInclusion hH hW hd hκ ω hω hJ hK) :=
  (A.weilClasses hH hW).injective_subtype.comp
    (A.determinantEquiv hH hW hd hκ ω hω hJ hK).symm.injective

/-- Every element of the K-determinant maps to a rational Weil class. -/
theorem determinantInclusion_mem (w) :
    A.determinantInclusion hH hW hd hκ ω hω hJ hK w ∈ A.weilClasses hH hW :=
  ((A.determinantEquiv hH hW hd hκ ω hω hJ hK).symm w).property

/-- The image of the K-determinant is the entire rational Weil space. -/
theorem range_determinantInclusion :
    LinearMap.range (A.determinantInclusion hH hW hd hκ ω hω hJ hK) =
      A.weilClasses hH hW := by
  let e := A.determinantEquiv hH hW hd hκ ω hω hJ hK
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact A.determinantInclusion_mem hH hW hd hκ ω hω hJ hK w
  · intro hx
    refine ⟨e ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)

/-- The determinant comparison uses the normalization q ∘ i = id. -/
theorem quotient_determinantInclusion (w) :
    quotient (K := K) _ (A.determinantInclusion hH hW hd hκ ω hω hJ hK w) = w :=
  (A.determinantEquiv hH hW hd hκ ω hω hJ hK).apply_symm_apply w

end Inclusion

#print axioms finrank_over_quadratic
#print axioms determinantEquiv
#print axioms determinantInclusion
#print axioms determinantInclusion_injective
#print axioms determinantInclusion_mem
#print axioms range_determinantInclusion
#print axioms quotient_determinantInclusion

#print axioms quotient_derivationKernelOperatorQ
#print axioms bijective_quotient_weilClasses

end HodgeBlocks.WeilAction
