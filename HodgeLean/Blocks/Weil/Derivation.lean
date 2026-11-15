import HodgeLean.Blocks.Weil.WeilClasses
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Derivations on exterior powers -/

open scoped TensorProduct

noncomputable section
namespace HodgeBlocks

variable {R : Type*} [Field R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The single Leibniz term: identity on every slot except slot `i`, which becomes `T`. -/
def leibnizTerm (T : M →ₗ[R] M) (n : ℕ) (i : Fin n) :
    MultilinearMap R (fun _ : Fin n => M) (⋀[R]^n M) :=
  (exteriorPower.ιMulti R n).toMultilinearMap.compLinearMap
    (Function.update (fun _ : Fin n => (LinearMap.id : M →ₗ[R] M)) i T)

theorem leibnizTerm_apply (T : M →ₗ[R] M) (n : ℕ) (i : Fin n) (v : Fin n → M) :
    leibnizTerm T n i v = exteriorPower.ιMulti R n (Function.update v i (T (v i))) := by
  rw [leibnizTerm, MultilinearMap.compLinearMap_apply]
  apply congrArg (⇑(exteriorPower.ιMulti R n))
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Function.update_of_ne h]

/-- Sum of the Leibniz terms as a bundled multilinear map. -/
def derivationMultilinear (T : M →ₗ[R] M) (n : ℕ) :
    MultilinearMap R (fun _ : Fin n => M) (⋀[R]^n M) :=
  ∑ i : Fin n, leibnizTerm T n i

theorem derivationMultilinear_apply (T : M →ₗ[R] M) (n : ℕ) (v : Fin n → M) :
    derivationMultilinear T n v = ∑ i : Fin n, exteriorPower.ιMulti R n
      (Function.update v i (T (v i))) := by
  simp [derivationMultilinear, leibnizTerm_apply]

/-- The Leibniz sum is alternating. -/
def derivationAlternating (T : M →ₗ[R] M) (n : ℕ) : M [⋀^Fin n]→ₗ[R] (⋀[R]^n M) :=
  { toMultilinearMap := derivationMultilinear T n
    map_eq_zero_of_eq' := by
      classical
      intro v i₀ j₀ hv hij
      change derivationMultilinear T n v = 0
      rw [derivationMultilinear_apply]
      have hpair : ∀ i : Fin n, i ≠ i₀ → i ≠ j₀ →
          exteriorPower.ιMulti R n (Function.update v i (T (v i))) = 0 := by
        intro i hi0 hj0
        exact (exteriorPower.ιMulti R n).map_eq_zero_of_eq' _ i₀ j₀
          (by rw [Function.update_of_ne (Ne.symm hi0),
              Function.update_of_ne (Ne.symm hj0)]; exact hv)
          hij
      rw [← Finset.sum_subset (Finset.subset_univ ({i₀, j₀} : Finset (Fin n)))
          (fun x _ hx => hpair x
            (fun h => hx (by simp [h]))
            (fun h => hx (by simp [h])))]
      rw [Finset.sum_pair hij]
      have hw : Function.update v j₀ (T (v j₀)) =
          (Function.update v i₀ (T (v i₀))) ∘ Equiv.swap i₀ j₀ := by
        funext x
        simp only [Function.comp_apply]
        rcases eq_or_ne x i₀ with hx | hx
        · subst hx
          simp [hij, hij.symm, hv]
        · rcases eq_or_ne x j₀ with hx2 | hx2
          · subst hx2
            simp [hv]
          · simp [Equiv.swap_apply_of_ne_of_ne hx hx2, hx, hx2]
      rw [hw]
      exact (exteriorPower.ιMulti R n).map_add_swap _ hij }

theorem derivationAlternating_apply (T : M →ₗ[R] M) (n : ℕ) (v : Fin n → M) :
    derivationAlternating T n v = ∑ i : Fin n, exteriorPower.ιMulti R n
      (Function.update v i (T (v i))) :=
  derivationMultilinear_apply T n v

/-- The derivation extension of `T` to the `n`th exterior power. -/
noncomputable def derivationExt (T : M →ₗ[R] M) (n : ℕ) : ⋀[R]^n M →ₗ[R] ⋀[R]^n M :=
  exteriorPower.alternatingMapLinearEquiv (derivationAlternating T n)

@[simp] theorem derivationExt_ιMulti (T : M →ₗ[R] M) (n : ℕ) (v : Fin n → M) :
    derivationExt T n (exteriorPower.ιMulti R n v) =
      ∑ i : Fin n, exteriorPower.ιMulti R n (Function.update v i (T (v i))) := by
  rw [derivationExt, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    derivationAlternating_apply]

theorem derivationExt_ιMulti_of_eigen (T : M →ₗ[R] M) (n : ℕ) (v : Fin n → M)
    (c : Fin n → R) (hc : ∀ i, T (v i) = c i • v i) :
    derivationExt T n (exteriorPower.ιMulti R n v) =
      (∑ i, c i) • exteriorPower.ιMulti R n v := by
  classical
  rw [derivationExt_ιMulti]
  calc
    (∑ i : Fin n, exteriorPower.ιMulti R n (Function.update v i (T (v i)))) =
        ∑ i : Fin n, c i • exteriorPower.ιMulti R n v := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hc i, (exteriorPower.ιMulti R n).map_update_smul]
      simp
    _ = (∑ i, c i) • exteriorPower.ιMulti R n v := by rw [Finset.sum_smul]

/-- On the exterior power of an eigenspace, the induced derivation is scalar. -/
theorem derivationExt_comp_exteriorPower_map_eigenspace (T : M →ₗ[R] M) (n : ℕ) (c : R) :
    (derivationExt T n).comp
        (exteriorPower.map n (Module.End.eigenspace T c).subtype) =
      ((n : R) * c) • exteriorPower.map n (Module.End.eigenspace T c).subtype := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R n (Module.End.eigenspace T c))
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.comp_apply]
  have hm := DFunLike.congr_fun
    (exteriorPower.map_comp_ιMulti (Module.End.eigenspace T c).subtype) v
  have hm' : exteriorPower.map n (Module.End.eigenspace T c).subtype
      (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti R n ((Module.End.eigenspace T c).subtype ∘ v) := by
    simpa using hm
  change derivationExt T n
      (exteriorPower.map n (Module.End.eigenspace T c).subtype
        (exteriorPower.ιMulti R n v)) =
    ((n : R) * c) • exteriorPower.map n (Module.End.eigenspace T c).subtype
      (exteriorPower.ιMulti R n v)
  rw [hm', derivationExt_ιMulti_of_eigen T n _ (fun _ => c)]
  · simp [Finset.sum_const, nsmul_eq_mul]
  · intro i
    exact Module.End.mem_eigenspace_iff.mp (v i).2

theorem complexifyWedge_derivationExt {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V]
    {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d) (n : ℕ)
    (w : ⋀[ℚ]^n V) :
    complexifyWedge n (derivationExt A.J n w) =
      derivationExt A.Jc n (complexifyWedge n w) := by
  let F := (complexifyWedge n).comp (derivationExt A.J n)
  let G := ((derivationExt A.Jc n).restrictScalars ℚ).comp (complexifyWedge n)
  change F w = G w
  apply LinearMap.congr_fun
  apply LinearMap.ext_on (exteriorPower.ιMulti_span ℚ n V)
  rintro _ ⟨v, rfl⟩
  simp only [F, G, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    derivationExt_ιMulti, complexifyWedge_ιMulti, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (⇑(exteriorPower.ιMulti ℂ n))
  funext j
  by_cases h : j = i
  · subst h
    simp [LinearMap.baseChange_tmul]
  · simp [Function.update_of_ne h, LinearMap.baseChange_tmul]

/-- The canonical inclusion of a rational vector space into its complexification is injective. -/
theorem complexify_injective {V : Type*} [AddCommGroup V] [Module ℚ V] :
    Function.Injective (complexify V) := by
  obtain ⟨f, -, hf⟩ := LinearMap.exists_extend_of_notMem
    (p := (⊥ : Submodule ℚ ℂ)) (0 : (⊥ : Submodule ℚ ℂ) →ₗ[ℚ] ℚ)
    (show (1 : ℂ) ∉ (⊥ : Submodule ℚ ℂ) by simp) (1 : ℚ)
  let g : ℂ ⊗[ℚ] V →ₗ[ℚ] V := TensorProduct.lift
    { toFun := fun c => f c • LinearMap.id
      map_add' := by intros; ext; simp [add_smul]
      map_smul' := by intros; ext; simp [smul_smul] }
  intro x y h
  have h' := congrArg g h
  change g (1 ⊗ₜ[ℚ] x) = g (1 ⊗ₜ[ℚ] y) at h'
  change (f 1) • x = (f 1) • y at h'
  simpa [hf] using h'

namespace WeilAction

/-- The quadratic polynomial in the exterior derivation used to detect the two top Weil
eigenlines. -/
def derivationKernelOperator {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {M : QHodgeStructure 1 V} {d : ℚ}
    (A : WeilAction M d) (k : ℕ) :
    Module.End ℂ (⋀[ℂ]^(k + k) (TensorProduct ℚ ℂ V)) :=
  let T := derivationExt A.Jc (k + k)
  T.comp T + (4 * (k : ℂ) ^ 2 * (d : ℂ)) • LinearMap.id

/-- Both top eigenspace exterior powers are killed by the quadratic derivation operator. -/
theorem sup_le_eigenspace_ker {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {M : QHodgeStructure 1 V} {d : ℚ}
    (A : WeilAction M d) (hd : 0 < d) (k : ℕ) :
    LinearMap.range (exteriorPower.map (k + k) A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map (k + k) A.Vsbar.subtype) ≤
      LinearMap.ker (derivationKernelOperator A k) := by
  let m := k + k
  let T := derivationExt A.Jc m
  let ω := WeilAction.omegaC d
  let F := exteriorPower.map m A.Vs.subtype
  let Fbar := exteriorPower.map m A.Vsbar.subtype
  have hω2 : ω ^ 2 = -(d : ℂ) := WeilAction.omegaC_sq hd
  have hscalar (s : ℂ) (hs : s = ω ∨ s = -ω) :
      (((m : ℂ) * s) * ((m : ℂ) * s) + 4 * (k : ℂ) ^ 2 * (d : ℂ)) = 0 := by
    rcases hs with rfl | rfl
    · rw [show (m : ℂ) = 2 * (k : ℂ) by simp [m]; ring]
      calc
        (2 * (k : ℂ) * ω) * (2 * (k : ℂ) * ω) + 4 * (k : ℂ) ^ 2 * (d : ℂ) =
            4 * (k : ℂ) ^ 2 * (ω ^ 2 + (d : ℂ)) := by ring
        _ = 0 := by rw [hω2]; ring
    · rw [show (m : ℂ) = 2 * (k : ℂ) by simp [m]; ring]
      calc
        (2 * (k : ℂ) * -ω) * (2 * (k : ℂ) * -ω) + 4 * (k : ℂ) ^ 2 * (d : ℂ) =
            4 * (k : ℂ) ^ 2 * (ω ^ 2 + (d : ℂ)) := by ring
        _ = 0 := by rw [hω2]; ring
  have hside (s : ℂ) (hs : s = ω ∨ s = -ω) :
      LinearMap.range (exteriorPower.map m (Module.End.eigenspace A.Jc s).subtype) ≤
        LinearMap.ker (derivationKernelOperator A k) := by
    let Fs := exteriorPower.map m (Module.End.eigenspace A.Jc s).subtype
    have hT := derivationExt_comp_exteriorPower_map_eigenspace A.Jc m s
    intro x hx
    rcases hx with ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    change T (T (Fs y)) + (4 * (k : ℂ) ^ 2 * (d : ℂ)) • Fs y = 0
    have hTy : T (Fs y) = ((m : ℂ) * s) • Fs y := by
      simpa [T, LinearMap.comp_apply] using LinearMap.congr_fun hT y
    rw [hTy, map_smul, hTy, smul_smul, ← add_smul, hscalar s hs, zero_smul]
  apply sup_le
  · change LinearMap.range F ≤ _
    apply hside ω (Or.inl rfl)
  · change LinearMap.range Fbar ≤ _
    apply hside (-ω) (Or.inr rfl)

/-- The two complex eigenspaces of a positive Weil action are complementary. -/
theorem isCompl_Vs_Vsbar {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {M : QHodgeStructure 1 V} {d : ℚ}
    (A : WeilAction M d) (hd : 0 < d) : IsCompl A.Vs A.Vsbar := by
  let ω : ℂ := WeilAction.omegaC d
  have hω2 : ω ^ 2 = -(d : ℂ) := WeilAction.omegaC_sq hd
  have hω : ω ≠ 0 := WeilAction.omegaC_ne_zero hd
  have h2ω : (2 : ℂ) * ω ≠ 0 := mul_ne_zero (by norm_num) hω
  have hJ2 (x : TensorProduct ℚ ℂ V) : A.Jc (A.Jc x) = -(d : ℂ) • x := by
    have h := LinearMap.congr_fun A.Jc_sq x
    simpa [LinearMap.comp_apply] using h
  have hplus (x : TensorProduct ℚ ℂ V) :
      A.Jc (A.Jc x + ω • x) = ω • (A.Jc x + ω • x) := by
    rw [map_add, map_smul, hJ2, smul_add, smul_smul]
    rw [← hω2]
    simp only [pow_two]
    module
  have hminus (x : TensorProduct ℚ ℂ V) :
      A.Jc (ω • x - A.Jc x) = (-ω) • (ω • x - A.Jc x) := by
    rw [map_sub, map_smul, hJ2, smul_sub, smul_smul]
    rw [← hω2]
    simp only [pow_two]
    module
  rw [isCompl_iff]
  constructor
  · rw [disjoint_iff]
    exact A.inf_Vs_Vsbar hd
  · rw [codisjoint_iff]
    apply top_unique
    intro x _
    let u := ((2 : ℂ) * ω)⁻¹ • (A.Jc x + ω • x)
    let v := ((2 : ℂ) * ω)⁻¹ • (ω • x - A.Jc x)
    have hu : u ∈ A.Vs := by
      change u ∈ Module.End.eigenspace A.Jc ω
      rw [Module.End.mem_eigenspace_iff]
      simp only [u, map_smul, hplus, smul_smul]
      rw [mul_comm]
    have hv : v ∈ A.Vsbar := by
      change v ∈ Module.End.eigenspace A.Jc (-ω)
      rw [Module.End.mem_eigenspace_iff]
      simp only [v, map_smul, hminus, smul_smul]
      rw [mul_comm]
    have huv : u + v = x := by
      simp only [u, v, ← smul_add]
      have hi : A.Jc x + ω • x + (ω • x - A.Jc x) = ((2 : ℂ) * ω) • x := by
        module
      rw [hi, inv_smul_smul₀ h2ω]
    rw [← huv]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hu) (Submodule.mem_sup_right hv)

/-- For positive exterior degree, the current rational-generator definition of mixed wedges is
vacuous: a rational vector cannot lie in either non-real weight-one Hodge summand. -/
theorem mixedWedgeSpan_eq_bot {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (M : QHodgeStructure 1 V) (k : ℕ) (hk : 1 ≤ k) :
    mixedWedgeSpan M k = ⊥ := by
  rw [mixedWedgeSpan, Submodule.span_eq_bot]
  rintro w ⟨v, hv1, _hv2, rfl⟩
  let i : Fin k := ⟨0, hk⟩
  have hx := hv1 i
  have hsigma : sigmaQ V (complexify V (v (Fin.castAdd k i))) =
      complexify V (v (Fin.castAdd k i)) := by
    rw [complexify_apply]
    change sigmaQR V (1 ⊗ₜ[ℚ] v (Fin.castAdd k i)) = _
    rw [sigmaQ_tmul]
    norm_num
  have hx' : complexify V (v (Fin.castAdd k i)) ∈ M.H (0, 1) := by
    rw [← M.conj_symm 1 0]
    rw [← hsigma]
    exact Submodule.mem_map_of_mem hx
  have hdis : Disjoint (M.H (1, 0)) (M.H (0, 1)) :=
    M.isInternal.submodule_iSupIndep.pairwiseDisjoint (by norm_num)
  have hcx : complexify V (v (Fin.castAdd k i)) = 0 := by
    have hbot := hdis.le_bot ⟨hx, hx'⟩
    simpa using hbot
  have hvzero : v (Fin.castAdd k i) = 0 := by
    exact complexify_injective (hcx.trans (map_zero (complexify V)).symm)
  exact (exteriorPower.ιMulti ℚ (k + k)).map_coord_zero
    (Fin.castAdd k i) (by simpa using hvzero)

end WeilAction


#print axioms leibnizTerm
#print axioms leibnizTerm_apply
#print axioms derivationMultilinear
#print axioms derivationMultilinear_apply
#print axioms derivationAlternating
#print axioms derivationAlternating_apply
#print axioms derivationExt
#print axioms derivationExt_ιMulti
#print axioms derivationExt_ιMulti_of_eigen
#print axioms derivationExt_comp_exteriorPower_map_eigenspace
#print axioms complexifyWedge_derivationExt
#print axioms complexify_injective
#print axioms WeilAction.derivationKernelOperator
#print axioms WeilAction.sup_le_eigenspace_ker
#print axioms WeilAction.isCompl_Vs_Vsbar
#print axioms WeilAction.mixedWedgeSpan_eq_bot

end HodgeBlocks
