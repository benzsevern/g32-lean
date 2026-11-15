import HodgeLean.Blocks.Weil.KernelIdentity
import Mathlib.RingTheory.Flat.Basic

/-! # Rational form of the Weil kernel identity -/

open scoped TensorProduct

noncomputable section

namespace HodgeBlocks

/-- Extending scalars between fields preserves the dimension of the kernel of a linear map. -/
theorem finrank_ker_baseChange (K L M N : Type*) [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) :
    Module.finrank L ↥(LinearMap.ker (f.baseChange L)) =
      Module.finrank K ↥(LinearMap.ker f) := by
  let i := (LinearMap.ker f).subtype
  have hi : Function.Injective (i.baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap i Subtype.val_injective
  have hexact : Function.Exact (i.baseChange L) (f.baseChange L) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_exact L f.exact_subtype_ker_map)
  have hrange : LinearMap.range (i.baseChange L) = LinearMap.ker (f.baseChange L) :=
    (LinearMap.exact_iff.mp hexact).symm
  rw [← hrange]
  rw [← (LinearEquiv.ofInjective (i.baseChange L) hi).finrank_eq]
  exact Module.finrank_baseChange

set_option maxRecDepth 100000 in
theorem complexifyWedge_injective {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (n : ℕ) : Function.Injective (complexifyWedge (V := V) n) := by
  let b := Module.finBasis ℚ V
  let B := b.exteriorPower n
  let BC := (b.baseChange ℂ).exteriorPower n
  have hmap (s) : complexifyWedge n (B s) = BC s := by
    rw [exteriorPower.basis_apply, exteriorPower.basis_apply]
    unfold exteriorPower.ιMulti_family
    rw [complexifyWedge_ιMulti]
    congr 1
    funext i
    simp [Function.comp_apply, Module.Basis.baseChange_apply]
  intro x y hxy
  apply B.repr.injective
  ext s
  rw [← B.sum_repr x, ← B.sum_repr y, map_sum, map_sum] at hxy
  simp_rw [map_smul, hmap] at hxy
  change (∑ c, ((B.repr x c : ℚ) : ℂ) • BC c) =
    (∑ c, ((B.repr y c : ℚ) : ℂ) • BC c) at hxy
  have h := congrArg (fun z => BC.repr z s) hxy
  have h' : ((B.repr x s : ℚ) : ℂ) = ((B.repr y s : ℚ) : ℂ) := by
    simpa only [map_sum, map_smul, Module.Basis.repr_self,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply,
      Pi.zero_apply, smul_eq_mul, Finsupp.zero_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left] using h
  exact_mod_cast h'

/-- Every zeroth exterior power is one-dimensional. -/
theorem finrank_exteriorPower_zero (K E : Type*) [Field K] [AddCommGroup E]
    [Module K E] [Module.Finite K E] : Module.finrank K (⋀[K]^0 E) = 1 := by
  letI : Unique (Set.powersetCard (Fin (Module.finrank K E)) 0) :=
    { default := ⟨∅, by simp⟩
      uniq s := Subtype.ext (Finset.card_eq_zero.mp s.2) }
  calc
    Module.finrank K (⋀[K]^0 E) =
        Fintype.card (Set.powersetCard (Fin (Module.finrank K E)) 0) :=
      Module.finrank_eq_card_basis ((Module.finBasis K E).exteriorPower 0)
    _ = 1 := Fintype.card_unique

/-- In degree zero the exterior power of any subspace inclusion is onto. -/
theorem range_exteriorPower_map_subtype_zero_eq_top (K E : Type*) [Field K]
    [AddCommGroup E] [Module K E] [Module.Finite K E] (P : Submodule K E) :
    LinearMap.range (exteriorPower.map 0 P.subtype) = ⊤ := by
  rw [LinearMap.range_eq_top]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := exteriorPower.map 0 P.subtype)
    (by rw [finrank_exteriorPower_zero, finrank_exteriorPower_zero])).mp
      (exteriorPower.map_injective_field P.injective_subtype)

/-- The top exterior power of a finite-dimensional vector space is one-dimensional. -/
theorem finrank_topExteriorPower (K E : Type*) [Field K] [AddCommGroup E]
    [Module K E] [Module.Finite K E] :
    Module.finrank K (⋀[K]^(Module.finrank K E) E) = 1 := by
  letI : Unique (Set.powersetCard (Fin (Module.finrank K E)) (Module.finrank K E)) :=
    { default := ⟨Finset.univ, by simp⟩
      uniq s := Subtype.ext (Finset.eq_univ_of_card _ (by simpa using s.2)) }
  calc
    Module.finrank K (⋀[K]^(Module.finrank K E) E) =
        Fintype.card (Set.powersetCard (Fin (Module.finrank K E))
          (Module.finrank K E)) :=
      Module.finrank_eq_card_basis
        ((Module.finBasis K E).exteriorPower (Module.finrank K E))
    _ = 1 := Fintype.card_unique

/-- The image of the top exterior power of a subspace inclusion is a line. -/
theorem finrank_range_exteriorPower_map_subtype_of_finrank
    (K E : Type*) [Field K] [AddCommGroup E] [Module K E] [Module.Finite K E]
    (P : Submodule K E) (n : ℕ) (hn : Module.finrank K P = n) :
    Module.finrank K ↥(LinearMap.range (exteriorPower.map n P.subtype)) = 1 := by
  rw [LinearMap.finrank_range_of_inj
    (exteriorPower.map_injective_field P.injective_subtype)]
  rw [← hn]
  exact finrank_topExteriorPower K P

namespace WeilAction

/-- The canonical basis-matching equivalence from the scalar extension of a rational
exterior power to the exterior power of the scalar extension. -/
def exteriorPowerBaseChangeEquiv {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (n : ℕ) :
    ℂ ⊗[ℚ] (⋀[ℚ]^n V) ≃ₗ[ℂ] ⋀[ℂ]^n (ℂ ⊗[ℚ] V) :=
  let e := Module.finBasis ℚ V
  let B := e.exteriorPower n
  let BC := (e.baseChange ℂ).exteriorPower n
  (B.baseChange ℂ).equiv BC (Equiv.refl _)

set_option maxHeartbeats 1000000 in
-- Elaborating the equality of the two basis-defined linear maps needs additional heartbeats.
/-- The basis-matching base-change equivalence agrees with `complexifyWedge` on rational
vectors. -/
theorem exteriorPowerBaseChangeEquiv_tmul {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (n : ℕ) (w : ⋀[ℚ]^n V) :
    exteriorPowerBaseChangeEquiv n (1 ⊗ₜ[ℚ] w) = complexifyWedge n w := by
  let e := Module.finBasis ℚ V
  let B := e.exteriorPower n
  let BC := (e.baseChange ℂ).exteriorPower n
  have hmap (s) : complexifyWedge n (B s) = BC s := by
    rw [exteriorPower.basis_apply, exteriorPower.basis_apply]
    unfold exteriorPower.ιMulti_family
    rw [complexifyWedge_ιMulti]
    congr 1
    funext i
    simp [Function.comp_apply, Module.Basis.baseChange_apply]
  let F : (⋀[ℚ]^n V) →ₗ[ℚ] ⋀[ℂ]^n (ℂ ⊗[ℚ] V) :=
    (exteriorPowerBaseChangeEquiv n).toLinearMap.restrictScalars ℚ |>.comp
      (TensorProduct.mk ℚ ℂ (⋀[ℚ]^n V) 1)
  have hF : F = complexifyWedge n := by
    apply B.ext
    intro s
    change exteriorPowerBaseChangeEquiv n (1 ⊗ₜ[ℚ] B s) = complexifyWedge n (B s)
    rw [hmap]
    change (B.baseChange ℂ).equiv BC (Equiv.refl _) (1 ⊗ₜ[ℚ] B s) = BC s
    rw [← Module.Basis.baseChange_apply]
    exact (B.baseChange ℂ).equiv_apply s BC (Equiv.refl _)
  exact DFunLike.congr_fun hF w

/-- The rational quadratic exterior-derivation operator whose complexification is
`derivationKernelOperator`. -/
def derivationKernelOperatorQ {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {M : QHodgeStructure 1 V} {d : ℚ}
    (A : WeilAction M d) (k : ℕ) : Module.End ℚ (⋀[ℚ]^(k + k) V) :=
  let T := derivationExt A.J (k + k)
  T.comp T + (4 * (k : ℚ) ^ 2 * d) • LinearMap.id

/-- Complexification intertwines the rational and complex quadratic operators. -/
theorem complexifyWedge_derivationKernelOperatorQ
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d) (k : ℕ)
    (w : ⋀[ℚ]^(k + k) V) :
    complexifyWedge (k + k) (derivationKernelOperatorQ A k w) =
      derivationKernelOperator A k (complexifyWedge (k + k) w) := by
  change complexifyWedge (k + k)
      (derivationExt A.J (k + k) (derivationExt A.J (k + k) w) +
        (4 * (k : ℚ) ^ 2 * d) • w) = _
  rw [map_add, complexifyWedge_derivationExt, complexifyWedge_derivationExt, map_smul]
  change _ = derivationExt A.Jc (k + k)
      (derivationExt A.Jc (k + k) (complexifyWedge (k + k) w)) +
        (4 * (k : ℂ) ^ 2 * (d : ℂ)) • complexifyWedge (k + k) w
  congr 1
  rw [show (4 * (k : ℂ) ^ 2 * (d : ℂ)) =
      algebraMap ℚ ℂ (4 * (k : ℚ) ^ 2 * d) by norm_num]
  exact (IsScalarTower.algebraMap_smul ℚ
    (4 * (k : ℚ) ^ 2 * d) (complexifyWedge (k + k) w)).symm

/-- The canonical exterior-power base-change equivalence conjugates the rational quadratic
operator to its complex counterpart. -/
theorem exteriorPowerBaseChangeEquiv_derivationKernelOperatorQ
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d) (k : ℕ) :
    (exteriorPowerBaseChangeEquiv (V := V) (k + k)).toLinearMap.comp
        ((derivationKernelOperatorQ A k).baseChange ℂ) =
      (derivationKernelOperator A k).comp
        (exteriorPowerBaseChangeEquiv (V := V) (k + k)).toLinearMap := by
  let e := Module.finBasis ℚ V
  let B := e.exteriorPower (k + k)
  apply (B.baseChange ℂ).ext
  intro s
  simp only [LinearMap.coe_comp, Function.comp_apply, Module.Basis.baseChange_apply,
    LinearMap.baseChange_tmul]
  change exteriorPowerBaseChangeEquiv (k + k)
      (1 ⊗ₜ[ℚ] derivationKernelOperatorQ A k (B s)) =
    derivationKernelOperator A k
      (exteriorPowerBaseChangeEquiv (k + k) (1 ⊗ₜ[ℚ] B s))
  rw [exteriorPowerBaseChangeEquiv_tmul,
    exteriorPowerBaseChangeEquiv_tmul,
    complexifyWedge_derivationKernelOperatorQ]

/-- The exterior-power base-change equivalence restricts to the kernels of the conjugate
quadratic operators. -/
def kernelDerivationOperatorBaseChangeEquiv
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d) (k : ℕ) :
    LinearMap.ker ((derivationKernelOperatorQ A k).baseChange ℂ) ≃ₗ[ℂ]
      LinearMap.ker (derivationKernelOperator A k) := by
  let Φ := exteriorPowerBaseChangeEquiv (V := V) (k + k)
  have hconj := exteriorPowerBaseChangeEquiv_derivationKernelOperatorQ A k
  refine
    { toFun := fun x => ⟨Φ x, ?_⟩
      invFun := fun y => ⟨Φ.symm y, ?_⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp }
  · rw [LinearMap.mem_ker]
    have hx := congrArg (fun f => f x.1) hconj
    simpa [Φ, x.2] using hx.symm
  · rw [LinearMap.mem_ker]
    apply Φ.injective
    have hx := congrArg (fun f => f (Φ.symm y)) hconj
    simpa [Φ, y.2] using hx

/-- The rational quadratic kernel and its complex counterpart have the same dimension after
base change. -/
theorem finrank_ker_derivationKernelOperatorQ_baseChange
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d) (k : ℕ) :
    Module.finrank ℂ
        ↥(LinearMap.ker ((derivationKernelOperatorQ A k).baseChange ℂ)) =
      Module.finrank ℂ ↥(LinearMap.ker (derivationKernelOperator A k)) :=
  (kernelDerivationOperatorBaseChangeEquiv A k).finrank_eq

/-- When the middle degree is positive, the two top Weil eigenlines have two-dimensional
sum. -/
theorem finrank_sup_range_exteriorPower_Vs_Vsbar_eq_two
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType)
    (hd : 0 < d) (hκ : 1 ≤ Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) :
    let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
    Module.finrank ℂ ↥(LinearMap.range (exteriorPower.map (k + k) A.Vs.subtype) ⊔
      LinearMap.range (exteriorPower.map (k + k) A.Vsbar.subtype)) = 2 := by
  classical
  dsimp only
  let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  let n := k + k
  let T := derivationExt A.Jc n
  let R := LinearMap.range (exteriorPower.map n A.Vs.subtype)
  let Rbar := LinearMap.range (exteriorPower.map n A.Vsbar.subtype)
  have hVs : Module.finrank ℂ ↥A.Vs = n := by
    simpa [k, n] using A.finrank_Vs_eq_twice_inf_H10 hH hWeil
  have hVsbar : Module.finrank ℂ ↥A.Vsbar = n := by
    rw [A.finrank_Vsbar_eq_Vs, hVs]
  have hR : Module.finrank ℂ R = 1 := by
    exact finrank_range_exteriorPower_map_subtype_of_finrank ℂ (ℂ ⊗[ℚ] V)
      A.Vs n hVs
  have hRbar : Module.finrank ℂ Rbar = 1 := by
    exact finrank_range_exteriorPower_map_subtype_of_finrank ℂ (ℂ ⊗[ℚ] V)
      A.Vsbar n hVsbar
  have hside (s : ℂ) :
      LinearMap.range
          (exteriorPower.map n (Module.End.eigenspace A.Jc s).subtype) ≤
        Module.End.eigenspace T ((n : ℂ) * s) := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    simpa [T, LinearMap.comp_apply] using LinearMap.congr_fun
      (derivationExt_comp_exteriorPower_map_eigenspace A.Jc n s) y
  have hleft : R ≤ Module.End.eigenspace T ((n : ℂ) * omegaC d) := by
    change LinearMap.range
      (exteriorPower.map n (Module.End.eigenspace A.Jc (omegaC d)).subtype) ≤ _
    exact hside (omegaC d)
  have hright : Rbar ≤ Module.End.eigenspace T ((n : ℂ) * (-omegaC d)) := by
    change LinearMap.range
      (exteriorPower.map n (Module.End.eigenspace A.Jc (-omegaC d)).subtype) ≤ _
    exact hside (-omegaC d)
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hω0 : omegaC d ≠ 0 := omegaC_ne_zero hd
  have hne : (n : ℂ) * omegaC d ≠ (n : ℂ) * (-omegaC d) := by
    intro h
    have hz : (2 * (n : ℂ)) * omegaC d = 0 := by linear_combination h
    exact (mul_ne_zero (mul_ne_zero (by norm_num) hn0) hω0) hz
  have heig : Disjoint (Module.End.eigenspace T ((n : ℂ) * omegaC d))
      (Module.End.eigenspace T ((n : ℂ) * (-omegaC d))) := by
    have hi := (Module.End.eigenspaces_iSupIndep T).disjoint_biSup
      (x := (n : ℂ) * omegaC d)
      (y := {((n : ℂ) * (-omegaC d))}) (by simpa using hne)
    simpa using hi
  have hdisj : Disjoint R Rbar := heig.mono hleft hright
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq R Rbar
  rw [hdisj.eq_bot, finrank_bot, hR, hRbar] at hdim
  simpa [R, Rbar, n, k] using hdim

/-- Rational Weil classes are exactly the kernel of the rational quadratic derivation
operator. -/
theorem weilClasses_eq_ker_derivationKernelOperatorQ
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) (hd : 0 < d) :
    A.weilClasses hH hWeil =
      LinearMap.ker (derivationKernelOperatorQ A
        (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))) := by
  let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  let C := complexifyWedge (V := V) (k + k)
  let S := LinearMap.range (exteriorPower.map (k + k) A.Vs.subtype) ⊔
    LinearMap.range (exteriorPower.map (k + k) A.Vsbar.subtype)
  have hker : LinearMap.ker (derivationKernelOperator A k) = S := by
    simpa [k, S] using A.ker_derivationKernelOperator_eq_sup hH hWeil hd
  ext w
  change C w ∈ S.restrictScalars ℚ ↔ derivationKernelOperatorQ A k w = 0
  change C w ∈ S ↔ _
  rw [← hker, LinearMap.mem_ker, ← A.complexifyWedge_derivationKernelOperatorQ k w]
  constructor
  · intro hw
    apply complexifyWedge_injective (k + k)
    simpa using hw
  · intro hw
    simp [hw]

/-- For a positive-dimensional Weil factor, the rational Weil-class space is exactly
two-dimensional. -/
theorem finrank_weilClasses_eq_two {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) (hd : 0 < d)
    (hκ : 1 ≤ Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) :
    Module.finrank ℚ ↥(A.weilClasses hH hWeil) = 2 := by
  let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  rw [A.weilClasses_eq_ker_derivationKernelOperatorQ hH hWeil hd]
  rw [← finrank_ker_baseChange ℚ ℂ (⋀[ℚ]^(k + k) V) (⋀[ℚ]^(k + k) V)
    (derivationKernelOperatorQ A k)]
  rw [A.finrank_ker_derivationKernelOperatorQ_baseChange k]
  rw [A.ker_derivationKernelOperator_eq_sup hH hWeil hd]
  exact A.finrank_sup_range_exteriorPower_Vs_Vsbar_eq_two hH hWeil hd hκ

end WeilAction

#print axioms complexifyWedge_injective
#print axioms finrank_ker_baseChange
#print axioms finrank_exteriorPower_zero
#print axioms range_exteriorPower_map_subtype_zero_eq_top
#print axioms finrank_topExteriorPower
#print axioms finrank_range_exteriorPower_map_subtype_of_finrank
#print axioms WeilAction.exteriorPowerBaseChangeEquiv
#print axioms WeilAction.exteriorPowerBaseChangeEquiv_tmul
#print axioms WeilAction.derivationKernelOperatorQ
#print axioms WeilAction.complexifyWedge_derivationKernelOperatorQ
#print axioms WeilAction.exteriorPowerBaseChangeEquiv_derivationKernelOperatorQ
#print axioms WeilAction.kernelDerivationOperatorBaseChangeEquiv
#print axioms WeilAction.finrank_ker_derivationKernelOperatorQ_baseChange
#print axioms WeilAction.finrank_sup_range_exteriorPower_Vs_Vsbar_eq_two
#print axioms WeilAction.weilClasses_eq_ker_derivationKernelOperatorQ
#print axioms WeilAction.finrank_weilClasses_eq_two

end HodgeBlocks
