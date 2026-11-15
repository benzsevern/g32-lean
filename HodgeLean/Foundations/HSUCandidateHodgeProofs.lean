import HodgeLean.Foundations.HSUCandidateHodgeDefs

/-! # Proofs for the stage-3 `hSU` specification (the explicit structure's Hodge tensors)

All eighteen `_aux` theorems are proved, by three parallel provers (statements 1-4, 5-13 and
14-18). -/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HodgeLean.Foundations.SchurWeyl.dualAddCommGroup

namespace HodgeLean.Foundations

open WeilPower SchurWeyl
open scoped TensorProduct

section General

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)} {hH : DirectSum.IsInternal H}

private theorem hsuA_mem_iInf {W : Type*} [AddCommGroup W] [Module ℚ W] {κ : Type*}
    {L : κ → LieSubalgebra ℚ (Module.End ℚ W)} {X : Module.End ℚ W} :
    X ∈ ⨅ i, L i ↔ ∀ i, X ∈ L i := by
  rw [iInf, ← SetLike.mem_coe, LieSubalgebra.coe_sInf]
  simp

theorem spec_hodge_iff_gradingOperator_mem_mixedTensorStabilizer_aux {n : ℕ}
    (t : Fin n → BoundedTensor V) :
    (∀ i, (t i).2 ∈
      LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) (MixedTensorOfType V (t i).1)) ↔
      gradingOperator H hH ∈ mixedTensorStabilizer t := by
  constructor
  · intro ht
    exact spec_hodgeLieAlgebra_le_mixedTensorStabilizer t ht
      (gradingOperator_mem_span_hodgeLieAlgebra H hH)
  · intro hC i
    have hle : hodgeLieAlgebra H hH ≤ ⨅ i, lieAnnihilator (MixedTensorOfType V (t i).1) (t i).2 :=
      hodgeLieAlgebra_le H hH hC
    rw [LieModule.mem_maxTrivSubmodule]
    intro X
    have hX : (X : Module.End ℚ V) ∈ lieAnnihilator (MixedTensorOfType V (t i).1) (t i).2 :=
      hsuA_mem_iInf.mp (hle X.2) i
    rw [LieSubalgebra.coe_bracket_of_module]
    exact mem_lieAnnihilator _ |>.mp hX

end General

section WeilTensor

section Hsu3LaneC

open PiTensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- `v ↦ v` in `⨂[ℚ] _ : Fin 1, V`, as a linear map. -/
private abbrev hsu3S1 {M : Type*} [AddCommGroup M] [Module ℚ M] : M →ₗ[ℚ] ⨂[ℚ] _ : Fin 1, M :=
  (PiTensorProduct.subsingletonEquiv (R := ℚ) (s := fun _ : Fin 1 => M) 0).symm.toLinearMap

private theorem hsu3S1_apply {M : Type*} [AddCommGroup M] [Module ℚ M] (v : M) :
    hsu3S1 v = tprod ℚ (fun _ : Fin 1 => v) := by
  simp only [hsu3S1, LinearEquiv.coe_coe, subsingletonEquiv_symm_apply]
  congr 1
  funext i
  fin_cases i
  simp

/-- The bilinear map `(v, φ) ↦ v ⊗ φ` into `T^{1,1}(V)`. -/
private abbrev hsu3Beta : V →ₗ[ℚ] Module.Dual ℚ V →ₗ[ℚ] MixedTensorOfType V (1, 1) :=
  (TensorProduct.mk ℚ _ _).compl₁₂ hsu3S1 hsu3S1

private theorem hsu3Beta_apply (v : V) (φ : Module.Dual ℚ V) :
    hsu3Beta v φ = tprod ℚ (fun _ : Fin 1 => v) ⊗ₜ tprod ℚ (fun _ : Fin 1 => φ) := by
  simp [hsu3Beta, hsu3S1_apply]

private theorem hsu3_lie_beta (X : Module.End ℚ V) (v : V) (φ : Module.Dual ℚ V) :
    ⁅X, hsu3Beta v φ⁆ = hsu3Beta (X v) φ - hsu3Beta v (φ ∘ₗ X) := by
  rw [hsu3Beta_apply, hsu3Beta_apply, hsu3Beta_apply]
  change mixedLie ℚ V (Fin 1) (Fin 1) X _ = _
  rw [mixedLie_apply]
  simp [tensorDer_tprod, Function.update_eq_const_of_subsingleton]
  rfl

variable {ι : Type*} [Fintype ι]

private theorem hsu3EndTensor_eq (b : Module.Basis ι ℚ V) (A : Module.End ℚ V) :
    endTensor b A = ∑ j, hsu3Beta (A (b j)) (b.coord j) := by
  simp [endTensor]

private theorem hsu3_sum_beta_comp (b : Module.Basis ι ℚ V) (T X : Module.End ℚ V) :
    ∑ j, hsu3Beta (T (b j)) (b.coord j ∘ₗ X) = ∑ j, hsu3Beta (T (X (b j))) (b.coord j) := by
  have h (j : ι) : b.coord j ∘ₗ X = ∑ k, b.coord j (X (b k)) • b.coord k := by
    exact (b.sum_dual_apply_smul_coord _).symm
  simp_rw [h, map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← b.sum_repr (X (b k))]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply]

private theorem hsu3_lie_endTensor (b : Module.Basis ι ℚ V) (X A : Module.End ℚ V) :
    ⁅X, endTensor b A⁆ = endTensor b (X * A - A * X) := by
  rw [hsu3EndTensor_eq, hsu3EndTensor_eq, lie_sum]
  simp_rw [hsu3_lie_beta]
  rw [Finset.sum_sub_distrib, hsu3_sum_beta_comp]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, LinearMap.sub_apply,
    Finset.sum_sub_distrib]

private theorem hsu3_endTensor_eq_zero (b : Module.Basis ι ℚ V) (A : Module.End ℚ V)
    (h : endTensor b A = 0) : A = 0 := by
  classical
  let ev : ι → ι → MixedTensorOfType V (1, 1) →ₗ[ℚ] ℚ := fun k l =>
    TensorProduct.lift ((LinearMap.mul ℚ ℚ).compl₁₂
      (b.coord k ∘ₗ (PiTensorProduct.subsingletonEquiv (R := ℚ) (s := fun _ : Fin 1 => V) 0).toLinearMap)
      ((LinearMap.applyₗ (b l)) ∘ₗ
        (PiTensorProduct.subsingletonEquiv (R := ℚ) (s := fun _ : Fin 1 => Module.Dual ℚ V) 0).toLinearMap))
  have hev (k l : ι) (v : V) (φ : Module.Dual ℚ V) : ev k l (hsu3Beta v φ) = b.coord k v * φ (b l) := by
    simp [ev, hsu3Beta]
  have hA (k l : ι) : b.coord k (A (b l)) = 0 := by
    have := congrArg (ev k l) h
    rw [hsu3EndTensor_eq, map_sum, map_zero] at this
    simp_rw [hev, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] at this
    simpa using this
  apply b.ext
  intro l
  apply b.ext_elem
  intro k
  simpa using hA k l

private theorem hsu3_update_vec2_zero {M : Type*} (a b c : M) :
    Function.update ![a, b] 0 c = ![c, b] := by
  funext i; fin_cases i <;> rfl

private theorem hsu3_update_vec2_one {M : Type*} (a b c : M) :
    Function.update ![a, b] 1 c = ![a, c] := by
  funext i; fin_cases i <;> rfl

/-- The bilinear map `(φ, ψ) ↦ 1 ⊗ φ ⊗ ψ` into `T^{0,2}(V)`. -/
private def hsu3Gamma : Module.Dual ℚ V →ₗ[ℚ] Module.Dual ℚ V →ₗ[ℚ] MixedTensorOfType V (0, 2) :=
  LinearMap.mk₂ ℚ (fun φ ψ => tprod ℚ (fun k : Fin 0 => k.elim0) ⊗ₜ tprod ℚ ![φ, ψ])
    (fun φ φ' ψ => by
      rw [← TensorProduct.tmul_add]; congr 1
      have := (PiTensorProduct.tprod ℚ).map_update_add ![0, ψ] 0 φ φ'
      simpa only [hsu3_update_vec2_zero] using this)
    (fun c φ ψ => by
      rw [← TensorProduct.tmul_smul]; congr 1
      have := (PiTensorProduct.tprod ℚ).map_update_smul ![0, ψ] 0 c φ
      simpa only [hsu3_update_vec2_zero] using this)
    (fun φ ψ ψ' => by
      rw [← TensorProduct.tmul_add]; congr 1
      have := (PiTensorProduct.tprod ℚ).map_update_add ![φ, 0] 1 ψ ψ'
      simpa only [hsu3_update_vec2_one] using this)
    (fun c φ ψ => by
      rw [← TensorProduct.tmul_smul]; congr 1
      have := (PiTensorProduct.tprod ℚ).map_update_smul ![φ, 0] 1 c ψ
      simpa only [hsu3_update_vec2_one] using this)

private theorem hsu3Gamma_apply (φ ψ : Module.Dual ℚ V) :
    hsu3Gamma φ ψ = tprod ℚ (fun k : Fin 0 => k.elim0) ⊗ₜ tprod ℚ ![φ, ψ] := rfl

private theorem hsu3_lie_gamma (X : Module.End ℚ V) (φ ψ : Module.Dual ℚ V) :
    ⁅X, hsu3Gamma φ ψ⁆ = -(hsu3Gamma (φ ∘ₗ X) ψ + hsu3Gamma φ (ψ ∘ₗ X)) := by
  rw [hsu3Gamma_apply, hsu3Gamma_apply, hsu3Gamma_apply]
  change mixedLie ℚ V (Fin 0) (Fin 2) X _ = _
  rw [mixedLie_apply]
  simp only [tensorDer_apply, Finset.univ_eq_empty, Finset.sum_empty, LinearMap.rTensor_zero,
    LinearMap.zero_apply, zero_sub, LinearMap.lTensor_tmul, Fin.sum_univ_two,
    LinearMap.add_apply, slot_tprod, hsu3_update_vec2_zero, hsu3_update_vec2_one,
    TensorProduct.tmul_add, Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.dualMap_apply']

private theorem hsu3FormTensor_eq (b : Module.Basis ι ℚ V) (F : LinearMap.BilinForm ℚ V) :
    formTensor b F = ∑ i, ∑ j, F (b i) (b j) • hsu3Gamma (b.coord i) (b.coord j) := rfl

private theorem hsu3_sum_gamma_left (b : Module.Basis ι ℚ V) (F : LinearMap.BilinForm ℚ V)
    (X : Module.End ℚ V) :
    ∑ i, ∑ j, F (b i) (b j) • hsu3Gamma (b.coord i ∘ₗ X) (b.coord j) =
      ∑ i, ∑ j, F (X (b i)) (b j) • hsu3Gamma (b.coord i) (b.coord j) := by
  have h (j : ι) : b.coord j ∘ₗ X = ∑ k, b.coord j (X (b k)) • b.coord k :=
    (b.sum_dual_apply_smul_coord _).symm
  have h' (k : ι) (y : V) : F (X (b k)) y = ∑ i, b.coord i (X (b k)) * F (b i) y := by
    have := congrArg (fun x => F x y) (b.sum_repr (X (b k)))
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at this
    simpa only [Module.Basis.coord_apply] using this.symm
  simp_rw [h, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul]
  simp_rw [h', Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [mul_comm]

private theorem hsu3_sum_gamma_right (b : Module.Basis ι ℚ V) (F : LinearMap.BilinForm ℚ V)
    (X : Module.End ℚ V) :
    ∑ i, ∑ j, F (b i) (b j) • hsu3Gamma (b.coord i) (b.coord j ∘ₗ X) =
      ∑ i, ∑ j, F (b i) (X (b j)) • hsu3Gamma (b.coord i) (b.coord j) := by
  have h (j : ι) : b.coord j ∘ₗ X = ∑ k, b.coord j (X (b k)) • b.coord k :=
    (b.sum_dual_apply_smul_coord _).symm
  have h' (k : ι) (y : V) : F y (X (b k)) = ∑ i, b.coord i (X (b k)) * F y (b i) := by
    have := congrArg (fun x => F y x) (b.sum_repr (X (b k)))
    simp only [map_sum, map_smul, smul_eq_mul] at this
    simpa only [Module.Basis.coord_apply] using this.symm
  simp_rw [h, map_sum, map_smul, Finset.smul_sum, smul_smul]
  simp_rw [h', Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_comm]

private theorem hsu3_lie_formTensor (b : Module.Basis ι ℚ V) (F : LinearMap.BilinForm ℚ V)
    (X : Module.End ℚ V) :
    ⁅X, formTensor b F⁆ =
      -formTensor b (F.compl₁₂ X LinearMap.id + F.compl₁₂ LinearMap.id X) := by
  rw [hsu3FormTensor_eq, hsu3FormTensor_eq, lie_sum]
  have hg (φ ψ : Module.Dual ℚ V) := hsu3_lie_gamma X φ ψ
  simp_rw [lie_mixedTensor] at hg
  simp_rw [lie_sum, lie_mixedTensor, map_smul, hg, smul_neg, smul_add, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, hsu3_sum_gamma_left, hsu3_sum_gamma_right]
  simp [add_smul, Finset.sum_add_distrib]

private theorem hsu3_formTensor_apply_eq_zero (b : Module.Basis ι ℚ V)
    (F : LinearMap.BilinForm ℚ V) (h : formTensor b F = 0) (k l : ι) : F (b k) (b l) = 0 := by
  classical
  let ev : MixedTensorOfType V (0, 2) →ₗ[ℚ] ℚ :=
    LinearMap.applyₗ (PiTensorProduct.tprod ℚ ![b k, b l]) ∘ₗ PiTensorProduct.dualDistrib ∘ₗ
      (TensorProduct.lid ℚ _).toLinearMap ∘ₗ
      (PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℚ) (s := fun _ => V)).toLinearMap.rTensor _
  have hev (φ ψ : Module.Dual ℚ V) : ev (hsu3Gamma φ ψ) = φ (b k) * ψ (b l) := by
    simp only [ev, hsu3Gamma_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.rTensor_tmul, LinearEquiv.coe_coe, PiTensorProduct.isEmptyEquiv_apply_tprod,
      TensorProduct.lid_tmul, one_smul, LinearMap.applyₗ_apply_apply]
    rw [PiTensorProduct.dualDistrib_apply]
    simp [Fin.prod_univ_two]
  have := congrArg ev h
  rw [hsu3FormTensor_eq, map_zero] at this
  simp only [map_sum, map_smul, hev, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at this
  simpa using this

private theorem hsu3_mem_lieAnnihilator_endTensor (b : Module.Basis ι ℚ V) (A X : Module.End ℚ V) :
    X ∈ lieAnnihilator (MixedTensorOfType V (1, 1)) (endTensor b A) ↔ X * A = A * X := by
  rw [mem_lieAnnihilator, hsu3_lie_endTensor]
  constructor
  · intro h; exact sub_eq_zero.mp (hsu3_endTensor_eq_zero b _ h)
  · intro h; rw [h, sub_self, hsu3EndTensor_eq]; simp

private theorem hsu3_mem_lieAnnihilator_formTensor (b : Module.Basis ι ℚ V)
    (F : LinearMap.BilinForm ℚ V) (X : Module.End ℚ V) :
    X ∈ lieAnnihilator (MixedTensorOfType V (0, 2)) (formTensor b F) ↔
      ∀ k l, F (X (b k)) (b l) + F (b k) (X (b l)) = 0 := by
  rw [mem_lieAnnihilator, hsu3_lie_formTensor, neg_eq_zero]
  constructor
  · intro h k l
    simpa using hsu3_formTensor_apply_eq_zero b _ h k l
  · intro h
    have : F.compl₁₂ X LinearMap.id + F.compl₁₂ LinearMap.id X = 0 :=
      LinearMap.ext_basis b b fun k l => by simpa using h k l
    rw [this]; simp [formTensor]

/-- The complexification of a kernel, computed by a complex map compatible with the rational one
through an injective comparison map. -/
private theorem hsu3_complexSpan_ker [FiniteDimensional ℚ V] {M M' : Type*} [AddCommGroup M]
    [Module ℚ M] [AddCommGroup M'] [Module ℂ M'] (f : Module.End ℚ V →ₗ[ℚ] M)
    (g : Module.End ℂ (ℂ ⊗[ℚ] V) →ₗ[ℂ] M') (ψ : ℂ ⊗[ℚ] M →ₗ[ℂ] M') (hψ : Function.Injective ψ)
    (h : ∀ X, g (X.baseChange ℂ) = ψ (1 ⊗ₜ f X)) :
    complexSpan (LinearMap.ker f) = LinearMap.ker g := by
  have key : ∀ y, ψ (f.baseChange ℂ y) = g (endBaseChangeEquiv V y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul z X =>
      rw [LinearMap.baseChange_tmul, endBaseChangeEquiv_apply, tensorProductEnd_tmul, map_smul, h,
        ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  ext c
  rw [mem_complexSpan_iff, ← ker_baseChange_eq, LinearMap.mem_ker, LinearMap.mem_ker,
    ← hψ.eq_iff, map_zero, key, LinearEquiv.apply_symm_apply]

end Hsu3LaneC

section Hsu3Candidate

private abbrev hsu3B : Module.Basis (Fin 12) ℚ (Fin 12 → ℚ) := Pi.basisFun ℚ (Fin 12)

/-- The commutant of `J_ℂ`. -/
private def hsu3CommC : Submodule ℂ (Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))) :=
  LinearMap.ker (LinearMap.mulRight ℂ (hsuJ.baseChange ℂ) - LinearMap.mulLeft ℂ (hsuJ.baseChange ℂ))

private theorem mem_hsu3CommC (c : Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))) :
    c ∈ hsu3CommC ↔ c.comp (hsuJ.baseChange ℂ) = (hsuJ.baseChange ℂ).comp c := by
  simp [hsu3CommC, sub_eq_zero, Module.End.mul_eq_comp]

/-- The skewness defect of `c` for `E_ℂ` on the basis `1 ⊗ eᵢ`. -/
private def hsu3SkewMap :
    Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ)) →ₗ[ℂ] (Fin 12 × Fin 12 → ℂ) where
  toFun c p := hsuE.baseChange ℂ (c (1 ⊗ₜ hsu3B p.1)) (1 ⊗ₜ hsu3B p.2) +
    hsuE.baseChange ℂ (1 ⊗ₜ hsu3B p.1) (c (1 ⊗ₜ hsu3B p.2))
  map_add' c d := by funext p; simp only [LinearMap.add_apply, map_add, Pi.add_apply]; ring
  map_smul' z c := by
    funext p; simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

private def hsu3SkewC : Submodule ℂ (Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))) :=
  LinearMap.ker hsu3SkewMap

private theorem mem_hsu3SkewC (c : Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))) :
    c ∈ hsu3SkewC ↔ ∀ x y, hsuE.baseChange ℂ (c x) y = -hsuE.baseChange ℂ x (c y) := by
  rw [hsu3SkewC, LinearMap.mem_ker]
  constructor
  · intro h
    have hB : (hsuE.baseChange ℂ).compl₁₂ c LinearMap.id +
        (hsuE.baseChange ℂ).compl₁₂ LinearMap.id c = 0 := by
      refine LinearMap.ext_basis (Algebra.TensorProduct.basis ℂ hsu3B)
        (Algebra.TensorProduct.basis ℂ hsu3B) fun k l => ?_
      have := congrFun h (k, l)
      simpa [Algebra.TensorProduct.basis_apply, hsu3SkewMap] using this
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply,
      LinearMap.zero_apply] at this
    exact eq_neg_of_add_eq_zero_left this
  · intro h
    funext p
    simp [hsu3SkewMap, h]

/-- The rational skewness defect on the standard basis. -/
private def hsu3SkewMapQ : Module.End ℚ (Fin 12 → ℚ) →ₗ[ℚ] (Fin 12 × Fin 12 → ℚ) where
  toFun X p := hsuE (X (hsu3B p.1)) (hsu3B p.2) + hsuE (hsu3B p.1) (X (hsu3B p.2))
  map_add' X Y := by funext p; simp only [LinearMap.add_apply, map_add, Pi.add_apply]; ring
  map_smul' z X := by
    funext p; simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

private theorem hsu3_annJ :
    (lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (1, 1)) hsuJTensor).toSubmodule =
      LinearMap.ker (LinearMap.mulRight ℚ hsuJ - LinearMap.mulLeft ℚ hsuJ) := by
  ext X
  rw [LieSubalgebra.mem_toSubmodule, hsuJTensor, hsu3_mem_lieAnnihilator_endTensor]
  simp [sub_eq_zero]

private theorem hsu3_annE :
    (lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (0, 2)) hsuETensor).toSubmodule =
      LinearMap.ker hsu3SkewMapQ := by
  ext X
  rw [LieSubalgebra.mem_toSubmodule, hsuETensor, hsu3_mem_lieAnnihilator_formTensor,
    LinearMap.mem_ker]
  constructor
  · intro h; funext p; exact h p.1 p.2
  · intro h k l; exact congrFun h (k, l)

private theorem hsu3_complexSpan_annJ :
    complexSpan (lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (1, 1)) hsuJTensor).toSubmodule =
      hsu3CommC := by
  rw [hsu3_annJ, hsu3CommC]
  refine hsu3_complexSpan_ker _ _ (endBaseChangeEquiv (Fin 12 → ℚ)).toLinearMap
    (endBaseChangeEquiv (Fin 12 → ℚ)).injective fun X => ?_
  simp only [LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
    LinearEquiv.coe_coe, endBaseChangeEquiv_apply, tensorProductEnd_one_tmul,
    LinearMap.baseChange_sub, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

private theorem hsu3_complexSpan_annE :
    complexSpan (lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (0, 2)) hsuETensor).toSubmodule =
      hsu3SkewC := by
  rw [hsu3_annE, hsu3SkewC]
  refine hsu3_complexSpan_ker _ _ (TensorProduct.piScalarRight ℚ ℂ ℂ (Fin 12 × Fin 12)).toLinearMap
    (TensorProduct.piScalarRight ℚ ℂ ℂ (Fin 12 × Fin 12)).injective fun X => ?_
  funext p
  simp [hsu3SkewMap, hsu3SkewMapQ, TensorProduct.piScalarRightHom_tmul,
    LinearMap.BilinForm.baseChange_tmul, add_smul]

private theorem hsu3_mem_iInf {κ : Type*} (L : κ → LieSubalgebra ℚ (Module.End ℚ (Fin 12 → ℚ)))
    (X : Module.End ℚ (Fin 12 → ℚ)) : X ∈ ⨅ i, L i ↔ ∀ i, X ∈ L i := by
  rw [iInf, ← SetLike.mem_coe, LieSubalgebra.coe_sInf]
  simp


private abbrev hsu3W := Module.End.eigenspace (hsuJ.baseChange ℂ) root

private abbrev hsu3Split := polarizedSplitting hsuE spec_hsuE_nondegenerate_aux hsuJ
  spec_hsuJ_sq_aux spec_hsuE_skew_aux

private theorem hsu3Split_conj_apply (c : Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ)))
    (x : ℂ ⊗[ℚ] (Fin 12 → ℚ)) : hsu3Split.conj c (hsu3Split x) = hsu3Split (c x) := by
  simp [LinearEquiv.conj_apply]

private theorem hsu3Split_conj_J : hsu3Split.conj (hsuJ.baseChange ℂ) = splitJ hsu3W := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := hsu3Split.surjective z
  rw [hsu3Split_conj_apply]
  exact polarizedSplitting_J _ _ _ _ _ x

private theorem hsu3Split_form (z t : ℂ ⊗[ℚ] (Fin 12 → ℚ)) :
    hsuE.baseChange ℂ z t = splitForm hsu3W (hsu3Split z) (hsu3Split t) :=
  polarizedSplitting_form _ _ _ _ _ spec_hsuE_isAlt_aux z t


end Hsu3Candidate

section Hsu3WeilEval

open PiTensorProduct


variable {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}

/-- Evaluation of a `(0, n)` tensor on an `n`-tuple of vectors. -/
private def hsu3Ev (v : Fin n → V) : MixedTensorOfType V (0, n) →ₗ[ℚ] ℚ :=
  LinearMap.applyₗ (tprod ℚ v) ∘ₗ PiTensorProduct.dualDistrib ∘ₗ
    (TensorProduct.lid ℚ _).toLinearMap ∘ₗ
    (PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℚ) (s := fun _ => V)).toLinearMap.rTensor _

private theorem hsu3Ev_tprod (v : Fin n → V) (φ : Fin n → Module.Dual ℚ V) :
    hsu3Ev v (tprod ℚ (fun k : Fin 0 => k.elim0) ⊗ₜ tprod ℚ φ) = ∏ i, φ i (v i) := by
  simp only [hsu3Ev, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.rTensor_tmul, LinearEquiv.coe_coe, PiTensorProduct.isEmptyEquiv_apply_tprod,
    TensorProduct.lid_tmul, one_smul, LinearMap.applyₗ_apply_apply]
  rw [PiTensorProduct.dualDistrib_apply]

private theorem hsu3_ext0 {N : Type*} [AddCommGroup N] [Module ℚ N]
    {f g : MixedTensorOfType V (0, n) →ₗ[ℚ] N}
    (h : ∀ φ : Fin n → Module.Dual ℚ V,
      f (tprod ℚ (fun k : Fin 0 => k.elim0) ⊗ₜ tprod ℚ φ) =
        g (tprod ℚ (fun k : Fin 0 => k.elim0) ⊗ₜ tprod ℚ φ)) : f = g := by
  apply TensorProduct.ext'
  intro x y
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    have ha : a = fun k : Fin 0 => k.elim0 := funext fun k => k.elim0
    subst ha
    rw [← TensorProduct.smul_tmul', map_smul, map_smul]
    congr 1
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      rw [TensorProduct.tmul_smul, map_smul, map_smul, h]
    | add y y' hy hy' => rw [TensorProduct.tmul_add, map_add, map_add, hy, hy']
  | add x x' hx hx' => rw [TensorProduct.add_tmul, map_add, map_add, hx, hx']

private theorem hsu3Ev_lie (X : Module.End ℚ V) (v : Fin n → V) (T : MixedTensorOfType V (0, n)) :
    hsu3Ev v ⁅X, T⁆ = -∑ i, hsu3Ev (Function.update v i (X (v i))) T := by
  have key : (hsu3Ev v) ∘ₗ (mixedLie ℚ V (Fin 0) (Fin n) X) =
      -∑ i, hsu3Ev (Function.update v i (X (v i))) := by
    refine hsu3_ext0 fun φ => ?_
    rw [LinearMap.comp_apply, mixedLie_apply]
    simp only [tensorDer_apply, Finset.univ_eq_empty, Finset.sum_empty, LinearMap.rTensor_zero,
      LinearMap.zero_apply, zero_sub, LinearMap.lTensor_tmul, LinearMap.sum_apply, slot_tprod,
      TensorProduct.tmul_sum, map_neg, map_sum, LinearMap.neg_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsu3Ev_tprod, hsu3Ev_tprod]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp [LinearMap.dualMap_apply']
    · simp [Function.update_of_ne hj]
  have := LinearMap.congr_fun key T
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.sum_apply] at this
  exact this

private theorem hsu3Ev_injective [FiniteDimensional ℚ V] (T : MixedTensorOfType V (0, n))
    (h : ∀ v, hsu3Ev v T = 0) : T = 0 := by
  let e₁ := (PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℚ) (s := fun _ => V)).rTensor
    (⨂[ℚ] _ : Fin n, Module.Dual ℚ V)
  let e₂ := TensorProduct.lid ℚ (⨂[ℚ] _ : Fin n, Module.Dual ℚ V)
  let e₃ := PiTensorProduct.dualDistribEquiv (R := ℚ) (ι := Fin n) (M := fun _ => V)
  have h3 : e₃ (e₂ (e₁ T)) = 0 := by
    change PiTensorProduct.dualDistrib (e₂ (e₁ T)) = 0
    apply PiTensorProduct.ext
    ext v
    exact h v
  simpa using h3

end Hsu3WeilEval

section Hsu3WeilCoords

open Matrix PiTensorProduct

private theorem hsu3_sum_det_updateCol (Z M : Matrix (Fin 6) (Fin 6) ℂ) :
    ∑ i, (Z.updateCol i (M *ᵥ fun k => Z k i)).det = M.trace * Z.det := by
  have h (i : Fin 6) : (Z.updateCol i (M *ᵥ fun k => Z k i)).det = (Z.adjugate * M * Z) i i := by
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  simp_rw [h]
  change (Z.adjugate * M * Z).trace = _
  rw [Matrix.trace_mul_cycle, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, smul_eq_mul, mul_comm]

private theorem hsu3_card_eq_sum (s : Fin 6 → Fin 2) :
    (Finset.univ.filter fun i => s i = 1).card = ∑ i, (s i).val := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Fin.exists_fin_two.mp ⟨s i, rfl⟩ with h | h <;> rw [h] <;> rfl

private theorem hsu3_re_root_pow (m : ℕ) :
    (root ^ m).re = if Even m then ((-3 : ℚ) ^ (m / 2) : ℚ) else 0 := by
  have hm : root ^ m = ((-3 : ℝ) ^ (m / 2) : ℝ) * root ^ (m % 2) := by
    conv_lhs => rw [← Nat.div_add_mod m 2, pow_add, pow_mul, root_sq]
    push_cast; ring
  rw [hm]
  split_ifs with he
  · rw [Nat.even_iff.mp he, pow_zero, mul_one, Complex.ofReal_re]
    push_cast; ring
  · rw [Nat.odd_iff.mp (Nat.not_even_iff_odd.mp he), pow_one, Complex.re_ofReal_mul]
    simp [root]

private theorem hsu3_re_prod (c : Fin 6 → Fin 2 → ℚ) :
    (∏ i, ((c i 0 : ℂ) + root * (c i 1 : ℂ))).re =
      ∑ s : Fin 6 → Fin 2, (hsuWeilCoeff s : ℝ) * ((∏ i, c i (s i) : ℚ) : ℝ) := by
  have h1 : ∏ i, ((c i 0 : ℂ) + root * (c i 1 : ℂ)) =
      ∏ i, ∑ t : Fin 2, root ^ t.val * (c i t : ℂ) := by
    simp [Fin.sum_univ_two]
  rw [h1, Finset.prod_univ_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← hsu3_card_eq_sum]
  have : (∏ i, (c i (s i) : ℂ)) = (((∏ i, c i (s i) : ℚ) : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_mul_ofReal, hsu3_re_root_pow, hsuWeilCoeff]

private def hsu3I0 (k : Fin 6) : Fin 12 := ⟨2 * k.val, by omega⟩
private def hsu3I1 (k : Fin 6) : Fin 12 := ⟨2 * k.val + 1, by omega⟩

private theorem hsu3I0_inj {k l : Fin 6} : hsu3I0 k = hsu3I0 l ↔ k = l := by
  simp only [hsu3I0, Fin.ext_iff]; omega

private theorem hsu3I1_inj {k l : Fin 6} : hsu3I1 k = hsu3I1 l ↔ k = l := by
  simp only [hsu3I1, Fin.ext_iff]; omega

private theorem hsu3I1_ne_I0 (k l : Fin 6) : hsu3I1 k ≠ hsu3I0 l := by
  simp only [hsu3I0, hsu3I1, ne_eq, Fin.ext_iff]; omega

private theorem hsu3_cases (j : Fin 12) : ∃ k : Fin 6, j = hsu3I0 k ∨ j = hsu3I1 k :=
  ⟨⟨j.val / 2, by omega⟩, by
    rcases Nat.mod_two_eq_zero_or_one j.val with h | h
    · left; ext; simp [hsu3I0]; omega
    · right; ext; simp [hsu3I1]; omega⟩

/-- The `K`-coordinates `z_k = x₂ₖ + √-3 x₂ₖ₊₁`. -/
private def hsu3Z : (Fin 12 → ℚ) →ₗ[ℚ] (Fin 6 → ℂ) where
  toFun v k := (v (hsu3I0 k) : ℂ) + root * (v (hsu3I1 k) : ℂ)
  map_add' v w := by funext k; simp only [Pi.add_apply, Rat.cast_add]; ring
  map_smul' c v := by
    funext k; simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, RingHom.id_apply,
      Rat.smul_def]; ring

private theorem hsu3Z_apply (v : Fin 12 → ℚ) (k : Fin 6) :
    hsu3Z v k = (v (hsu3I0 k) : ℂ) + root * (v (hsu3I1 k) : ℂ) := rfl

private theorem hsu3J_I0 (v : Fin 12 → ℚ) (k : Fin 6) : hsuJ v (hsu3I0 k) = -3 * v (hsu3I1 k) := by
  rw [hsuJ_apply]; fin_cases k <;> rfl

private theorem hsu3J_I1 (v : Fin 12 → ℚ) (k : Fin 6) : hsuJ v (hsu3I1 k) = v (hsu3I0 k) := by
  rw [hsuJ_apply]; fin_cases k <;> rfl

private theorem hsu3Z_J (v : Fin 12 → ℚ) : hsu3Z (hsuJ v) = root • hsu3Z v := by
  funext k
  rw [hsu3Z_apply, hsu3J_I0, hsu3J_I1, Pi.smul_apply, hsu3Z_apply, smul_eq_mul]
  push_cast
  linear_combination -(v (hsu3I1 k) : ℂ) * root_sq

private theorem hsu3_sum12 {R : Type*} [AddCommMonoid R] (f : Fin 12 → R) :
    ∑ j, f j = ∑ k : Fin 6, (f (hsu3I0 k) + f (hsu3I1 k)) := by
  rw [← (finProdFinEquiv : Fin 6 × Fin 2 ≃ Fin 12).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fin.sum_univ_two]
  congr 2 <;> ext <;> simp [hsu3I0, hsu3I1, finProdFinEquiv]; ring

private theorem hsu3_single_I1 (k : Fin 6) :
    Pi.single (hsu3I1 k) (1 : ℚ) = hsuJ (Pi.single (hsu3I0 k) 1) := by
  funext i
  obtain ⟨m, rfl | rfl⟩ := hsu3_cases i
  · rw [hsu3J_I0]
    simp [hsu3I1_ne_I0, (hsu3I1_ne_I0 k m).symm]
  · rw [hsu3J_I1, Pi.single_apply, Pi.single_apply]
    simp only [hsu3I0_inj, hsu3I1_inj]

/-- The `K`-matrix of a `J`-linear rational endomorphism. -/
private def hsu3M (X : Module.End ℚ (Fin 12 → ℚ)) : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.of fun k l => hsu3Z (X (Pi.single (hsu3I0 l) 1)) k

private theorem hsu3Z_single_I0 (l : Fin 6) (x : ℚ) :
    hsu3Z (Pi.single (hsu3I0 l) x) = Pi.single l (x : ℂ) := by
  funext k
  rw [hsu3Z_apply]
  rw [Pi.single_apply, Pi.single_apply, Pi.single_apply]
  simp only [hsu3I0_inj, hsu3I1_ne_I0, ite_false]
  split_ifs <;> simp

private theorem hsu3Z_X {X : Module.End ℚ (Fin 12 → ℚ)} (hX : X * hsuJ = hsuJ * X)
    (v : Fin 12 → ℚ) : hsu3Z (X v) = hsu3M X *ᵥ hsu3Z v := by
  have hlin : hsu3Z ∘ₗ X = ((Matrix.mulVecLin (hsu3M X)).restrictScalars ℚ) ∘ₗ hsu3Z := by
    refine LinearMap.pi_ext fun j x => ?_
    obtain ⟨k, rfl | rfl⟩ := hsu3_cases j
    · have hs : Pi.single (hsu3I0 k) x = x • Pi.single (hsu3I0 k) (1 : ℚ) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
      rw [hs]
      simp only [map_smul, Matrix.mulVec_smul]
      rw [hsu3Z_single_I0, Matrix.mulVec_single]
      funext i
      simp [hsu3M, Rat.smul_def]
    · have hs : Pi.single (hsu3I1 k) x = x • hsuJ (Pi.single (hsu3I0 k) (1 : ℚ)) := by
        rw [← hsu3_single_I1, ← Pi.single_smul, smul_eq_mul, mul_one]
      have hXJ : X (hsuJ (Pi.single (hsu3I0 k) (1 : ℚ))) =
          hsuJ (X (Pi.single (hsu3I0 k) (1 : ℚ))) := by
        rw [← Module.End.mul_apply, hX, Module.End.mul_apply]
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
      rw [hs]
      simp only [map_smul, Matrix.mulVec_smul]
      rw [hXJ, hsu3Z_J, hsu3Z_J, hsu3Z_single_I0, Matrix.mulVec_smul, Matrix.mulVec_single]
      funext i
      simp [hsu3M, Rat.smul_def]
  exact LinearMap.congr_fun hlin v

/-- The matrix of `K`-coordinates of a 6-tuple of vectors (columns `z (v i)`). -/
private def hsu3ZMat (v : Fin 6 → Fin 12 → ℚ) : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.of fun k i => hsu3Z (v i) k

private theorem hsu3_map_w (f : MixedTensorOfType (Fin 12 → ℚ) (0, 6) →ₗ[ℚ] ℚ) :
    f hsuWeilTensor = ∑ σ : Equiv.Perm (Fin 6), ∑ s : Fin 6 → Fin 2,
    (((Equiv.Perm.sign σ : ℤ) : ℚ) * hsuWeilCoeff s) * f
      (tprod ℚ (fun k : Fin 0 => k.elim0) ⊗ₜ
        tprod ℚ (fun i => (Pi.basisFun ℚ (Fin 12)).coord
          ⟨2 * (σ i).val + (s i).val, by have := (σ i).isLt; have := (s i).isLt; omega⟩)) := by
  unfold hsuWeilTensor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, smul_eq_mul]

private theorem hsu3Ev_w (v : Fin 6 → Fin 12 → ℚ) :
    ((hsu3Ev v hsuWeilTensor : ℚ) : ℝ) = (hsu3ZMat v).det.re := by
  rw [Matrix.det_apply, Complex.re_sum, hsu3_map_w, Rat.cast_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h := hsu3_re_prod (fun i t => v i ⟨2 * (σ i).val + t.val, by
    have := (σ i).isLt; have := t.isLt; omega⟩)
  have hp : ∏ i, hsu3ZMat v (σ i) i = ∏ i, (((v i ⟨2 * (σ i).val + (0 : Fin 2).val, by
      have := (σ i).isLt; omega⟩ : ℚ) : ℂ) + root * ((v i ⟨2 * (σ i).val + (1 : Fin 2).val, by
      have := (σ i).isLt; omega⟩ : ℚ) : ℂ)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hsu3ZMat, Matrix.of_apply, hsu3Z_apply]
    rfl
  rw [Units.smul_def, zsmul_eq_mul, hp, ← Complex.ofReal_intCast, Complex.re_ofReal_mul, h,
    Finset.mul_sum, Rat.cast_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hsu3Ev_tprod]
  simp only [Module.Basis.coord_apply, Pi.basisFun_repr]
  push_cast
  ring

private theorem hsu3_trace_M {X : Module.End ℚ (Fin 12 → ℚ)} (hX : X * hsuJ = hsuJ * X) :
    (hsu3M X).trace = (LinearMap.trace ℚ _ X : ℂ) / 2 -
      root * (LinearMap.trace ℚ _ (hsuJ * X) : ℂ) / 6 := by
  have htr (Y : Module.End ℚ (Fin 12 → ℚ)) :
      LinearMap.trace ℚ _ Y = ∑ j, Y (Pi.single j 1) j := by
    rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ (Fin 12)), LinearMap.toMatrix_eq_toMatrix',
      Matrix.trace]
    simp [LinearMap.toMatrix'_apply]
  have hXJ (k : Fin 6) : X (Pi.single (hsu3I1 k) 1) = hsuJ (X (Pi.single (hsu3I0 k) 1)) := by
    rw [hsu3_single_I1, ← Module.End.mul_apply, hX, Module.End.mul_apply]
  have hJJ (u : Fin 12 → ℚ) : hsuJ (hsuJ u) = (-3 : ℚ) • u := by
    have := LinearMap.congr_fun spec_hsuJ_sq_aux u
    simpa using this
  rw [htr, htr, hsu3_sum12, hsu3_sum12]
  simp only [Module.End.mul_apply, hXJ, hsu3J_I0, hsu3J_I1]
  rw [Matrix.trace]
  simp only [Matrix.diag, hsu3M, Matrix.of_apply, hsu3Z_apply]
  push_cast
  rw [Finset.sum_div, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring


private theorem hsu3ZMat_update (v : Fin 6 → Fin 12 → ℚ) (i : Fin 6) (u : Fin 12 → ℚ) :
    hsu3ZMat (Function.update v i u) = (hsu3ZMat v).updateCol i (hsu3Z u) := by
  ext k l
  rw [Matrix.updateCol_apply]
  by_cases h : l = i
  · subst h; simp [hsu3ZMat]
  · simp [hsu3ZMat, h]

private theorem hsu3Ev_lie_det (X : Module.End ℚ (Fin 12 → ℚ)) (v : Fin 6 → Fin 12 → ℚ)
    (T : MixedTensorOfType (Fin 12 → ℚ) (0, 6))
    (hT : ∀ u, ((hsu3Ev u T : ℚ) : ℝ) = (hsu3ZMat u).det.re) :
    ((hsu3Ev v ⁅X, T⁆ : ℚ) : ℝ) =
      -(∑ i, ((hsu3ZMat v).updateCol i (hsu3Z (X (v i)))).det).re := by
  rw [hsu3Ev_lie, Rat.cast_neg, Rat.cast_sum, Complex.re_sum]
  simp only [hT, hsu3ZMat_update]

private theorem hsu3Ev_lie_w (X : Module.End ℚ (Fin 12 → ℚ)) (v : Fin 6 → Fin 12 → ℚ) :
    ((hsu3Ev v ⁅X, hsuWeilTensor⁆ : ℚ) : ℝ) =
      -(∑ i, ((hsu3ZMat v).updateCol i (hsu3Z (X (v i)))).det).re :=
  hsu3Ev_lie_det X v hsuWeilTensor hsu3Ev_w

/-- A `J`-linear endomorphism whose `K`-trace vanishes kills the Weil tensor. -/
private theorem hsu3_lie_w_eq_zero {X : Module.End ℚ (Fin 12 → ℚ)} (hX : X * hsuJ = hsuJ * X)
    (htr : (hsu3M X).trace = 0) : ⁅X, hsuWeilTensor⁆ = 0 := by
  refine hsu3Ev_injective _ fun v => ?_
  have h := hsu3Ev_lie_w X v
  have hcol (i : Fin 6) : hsu3Z (X (v i)) = hsu3M X *ᵥ fun k => hsu3ZMat v k i :=
    hsu3Z_X hX (v i)
  simp only [hcol, hsu3_sum_det_updateCol, htr, zero_mul, Complex.zero_re, neg_zero] at h
  exact_mod_cast h

private def hsu3V0 : Fin 6 → Fin 12 → ℚ :=
  ![Pi.single 1 1, Pi.single 2 1, Pi.single 4 1, Pi.single 6 1, Pi.single 8 1, Pi.single 10 1]

private theorem hsu3ZMat_V0 : hsu3ZMat hsu3V0 = Matrix.diagonal ![root, 1, 1, 1, 1, 1] := by
  ext k i
  fin_cases k <;> fin_cases i <;>
    simp [hsu3ZMat, hsu3Z_apply, hsu3V0, hsu3I0, hsu3I1, Pi.single_apply, Matrix.diagonal]

/-- The Weil operator does not kill the Weil tensor. -/
private theorem hsu3_lie_J_w_ne_zero : ⁅hsuJ, hsuWeilTensor⁆ ≠ 0 := by
  intro h0
  have h := hsu3Ev_lie_w hsuJ hsu3V0
  have hcol (i : Fin 6) : hsu3Z (hsuJ (hsu3V0 i)) = root • fun k => hsu3ZMat hsu3V0 k i :=
    hsu3Z_J (hsu3V0 i)
  simp only [hcol, Matrix.det_updateCol_smul, Matrix.updateCol_eq_self, hsu3ZMat_V0,
    Matrix.det_diagonal, Fin.prod_univ_six, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    h0, map_zero, Rat.cast_zero] at h
  have hr : root * (root * 1 * 1 * 1 * 1 * 1) = -3 := by rw [← root_sq]; ring
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hr] at h
  norm_num at h

private theorem hsu3_skew_of_mem_annE {X : Module.End ℚ (Fin 12 → ℚ)}
    (hX : X ∈ lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (0, 2)) hsuETensor) :
    ∀ x y, hsuE (X x) y = -hsuE x (X y) := by
  rw [hsuETensor, hsu3_mem_lieAnnihilator_formTensor] at hX
  have hB : hsuE.compl₁₂ X LinearMap.id + hsuE.compl₁₂ LinearMap.id X = 0 :=
    LinearMap.ext_basis hsu3B hsu3B fun k l => by simpa using hX k l
  intro x y
  have := LinearMap.congr_fun₂ hB x y
  simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply,
    LinearMap.zero_apply] at this
  exact eq_neg_of_add_eq_zero_left this

private theorem hsu3_comm_of_mem_annJ {X : Module.End ℚ (Fin 12 → ℚ)}
    (hX : X ∈ lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (1, 1)) hsuJTensor) :
    X * hsuJ = hsuJ * X := by
  rwa [hsuJTensor, hsu3_mem_lieAnnihilator_endTensor] at hX

private theorem hsu3_trace_dualLie {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (f : Module.End ℂ W) :
    LinearMap.trace ℂ _ (dualLie ℂ W f) = -LinearMap.trace ℂ W f := by
  rw [dualLie_apply, map_neg]
  congr 1
  exact LinearMap.congr_fun (LinearMap.trace_transpose ℂ W) f

private theorem hsu3_conj_eq_blockLie {c : Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))}
    (hc : c ∈ hsu3CommC) (hs : c ∈ hsu3SkewC) :
    hsu3Split.conj c = blockLie hsu3W (firstBlock hsu3W (hsu3Split.conj c)) := by
  rw [mem_hsu3CommC] at hc
  rw [mem_hsu3SkewC] at hs
  have hc' : (hsu3Split.conj c).comp (splitJ hsu3W) = (splitJ hsu3W).comp (hsu3Split.conj c) := by
    rw [← hsu3Split_conj_J, ← LinearEquiv.conj_comp, ← LinearEquiv.conj_comp, hc]
  have hs' : ∀ x y, splitForm hsu3W (hsu3Split.conj c x) y =
      -splitForm hsu3W x (hsu3Split.conj c y) := by
    intro x y
    obtain ⟨x, rfl⟩ := hsu3Split.surjective x
    obtain ⟨y, rfl⟩ := hsu3Split.surjective y
    rw [hsu3Split_conj_apply, hsu3Split_conj_apply, ← hsu3Split_form, ← hsu3Split_form, hs]
  exact eq_blockLie_of_commutes_skew hsu3W (hsu3Split.conj c) hc' hs'

private theorem hsu3_trace_of_commSkew {c : Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))}
    (hc : c ∈ hsu3CommC) (hs : c ∈ hsu3SkewC) :
    LinearMap.trace ℂ _ c = 0 ∧
      LinearMap.trace ℂ _ ((hsuJ.baseChange ℂ) ∘ₗ c) =
        2 * root * LinearMap.trace ℂ _ (firstBlock hsu3W (hsu3Split.conj c)) := by
  have hb := hsu3_conj_eq_blockLie hc hs
  set f := firstBlock hsu3W (hsu3Split.conj c)
  constructor
  · rw [← LinearMap.trace_conj' c hsu3Split, hb]
    change LinearMap.trace ℂ _ (f.prodMap (dualLie ℂ hsu3W f)) = 0
    rw [LinearMap.trace_prodMap', hsu3_trace_dualLie, add_neg_cancel]
  · rw [← LinearMap.trace_conj' _ hsu3Split, LinearEquiv.conj_comp, hsu3Split_conj_J, hb]
    have : (splitJ hsu3W).comp (blockLie hsu3W f) =
        (root • f).prodMap (-root • dualLie ℂ hsu3W f) := by
      ext x <;> simp [splitJ, blockLie]
    rw [this, LinearMap.trace_prodMap', map_smul, map_smul, hsu3_trace_dualLie, smul_eq_mul,
      smul_eq_mul]
    ring

private abbrev hsu3AnnJ : LieSubalgebra ℚ (Module.End ℚ (Fin 12 → ℚ)) :=
  lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (1, 1)) hsuJTensor
private abbrev hsu3AnnE : LieSubalgebra ℚ (Module.End ℚ (Fin 12 → ℚ)) :=
  lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (0, 2)) hsuETensor
private abbrev hsu3AnnW : LieSubalgebra ℚ (Module.End ℚ (Fin 12 → ℚ)) :=
  lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (0, 6)) hsuWeilTensor

/-- The rational stabilizer of `[J, E]`. -/
private abbrev hsu3P : Submodule ℚ (Module.End ℚ (Fin 12 → ℚ)) :=
  (⨅ i, lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (hsuWeilPair i).1)
    (hsuWeilPair i).2).toSubmodule

/-- The rational stabilizer of `[J, E, w]`. -/
private abbrev hsu3A : Submodule ℚ (Module.End ℚ (Fin 12 → ℚ)) :=
  (⨅ i, lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (hsuWeilTriple i).1)
    (hsuWeilTriple i).2).toSubmodule

private theorem mem_hsu3P (X : Module.End ℚ (Fin 12 → ℚ)) :
    X ∈ hsu3P ↔ X ∈ hsu3AnnJ ∧ X ∈ hsu3AnnE := by
  rw [LieSubalgebra.mem_toSubmodule, hsu3_mem_iInf, Fin.forall_fin_two]
  rfl

private theorem mem_hsu3A (X : Module.End ℚ (Fin 12 → ℚ)) :
    X ∈ hsu3A ↔ X ∈ hsu3AnnJ ∧ X ∈ hsu3AnnE ∧ X ∈ hsu3AnnW := by
  rw [LieSubalgebra.mem_toSubmodule, hsu3_mem_iInf]
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

/-- The rational functional `X ↦ tr (J X)`. -/
private def hsu3TrJ : Module.End ℚ (Fin 12 → ℚ) →ₗ[ℚ] ℚ :=
  LinearMap.trace ℚ _ ∘ₗ LinearMap.mulLeft ℚ hsuJ

private theorem hsu3TrJ_apply (X : Module.End ℚ (Fin 12 → ℚ)) :
    hsu3TrJ X = LinearMap.trace ℚ _ (hsuJ * X) := rfl

private theorem hsu3_finrank_complexSpan (W : Submodule ℚ (Module.End ℚ (Fin 12 → ℚ))) :
    Module.finrank ℂ (complexSpan W) = Module.finrank ℚ W := by
  have : Module.Free ℚ W := Module.Free.of_divisionRing ℚ W
  rw [complexSpan_eq_map]
  have : (W.baseChange ℂ).map (LinearMap.tensorProductEnd ℚ ℂ (Fin 12 → ℚ)).toLinearMap =
      (W.baseChange ℂ).map (endBaseChangeEquiv (Fin 12 → ℚ) : _ →ₗ[ℂ] _) := rfl
  rw [this, LinearEquiv.finrank_map_eq, Submodule.baseChange, LinearMap.finrank_range_of_inj,
    Module.finrank_baseChange]
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ W.injective_subtype

private theorem hsu3_finrank_P : Module.finrank ℚ hsu3P = 36 := by
  rw [← hsu3_finrank_complexSpan]
  exact spec_finrank_hsuWeilPair

private theorem hsu3_commSkew_of_mem_P {X : Module.End ℚ (Fin 12 → ℚ)} (hX : X ∈ hsu3P) :
    X.baseChange ℂ ∈ hsu3CommC ∧ X.baseChange ℂ ∈ hsu3SkewC := by
  rw [mem_hsu3P] at hX
  constructor
  · rw [← hsu3_complexSpan_annJ]
    exact Submodule.subset_span ⟨X, hX.1, rfl⟩
  · rw [← hsu3_complexSpan_annE]
    exact Submodule.subset_span ⟨X, hX.2, rfl⟩

private theorem hsu3_traces_of_mem_P {X : Module.End ℚ (Fin 12 → ℚ)} (hX : X ∈ hsu3P) :
    LinearMap.trace ℚ _ X = 0 ∧
      ((hsu3TrJ X : ℚ) : ℂ) = 2 * root *
        LinearMap.trace ℂ _ (firstBlock hsu3W (hsu3Split.conj (X.baseChange ℂ))) := by
  obtain ⟨hc, hs⟩ := hsu3_commSkew_of_mem_P hX
  obtain ⟨h1, h2⟩ := hsu3_trace_of_commSkew hc hs
  rw [LinearMap.trace_baseChange] at h1
  refine ⟨by simpa using h1, ?_⟩
  rw [← h2, ← LinearMap.baseChange_comp, LinearMap.trace_baseChange, hsu3TrJ_apply]
  rfl

/-- The trace-zero part of the stabilizer of `[J, E]`. -/
private abbrev hsu3A0 : Submodule ℚ (Module.End ℚ (Fin 12 → ℚ)) := hsu3P ⊓ LinearMap.ker hsu3TrJ

private theorem hsu3_A0_le_A : hsu3A0 ≤ hsu3A := by
  intro X hX
  obtain ⟨hP, hT⟩ := Submodule.mem_inf.mp hX
  rw [LinearMap.mem_ker] at hT
  have hP' := (mem_hsu3P X).mp hP
  refine (mem_hsu3A X).mpr ⟨hP'.1, hP'.2, ?_⟩
  have hc := hsu3_comm_of_mem_annJ hP'.1
  have htr := hsu3_trace_M hc
  rw [(hsu3_traces_of_mem_P hP).1, ← hsu3TrJ_apply, hT] at htr
  simp only [Rat.cast_zero, zero_div, mul_zero, sub_zero] at htr
  rw [mem_lieAnnihilator]
  exact hsu3_lie_w_eq_zero hc htr

private theorem hsu3_J_mem_P : hsuJ ∈ hsu3P := by
  rw [mem_hsu3P]
  constructor
  · exact (hsu3_mem_lieAnnihilator_endTensor _ _ _).mpr rfl
  · rw [← LieSubalgebra.mem_toSubmodule, hsu3_annE, LinearMap.mem_ker]
    funext p
    simp only [hsu3SkewMapQ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    rw [spec_hsuE_skew_aux, neg_add_cancel]

private theorem hsu3_A_lt_P : hsu3A < hsu3P := by
  refine lt_of_le_of_ne (fun X hX => ?_) fun h => ?_
  · obtain ⟨h0, h1, -⟩ := (mem_hsu3A X).mp hX
    exact (mem_hsu3P X).mpr ⟨h0, h1⟩
  · have hJ : hsuJ ∈ hsu3A := h ▸ hsu3_J_mem_P
    exact hsu3_lie_J_w_ne_zero ((mem_lieAnnihilator _).mp ((mem_hsu3A hsuJ).mp hJ).2.2)

private theorem hsu3_finrank_A0 : 35 ≤ Module.finrank ℚ hsu3A0 := by
  change 35 ≤ Module.finrank ℚ ↥(hsu3P ⊓ LinearMap.ker hsu3TrJ)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq hsu3P (LinearMap.ker hsu3TrJ)
  have h2 := LinearMap.finrank_range_add_finrank_ker hsu3TrJ
  have h3 : Module.finrank ℚ (LinearMap.range hsu3TrJ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range hsu3TrJ)
    rwa [Module.finrank_self] at this
  have h4 := Submodule.finrank_le (hsu3P ⊔ LinearMap.ker hsu3TrJ)
  have h5 : Module.finrank ℚ (Module.End ℚ (Fin 12 → ℚ)) = 144 := by
    rw [Module.finrank_linearMap, Module.finrank_fin_fun]
  rw [h5] at h2 h4
  rw [hsu3_finrank_P] at h1
  omega

private theorem hsu3_A0_eq_A : hsu3A0 = hsu3A := by
  refine Submodule.eq_of_le_of_finrank_le hsu3_A0_le_A ?_
  have := Submodule.finrank_lt_finrank_of_lt hsu3_A_lt_P
  rw [hsu3_finrank_P] at this
  have := hsu3_finrank_A0
  omega

private theorem hsu3_complexSpan_A0_le :
    complexSpan hsu3A0 ≤ (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq
      spec_hsuE_skew).toSubmodule := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨X, hX, rfl⟩
  obtain ⟨hP, hT⟩ := Submodule.mem_inf.mp hX
  rw [LinearMap.mem_ker] at hT
  obtain ⟨hc, hs⟩ := hsu3_commSkew_of_mem_P hP
  have htr := (hsu3_traces_of_mem_P hP).2
  rw [hT, Rat.cast_zero, eq_comm, mul_eq_zero] at htr
  have hf := htr.resolve_left (mul_ne_zero two_ne_zero root_ne_zero)
  rw [SetLike.mem_coe, LieSubalgebra.mem_toSubmodule, mem_complexSU _ _ _ _ _ spec_hsuE_isAlt_aux]
  exact ⟨(mem_hsu3CommC _).mp hc, (mem_hsu3SkewC _).mp hs, hf⟩

end Hsu3WeilCoords

theorem spec_mixedTensorStabilizer_hsuWeilTriple_aux :
    mixedTensorStabilizer hsuWeilTriple =
      (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq
        spec_hsuE_skew).toSubmodule := by
  change complexSpan hsu3A = _
  rw [← hsu3_A0_eq_A]
  refine Submodule.eq_of_le_of_finrank_le hsu3_complexSpan_A0_le ?_
  rw [spec_finrank_hsu_complexSU, hsu3_finrank_complexSpan]
  exact hsu3_finrank_A0

theorem spec_finrank_hsuWeilTriple_aux :
    Module.finrank ℂ (mixedTensorStabilizer hsuWeilTriple) = 35 := by
  rw [spec_mixedTensorStabilizer_hsuWeilTriple_aux, spec_finrank_hsu_complexSU]

private theorem hsu3_mem_annRosati {X : Module.End ℚ (Fin 12 → ℚ)}
    (hJ : X ∈ lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (1, 1)) hsuJTensor)
    (hE : X ∈ lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (0, 2)) hsuETensor) :
    X ∈ lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (0, 2)) hsuRosatiTensor := by
  have hs := hsu3_skew_of_mem_annE hE
  have hc := hsu3_comm_of_mem_annJ hJ
  rw [hsuRosatiTensor, hsu3_mem_lieAnnihilator_formTensor]
  intro k l
  have hy : hsuJ (X (hsu3B l)) = X (hsuJ (hsu3B l)) := by
    rw [← Module.End.mul_apply, ← hc, Module.End.mul_apply]
  simp only [LinearMap.compl₂_apply, hy, hs (hsu3B k) (hsuJ (hsu3B l)), neg_add_cancel]

private theorem hsu3_stab_rosati : mixedTensorStabilizer hsuRosatiTriple =
    mixedTensorStabilizer hsuWeilPair := by
  unfold mixedTensorStabilizer
  congr 1
  ext X
  rw [LieSubalgebra.mem_toSubmodule, LieSubalgebra.mem_toSubmodule, hsu3_mem_iInf, hsu3_mem_iInf,
    Fin.forall_fin_two]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact hsu3_mem_annRosati h0 h1

theorem spec_finrank_hsuRosatiTriple_aux :
    Module.finrank ℂ (mixedTensorStabilizer hsuRosatiTriple) = 36 := by
  rw [hsu3_stab_rosati, spec_finrank_hsuWeilPair]

end WeilTensor

section CMHodge

private abbrev hsuBu (j : Fin 12) : ℂ ⊗[ℚ] (Fin 12 → ℚ) := (1 : ℂ) ⊗ₜ Pi.single j (1 : ℚ)

private theorem hsuB_tmul_eq (c : ℂ) (j : Fin 12) :
    c ⊗ₜ[ℚ] (Pi.single j (1 : ℚ) : Fin 12 → ℚ) = c • hsuBu j := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem hsuB_vec_eq (k : Fin 6) :
    hsuPeriodVec k = (hsuPeriodSign k * root) • hsuBu ⟨2 * k.val, by omega⟩ +
      hsuBu ⟨2 * k.val + 1, by omega⟩ := by
  rw [hsuPeriodVec, hsuB_tmul_eq]

private theorem hsuB_vecBar_eq (k : Fin 6) :
    hsuPeriodVecBar k = (-(hsuPeriodSign k * root)) • hsuBu ⟨2 * k.val, by omega⟩ +
      hsuBu ⟨2 * k.val + 1, by omega⟩ := by
  rw [hsuPeriodVecBar, hsuB_tmul_eq]

/-- The `j`-th coordinate of a vector of `ℂ ⊗[ℚ] ℚ¹²`. -/
private def hsuBcrd (j : Fin 12) : ℂ ⊗[ℚ] (Fin 12 → ℚ) →ₗ[ℂ] ℂ :=
  (TensorProduct.AlgebraTensorModule.rid ℚ ℂ ℂ).toLinearMap ∘ₗ
    ((LinearMap.proj j : (Fin 12 → ℚ) →ₗ[ℚ] ℚ).baseChange ℂ)

private theorem hsuBcrd_u (j i : Fin 12) : hsuBcrd j (hsuBu i) = if i = j then 1 else 0 := by
  simp [hsuBcrd, Pi.single_apply, eq_comm]

private theorem hsuBcrd_vec (i l : Fin 6) :
    hsuBcrd ⟨2 * i.val + 1, by omega⟩ (hsuPeriodVec l) = if l = i then 1 else 0 := by
  rw [hsuB_vec_eq, map_add, map_smul, hsuBcrd_u, hsuBcrd_u]
  simp only [Fin.ext_iff]
  split_ifs <;> first | omega | simp

private theorem hsuBcrd_vecBar (i l : Fin 6) :
    hsuBcrd ⟨2 * i.val + 1, by omega⟩ (hsuPeriodVecBar l) = if l = i then 1 else 0 := by
  rw [hsuB_vecBar_eq, map_add, map_smul, hsuBcrd_u, hsuBcrd_u]
  simp only [Fin.ext_iff]
  split_ifs <;> first | omega | simp

private theorem hsuB_linearIndependent_of_crd (v : Fin 6 → ℂ ⊗[ℚ] (Fin 12 → ℚ))
    (hv : ∀ i l, hsuBcrd ⟨2 * i.val + 1, by omega⟩ (v l) = if l = i then 1 else 0) :
    LinearIndependent ℂ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (hsuBcrd ⟨2 * i.val + 1, by omega⟩) hg
  simpa [map_sum, hv] using h

private theorem hsuB_linearIndependent_vec : LinearIndependent ℂ hsuPeriodVec :=
  hsuB_linearIndependent_of_crd _ hsuBcrd_vec

private theorem hsuB_linearIndependent_vecBar : LinearIndependent ℂ hsuPeriodVecBar :=
  hsuB_linearIndependent_of_crd _ hsuBcrd_vecBar


private theorem hsuB_sign_ne_zero (k : Fin 6) : hsuPeriodSign k ≠ 0 := by
  unfold hsuPeriodSign; split_ifs <;> norm_num

private theorem hsuB_u_mem_sup (j : Fin 12) :
    hsuBu j ∈ Submodule.span ℂ (Set.range hsuPeriodVec) ⊔
      Submodule.span ℂ (Set.range hsuPeriodVecBar) := by
  set k : Fin 6 := ⟨j.val / 2, by omega⟩ with hk
  have hf : hsuPeriodVec k ∈ Submodule.span ℂ (Set.range hsuPeriodVec) ⊔
      Submodule.span ℂ (Set.range hsuPeriodVecBar) :=
    Submodule.mem_sup_left (Submodule.subset_span ⟨k, rfl⟩)
  have hfb : hsuPeriodVecBar k ∈ Submodule.span ℂ (Set.range hsuPeriodVec) ⊔
      Submodule.span ℂ (Set.range hsuPeriodVecBar) :=
    Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩)
  have hε := hsuB_sign_ne_zero k
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h
  · have hj : j = ⟨2 * k.val, by omega⟩ := Fin.ext (by simp only [hk]; omega)
    have : hsuBu j = (2 * hsuPeriodSign k * root)⁻¹ • (hsuPeriodVec k - hsuPeriodVecBar k) := by
      rw [hj, hsuB_vec_eq, hsuB_vecBar_eq, add_sub_add_right_eq_sub, ← sub_smul, smul_smul,
        show (2 * hsuPeriodSign k * root)⁻¹ * (hsuPeriodSign k * root - -(hsuPeriodSign k * root)) =
          1 by field_simp [root_ne_zero]; ring, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (sub_mem hf hfb)
  · have hj : j = ⟨2 * k.val + 1, by omega⟩ := Fin.ext (by simp only [hk]; omega)
    have : hsuBu j = (2 : ℂ)⁻¹ • (hsuPeriodVec k + hsuPeriodVecBar k) := by
      rw [hj, hsuB_vec_eq, hsuB_vecBar_eq, add_add_add_comm, ← add_smul, add_neg_cancel,
        zero_smul, zero_add, ← two_smul ℂ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (add_mem hf hfb)

private theorem hsuB_sup_eq_top :
    Submodule.span ℂ (Set.range hsuPeriodVec) ⊔ Submodule.span ℂ (Set.range hsuPeriodVecBar) = ⊤ := by
  rw [eq_top_iff, ← (Algebra.TensorProduct.basis ℂ (Pi.basisFun ℚ (Fin 12))).span_eq,
    Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [Algebra.TensorProduct.basis_apply, Pi.basisFun_apply]
  exact hsuB_u_mem_sup j

private theorem hsuB_finrank_total : Module.finrank ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ)) = 12 := by
  rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

private theorem hsuB_isCompl :
    IsCompl (Submodule.span ℂ (Set.range hsuPeriodVec))
      (Submodule.span ℂ (Set.range hsuPeriodVecBar)) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℂ (Set.range hsuPeriodVec))
    (Submodule.span ℂ (Set.range hsuPeriodVecBar))
  rw [hsuB_sup_eq_top, finrank_top, hsuB_finrank_total,
    finrank_span_eq_card hsuB_linearIndependent_vec,
    finrank_span_eq_card hsuB_linearIndependent_vecBar, Fintype.card_fin] at h
  refine ⟨disjoint_iff.mpr (Submodule.finrank_eq_zero.mp (by omega)),
    codisjoint_iff.mpr hsuB_sup_eq_top⟩

theorem spec_hsuCMHodge_isInternal_aux : DirectSum.IsInternal hsuCMHodge :=
  isInternal_pair hsuB_isCompl (by simp)

theorem spec_hsuCMHodge_pure_aux : ∀ p q : ℤ, p + q ≠ 1 → hsuCMHodge (p, q) = ⊥ := by
  intro p q h
  have h1 : ((p, q) : ℤ × ℤ) ≠ (1, 0) := by simp only [ne_eq, Prod.mk.injEq]; omega
  have h2 : ((p, q) : ℤ × ℤ) ≠ (0, 1) := by simp only [ne_eq, Prod.mk.injEq]; omega
  simp only [hsuCMHodge, h1, h2, ite_false]

private theorem hsuB_sign_conj (k : Fin 6) : starRingEnd ℂ (hsuPeriodSign k) = hsuPeriodSign k := by
  unfold hsuPeriodSign; split_ifs <;> simp

private theorem hsuB_conj_vec (k : Fin 6) :
    complexConj (Fin 12 → ℚ) (hsuPeriodVec k) = hsuPeriodVecBar k := by
  rw [hsuPeriodVec, hsuPeriodVecBar, map_add, complexConj_tmul, complexConj_tmul, map_mul,
    hsuB_sign_conj, conj_root, map_one]
  ring_nf

private theorem hsuB_conj_vecBar (k : Fin 6) :
    complexConj (Fin 12 → ℚ) (hsuPeriodVecBar k) = hsuPeriodVec k := by
  rw [hsuPeriodVec, hsuPeriodVecBar, map_add, complexConj_tmul, complexConj_tmul, map_neg, map_mul,
    hsuB_sign_conj, conj_root, map_one]
  ring_nf


private theorem hsuB_conj_span {v w : Fin 6 → ℂ ⊗[ℚ] (Fin 12 → ℚ)}
    (hvw : ∀ k, complexConj (Fin 12 → ℚ) (v k) = w k) {x : ℂ ⊗[ℚ] (Fin 12 → ℚ)}
    (hx : x ∈ Submodule.span ℂ (Set.range v)) :
    complexConj (Fin 12 → ℚ) x ∈ Submodule.span ℂ (Set.range w) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    rw [hvw]
    exact Submodule.subset_span ⟨k, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy => rw [complexConj_smul]; exact Submodule.smul_mem _ _ hy

theorem spec_hsuCMHodge_conj_aux :
    ∀ p q : ℤ, ∀ x ∈ hsuCMHodge (p, q),
      complexConj (Fin 12 → ℚ) x ∈ hsuCMHodge (q, p) := by
  intro p q x hx
  by_cases h1 : ((p, q) : ℤ × ℤ) = (1, 0)
  · simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simp only [hsuCMHodge, ite_true] at hx
    simp only [hsuCMHodge, Prod.mk.injEq, ite_true]
    simpa using hsuB_conj_span hsuB_conj_vec hx
  · by_cases h2 : ((p, q) : ℤ × ℤ) = (0, 1)
    · simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      simp only [hsuCMHodge, Prod.mk.injEq, ite_true] at hx
      simpa [hsuCMHodge] using hsuB_conj_span hsuB_conj_vecBar (by simpa using hx)
    · simp only [hsuCMHodge, h1, h2, ite_false, Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact Submodule.zero_mem _

private theorem hsuB_J_ev (k : Fin 6) :
    hsuJ (Pi.single (⟨2 * k.val, by omega⟩ : Fin 12) (1 : ℚ)) =
      Pi.single (⟨2 * k.val + 1, by omega⟩ : Fin 12) (1 : ℚ) := by
  rw [hsuJ_apply]
  funext i
  fin_cases k <;> fin_cases i <;> simp

private theorem hsuB_J_od (k : Fin 6) :
    hsuJ (Pi.single (⟨2 * k.val + 1, by omega⟩ : Fin 12) (1 : ℚ)) =
      (-3 : ℚ) • Pi.single (⟨2 * k.val, by omega⟩ : Fin 12) (1 : ℚ) := by
  rw [hsuJ_apply]
  funext i
  fin_cases k <;> fin_cases i <;> simp

private theorem hsuB_qsmul (q : ℚ) (x : ℂ ⊗[ℚ] (Fin 12 → ℚ)) : q • x = (q : ℂ) • x :=
  (Rat.cast_smul_eq_qsmul ℂ q x).symm

private theorem hsuB_sign_sq (k : Fin 6) : hsuPeriodSign k * hsuPeriodSign k = 1 := by
  unfold hsuPeriodSign; split_ifs <;> norm_num

private theorem hsuB_root_mul_root : root * root = -3 := by rw [← sq, root_sq]

private theorem hsuB_JC_ev (k : Fin 6) :
    hsuJ.baseChange ℂ (hsuBu ⟨2 * k.val, by omega⟩) = hsuBu ⟨2 * k.val + 1, by omega⟩ := by
  rw [LinearMap.baseChange_tmul, hsuB_J_ev]

private theorem hsuB_JC_od (k : Fin 6) :
    hsuJ.baseChange ℂ (hsuBu ⟨2 * k.val + 1, by omega⟩) =
      (-3 : ℂ) • hsuBu ⟨2 * k.val, by omega⟩ := by
  rw [LinearMap.baseChange_tmul, hsuB_J_od, TensorProduct.tmul_smul, hsuB_qsmul]
  norm_num

private theorem hsuB_J_vec (k : Fin 6) :
    hsuJ.baseChange ℂ (hsuPeriodVec k) = (hsuPeriodSign k * root) • hsuPeriodVec k := by
  have h1 := hsuB_sign_sq k
  have h2 := hsuB_root_mul_root
  rw [hsuB_vec_eq, map_add, map_smul, hsuB_JC_ev, hsuB_JC_od, smul_add, smul_smul]
  rw [add_comm]
  congr 1
  congr 1
  linear_combination (-(root * root)) * h1 - h2

private theorem hsuB_J_vecBar (k : Fin 6) :
    hsuJ.baseChange ℂ (hsuPeriodVecBar k) = (-(hsuPeriodSign k * root)) • hsuPeriodVecBar k := by
  have h1 := hsuB_sign_sq k
  have h2 := hsuB_root_mul_root
  rw [hsuB_vecBar_eq, map_add, map_smul, hsuB_JC_ev, hsuB_JC_od, smul_add, smul_smul]
  rw [add_comm]
  congr 1
  congr 1
  linear_combination (-(root * root)) * h1 - h2

private theorem hsuB_J_span {v : Fin 6 → ℂ ⊗[ℚ] (Fin 12 → ℚ)} (c : Fin 6 → ℂ)
    (hv : ∀ k, hsuJ.baseChange ℂ (v k) = c k • v k) {x : ℂ ⊗[ℚ] (Fin 12 → ℚ)}
    (hx : x ∈ Submodule.span ℂ (Set.range v)) :
    hsuJ.baseChange ℂ x ∈ Submodule.span ℂ (Set.range v) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

theorem spec_hsuCMHodge_J_aux :
    ∀ pq : ℤ × ℤ, ∀ x ∈ hsuCMHodge pq, hsuJ.baseChange ℂ x ∈ hsuCMHodge pq := by
  intro pq x hx
  simp only [hsuCMHodge] at hx ⊢
  split_ifs at hx ⊢
  · exact hsuB_J_span _ hsuB_J_vec hx
  · exact hsuB_J_span _ hsuB_J_vecBar hx
  · rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
    exact Submodule.zero_mem _


private theorem hsuB_hodge_one_zero :
    hsuCMHodge (1, 0) = Submodule.span ℂ (Set.range hsuPeriodVec) := by
  simp [hsuCMHodge]

private theorem hsuB_inf_eigenspace (μ : ℂ) (S : Finset (Fin 6))
    (hS : ∀ k, k ∈ S ↔ hsuPeriodSign k * root = μ) :
    Submodule.span ℂ (Set.range hsuPeriodVec) ⊓ Module.End.eigenspace (hsuJ.baseChange ℂ) μ =
      Submodule.span ℂ (Set.range fun k : S => hsuPeriodVec k) := by
  apply le_antisymm
  · rintro x ⟨hx, hxμ⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hxμ
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
    have hzero : ∀ k, c k * (hsuPeriodSign k * root - μ) = 0 := by
      have h := hxμ
      simp only [map_sum, map_smul, hsuB_J_vec, smul_smul, Finset.smul_sum] at h
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h
      simp only [← sub_smul] at h
      intro k
      have := (Fintype.linearIndependent_iff.mp hsuB_linearIndependent_vec) _ h k
      linear_combination this
    have hc : ∀ k ∉ S, c k = 0 := by
      intro k hk
      have h1 : hsuPeriodSign k * root - μ ≠ 0 := sub_ne_zero.mpr ((hS k).not.mp hk)
      exact (mul_eq_zero.mp (hzero k)).resolve_right h1
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun k _ hk => by rw [hc k hk, zero_smul]),
      ← Finset.sum_coe_sort]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ⟨Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, hsuB_J_vec, (hS k).mp k.2]

private theorem hsuB_finrank_inf_eigenspace (μ : ℂ) (S : Finset (Fin 6))
    (hS : ∀ k, k ∈ S ↔ hsuPeriodSign k * root = μ) :
    Module.finrank ℂ ↥(Submodule.span ℂ (Set.range hsuPeriodVec) ⊓
      Module.End.eigenspace (hsuJ.baseChange ℂ) μ) = S.card := by
  rw [hsuB_inf_eigenspace μ S hS]
  exact (finrank_span_eq_card (hsuB_linearIndependent_vec.comp _ Subtype.val_injective)).trans
    (Fintype.card_coe S)

theorem spec_hsuCMHodge_weilType_aux :
    Module.finrank ℂ ↥(hsuCMHodge (1, 0) ⊓ Module.End.eigenspace (hsuJ.baseChange ℂ) root) = 3 ∧
      Module.finrank ℂ
        ↥(hsuCMHodge (1, 0) ⊓ Module.End.eigenspace (hsuJ.baseChange ℂ) (-root)) = 3 := by
  have hr := root_ne_zero
  rw [hsuB_hodge_one_zero]
  constructor
  · rw [hsuB_finrank_inf_eigenspace root {3, 4, 5}]
    · rfl
    · intro k
      fin_cases k <;> simp [hsuPeriodSign, hr, neg_eq_iff_add_eq_zero, ← two_mul]
  · rw [hsuB_finrank_inf_eigenspace (-root) {0, 1, 2}]
    · rfl
    · intro k
      fin_cases k <;> simp [hsuPeriodSign, hr, eq_neg_iff_add_eq_zero, ← two_mul]

private theorem hsuB_E_u (i j : Fin 12) :
    hsuE.baseChange ℂ (hsuBu i) (hsuBu j) = (hsuE (Pi.single i 1) (Pi.single j 1) : ℂ) := by
  simp [LinearMap.BilinForm.baseChange_tmul]

private theorem hsuB_E_ev_od (k l : Fin 6) :
    hsuE (Pi.single (⟨2 * k.val, by omega⟩ : Fin 12) (1 : ℚ))
      (Pi.single (⟨2 * l.val + 1, by omega⟩ : Fin 12) (1 : ℚ)) =
      if k = l then hsuWeights k else 0 := by
  rw [hsuE_apply]
  fin_cases k <;> fin_cases l <;> simp [hsuWeights]


private theorem hsuB_E_ev_ev (k l : Fin 6) :
    hsuE (Pi.single (⟨2 * k.val, by omega⟩ : Fin 12) (1 : ℚ))
      (Pi.single (⟨2 * l.val, by omega⟩ : Fin 12) (1 : ℚ)) = 0 := by
  rw [hsuE_apply]
  fin_cases k <;> fin_cases l <;> simp

private theorem hsuB_E_od_od (k l : Fin 6) :
    hsuE (Pi.single (⟨2 * k.val + 1, by omega⟩ : Fin 12) (1 : ℚ))
      (Pi.single (⟨2 * l.val + 1, by omega⟩ : Fin 12) (1 : ℚ)) = 0 := by
  rw [hsuE_apply]
  fin_cases k <;> fin_cases l <;> simp

private theorem hsuB_E_od_ev (k l : Fin 6) :
    hsuE (Pi.single (⟨2 * k.val + 1, by omega⟩ : Fin 12) (1 : ℚ))
      (Pi.single (⟨2 * l.val, by omega⟩ : Fin 12) (1 : ℚ)) =
      if k = l then -hsuWeights k else 0 := by
  rw [hsuE_apply]
  fin_cases k <;> fin_cases l <;> simp [hsuWeights]

private theorem hsuB_E_vec_vec (k l : Fin 6) :
    hsuE.baseChange ℂ (hsuPeriodVec k) (hsuPeriodVec l) = 0 := by
  rw [hsuB_vec_eq, hsuB_vec_eq]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hsuB_E_u,
    hsuB_E_ev_ev, hsuB_E_od_od, hsuB_E_ev_od, hsuB_E_od_ev, smul_eq_mul]
  split_ifs with h
  · subst h; push_cast; ring
  · simp

theorem spec_hsuCMHodge_isotropic_aux :
    ∀ x ∈ hsuCMHodge (1, 0), ∀ y ∈ hsuCMHodge (1, 0), hsuE.baseChange ℂ x y = 0 := by
  intro x hx y hy
  simp only [hsuCMHodge, ite_true] at hx hy
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
  simp [map_sum, LinearMap.sum_apply, hsuB_E_vec_vec]


private theorem hsuB_E_vec_vecBar (k l : Fin 6) :
    hsuE.baseChange ℂ (hsuPeriodVec k) (hsuPeriodVecBar l) =
      if k = l then 2 * hsuPeriodSign k * root * (hsuWeights k : ℂ) else 0 := by
  rw [hsuB_vec_eq, hsuB_vecBar_eq]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hsuB_E_u,
    hsuB_E_ev_ev, hsuB_E_od_od, hsuB_E_ev_od, hsuB_E_od_ev, smul_eq_mul]
  split_ifs with h
  · subst h; push_cast; ring
  · simp

/-- The positive weight `-ε_k w_k` of block `k` in the second Riemann relation. -/
private def hsuBq (k : Fin 6) : ℝ := ![1, 1, 1, 1, 1, 2] k

private theorem hsuBq_pos (k : Fin 6) : 0 < hsuBq k := by
  fin_cases k <;> simp [hsuBq]

private theorem hsuB_I_E_coeff (k : Fin 6) :
    Complex.I * (2 * hsuPeriodSign k * root * (hsuWeights k : ℂ)) =
      ((2 * Real.sqrt 3 * hsuBq k : ℝ) : ℂ) := by
  have h : Complex.I * root = -(Real.sqrt 3 : ℂ) := by
    rw [root, ← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have h' : Complex.I * (2 * hsuPeriodSign k * root * (hsuWeights k : ℂ)) =
      2 * hsuPeriodSign k * (hsuWeights k : ℂ) * (Complex.I * root) := by ring
  rw [h', h]
  fin_cases k <;> (simp [hsuPeriodSign, hsuWeights, hsuBq]; try ring)

theorem spec_hsuCMHodge_positive_aux :
    ∀ x ∈ hsuCMHodge (1, 0), x ≠ 0 →
      0 < (Complex.I * hsuE.baseChange ℂ x (complexConj (Fin 12 → ℚ) x)).re := by
  intro x hx hx0
  rw [hsuB_hodge_one_zero] at hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  have hconj : complexConj (Fin 12 → ℚ) (∑ k, c k • hsuPeriodVec k) =
      ∑ k, starRingEnd ℂ (c k) • hsuPeriodVecBar k := by
    simp only [map_sum, complexConj_smul, hsuB_conj_vec]
  have hE : Complex.I * hsuE.baseChange ℂ (∑ k, c k • hsuPeriodVec k)
      (∑ k, starRingEnd ℂ (c k) • hsuPeriodVecBar k) =
      ((∑ k, Complex.normSq (c k) * (2 * Real.sqrt 3 * hsuBq k) : ℝ) : ℂ) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      hsuB_E_vec_vecBar, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Finset.mul_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.ofReal_mul, ← hsuB_I_E_coeff, ← Complex.mul_conj]
    ring
  rw [hconj, hE, Complex.ofReal_re]
  have hc : ∃ k, c k ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (by simp [h])
  obtain ⟨k, hk⟩ := hc
  refine Finset.sum_pos' (fun i _ => ?_) ⟨k, Finset.mem_univ _, ?_⟩
  · exact mul_nonneg (Complex.normSq_nonneg _)
      (mul_nonneg (by positivity) (hsuBq_pos i).le)
  · exact mul_pos (Complex.normSq_pos.mpr hk)
      (mul_pos (by positivity) (hsuBq_pos k))

private theorem hsuB_torus_apply (x : Fin 12 → ℚ) :
    hsuCMTorus x = ![3 * x 1, -x 0, 3 * x 3, -x 2, 3 * x 5, -x 4, -3 * x 7, x 6, -3 * x 9, x 8,
      -3 * x 11, x 10] := by
  funext i
  fin_cases i <;>
    simp [hsuCMTorus, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      hsuCMTorus₁₂, hsuJ₁₂]

private theorem hsuB_T_ev (k : Fin 6) :
    hsuCMTorus (Pi.single (⟨2 * k.val, by omega⟩ : Fin 12) (1 : ℚ)) =
      (if k.val < 3 then -1 else 1 : ℚ) • Pi.single (⟨2 * k.val + 1, by omega⟩ : Fin 12) (1 : ℚ) := by
  rw [hsuB_torus_apply]
  funext i
  fin_cases k <;> fin_cases i <;> simp

private theorem hsuB_T_od (k : Fin 6) :
    hsuCMTorus (Pi.single (⟨2 * k.val + 1, by omega⟩ : Fin 12) (1 : ℚ)) =
      (if k.val < 3 then 3 else -3 : ℚ) • Pi.single (⟨2 * k.val, by omega⟩ : Fin 12) (1 : ℚ) := by
  rw [hsuB_torus_apply]
  funext i
  fin_cases k <;> fin_cases i <;> simp

private theorem hsuB_TC_ev (k : Fin 6) :
    hsuCMTorus.baseChange ℂ (hsuBu ⟨2 * k.val, by omega⟩) =
      hsuPeriodSign k • hsuBu ⟨2 * k.val + 1, by omega⟩ := by
  rw [LinearMap.baseChange_tmul, hsuB_T_ev, TensorProduct.tmul_smul, hsuB_qsmul, hsuPeriodSign]
  split_ifs <;> norm_num

private theorem hsuB_TC_od (k : Fin 6) :
    hsuCMTorus.baseChange ℂ (hsuBu ⟨2 * k.val + 1, by omega⟩) =
      (-3 * hsuPeriodSign k) • hsuBu ⟨2 * k.val, by omega⟩ := by
  rw [LinearMap.baseChange_tmul, hsuB_T_od, TensorProduct.tmul_smul, hsuB_qsmul, hsuPeriodSign]
  split_ifs <;> norm_num

private theorem hsuB_T_vec (k : Fin 6) :
    hsuCMTorus.baseChange ℂ (hsuPeriodVec k) = root • hsuPeriodVec k := by
  have h1 := hsuB_sign_sq k
  have h2 := hsuB_root_mul_root
  rw [hsuB_vec_eq, map_add, map_smul, hsuB_TC_ev, hsuB_TC_od, smul_add, smul_smul,
    smul_smul]
  rw [add_comm]
  congr 1
  · congr 1
    linear_combination -hsuPeriodSign k * h2
  · congr 1
    linear_combination root * h1

private theorem hsuB_T_vecBar (k : Fin 6) :
    hsuCMTorus.baseChange ℂ (hsuPeriodVecBar k) = (-root) • hsuPeriodVecBar k := by
  have h1 := hsuB_sign_sq k
  have h2 := hsuB_root_mul_root
  rw [hsuB_vecBar_eq, map_add, map_smul, hsuB_TC_ev, hsuB_TC_od, smul_add, smul_smul,
    smul_smul]
  rw [add_comm]
  congr 1
  · congr 1
    linear_combination -hsuPeriodSign k * h2
  · congr 1
    linear_combination -root * h1

private theorem hsuB_sqrt3_ne_zero : (Real.sqrt 3 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))

private theorem hsuB_eq_on_span {v : Fin 6 → ℂ ⊗[ℚ] (Fin 12 → ℚ)}
    (f g : Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))) (h : ∀ k, f (v k) = g (v k))
    {x : ℂ ⊗[ℚ] (Fin 12 → ℚ)} (hx : x ∈ Submodule.span ℂ (Set.range v)) : f x = g x := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  simp only [map_sum, map_smul, h]

theorem spec_hsuCMHodge_gradingOperator_eq_aux :
    gradingOperator hsuCMHodge spec_hsuCMHodge_isInternal_aux =
      ((Real.sqrt 3 : ℂ)⁻¹) • hsuCMTorus.baseChange ℂ := by
  have hs : (Real.sqrt 3 : ℂ)⁻¹ * root = Complex.I := by
    rw [root]; field_simp [hsuB_sqrt3_ne_zero]
  refine linearMap_ext_of_isInternal spec_hsuCMHodge_isInternal_aux fun pq x hx => ?_
  obtain ⟨p, q⟩ := pq
  rw [gradingOperator_apply_of_mem _ _ hx]
  simp only [hsuCMHodge] at hx
  split_ifs at hx with h1 h2
  · simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    refine hsuB_eq_on_span ((Complex.I * (((1 : ℤ) : ℂ) - ((0 : ℤ) : ℂ))) • LinearMap.id) _
      (fun k => ?_) hx
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hsuB_T_vec, smul_smul, hs, LinearMap.id_apply]
    norm_num
  · simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    refine hsuB_eq_on_span ((Complex.I * (((0 : ℤ) : ℂ) - ((1 : ℤ) : ℂ))) • LinearMap.id) _
      (fun k => ?_) hx
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hsuB_T_vecBar, smul_smul, mul_neg, hs,
      LinearMap.id_apply]
    norm_num
  · rw [(Submodule.mem_bot ℂ).mp hx]
    simp


private theorem hsuB_torus_comp_J : hsuCMTorus.comp hsuJ = hsuJ.comp hsuCMTorus := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hsuB_torus_apply, hsuJ_apply, hsuJ_apply,
    hsuB_torus_apply]
  funext i
  fin_cases i <;> simp

private theorem hsuB_torus_skew (x y : Fin 12 → ℚ) :
    hsuE (hsuCMTorus x) y = -hsuE x (hsuCMTorus y) := by
  rw [hsuE_apply, hsuE_apply, hsuB_torus_apply, hsuB_torus_apply]
  simp
  ring

private theorem hsuB_torus_baseChange_skew (x y : ℂ ⊗[ℚ] (Fin 12 → ℚ)) :
    hsuE.baseChange ℂ (hsuCMTorus.baseChange ℂ x) y =
      -hsuE.baseChange ℂ x (hsuCMTorus.baseChange ℂ y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', neg_add]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy', neg_add]
    | tmul b y =>
      simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hsuB_torus_skew,
        neg_smul]

/-- The `√-3` eigenvector `√-3 e₂ₖ + e₂ₖ₊₁` of `J_ℂ` in block `k`. -/
private def hsuBg (k : Fin 6) : ℂ ⊗[ℚ] (Fin 12 → ℚ) :=
  root • hsuBu ⟨2 * k.val, by omega⟩ + hsuBu ⟨2 * k.val + 1, by omega⟩

private theorem hsuB_J_g (k : Fin 6) : hsuJ.baseChange ℂ (hsuBg k) = root • hsuBg k := by
  have h2 := hsuB_root_mul_root
  rw [hsuBg, map_add, map_smul, hsuB_JC_ev, hsuB_JC_od, smul_add, smul_smul, add_comm, h2]

private theorem hsuB_T_g (k : Fin 6) :
    hsuCMTorus.baseChange ℂ (hsuBg k) = (hsuPeriodSign k * root) • hsuBg k := by
  have h2 := hsuB_root_mul_root
  rw [hsuBg, map_add, map_smul, hsuB_TC_ev, hsuB_TC_od, smul_add, smul_smul, smul_smul,
    add_comm]
  congr 1
  · congr 1
    linear_combination -hsuPeriodSign k * h2
  · congr 1
    ring

private theorem hsuBcrd_g (i l : Fin 6) :
    hsuBcrd ⟨2 * i.val + 1, by omega⟩ (hsuBg l) = if l = i then 1 else 0 := by
  rw [hsuBg, map_add, map_smul, hsuBcrd_u, hsuBcrd_u]
  simp only [Fin.ext_iff]
  split_ifs <;> first | omega | simp

private abbrev hsuBW := Module.End.eigenspace (hsuJ.baseChange ℂ) root

private abbrev hsuBSplit := polarizedSplitting hsuE spec_hsuE_nondegenerate hsuJ
  spec_hsuJ_sq spec_hsuE_skew

private theorem hsuB_finrank_W : Module.finrank ℂ hsuBW = 6 := by
  have h := hsuBSplit.finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Module.finrank_prod, Subspace.dual_finrank_eq] at h
  change Module.finrank ℂ (Module.End.eigenspace (hsuJ.baseChange ℂ) root) = 6
  omega

private def hsuBgW (k : Fin 6) : hsuBW :=
  ⟨hsuBg k, Module.End.mem_eigenspace_iff.mpr (hsuB_J_g k)⟩

private theorem hsuB_linearIndependent_gW : LinearIndependent ℂ hsuBgW :=
  LinearIndependent.of_comp hsuBW.subtype (hsuB_linearIndependent_of_crd _ hsuBcrd_g)

private def hsuBbW : Module.Basis (Fin 6) ℂ hsuBW :=
  basisOfLinearIndependentOfCardEqFinrank hsuB_linearIndependent_gW
    (by rw [Fintype.card_fin, hsuB_finrank_W])

private theorem hsuB_firstBlock_apply (X : Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))) (x : hsuBW)
    (hX : X x ∈ hsuBW) :
    firstBlock hsuBW (hsuBSplit.conj X) x = ⟨X x, hX⟩ := by
  have h1 : hsuBSplit.symm (x, 0) = (x : ℂ ⊗[ℚ] (Fin 12 → ℚ)) := by
    rw [polarizedSplitting_symm_apply, map_zero]
    simp
  have h2 : hsuBSplit (X x) = (⟨X x, hX⟩, 0) :=
    polarizedSplitting_pos _ _ _ _ _ ⟨X x, hX⟩
  simp only [firstBlock, LinearMap.comp_apply, LinearEquiv.conj_apply, LinearMap.inl_apply,
    LinearEquiv.coe_coe, h1, h2, LinearMap.fst_apply]

theorem spec_hsuCMHodge_gradingOperator_mem_complexSU_aux :
    gradingOperator hsuCMHodge spec_hsuCMHodge_isInternal_aux ∈
      complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq spec_hsuE_skew := by
  rw [spec_hsuCMHodge_gradingOperator_eq_aux,
    mem_complexSU _ _ _ _ _ spec_hsuE_isAlt_aux]
  set s : ℂ := (Real.sqrt 3 : ℂ)⁻¹
  have hcomm : (hsuCMTorus.baseChange ℂ).comp (hsuJ.baseChange ℂ) =
      (hsuJ.baseChange ℂ).comp (hsuCMTorus.baseChange ℂ) := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hsuB_torus_comp_J]
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearMap.smul_comp, LinearMap.comp_smul, hcomm]
  · intro x y
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, map_smul,
      hsuB_torus_baseChange_skew, smul_neg]
  · have hW : ∀ k, (s • hsuCMTorus.baseChange ℂ) (hsuBbW k : ℂ ⊗[ℚ] (Fin 12 → ℚ)) ∈ hsuBW := by
      intro k
      rw [Module.End.mem_eigenspace_iff, ← LinearMap.comp_apply, LinearMap.comp_smul, ← hcomm,
        ← LinearMap.smul_comp, LinearMap.comp_apply, Module.End.mem_eigenspace_iff.mp
          (hsuBbW k).2, map_smul]
    have hval : ∀ k, firstBlock hsuBW (hsuBSplit.conj (s • hsuCMTorus.baseChange ℂ))
        (hsuBbW k) = (s * (hsuPeriodSign k * root)) • hsuBbW k := by
      intro k
      rw [hsuB_firstBlock_apply _ _ (hW k)]
      apply Subtype.ext
      simp only [hsuBbW, coe_basisOfLinearIndependentOfCardEqFinrank, hsuBgW,
        LinearMap.smul_apply, hsuB_T_g, smul_smul, SetLike.val_smul]
    rw [LinearMap.trace_eq_matrix_trace ℂ hsuBbW, Matrix.trace]
    simp only [Matrix.diag, LinearMap.toMatrix_apply, hval]
    simp only [map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    simp [Fin.sum_univ_succ, hsuPeriodSign]

theorem spec_hsuWeilTriple_hodge_hsuCMHodge_aux :
    ∀ i, (hsuWeilTriple i).2 ∈
      LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal_aux)
        (MixedTensorOfType (Fin 12 → ℚ) (hsuWeilTriple i).1) := by
  refine (spec_hodge_iff_gradingOperator_mem_mixedTensorStabilizer_aux hsuWeilTriple).mpr ?_
  rw [spec_mixedTensorStabilizer_hsuWeilTriple_aux, LieSubalgebra.mem_toSubmodule]
  exact spec_hsuCMHodge_gradingOperator_mem_complexSU_aux

theorem spec_hodgeLieAlgebra_hsuCMHodge_aux :
    (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal_aux).toSubmodule = ℚ ∙ hsuCMTorus := by
  have hC := spec_hsuCMHodge_gradingOperator_eq_aux
  have hs : ((Real.sqrt 3 : ℂ)⁻¹) ≠ 0 := by
    refine inv_ne_zero ?_
    rw [Complex.ofReal_ne_zero]
    positivity
  have hle : hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal_aux ≤
      lineLieSubalgebra hsuCMTorus := by
    refine hodgeLieAlgebra_le _ _ ?_
    rw [hC]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨hsuCMTorus, Submodule.mem_span_singleton_self hsuCMTorus, rfl⟩)
  have hT0 : hsuCMTorus ≠ 0 := by
    intro h
    have h1 := congrArg (fun f : Module.End ℚ (Fin 12 → ℚ) => f (Pi.single 1 1) 0) h
    simp [hsuCMTorus, hsuCMTorus₁₂, hsuJ₁₂, Matrix.toLin'_apply, Matrix.mulVec_single] at h1
  have hne : (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal_aux).toSubmodule ≠ ⊥ := by
    intro hbot
    have hmem :=
      gradingOperator_mem_span_hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal_aux
    rw [hbot, Submodule.bot_coe, Set.image_singleton, LinearMap.baseChange_zero,
      Submodule.span_zero_singleton, Submodule.mem_bot, hC, smul_eq_zero] at hmem
    rcases hmem with h | h
    · exact hs h
    · exact hT0 (LinearMap.baseChangeHom_injective (R := ℚ) (S := ℂ) (M := Fin 12 → ℚ)
        (N := Fin 12 → ℚ) (by simpa using h))
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [finrank_span_singleton hT0, Nat.one_le_iff_ne_zero]
  intro h0
  exact hne (Submodule.finrank_eq_zero.mp h0)

theorem spec_hsuCMHodge_hSU_fails_aux :
    complexSpan (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal_aux).toSubmodule ≠
      (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq spec_hsuE_skew).toSubmodule := by
  intro h
  have h35 := spec_finrank_hsu_complexSU
  rw [← h, spec_hodgeLieAlgebra_hsuCMHodge_aux] at h35
  have hle : complexSpan (ℚ ∙ hsuCMTorus) ≤ ℂ ∙ hsuCMTorus.baseChange ℂ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨X, hX, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hX
    refine Submodule.mem_span_singleton.mpr ⟨(a : ℂ), ?_⟩
    dsimp only
    rw [LinearMap.baseChange_smul, ← Rat.cast_smul_eq_qsmul ℂ]
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank ℂ (ℂ ∙ hsuCMTorus.baseChange ℂ) ≤ 1 := by
    simpa using finrank_span_le_card ({hsuCMTorus.baseChange ℂ} : Set _)
  have h3 := h1.trans h2
  omega

end CMHodge

section Assembly

variable {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))} {hH : DirectSum.IsInternal H}

theorem spec_hsu_hodgeLieAlgebra_le_complexSU_aux
    (ht : ∀ i, (hsuWeilTriple i).2 ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH)
      (MixedTensorOfType (Fin 12 → ℚ) (hsuWeilTriple i).1)) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule ≤
      (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq spec_hsuE_skew).toSubmodule := by
  rw [← spec_mixedTensorStabilizer_hsuWeilTriple_aux]
  exact spec_hodgeLieAlgebra_le_mixedTensorStabilizer hsuWeilTriple ht

theorem spec_hsu_hSU_of_weilTriple_and_generators_aux {m : ℕ}
    (g : Fin m → Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ)))
    (ht : ∀ i, (hsuWeilTriple i).2 ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH)
      (MixedTensorOfType (Fin 12 → ℚ) (hsuWeilTriple i).1))
    (hgenerate : (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq
      spec_hsuE_skew).toSubmodule ≤ Submodule.span ℂ (Set.range g))
    (hg : ∀ i, g i ∈ complexSpan (hodgeLieAlgebra H hH).toSubmodule) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule =
      (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq spec_hsuE_skew).toSubmodule := by
  exact spec_hSU_of_mixedTensorStabilizer_and_generators hsuWeilTriple _ g ht
    spec_mixedTensorStabilizer_hsuWeilTriple_aux hgenerate hg

end Assembly

end HodgeLean.Foundations
