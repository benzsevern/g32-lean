import HodgeLean.Foundations.HSUTensorsDefs

/-! # Proofs for the bounded mixed tensor `hSU` specification

All seventeen `_aux` theorems are proved; three parallel provers wrote them (statements 1-6,
7-12 and 13-17). -/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HodgeLean.Foundations.SchurWeyl.dualAddCommGroup

namespace HodgeLean.Foundations

open WeilPower SchurWeyl
open scoped TensorProduct

section Mixed

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem spec_mixedTensorStabilizer_const_aux {a b n : ℕ}
    (t : Fin n → MixedTensorOfType V (a, b)) :
    mixedTensorStabilizer (fun i => (⟨(a, b), t i⟩ : BoundedTensor V)) =
      finiteTensorStabilizer t := by
  rfl

theorem lieAnnihilator_directSum_of {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ (M i)]
    [∀ i, LieRingModule (Module.End ℚ V) (M i)] [∀ i, LieModule ℚ (Module.End ℚ V) (M i)]
    (i : ι) (v : M i) :
    lieAnnihilator (V := V) (DirectSum ι M) (DirectSum.of M i v) =
      lieAnnihilator (V := V) (M i) v := by
  ext X
  rw [mem_lieAnnihilator, mem_lieAnnihilator]
  constructor
  · intro h
    have := congrArg (fun w : DirectSum ι M => w i) h
    simpa only [DirectSum.lie_module_bracket_apply, DirectSum.of_eq_same,
      DirectSum.zero_apply] using this
  · intro h
    ext j
    rw [DirectSum.lie_module_bracket_apply, DirectSum.zero_apply]
    by_cases hij : i = j
    · subst hij
      rw [DirectSum.of_eq_same, h]
    · rw [DirectSum.of_eq_of_ne i j v (Ne.symm hij), lie_zero]

theorem spec_mixedTensorStabilizer_eq_directSum_aux {n : ℕ} (t : Fin n → BoundedTensor V) :
    mixedTensorStabilizer t =
      finiteTensorStabilizer (N := DirectSum (Fin n) fun i => MixedTensorOfType V (t i).1)
        (fun i => DirectSum.of (fun i => MixedTensorOfType V (t i).1) i (t i).2) := by
  unfold mixedTensorStabilizer finiteTensorStabilizer
  congr 3
  funext i
  exact (lieAnnihilator_directSum_of (M := fun i => MixedTensorOfType V (t i).1) i
    (t i).2).symm

theorem lie_vecTensor (X : Module.End ℚ V) (v : V) :
    ⁅X, vecTensor v⁆ = vecTensor (X v) := by
  rw [lie_mixedTensor, mixedLie_apply, vecTensor, vecTensor]
  simp [tensorDer_apply, slot_tprod, Function.update_eq_const_of_subsingleton]
  rfl

theorem vecTensor_eq_zero_iff (v : V) : vecTensor v = 0 ↔ v = 0 := by
  constructor
  · intro h
    let ψ : MixedTensorOfType V (1, 0) →ₗ[ℚ] V :=
      (TensorProduct.rid ℚ V).toLinearMap ∘ₗ
        TensorProduct.map (PiTensorProduct.subsingletonEquiv (R := ℚ)
          (s := fun _ : Fin 1 => V) (0 : Fin 1)).toLinearMap
          (PiTensorProduct.isEmptyEquiv (R := ℚ) (s := fun _ : Fin 0 => Module.Dual ℚ V)
            (Fin 0)).toLinearMap
    have hψ : ψ (vecTensor v) = v := by
      simp [ψ, vecTensor]
    rw [← hψ, h, map_zero]
  · rintro rfl
    have h : PiTensorProduct.tprod ℚ (fun _ : Fin 1 => (0 : V)) = 0 :=
      (PiTensorProduct.tprod ℚ).map_coord_zero (0 : Fin 1) rfl
    rw [vecTensor, h, TensorProduct.zero_tmul]

theorem spec_finiteTensorStabilizer_vec_aux {n : ℕ} (t : Fin n → V) :
    finiteTensorStabilizer (N := V) t =
      mixedTensorStabilizer (fun i => (⟨(1, 0), vecTensor (t i)⟩ : BoundedTensor V)) := by
  unfold mixedTensorStabilizer finiteTensorStabilizer
  congr 3
  funext i
  ext X
  change X ∈ lieAnnihilator V (t i) ↔ X ∈ lieAnnihilator (MixedTensorOfType V (1, 0)) _
  rw [mem_lieAnnihilator, mem_lieAnnihilator, lie_vecTensor, vecTensor_eq_zero_iff]
  rfl

theorem complexAction_commutator {N : Type*} [AddCommGroup N] [Module ℚ N]
    [LieRingModule (Module.End ℚ V) N] [LieModule ℚ (Module.End ℚ V) N] [FiniteDimensional ℚ V]
    (X Y : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    complexAction N (X * Y - Y * X) =
      complexAction N X * complexAction N Y - complexAction N Y * complexAction N X := by
  have hspan : ∀ Z : Module.End ℂ (ℂ ⊗[ℚ] V),
      Z ∈ Submodule.span ℂ ((fun A : Module.End ℚ V => A.baseChange ℂ) '' Set.univ) := by
    intro Z
    have : Z ∈ complexSpan (⊤ : Submodule ℚ (Module.End ℚ V)) := by
      rw [complexSpan_top]; trivial
    simpa [complexSpan] using this
  have hbase : ∀ A B : Module.End ℚ V,
      complexAction N (A.baseChange ℂ * B.baseChange ℂ - B.baseChange ℂ * A.baseChange ℂ) =
        complexAction N (A.baseChange ℂ) * complexAction N (B.baseChange ℂ) -
          complexAction N (B.baseChange ℂ) * complexAction N (A.baseChange ℂ) := by
    intro A B
    have h1 : A.baseChange ℂ * B.baseChange ℂ - B.baseChange ℂ * A.baseChange ℂ =
        (A * B - B * A).baseChange ℂ := by
      rw [LinearMap.baseChange_sub, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.baseChange_comp,
        LinearMap.baseChange_comp]
    have h2 : LieModule.toEnd ℚ (Module.End ℚ V) N (A * B - B * A) =
        LieModule.toEnd ℚ (Module.End ℚ V) N A * LieModule.toEnd ℚ (Module.End ℚ V) N B -
          LieModule.toEnd ℚ (Module.End ℚ V) N B * LieModule.toEnd ℚ (Module.End ℚ V) N A := by
      rw [← Ring.lie_def, LieHom.map_lie, Ring.lie_def]
    rw [h1, complexAction_baseChange, complexAction_baseChange, complexAction_baseChange, h2,
      LinearMap.baseChange_sub, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.baseChange_comp,
      LinearMap.baseChange_comp]
  have hleft : ∀ A : Module.End ℚ V, ∀ Y : Module.End ℂ (ℂ ⊗[ℚ] V),
      complexAction N (A.baseChange ℂ * Y - Y * A.baseChange ℂ) =
        complexAction N (A.baseChange ℂ) * complexAction N Y -
          complexAction N Y * complexAction N (A.baseChange ℂ) := by
    intro A Y
    induction hspan Y using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨B, -, rfl⟩ := hx
      exact hbase A B
    | zero => simp
    | add x y _ _ hx hy =>
      rw [mul_add, add_mul, add_sub_add_comm, map_add, hx, hy, map_add, mul_add, add_mul]
      abel
    | smul c x _ hx =>
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, map_smul, hx, map_smul, mul_smul_comm,
        smul_mul_assoc, smul_sub]
  induction hspan X using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨A, -, rfl⟩ := hx
    exact hleft A Y
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add, add_mul, add_sub_add_comm, map_add, hx, hy, map_add, mul_add, add_mul]
    abel
  | smul c x _ hx =>
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, map_smul, hx, map_smul, mul_smul_comm,
      smul_mul_assoc, smul_sub]

theorem spec_complexAction_mixed_lie_aux [FiniteDimensional ℚ V] (ab : ℕ × ℕ)
    (X Y : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    complexAction (MixedTensorOfType V ab) (X * Y - Y * X) =
      complexAction (MixedTensorOfType V ab) X * complexAction (MixedTensorOfType V ab) Y -
        complexAction (MixedTensorOfType V ab) Y * complexAction (MixedTensorOfType V ab) X :=
  complexAction_commutator X Y

variable [FiniteDimensional ℚ V]
  {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)} {hH : DirectSum.IsInternal H}

theorem spec_hodgeLieAlgebra_le_mixedTensorStabilizer_aux {n : ℕ}
    (t : Fin n → BoundedTensor V)
    (ht : ∀ i, (t i).2 ∈
      LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) (MixedTensorOfType V (t i).1)) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule ≤ mixedTensorStabilizer t := by
  have hle : hodgeLieAlgebra H hH ≤ ⨅ i, lieAnnihilator (MixedTensorOfType V (t i).1) (t i).2 := by
    refine le_iInf fun i X hX => ?_
    rw [mem_lieAnnihilator]
    have := (LieModule.mem_maxTrivSubmodule (R := ℚ) (L := hodgeLieAlgebra H hH)
      (M := MixedTensorOfType V (t i).1) _).mp (ht i) ⟨X, hX⟩
    simpa using this
  exact Submodule.span_mono (Set.image_mono hle)

theorem spec_hSU_of_mixedTensorStabilizer_and_generators_aux {n m : ℕ}
    (t : Fin n → BoundedTensor V)
    (L : LieSubalgebra ℂ (Module.End ℂ (ℂ ⊗[ℚ] V)))
    (g : Fin m → Module.End ℂ (ℂ ⊗[ℚ] V))
    (ht : ∀ i, (t i).2 ∈
      LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) (MixedTensorOfType V (t i).1))
    (hstabilizer : mixedTensorStabilizer t = L.toSubmodule)
    (hgenerate : L.toSubmodule ≤ Submodule.span ℂ (Set.range g))
    (hg : ∀ i, g i ∈ complexSpan (hodgeLieAlgebra H hH).toSubmodule) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule = L.toSubmodule := by
  apply le_antisymm
  · exact hstabilizer ▸ spec_hodgeLieAlgebra_le_mixedTensorStabilizer_aux t ht
  · exact hgenerate.trans (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hg i))

end Mixed

section Candidate

/-- The Weil operator of the candidate, coordinatewise. -/
theorem hsuJ_apply (x : Fin 12 → ℚ) :
    hsuJ x = ![-3 * x 1, x 0, -3 * x 3, x 2, -3 * x 5, x 4, -3 * x 7, x 6, -3 * x 9, x 8,
      -3 * x 11, x 10] := by
  funext i
  fin_cases i <;>
    simp [hsuJ, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hsuJ₁₂]

/-- The polarization of the candidate, coordinatewise. -/
theorem hsuE_apply (x y : Fin 12 → ℚ) :
    hsuE x y = (x 0 * y 1 - x 1 * y 0) + (x 2 * y 3 - x 3 * y 2) + (x 4 * y 5 - x 5 * y 4)
      - (x 6 * y 7 - x 7 * y 6) - (x 8 * y 9 - x 9 * y 8) - 2 * (x 10 * y 11 - x 11 * y 10) := by
  simp [hsuE, Matrix.toBilin'_apply', Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hsuE₁₂,
    hsuWeights]
  ring

theorem spec_hsuJ_sq_aux : hsuJ.comp hsuJ = (-3 : ℚ) • LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, hsuJ_apply, hsuJ_apply]
  funext i
  fin_cases i <;> simp

theorem spec_hsuE_isAlt_aux : hsuE.IsAlt := by
  exact fun x => by rw [hsuE_apply]; ring

theorem spec_hsuE_skew_aux : ∀ x y, hsuE (hsuJ x) y = -hsuE x (hsuJ y) := by
  intro x y
  rw [hsuE_apply, hsuE_apply, hsuJ_apply, hsuJ_apply]
  simp
  ring

theorem spec_hsuE_rosati_aux : ∀ x y, hsuE (hsuJ x) (hsuJ y) = 3 * hsuE x y := by
  intro x y
  rw [hsuE_apply, hsuE_apply, hsuJ_apply, hsuJ_apply]
  simp
  ring

/-- The polarization of the candidate separates points on the left. -/
theorem hsuE_separatingLeft (x : Fin 12 → ℚ) (h : ∀ y, hsuE x y = 0) : x = 0 := by
  funext i
  fin_cases i
  all_goals first
    | (have := h (Pi.single 1 1); simp [hsuE_apply] at this; simpa using this)
    | (have := h (Pi.single 0 1); simp [hsuE_apply] at this; simpa using this)
    | (have := h (Pi.single 3 1); simp [hsuE_apply] at this; simpa using this)
    | (have := h (Pi.single 2 1); simp [hsuE_apply] at this; simpa using this)
    | (have := h (Pi.single 5 1); simp [hsuE_apply] at this; simpa using this)
    | (have := h (Pi.single 4 1); simp [hsuE_apply] at this; simpa using this)
    | (have := h (Pi.single 7 1); simp [hsuE_apply] at this; simpa using this)
    | (have := h (Pi.single 6 1); simp [hsuE_apply] at this; simpa using this)
    | (have := h (Pi.single 9 1); simp [hsuE_apply] at this; simpa using this)
    | (have := h (Pi.single 8 1); simp [hsuE_apply] at this; simpa using this)
    | (have := h (Pi.single 11 1); simp [hsuE_apply] at this; simpa using this)
    | (have := h (Pi.single 10 1); simp [hsuE_apply] at this; simpa using this)

theorem spec_hsuE_nondegenerate_aux : hsuE.Nondegenerate := by
  refine ⟨hsuE_separatingLeft, fun y h => hsuE_separatingLeft y fun x => ?_⟩
  have hx := h x
  rw [hsuE_apply] at hx ⊢
  linarith

theorem spec_hsuE_hermitian_diag_aux (k l : Fin 6) :
    hsuE (Pi.single ⟨2 * k.val, by omega⟩ 1) (hsuJ (Pi.single ⟨2 * l.val, by omega⟩ 1)) =
        (if k = l then hsuWeights k else 0) ∧
      hsuE (Pi.single ⟨2 * k.val, by omega⟩ 1) (Pi.single ⟨2 * l.val, by omega⟩ 1) = 0 := by
  rw [hsuE_apply, hsuE_apply, hsuJ_apply]
  fin_cases k <;> fin_cases l <;> simp [hsuWeights]

section LaneC

open PiTensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- `v ↦ v` in `⨂[ℚ] _ : Fin 1, V`, as a linear map. -/
private abbrev hsuS1 {M : Type*} [AddCommGroup M] [Module ℚ M] : M →ₗ[ℚ] ⨂[ℚ] _ : Fin 1, M :=
  (PiTensorProduct.subsingletonEquiv (R := ℚ) (s := fun _ : Fin 1 => M) 0).symm.toLinearMap

private theorem hsuS1_apply {M : Type*} [AddCommGroup M] [Module ℚ M] (v : M) :
    hsuS1 v = tprod ℚ (fun _ : Fin 1 => v) := by
  simp only [hsuS1, LinearEquiv.coe_coe, subsingletonEquiv_symm_apply]
  congr 1
  funext i
  fin_cases i
  simp

/-- The bilinear map `(v, φ) ↦ v ⊗ φ` into `T^{1,1}(V)`. -/
private abbrev hsuBeta : V →ₗ[ℚ] Module.Dual ℚ V →ₗ[ℚ] MixedTensorOfType V (1, 1) :=
  (TensorProduct.mk ℚ _ _).compl₁₂ hsuS1 hsuS1

private theorem hsuBeta_apply (v : V) (φ : Module.Dual ℚ V) :
    hsuBeta v φ = tprod ℚ (fun _ : Fin 1 => v) ⊗ₜ tprod ℚ (fun _ : Fin 1 => φ) := by
  simp [hsuBeta, hsuS1_apply]

private theorem hsu_lie_beta (X : Module.End ℚ V) (v : V) (φ : Module.Dual ℚ V) :
    ⁅X, hsuBeta v φ⁆ = hsuBeta (X v) φ - hsuBeta v (φ ∘ₗ X) := by
  rw [hsuBeta_apply, hsuBeta_apply, hsuBeta_apply]
  change mixedLie ℚ V (Fin 1) (Fin 1) X _ = _
  rw [mixedLie_apply]
  simp [tensorDer_tprod, Function.update_eq_const_of_subsingleton]
  rfl

variable {ι : Type*} [Fintype ι]

private theorem hsuEndTensor_eq (b : Module.Basis ι ℚ V) (A : Module.End ℚ V) :
    endTensor b A = ∑ j, hsuBeta (A (b j)) (b.coord j) := by
  simp [endTensor]

private theorem hsu_sum_beta_comp (b : Module.Basis ι ℚ V) (T X : Module.End ℚ V) :
    ∑ j, hsuBeta (T (b j)) (b.coord j ∘ₗ X) = ∑ j, hsuBeta (T (X (b j))) (b.coord j) := by
  have h (j : ι) : b.coord j ∘ₗ X = ∑ k, b.coord j (X (b k)) • b.coord k := by
    exact (b.sum_dual_apply_smul_coord _).symm
  simp_rw [h, map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← b.sum_repr (X (b k))]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply]

private theorem hsu_lie_endTensor (b : Module.Basis ι ℚ V) (X A : Module.End ℚ V) :
    ⁅X, endTensor b A⁆ = endTensor b (X * A - A * X) := by
  rw [hsuEndTensor_eq, hsuEndTensor_eq, lie_sum]
  simp_rw [hsu_lie_beta]
  rw [Finset.sum_sub_distrib, hsu_sum_beta_comp]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, LinearMap.sub_apply,
    Finset.sum_sub_distrib]

private theorem hsu_endTensor_eq_zero (b : Module.Basis ι ℚ V) (A : Module.End ℚ V)
    (h : endTensor b A = 0) : A = 0 := by
  classical
  let ev : ι → ι → MixedTensorOfType V (1, 1) →ₗ[ℚ] ℚ := fun k l =>
    TensorProduct.lift ((LinearMap.mul ℚ ℚ).compl₁₂
      (b.coord k ∘ₗ (PiTensorProduct.subsingletonEquiv (R := ℚ) (s := fun _ : Fin 1 => V) 0).toLinearMap)
      ((LinearMap.applyₗ (b l)) ∘ₗ
        (PiTensorProduct.subsingletonEquiv (R := ℚ) (s := fun _ : Fin 1 => Module.Dual ℚ V) 0).toLinearMap))
  have hev (k l : ι) (v : V) (φ : Module.Dual ℚ V) : ev k l (hsuBeta v φ) = b.coord k v * φ (b l) := by
    simp [ev, hsuBeta]
  have hA (k l : ι) : b.coord k (A (b l)) = 0 := by
    have := congrArg (ev k l) h
    rw [hsuEndTensor_eq, map_sum, map_zero] at this
    simp_rw [hev, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] at this
    simpa using this
  apply b.ext
  intro l
  apply b.ext_elem
  intro k
  simpa using hA k l

private theorem hsu_update_vec2_zero {M : Type*} (a b c : M) :
    Function.update ![a, b] 0 c = ![c, b] := by
  funext i; fin_cases i <;> rfl

private theorem hsu_update_vec2_one {M : Type*} (a b c : M) :
    Function.update ![a, b] 1 c = ![a, c] := by
  funext i; fin_cases i <;> rfl

/-- The bilinear map `(φ, ψ) ↦ 1 ⊗ φ ⊗ ψ` into `T^{0,2}(V)`. -/
private def hsuGamma : Module.Dual ℚ V →ₗ[ℚ] Module.Dual ℚ V →ₗ[ℚ] MixedTensorOfType V (0, 2) :=
  LinearMap.mk₂ ℚ (fun φ ψ => tprod ℚ (fun k : Fin 0 => k.elim0) ⊗ₜ tprod ℚ ![φ, ψ])
    (fun φ φ' ψ => by
      rw [← TensorProduct.tmul_add]; congr 1
      have := (PiTensorProduct.tprod ℚ).map_update_add ![0, ψ] 0 φ φ'
      simpa only [hsu_update_vec2_zero] using this)
    (fun c φ ψ => by
      rw [← TensorProduct.tmul_smul]; congr 1
      have := (PiTensorProduct.tprod ℚ).map_update_smul ![0, ψ] 0 c φ
      simpa only [hsu_update_vec2_zero] using this)
    (fun φ ψ ψ' => by
      rw [← TensorProduct.tmul_add]; congr 1
      have := (PiTensorProduct.tprod ℚ).map_update_add ![φ, 0] 1 ψ ψ'
      simpa only [hsu_update_vec2_one] using this)
    (fun c φ ψ => by
      rw [← TensorProduct.tmul_smul]; congr 1
      have := (PiTensorProduct.tprod ℚ).map_update_smul ![φ, 0] 1 c ψ
      simpa only [hsu_update_vec2_one] using this)

private theorem hsuGamma_apply (φ ψ : Module.Dual ℚ V) :
    hsuGamma φ ψ = tprod ℚ (fun k : Fin 0 => k.elim0) ⊗ₜ tprod ℚ ![φ, ψ] := rfl

private theorem hsu_lie_gamma (X : Module.End ℚ V) (φ ψ : Module.Dual ℚ V) :
    ⁅X, hsuGamma φ ψ⁆ = -(hsuGamma (φ ∘ₗ X) ψ + hsuGamma φ (ψ ∘ₗ X)) := by
  rw [hsuGamma_apply, hsuGamma_apply, hsuGamma_apply]
  change mixedLie ℚ V (Fin 0) (Fin 2) X _ = _
  rw [mixedLie_apply]
  simp only [tensorDer_apply, Finset.univ_eq_empty, Finset.sum_empty, LinearMap.rTensor_zero,
    LinearMap.zero_apply, zero_sub, LinearMap.lTensor_tmul, Fin.sum_univ_two,
    LinearMap.add_apply, slot_tprod, hsu_update_vec2_zero, hsu_update_vec2_one,
    TensorProduct.tmul_add, Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.dualMap_apply']

private theorem hsuFormTensor_eq (b : Module.Basis ι ℚ V) (F : LinearMap.BilinForm ℚ V) :
    formTensor b F = ∑ i, ∑ j, F (b i) (b j) • hsuGamma (b.coord i) (b.coord j) := rfl

private theorem hsu_sum_gamma_left (b : Module.Basis ι ℚ V) (F : LinearMap.BilinForm ℚ V)
    (X : Module.End ℚ V) :
    ∑ i, ∑ j, F (b i) (b j) • hsuGamma (b.coord i ∘ₗ X) (b.coord j) =
      ∑ i, ∑ j, F (X (b i)) (b j) • hsuGamma (b.coord i) (b.coord j) := by
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

private theorem hsu_sum_gamma_right (b : Module.Basis ι ℚ V) (F : LinearMap.BilinForm ℚ V)
    (X : Module.End ℚ V) :
    ∑ i, ∑ j, F (b i) (b j) • hsuGamma (b.coord i) (b.coord j ∘ₗ X) =
      ∑ i, ∑ j, F (b i) (X (b j)) • hsuGamma (b.coord i) (b.coord j) := by
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

private theorem hsu_lie_formTensor (b : Module.Basis ι ℚ V) (F : LinearMap.BilinForm ℚ V)
    (X : Module.End ℚ V) :
    ⁅X, formTensor b F⁆ =
      -formTensor b (F.compl₁₂ X LinearMap.id + F.compl₁₂ LinearMap.id X) := by
  rw [hsuFormTensor_eq, hsuFormTensor_eq, lie_sum]
  have hg (φ ψ : Module.Dual ℚ V) := hsu_lie_gamma X φ ψ
  simp_rw [lie_mixedTensor] at hg
  simp_rw [lie_sum, lie_mixedTensor, map_smul, hg, smul_neg, smul_add, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, hsu_sum_gamma_left, hsu_sum_gamma_right]
  simp [add_smul, Finset.sum_add_distrib]

private theorem hsu_formTensor_apply_eq_zero (b : Module.Basis ι ℚ V)
    (F : LinearMap.BilinForm ℚ V) (h : formTensor b F = 0) (k l : ι) : F (b k) (b l) = 0 := by
  classical
  let ev : MixedTensorOfType V (0, 2) →ₗ[ℚ] ℚ :=
    LinearMap.applyₗ (PiTensorProduct.tprod ℚ ![b k, b l]) ∘ₗ PiTensorProduct.dualDistrib ∘ₗ
      (TensorProduct.lid ℚ _).toLinearMap ∘ₗ
      (PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℚ) (s := fun _ => V)).toLinearMap.rTensor _
  have hev (φ ψ : Module.Dual ℚ V) : ev (hsuGamma φ ψ) = φ (b k) * ψ (b l) := by
    simp only [ev, hsuGamma_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.rTensor_tmul, LinearEquiv.coe_coe, PiTensorProduct.isEmptyEquiv_apply_tprod,
      TensorProduct.lid_tmul, one_smul, LinearMap.applyₗ_apply_apply]
    rw [PiTensorProduct.dualDistrib_apply]
    simp [Fin.prod_univ_two]
  have := congrArg ev h
  rw [hsuFormTensor_eq, map_zero] at this
  simp only [map_sum, map_smul, hev, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at this
  simpa using this

private theorem hsu_mem_lieAnnihilator_endTensor (b : Module.Basis ι ℚ V) (A X : Module.End ℚ V) :
    X ∈ lieAnnihilator (MixedTensorOfType V (1, 1)) (endTensor b A) ↔ X * A = A * X := by
  rw [mem_lieAnnihilator, hsu_lie_endTensor]
  constructor
  · intro h; exact sub_eq_zero.mp (hsu_endTensor_eq_zero b _ h)
  · intro h; rw [h, sub_self, hsuEndTensor_eq]; simp

private theorem hsu_mem_lieAnnihilator_formTensor (b : Module.Basis ι ℚ V)
    (F : LinearMap.BilinForm ℚ V) (X : Module.End ℚ V) :
    X ∈ lieAnnihilator (MixedTensorOfType V (0, 2)) (formTensor b F) ↔
      ∀ k l, F (X (b k)) (b l) + F (b k) (X (b l)) = 0 := by
  rw [mem_lieAnnihilator, hsu_lie_formTensor, neg_eq_zero]
  constructor
  · intro h k l
    simpa using hsu_formTensor_apply_eq_zero b _ h k l
  · intro h
    have : F.compl₁₂ X LinearMap.id + F.compl₁₂ LinearMap.id X = 0 :=
      LinearMap.ext_basis b b fun k l => by simpa using h k l
    rw [this]; simp [formTensor]

/-- The complexification of a kernel, computed by a complex map compatible with the rational one
through an injective comparison map. -/
private theorem hsu_complexSpan_ker [FiniteDimensional ℚ V] {M M' : Type*} [AddCommGroup M]
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

end LaneC

section LaneCCandidate

private abbrev hsuB : Module.Basis (Fin 12) ℚ (Fin 12 → ℚ) := Pi.basisFun ℚ (Fin 12)

/-- The commutant of `J_ℂ`. -/
private def hsuCommC : Submodule ℂ (Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))) :=
  LinearMap.ker (LinearMap.mulRight ℂ (hsuJ.baseChange ℂ) - LinearMap.mulLeft ℂ (hsuJ.baseChange ℂ))

private theorem mem_hsuCommC (c : Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))) :
    c ∈ hsuCommC ↔ c.comp (hsuJ.baseChange ℂ) = (hsuJ.baseChange ℂ).comp c := by
  simp [hsuCommC, sub_eq_zero, Module.End.mul_eq_comp]

/-- The skewness defect of `c` for `E_ℂ` on the basis `1 ⊗ eᵢ`. -/
private def hsuSkewMap :
    Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ)) →ₗ[ℂ] (Fin 12 × Fin 12 → ℂ) where
  toFun c p := hsuE.baseChange ℂ (c (1 ⊗ₜ hsuB p.1)) (1 ⊗ₜ hsuB p.2) +
    hsuE.baseChange ℂ (1 ⊗ₜ hsuB p.1) (c (1 ⊗ₜ hsuB p.2))
  map_add' c d := by funext p; simp only [LinearMap.add_apply, map_add, Pi.add_apply]; ring
  map_smul' z c := by
    funext p; simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

private def hsuSkewC : Submodule ℂ (Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))) :=
  LinearMap.ker hsuSkewMap

private theorem mem_hsuSkewC (c : Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))) :
    c ∈ hsuSkewC ↔ ∀ x y, hsuE.baseChange ℂ (c x) y = -hsuE.baseChange ℂ x (c y) := by
  rw [hsuSkewC, LinearMap.mem_ker]
  constructor
  · intro h
    have hB : (hsuE.baseChange ℂ).compl₁₂ c LinearMap.id +
        (hsuE.baseChange ℂ).compl₁₂ LinearMap.id c = 0 := by
      refine LinearMap.ext_basis (Algebra.TensorProduct.basis ℂ hsuB)
        (Algebra.TensorProduct.basis ℂ hsuB) fun k l => ?_
      have := congrFun h (k, l)
      simpa [Algebra.TensorProduct.basis_apply, hsuSkewMap] using this
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply,
      LinearMap.zero_apply] at this
    exact eq_neg_of_add_eq_zero_left this
  · intro h
    funext p
    simp [hsuSkewMap, h]

/-- The rational skewness defect on the standard basis. -/
private def hsuSkewMapQ : Module.End ℚ (Fin 12 → ℚ) →ₗ[ℚ] (Fin 12 × Fin 12 → ℚ) where
  toFun X p := hsuE (X (hsuB p.1)) (hsuB p.2) + hsuE (hsuB p.1) (X (hsuB p.2))
  map_add' X Y := by funext p; simp only [LinearMap.add_apply, map_add, Pi.add_apply]; ring
  map_smul' z X := by
    funext p; simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

private theorem hsu_annJ :
    (lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (1, 1)) hsuJTensor).toSubmodule =
      LinearMap.ker (LinearMap.mulRight ℚ hsuJ - LinearMap.mulLeft ℚ hsuJ) := by
  ext X
  rw [LieSubalgebra.mem_toSubmodule, hsuJTensor, hsu_mem_lieAnnihilator_endTensor]
  simp [sub_eq_zero]

private theorem hsu_annE :
    (lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (0, 2)) hsuETensor).toSubmodule =
      LinearMap.ker hsuSkewMapQ := by
  ext X
  rw [LieSubalgebra.mem_toSubmodule, hsuETensor, hsu_mem_lieAnnihilator_formTensor,
    LinearMap.mem_ker]
  constructor
  · intro h; funext p; exact h p.1 p.2
  · intro h k l; exact congrFun h (k, l)

private theorem hsu_complexSpan_annJ :
    complexSpan (lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (1, 1)) hsuJTensor).toSubmodule =
      hsuCommC := by
  rw [hsu_annJ, hsuCommC]
  refine hsu_complexSpan_ker _ _ (endBaseChangeEquiv (Fin 12 → ℚ)).toLinearMap
    (endBaseChangeEquiv (Fin 12 → ℚ)).injective fun X => ?_
  simp only [LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
    LinearEquiv.coe_coe, endBaseChangeEquiv_apply, tensorProductEnd_one_tmul,
    LinearMap.baseChange_sub, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

private theorem hsu_complexSpan_annE :
    complexSpan (lieAnnihilator (MixedTensorOfType (Fin 12 → ℚ) (0, 2)) hsuETensor).toSubmodule =
      hsuSkewC := by
  rw [hsu_annE, hsuSkewC]
  refine hsu_complexSpan_ker _ _ (TensorProduct.piScalarRight ℚ ℂ ℂ (Fin 12 × Fin 12)).toLinearMap
    (TensorProduct.piScalarRight ℚ ℂ ℂ (Fin 12 × Fin 12)).injective fun X => ?_
  funext p
  simp [hsuSkewMap, hsuSkewMapQ, TensorProduct.piScalarRightHom_tmul,
    LinearMap.BilinForm.baseChange_tmul, add_smul]

private theorem hsu_mem_iInf {κ : Type*} (L : κ → LieSubalgebra ℚ (Module.End ℚ (Fin 12 → ℚ)))
    (X : Module.End ℚ (Fin 12 → ℚ)) : X ∈ ⨅ i, L i ↔ ∀ i, X ∈ L i := by
  rw [iInf, ← SetLike.mem_coe, LieSubalgebra.coe_sInf]
  simp

private theorem hsu_stab_polarizationOnly :
    mixedTensorStabilizer hsuPolarizationOnly = hsuSkewC := by
  rw [mixedTensorStabilizer, ← hsu_complexSpan_annE]
  congr 1
  ext X
  rw [LieSubalgebra.mem_toSubmodule, LieSubalgebra.mem_toSubmodule, hsu_mem_iInf,
    Fin.forall_fin_one]
  rfl

private theorem hsu_stab_weilPair :
    mixedTensorStabilizer hsuWeilPair = hsuCommC ⊓ hsuSkewC := by
  rw [mixedTensorStabilizer, ← hsu_complexSpan_annE, ← hsu_complexSpan_annJ, ← complexSpan_inf]
  congr 1
  ext X
  rw [Submodule.mem_inf, LieSubalgebra.mem_toSubmodule, LieSubalgebra.mem_toSubmodule,
    LieSubalgebra.mem_toSubmodule, hsu_mem_iInf, Fin.forall_fin_two]
  rfl

private theorem hsu_finrank_complexSpan (W : Submodule ℚ (Module.End ℚ (Fin 12 → ℚ))) :
    Module.finrank ℂ (complexSpan W) = Module.finrank ℚ W := by
  have : Module.Free ℚ W := Module.Free.of_divisionRing ℚ W
  rw [complexSpan_eq_map]
  have : (W.baseChange ℂ).map (LinearMap.tensorProductEnd ℚ ℂ (Fin 12 → ℚ)).toLinearMap =
      (W.baseChange ℂ).map (endBaseChangeEquiv (Fin 12 → ℚ) : _ →ₗ[ℂ] _) := rfl
  rw [this, LinearEquiv.finrank_map_eq, Submodule.baseChange, LinearMap.finrank_range_of_inj,
    Module.finrank_baseChange]
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ W.injective_subtype

private abbrev hsuW := Module.End.eigenspace (hsuJ.baseChange ℂ) root

private abbrev hsuSplit := polarizedSplitting hsuE spec_hsuE_nondegenerate_aux hsuJ
  spec_hsuJ_sq_aux spec_hsuE_skew_aux

private theorem hsu_finrank_W : Module.finrank ℂ hsuW = 6 := by
  have h := hsuSplit.finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Module.finrank_prod, Subspace.dual_finrank_eq] at h
  change Module.finrank ℂ (Module.End.eigenspace (hsuJ.baseChange ℂ) root) = 6
  omega

private theorem hsu_finrank_slEnd : Module.finrank ℂ (slEnd ℂ hsuW) = 35 := by
  have h := LinearMap.finrank_range_add_finrank_ker (K := ℂ) (V := Module.End ℂ hsuW)
    (V₂ := ℂ) (LinearMap.trace ℂ hsuW)
  have hr : LinearMap.range (LinearMap.trace ℂ hsuW) = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun z => ⟨(z / 6) • 1, ?_⟩
    rw [map_smul, LinearMap.trace_one, hsu_finrank_W, smul_eq_mul]
    push_cast
    field_simp
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_linearMap, hsu_finrank_W] at h
  exact Nat.eq_sub_of_add_eq' h

private theorem hsuSplit_conj_apply (c : Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ)))
    (x : ℂ ⊗[ℚ] (Fin 12 → ℚ)) : hsuSplit.conj c (hsuSplit x) = hsuSplit (c x) := by
  simp [LinearEquiv.conj_apply]

private theorem hsuSplit_conj_J : hsuSplit.conj (hsuJ.baseChange ℂ) = splitJ hsuW := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := hsuSplit.surjective z
  rw [hsuSplit_conj_apply]
  exact polarizedSplitting_J _ _ _ _ _ x

private theorem hsuSplit_form (z t : ℂ ⊗[ℚ] (Fin 12 → ℚ)) :
    hsuE.baseChange ℂ z t = splitForm hsuW (hsuSplit z) (hsuSplit t) :=
  polarizedSplitting_form _ _ _ _ _ spec_hsuE_isAlt_aux z t

private theorem hsu_map_commSkew :
    (hsuCommC ⊓ hsuSkewC).map (hsuSplit.conj : Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ)) →ₗ[ℂ] _) =
      LinearMap.range (blockLie hsuW).toLinearMap := by
  ext Y
  constructor
  · rintro ⟨c, ⟨hc, hs⟩, rfl⟩
    rw [SetLike.mem_coe, mem_hsuCommC] at hc
    rw [SetLike.mem_coe, mem_hsuSkewC] at hs
    have hc' : (hsuSplit.conj c).comp (splitJ hsuW) = (splitJ hsuW).comp (hsuSplit.conj c) := by
      rw [← hsuSplit_conj_J, ← LinearEquiv.conj_comp, ← LinearEquiv.conj_comp, hc]
    have hs' : ∀ x y, splitForm hsuW (hsuSplit.conj c x) y =
        -splitForm hsuW x (hsuSplit.conj c y) := by
      intro x y
      obtain ⟨x, rfl⟩ := hsuSplit.surjective x
      obtain ⟨y, rfl⟩ := hsuSplit.surjective y
      rw [hsuSplit_conj_apply, hsuSplit_conj_apply, ← hsuSplit_form, ← hsuSplit_form, hs]
    exact ⟨firstBlock hsuW (hsuSplit.conj c),
      (eq_blockLie_of_commutes_skew hsuW (hsuSplit.conj c) hc' hs').symm⟩
  · rintro ⟨f, rfl⟩
    refine ⟨hsuSplit.conj.symm (blockLie hsuW f), ⟨?_, ?_⟩, hsuSplit.conj.apply_symm_apply _⟩
    · rw [SetLike.mem_coe, mem_hsuCommC]
      apply hsuSplit.conj.injective
      rw [LinearEquiv.conj_comp, LinearEquiv.conj_comp, hsuSplit_conj_J,
        LinearEquiv.apply_symm_apply]
      exact blockLie_commutes hsuW f
    · rw [SetLike.mem_coe, mem_hsuSkewC]
      intro x y
      have h (z : ℂ ⊗[ℚ] (Fin 12 → ℚ)) : hsuSplit (hsuSplit.conj.symm (blockLie hsuW f) z) =
          blockLie hsuW f (hsuSplit z) := by
        rw [← hsuSplit_conj_apply, LinearEquiv.apply_symm_apply]
      rw [hsuSplit_form, hsuSplit_form, h, h]
      exact blockLie_skew hsuW f _ _

private theorem hsu_finrank_commSkew : Module.finrank ℂ ↥(hsuCommC ⊓ hsuSkewC) = 36 := by
  rw [← LinearEquiv.finrank_map_eq hsuSplit.conj, hsu_map_commSkew,
    LinearMap.finrank_range_of_inj (blockLie_injective hsuW), Module.finrank_linearMap,
    hsu_finrank_W]

private theorem hsu_complexSU_le_commSkew :
    (complexSU hsuE spec_hsuE_nondegenerate_aux hsuJ spec_hsuJ_sq_aux
      spec_hsuE_skew_aux).toSubmodule ≤ hsuCommC ⊓ hsuSkewC := by
  intro X hX
  have h := (mem_complexSU hsuE spec_hsuE_nondegenerate_aux hsuJ spec_hsuJ_sq_aux
    spec_hsuE_skew_aux spec_hsuE_isAlt_aux X).mp hX
  exact ⟨(mem_hsuCommC X).mpr h.1, (mem_hsuSkewC X).mpr h.2.1⟩

private theorem hsuE_swap (x y : Fin 12 → ℚ) : hsuE x y = -hsuE y x := by
  have h := spec_hsuE_isAlt_aux.neg_eq x y
  linarith

private theorem hsu_symm_of_mem (X : LinearMap.ker hsuSkewMapQ) (k l : Fin 12) :
    hsuE ((X : Module.End ℚ (Fin 12 → ℚ)) (hsuB k)) (hsuB l) =
      hsuE ((X : Module.End ℚ (Fin 12 → ℚ)) (hsuB l)) (hsuB k) := by
  have h := congrFun (LinearMap.mem_ker.mp X.2) (k, l)
  simp only [hsuSkewMapQ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h
  rw [hsuE_swap (hsuB k)] at h
  linarith

/-- The rational endomorphism attached to a symmetric function on pairs. -/
private def hsuOfSym (f : Sym2 (Fin 12) → ℚ) : Module.End ℚ (Fin 12 → ℚ) :=
  LinearMap.BilinForm.symmCompOfNondegenerate (Matrix.toBilin' (Matrix.of fun i j => f s(i, j)))
    hsuE spec_hsuE_nondegenerate_aux

private theorem hsuOfSym_apply (f : Sym2 (Fin 12) → ℚ) (k l : Fin 12) :
    hsuE (hsuOfSym f (hsuB k)) (hsuB l) = f s(k, l) := by
  rw [hsuOfSym, LinearMap.BilinForm.comp_symmCompOfNondegenerate_apply]
  simp [hsuB, Matrix.toBilin'_single]

private theorem hsuOfSym_mem (f : Sym2 (Fin 12) → ℚ) : hsuOfSym f ∈ LinearMap.ker hsuSkewMapQ := by
  rw [LinearMap.mem_ker]
  funext p
  simp only [hsuSkewMapQ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  rw [hsuE_swap (hsuB p.1), hsuOfSym_apply, hsuOfSym_apply, Sym2.eq_swap, add_neg_cancel]

/-- The kernel of the skewness defect is the space of symmetric functions on pairs. -/
private def hsuSkewKerEquiv : LinearMap.ker hsuSkewMapQ ≃ₗ[ℚ] (Sym2 (Fin 12) → ℚ) where
  toFun X := Sym2.lift ⟨fun k l => hsuE ((X : Module.End ℚ (Fin 12 → ℚ)) (hsuB k)) (hsuB l),
    hsu_symm_of_mem X⟩
  map_add' X Y := by
    funext z; induction z using Sym2.ind; simp [Sym2.lift_mk]
  map_smul' c X := by
    funext z; induction z using Sym2.ind; simp [Sym2.lift_mk]
  invFun f := ⟨hsuOfSym f, hsuOfSym_mem f⟩
  left_inv X := by
    apply Subtype.ext
    have hB : hsuE.compl₁₂ (hsuOfSym (Sym2.lift ⟨fun k l => hsuE
        ((X : Module.End ℚ (Fin 12 → ℚ)) (hsuB k)) (hsuB l), hsu_symm_of_mem X⟩)) LinearMap.id =
        hsuE.compl₁₂ (X : Module.End ℚ (Fin 12 → ℚ)) LinearMap.id := by
      refine LinearMap.ext_basis hsuB hsuB fun k l => ?_
      simp only [LinearMap.compl₁₂_apply, LinearMap.id_apply, hsuOfSym_apply, Sym2.lift_mk]
    apply LinearMap.ext
    intro v
    dsimp only
    rw [← sub_eq_zero]
    refine LinearMap.ker_eq_bot'.mp spec_hsuE_nondegenerate_aux.ker_eq_bot _
      (LinearMap.ext fun w => ?_)
    have := LinearMap.congr_fun₂ hB v w
    simp only [LinearMap.compl₁₂_apply, LinearMap.id_apply] at this
    simp only [map_sub, LinearMap.sub_apply, this, sub_self, LinearMap.zero_apply]
  right_inv f := by
    funext z; induction z using Sym2.ind
    rename_i i j
    exact hsuOfSym_apply f i j

private theorem hsu_finrank_skewC : Module.finrank ℂ hsuSkewC = 78 := by
  rw [← hsu_complexSpan_annE, hsu_annE, hsu_finrank_complexSpan, hsuSkewKerEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin]
  rfl

end LaneCCandidate
theorem spec_finrank_hsu_complexSU_aux :
    Module.finrank ℂ (complexSU hsuE spec_hsuE_nondegenerate_aux hsuJ spec_hsuJ_sq_aux
      spec_hsuE_skew_aux).toSubmodule = 35 := by
  rw [← hsu_finrank_slEnd]
  exact (complexSUEquiv hsuE spec_hsuE_nondegenerate_aux hsuJ spec_hsuJ_sq_aux
    spec_hsuE_skew_aux).toLinearEquiv.finrank_eq

theorem spec_finrank_hsuWeilPair_aux :
    Module.finrank ℂ (mixedTensorStabilizer hsuWeilPair) = 36 := by
  rw [hsu_stab_weilPair, hsu_finrank_commSkew]

theorem spec_hsu_complexSU_lt_weilPair_aux :
    (complexSU hsuE spec_hsuE_nondegenerate_aux hsuJ spec_hsuJ_sq_aux
      spec_hsuE_skew_aux).toSubmodule < mixedTensorStabilizer hsuWeilPair := by
  rw [hsu_stab_weilPair]
  refine Submodule.lt_of_le_of_finrank_lt_finrank hsu_complexSU_le_commSkew ?_
  rw [spec_finrank_hsu_complexSU_aux, hsu_finrank_commSkew]
  norm_num

theorem spec_finrank_hsuPolarizationOnly_aux :
    Module.finrank ℂ (mixedTensorStabilizer hsuPolarizationOnly) = 78 := by
  rw [hsu_stab_polarizationOnly, hsu_finrank_skewC]

theorem spec_hsu_complexSU_lt_polarizationOnly_aux :
    (complexSU hsuE spec_hsuE_nondegenerate_aux hsuJ spec_hsuJ_sq_aux
      spec_hsuE_skew_aux).toSubmodule < mixedTensorStabilizer hsuPolarizationOnly := by
  rw [hsu_stab_polarizationOnly]
  refine Submodule.lt_of_le_of_finrank_lt_finrank
    (hsu_complexSU_le_commSkew.trans inf_le_right) ?_
  rw [spec_finrank_hsu_complexSU_aux, hsu_finrank_skewC]
  norm_num

end Candidate

end HodgeLean.Foundations
