import HodgeLean.Foundations.Program.CyclotomicWeilDefs

/-! # Linear algebra of cyclotomic determinant lines

The trace-dual basis of the cyclotomic field gives explicit complex projectors onto the
embedding eigenspaces, and rational wedges whose complexifications are prescribed combinations
of the embedding determinant wedges.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct

namespace HodgeLean.Foundations

section Field

variable (m : ℕ)

/-- A rational basis of the cyclotomic field.
Source: Mathlib, `Module.finBasis`. -/
def cyc_basis : Module.Basis (Fin (Module.finrank ℚ (cyc_Field m))) ℚ (cyc_Field m) :=
  Module.finBasis ℚ (cyc_Field m)

/-- The trace-dual basis of `cyc_basis`.
Source: Mathlib, `LinearMap.BilinForm.dualBasis` and `traceForm_nondegenerate`. -/
def cyc_dual : Module.Basis (Fin (Module.finrank ℚ (cyc_Field m))) ℚ (cyc_Field m) :=
  (Algebra.traceForm ℚ (cyc_Field m)).dualBasis
    (traceForm_nondegenerate ℚ (cyc_Field m)) (cyc_basis m)

theorem cyc_dual_expand (y : cyc_Field m) :
    ∑ i, algebraMap ℚ (cyc_Field m) (Algebra.trace ℚ (cyc_Field m) (y * cyc_basis m i)) *
      cyc_dual m i = y := by
  conv_rhs => rw [← (cyc_dual m).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, cyc_dual, LinearMap.BilinForm.dualBasis_repr_apply,
    Algebra.traceForm_apply]

theorem cyc_trace_eq_sum (y : cyc_Field m) :
    algebraMap ℚ ℂ (Algebra.trace ℚ (cyc_Field m) y) =
      ∑ σ : cyc_Field m →ₐ[ℚ] ℂ, σ y :=
  trace_eq_sum_embeddings ℂ

theorem cyc_embedding_expand (s : cyc_Field m →ₐ[ℚ] ℂ) (y : cyc_Field m) :
    s y = ∑ u : cyc_Field m →ₐ[ℚ] ℂ,
      u y * ∑ i, u (cyc_basis m i) * s (cyc_dual m i) := by
  conv_lhs => rw [← cyc_dual_expand m y]
  rw [map_sum]
  simp_rw [map_mul, AlgHom.commutes, cyc_trace_eq_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem cyc_embeddings_linearIndependent :
    LinearIndependent ℂ (fun u : cyc_Field m →ₐ[ℚ] ℂ => (u : cyc_Field m → ℂ)) := by
  have hinj : Function.Injective
      (fun u : cyc_Field m →ₐ[ℚ] ℂ => (u.toRingHom.toMonoidHom : cyc_Field m →* ℂ)) := by
    intro u v huv
    ext x
    exact DFunLike.congr_fun huv x
  exact (linearIndependent_monoidHom (cyc_Field m) ℂ).comp _ hinj

open Classical in
theorem cyc_dual_delta (u s : cyc_Field m →ₐ[ℚ] ℂ) :
    ∑ i, u (cyc_basis m i) * s (cyc_dual m i) = if u = s then 1 else 0 := by
  let c : (cyc_Field m →ₐ[ℚ] ℂ) → ℂ := fun u =>
    (∑ i, u (cyc_basis m i) * s (cyc_dual m i)) - if u = s then 1 else 0
  have hrel : ∑ u, c u • (u : cyc_Field m → ℂ) = 0 := by
    funext y
    simp only [c, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply]
    rw [sub_eq_zero, cyc_embedding_expand m s y]
    exact Finset.sum_congr rfl fun u _ => mul_comm _ _
  have h := Fintype.linearIndependent_iff.mp (cyc_embeddings_linearIndependent m) c hrel u
  exact sub_eq_zero.mp h

end Field

section Projector

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}

theorem cyc_scalarC_mul (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (a b : cyc_Field m)
    (x : ℂ ⊗[ℚ] V) :
    (cyc_scalar e (a * b)).baseChange ℂ x =
      (cyc_scalar e a).baseChange ℂ ((cyc_scalar e b).baseChange ℂ x) := by
  change (cyc_rep e (a * b)).baseChange ℂ x = _
  rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]
  rfl

theorem cyc_scalarC_sum (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) {ι : Type*} (s : Finset ι)
    (a : ι → cyc_Field m) (x : ℂ ⊗[ℚ] V) :
    (cyc_scalar e (∑ i ∈ s, a i)).baseChange ℂ x =
      ∑ i ∈ s, (cyc_scalar e (a i)).baseChange ℂ x := by
  change (cyc_rep e (∑ i ∈ s, a i)).baseChange ℂ x = _
  rw [map_sum]
  change (LinearMap.baseChangeHom ℚ ℂ V V (∑ i ∈ s, cyc_rep e (a i))) x = _
  rw [map_sum, LinearMap.sum_apply]
  rfl

theorem cyc_scalarC_smul (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (q : ℚ) (a : cyc_Field m)
    (x : ℂ ⊗[ℚ] V) :
    (cyc_scalar e (algebraMap ℚ (cyc_Field m) q * a)).baseChange ℂ x =
      (algebraMap ℚ ℂ q) • (cyc_scalar e a).baseChange ℂ x := by
  rw [cyc_scalarC_mul]
  change (cyc_rep e (algebraMap ℚ (cyc_Field m) q)).baseChange ℂ _ = _
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.baseChange_smul,
    LinearMap.smul_apply, Module.End.one_eq_id, LinearMap.baseChange_id, LinearMap.id_apply,
    algebraMap_smul]

/-- The complex projector onto the eigenspace of one embedding, built from the trace-dual basis.
Source: Bourbaki, Algèbre, Ch. V, §8; the idempotents of `ℂ ⊗ F`. -/
def cyc_proj (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    Module.End ℂ (ℂ ⊗[ℚ] V) :=
  ∑ i, t (cyc_basis m i) • (cyc_scalar e (cyc_dual m i)).baseChange ℂ

theorem cyc_proj_apply (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ)
    (x : ℂ ⊗[ℚ] V) :
    cyc_proj e t x = ∑ i, t (cyc_basis m i) • (cyc_scalar e (cyc_dual m i)).baseChange ℂ x := by
  simp [cyc_proj, LinearMap.sum_apply]

theorem cyc_scalarC_expand (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (y : cyc_Field m)
    (x : ℂ ⊗[ℚ] V) :
    (cyc_scalar e y).baseChange ℂ x = ∑ j, (∑ u : cyc_Field m →ₐ[ℚ] ℂ, u (y * cyc_basis m j)) •
      (cyc_scalar e (cyc_dual m j)).baseChange ℂ x := by
  conv_lhs => rw [← cyc_dual_expand m y]
  rw [cyc_scalarC_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cyc_scalarC_smul, cyc_trace_eq_sum]

theorem cyc_scalarC_proj (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ)
    (a : cyc_Field m) (x : ℂ ⊗[ℚ] V) :
    (cyc_scalar e a).baseChange ℂ (cyc_proj e t x) = t a • cyc_proj e t x := by
  classical
  have hcoef (j) : ∑ i, t (cyc_basis m i) * ∑ u : cyc_Field m →ₐ[ℚ] ℂ,
        u (a * cyc_dual m i * cyc_basis m j) = t a * t (cyc_basis m j) := by
    calc ∑ i, t (cyc_basis m i) * ∑ u : cyc_Field m →ₐ[ℚ] ℂ,
          u (a * cyc_dual m i * cyc_basis m j)
        = ∑ u : cyc_Field m →ₐ[ℚ] ℂ, u a * u (cyc_basis m j) *
            ∑ i, t (cyc_basis m i) * u (cyc_dual m i) := by
          simp_rw [Finset.mul_sum, map_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = t a * t (cyc_basis m j) := by
          simp_rw [cyc_dual_delta, mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq]
          simp
  let B : Fin (Module.finrank ℚ (cyc_Field m)) → ℂ ⊗[ℚ] V :=
    fun j => (cyc_scalar e (cyc_dual m j)).baseChange ℂ x
  calc (cyc_scalar e a).baseChange ℂ (cyc_proj e t x)
      = ∑ i, t (cyc_basis m i) • ∑ j, (∑ u : cyc_Field m →ₐ[ℚ] ℂ,
          u (a * cyc_dual m i * cyc_basis m j)) • B j := by
        rw [cyc_proj_apply, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, ← cyc_scalarC_mul, cyc_scalarC_expand]
    _ = ∑ j, (∑ i, t (cyc_basis m i) * ∑ u : cyc_Field m →ₐ[ℚ] ℂ,
          u (a * cyc_dual m i * cyc_basis m j)) • B j := by
        simp_rw [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_smul]
    _ = t a • cyc_proj e t x := by
        simp_rw [hcoef, cyc_proj_apply, Finset.smul_sum, smul_smul]
        rfl

theorem cyc_proj_mem (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ)
    (x : ℂ ⊗[ℚ] V) : cyc_proj e t x ∈ cyc_eigenspace e t := by
  simp only [cyc_eigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  exact fun a => cyc_scalarC_proj e t a x

theorem cyc_proj_of_mem (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ)
    {x : ℂ ⊗[ℚ] V} (hx : x ∈ cyc_eigenspace e t) : cyc_proj e t x = x := by
  simp only [cyc_eigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx
  rw [cyc_proj_apply]
  simp_rw [hx, smul_smul, ← Finset.sum_smul, cyc_dual_delta]
  simp

end Projector

section Descent

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}

/-- A rational wedge whose complexification is the `x`-weighted sum of the embedding wedges of
the projections of `r`.
Source: G32 v0.16, Section 4.1; trace-dual expansion of the idempotents of `ℂ ⊗ F`. -/
def cyc_omega (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (x : cyc_Field m) (r : Fin h → V) :
    ⋀[ℚ]^h V :=
  ∑ j : Fin h → Fin (Module.finrank ℚ (cyc_Field m)),
    Algebra.trace ℚ (cyc_Field m) (x * ∏ i, cyc_basis m (j i)) •
      exteriorPower.ιMulti ℚ h (fun i => cyc_scalar e (cyc_dual m (j i)) (r i))

theorem cyc_ιMulti_proj_expand (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m))
    (s : cyc_Field m →ₐ[ℚ] ℂ) (r : Fin h → V) :
    exteriorPower.ιMulti ℂ h (fun i => cyc_proj e s ((1 : ℂ) ⊗ₜ[ℚ] r i)) =
      ∑ j : Fin h → Fin (Module.finrank ℚ (cyc_Field m)),
        (∏ i, s (cyc_basis m (j i))) • exteriorPower.ιMulti ℂ h
          (fun i => (cyc_scalar e (cyc_dual m (j i))).baseChange ℂ ((1 : ℂ) ⊗ₜ[ℚ] r i)) := by
  classical
  simp_rw [cyc_proj_apply]
  have := (exteriorPower.ιMulti ℂ h (M := ℂ ⊗[ℚ] V)).toMultilinearMap.map_sum
    (fun i l => s (cyc_basis m l) •
      (cyc_scalar e (cyc_dual m l)).baseChange ℂ ((1 : ℂ) ⊗ₜ[ℚ] r i))
  simp only [AlternatingMap.coe_multilinearMap] at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact AlternatingMap.map_smul_univ _ _ _

theorem cyc_complexify_omega (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (x : cyc_Field m)
    (r : Fin h → V) :
    HodgeBlocks.complexifyWedge h (cyc_omega e x r) =
      ∑ s : cyc_Field m →ₐ[ℚ] ℂ,
        s x • exteriorPower.ιMulti ℂ h (fun i => cyc_proj e s ((1 : ℂ) ⊗ₜ[ℚ] r i)) := by
  simp_rw [cyc_ιMulti_proj_expand, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, cyc_omega, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, HodgeBlocks.complexifyWedge_ιMulti, ← Finset.sum_smul,
    ← IsScalarTower.algebraMap_smul ℂ, cyc_trace_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, map_prod]

theorem cyc_ιMulti_mem_line (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ)
    (v : Fin h → ℂ ⊗[ℚ] V) (hv : ∀ i, v i ∈ cyc_eigenspace e t) :
    exteriorPower.ιMulti ℂ h v ∈ cyc_line e t :=
  ⟨exteriorPower.ιMulti ℂ h (fun i => ⟨v i, hv i⟩), by
    rw [exteriorPower.map_apply_ιMulti]
    rfl⟩

theorem cyc_omega_mem (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (x : cyc_Field m)
    (r : Fin h → V) : cyc_omega e x r ∈ cyc_wedges e := by
  change HodgeBlocks.complexifyWedge h _ ∈ cyc_topLines e
  rw [cyc_complexify_omega]
  refine Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ ?_
  exact Submodule.mem_iSup_of_mem s
    (cyc_ιMulti_mem_line e s _ fun i => cyc_proj_mem e s _)

theorem cyc_ιMulti_proj_eq (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ)
    (r : Fin h → V) :
    exteriorPower.ιMulti ℂ h (fun i => cyc_proj e t ((1 : ℂ) ⊗ₜ[ℚ] r i)) =
      ∑ k, t (cyc_basis m k) •
        HodgeBlocks.complexifyWedge h (cyc_omega e (cyc_dual m k) r) := by
  classical
  simp_rw [cyc_complexify_omega, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, cyc_dual_delta]
  simp

end Descent

section Main

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] {m h : ℕ}

theorem cyc_complexify_mem_descent (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) {w : ⋀[ℚ]^h V}
    (hw : w ∈ cyc_wedges e) :
    HodgeBlocks.complexifyWedge h w ∈ ((cyc_wedges e).baseChange ℂ).map
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) h).toLinearMap := by
  rw [← HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul]
  exact Submodule.mem_map_of_mem (Submodule.tmul_mem_baseChange_of_mem 1 hw)

theorem cyc_ιMulti_proj_mem_descent (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m))
    (t : cyc_Field m →ₐ[ℚ] ℂ) (u : Fin h → ℂ ⊗[ℚ] V) :
    exteriorPower.ιMulti ℂ h (fun i => cyc_proj e t (u i)) ∈ ((cyc_wedges e).baseChange ℂ).map
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) h).toLinearMap := by
  classical
  let b := (Module.finBasis ℚ V).baseChange ℂ
  have hu : (fun i => cyc_proj e t (u i)) =
      fun i => ∑ k, b.repr (u i) k • cyc_proj e t (b k) := by
    funext i
    conv_lhs => rw [← b.sum_repr (u i)]
    rw [map_sum]
    simp_rw [map_smul]
  rw [hu]
  have := (exteriorPower.ιMulti ℂ h (M := ℂ ⊗[ℚ] V)).toMultilinearMap.map_sum
    (fun i k => b.repr (u i) k • cyc_proj e t (b k))
  simp only [AlternatingMap.coe_multilinearMap] at this
  rw [this]
  refine Submodule.sum_mem _ fun κ _ => ?_
  rw [AlternatingMap.map_smul_univ]
  refine Submodule.smul_mem _ _ ?_
  simp only [b, Module.Basis.baseChange_apply]
  rw [cyc_ιMulti_proj_eq]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (cyc_complexify_mem_descent e (cyc_omega_mem e _ _))

/-- Scalar extension of the rational determinant wedges is the sum of the determinant lines. -/
theorem cyc_descent_eq (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    ((cyc_wedges e).baseChange ℂ).map
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) h).toLinearMap =
        cyc_topLines e := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    change HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv h ((1 : ℂ) ⊗ₜ[ℚ] w) ∈ _
    rw [HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul]
    exact hw
  · refine iSup_le fun t => ?_
    rw [cyc_line, LinearMap.range_eq_map, ← exteriorPower.ιMulti_span, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, exteriorPower.map_apply_ιMulti]
    have hv : ((cyc_eigenspace e t).subtype ∘ v) = fun i => cyc_proj e t (v i) :=
      funext fun i => (cyc_proj_of_mem e t (v i).2).symm
    rw [hv]
    exact cyc_ιMulti_proj_mem_descent e t _

theorem cyc_finrank_wedges_eq (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    Module.finrank ℚ ↥(cyc_wedges e) = Module.finrank ℂ ↥(cyc_topLines e) := by
  rw [← cyc_descent_eq e, LinearEquiv.finrank_map_eq]
  have := HodgeBlocks.finrank_ker_baseChange ℚ ℂ _ _ (cyc_wedges e).mkQ
  rw [ker_baseChange_eq, Submodule.ker_mkQ] at this
  exact this.symm

theorem cyc_finrank_eigenspace (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    Module.finrank ℂ ↥(cyc_eigenspace e t) = h := by
  have h1 := spec_a2a_finrank (cyc_rep e) t
  have h2 : Module.finrank ℚ V = h * Module.finrank ℚ (cyc_Field m) := by
    rw [e.finrank_eq, Module.finrank_pi_fintype]
    simp
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos (h1.trans h2)

theorem cyc_finrank_line (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    Module.finrank ℂ ↥(cyc_line e t) = 1 :=
  HodgeBlocks.finrank_range_exteriorPower_map_subtype_of_finrank ℂ (ℂ ⊗[ℚ] V)
    (cyc_eigenspace e t) h (cyc_finrank_eigenspace e t)

omit [Module.Finite ℚ V] in
theorem cyc_line_le_eigen (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ)
    (x : cyc_Field m) :
    cyc_line e t ≤ Module.End.eigenspace
      (HodgeBlocks.derivationExt ((cyc_scalar e x).baseChange ℂ) h) ((h : ℂ) * t x) := by
  let E := Module.End.eigenspace ((cyc_scalar e x).baseChange ℂ) (t x)
  have hle : cyc_eigenspace e t ≤ E := iInf_le _ x
  rintro _ ⟨y, rfl⟩
  have hmap : exteriorPower.map h (cyc_eigenspace e t).subtype =
      exteriorPower.map h E.subtype ∘ₗ exteriorPower.map h (Submodule.inclusion hle) := by
    rw [← exteriorPower.map_comp]
    rfl
  rw [hmap, LinearMap.comp_apply]
  apply Module.End.mem_eigenspace_iff.mpr
  exact LinearMap.congr_fun
    (HodgeBlocks.derivationExt_comp_exteriorPower_map_eigenspace _ h (t x)) _

omit [Module.Finite ℚ V] in
theorem cyc_line_iSupIndep [NeZero m] (hh : 0 < h) (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    iSupIndep (cyc_line e) := by
  let ζ := IsCyclotomicExtension.zeta m ℚ (cyc_Field m)
  let D := HodgeBlocks.derivationExt ((cyc_scalar e ζ).baseChange ℂ) h
  have hinj : Function.Injective (fun t : cyc_Field m →ₐ[ℚ] ℂ => (h : ℂ) * t ζ) := by
    intro t s hts
    have h1 : t ζ = s ζ := mul_left_cancel₀ (by exact_mod_cast hh.ne') hts
    refine AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top
      (IsCyclotomicExtension.zeta_spec m ℚ (cyc_Field m))) ?_
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact h1
  exact ((Module.End.eigenspaces_iSupIndep D).comp hinj).mono fun t => cyc_line_le_eigen e t ζ

theorem cyc_finrank_topLines [NeZero m] (hh : 0 < h) (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    Module.finrank ℂ ↥(cyc_topLines e) = Module.finrank ℚ (cyc_Field m) := by
  classical
  rw [cyc_topLines, Submodule.iSup_eq_range_dfinsupp_lsum,
    LinearMap.finrank_range_of_inj (cyc_line_iSupIndep hh e).dfinsupp_lsum_injective]
  change Module.finrank ℂ (DirectSum _ fun t => ↥(cyc_line e t)) = _
  rw [Module.finrank_directSum]
  simp only [cyc_finrank_line, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  exact AlgHom.card ℚ (cyc_Field m) ℂ

theorem cyc_finrank_field [NeZero m] : Module.finrank ℚ (cyc_Field m) = m.totient :=
  IsCyclotomicExtension.finrank (cyc_Field m)
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))

end Main

section Projection

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] {m h : ℕ}

theorem cyc_derivationExt_add {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
    (S T : Module.End R M) (n : ℕ) :
    HodgeBlocks.derivationExt (S + T) n =
      HodgeBlocks.derivationExt S n + HodgeBlocks.derivationExt T n := by
  classical
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R n M)
  rintro _ ⟨v, rfl⟩
  simp only [LinearMap.add_apply, HodgeBlocks.derivationExt_ιMulti, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlternatingMap.map_update_add]

theorem cyc_derivationExt_smul {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
    (c : R) (T : Module.End R M) (n : ℕ) :
    HodgeBlocks.derivationExt (c • T) n = c • HodgeBlocks.derivationExt T n := by
  classical
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R n M)
  rintro _ ⟨v, rfl⟩
  simp only [LinearMap.smul_apply, HodgeBlocks.derivationExt_ιMulti, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlternatingMap.map_update_smul]

theorem cyc_complexifyWedge_derivationExt (T : Module.End ℚ V) (n : ℕ) (w : ⋀[ℚ]^n V) :
    HodgeBlocks.complexifyWedge n (HodgeBlocks.derivationExt T n w) =
      HodgeBlocks.derivationExt (T.baseChange ℂ) n (HodgeBlocks.complexifyWedge n w) := by
  classical
  let F := (HodgeBlocks.complexifyWedge n).comp (HodgeBlocks.derivationExt T n)
  let G := ((HodgeBlocks.derivationExt (T.baseChange ℂ) n).restrictScalars ℚ).comp
    (HodgeBlocks.complexifyWedge n)
  change F w = G w
  apply LinearMap.congr_fun
  apply LinearMap.ext_on (exteriorPower.ιMulti_span ℚ n V)
  rintro _ ⟨v, rfl⟩
  simp only [F, G, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    HodgeBlocks.derivationExt_ιMulti, HodgeBlocks.complexifyWedge_ιMulti, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (⇑(exteriorPower.ιMulti ℂ n))
  funext j
  by_cases hj : j = i
  · subst hj
    simp [LinearMap.baseChange_tmul]
  · simp [Function.update_of_ne hj]

/-- Every nonzero rational determinant class has a nonzero component on every embedding line:
its complexification does not lie in the sum of the other determinant lines.
Source: G32 v0.16, Section 4.1, the Contraction paragraph; the `F`-line structure of `W_F`. -/
theorem cyc_projection_ne_zero [NeZero m] (hh : 0 < h) (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m))
    {w : ⋀[ℚ]^h V} (hw : w ∈ cyc_wedges e) (hw0 : w ≠ 0) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    HodgeBlocks.complexifyWedge h w ∉ ⨆ (s) (_ : s ≠ t), cyc_line e s := by
  classical
  intro hL
  let L' := ⨆ (s) (_ : s ≠ t), cyc_line e s
  let D : cyc_Field m → Module.End ℂ (⋀[ℂ]^h (ℂ ⊗[ℚ] V)) := fun x =>
    HodgeBlocks.derivationExt ((cyc_scalar e x).baseChange ℂ) h
  have hDline : ∀ x s, ∀ z ∈ cyc_line e s, D x z ∈ cyc_line e s := by
    intro x s z hz
    change HodgeBlocks.derivationExt _ h z ∈ _
    rw [Module.End.mem_eigenspace_iff.mp (cyc_line_le_eigen e s x hz)]
    exact Submodule.smul_mem _ _ hz
  have hDL : ∀ x, ∀ z ∈ L', D x z ∈ L' := by
    intro x
    have hle : L' ≤ L'.comap (D x) := iSup₂_le fun s hs z hz =>
      (le_iSup₂ (f := fun s (_ : s ≠ t) => cyc_line e s) s hs) (hDline x s z hz)
    exact fun z hz => hle hz
  let φ : cyc_Field m →ₗ[ℚ] ⋀[ℚ]^h V :=
    { toFun := fun x => HodgeBlocks.derivationExt (cyc_scalar e x) h w
      map_add' := fun x y => by
        change HodgeBlocks.derivationExt (cyc_rep e (x + y)) h w = _
        rw [map_add, cyc_derivationExt_add]
        rfl
      map_smul' := fun q x => by
        have h1 : (cyc_rep e).toLinearMap (q • x) = q • cyc_scalar e x :=
          (cyc_rep e).toLinearMap.map_smul q x
        change HodgeBlocks.derivationExt ((cyc_rep e).toLinearMap (q • x)) h w = _
        rw [h1, cyc_derivationExt_smul]
        rfl }
  have hφC : ∀ x, HodgeBlocks.complexifyWedge h (φ x) = D x (HodgeBlocks.complexifyWedge h w) :=
    fun x => cyc_complexifyWedge_derivationExt _ h w
  let W0 : Submodule ℚ (⋀[ℚ]^h V) := (L'.restrictScalars ℚ).comap (HodgeBlocks.complexifyWedge h)
  have hL'top : L' ≤ cyc_topLines e := iSup₂_le fun s _ => le_iSup (cyc_line e) s
  have hW0 : W0 ≤ cyc_wedges e := fun z hz => hL'top hz
  have hφW0 : LinearMap.range φ ≤ W0 := by
    rintro _ ⟨x, rfl⟩
    change HodgeBlocks.complexifyWedge h (φ x) ∈ L'
    rw [hφC]
    exact hDL x _ hL
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    have hz : D x (HodgeBlocks.complexifyWedge h w) = 0 := by
      rw [← hφC, LinearMap.mem_ker.mp hx, map_zero]
    have hmem : HodgeBlocks.complexifyWedge h w ∈
        ⨆ (μ : ℂ) (_ : μ ∈ {μ : ℂ | μ ≠ 0}), Module.End.eigenspace (D x) μ := by
      have hle : cyc_topLines e ≤
          ⨆ (μ : ℂ) (_ : μ ∈ {μ : ℂ | μ ≠ 0}), Module.End.eigenspace (D x) μ := by
        refine iSup_le fun s => (cyc_line_le_eigen e s x).trans ?_
        refine le_iSup₂_of_le ((h : ℂ) * s x) ?_ le_rfl
        exact mul_ne_zero (by exact_mod_cast hh.ne') ((map_ne_zero s).mpr hx0)
      exact hle hw
    have h0 : HodgeBlocks.complexifyWedge h w ∈ Module.End.eigenspace (D x) 0 := by
      rw [Module.End.mem_eigenspace_iff, zero_smul]
      exact hz
    have hdisj := (Module.End.eigenspaces_iSupIndep (D x)).disjoint_biSup
      (x := 0) (y := {μ : ℂ | μ ≠ 0}) (by simp)
    have h00 := (Submodule.disjoint_def.mp hdisj) _ h0 hmem
    exact hw0 (HodgeBlocks.complexifyWedge_injective h (by rw [h00, map_zero]))
  have hrank : Module.finrank ℚ ↥(LinearMap.range φ) = Module.finrank ℚ ↥(cyc_wedges e) := by
    rw [LinearMap.finrank_range_of_inj hinj, cyc_finrank_wedges_eq, cyc_finrank_topLines hh]
  have hfull : cyc_wedges e ≤ W0 := by
    rw [← Submodule.eq_of_le_of_finrank_eq (hφW0.trans hW0) hrank]
    exact hφW0
  have htop : cyc_topLines e ≤ L' := by
    rw [← cyc_descent_eq e, Submodule.baseChange_eq_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨w', hw', rfl⟩, rfl⟩
    change HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv h ((1 : ℂ) ⊗ₜ[ℚ] w') ∈ L'
    rw [HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul]
    exact hfull hw'
  have hbot : cyc_line e t = ⊥ :=
    ((cyc_line_iSupIndep hh e) t).eq_bot_of_le ((le_iSup (cyc_line e) t).trans htop)
  have hone := cyc_finrank_line e t
  rw [hbot, finrank_bot] at hone
  exact zero_ne_one hone

end Projection

end HodgeLean.Foundations
