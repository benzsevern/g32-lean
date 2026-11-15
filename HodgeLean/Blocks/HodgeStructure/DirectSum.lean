import HodgeLean.Blocks.HodgeStructure.Morphisms

/-! # Direct sums of pure rational Hodge structures -/

open scoped TensorProduct
noncomputable section
namespace HodgeBlocks

section InternalProd
variable {R M N ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Independence is preserved by coordinatewise products of submodules. -/
theorem iSupIndep_prod {A : ι → Submodule R M} {B : ι → Submodule R N}
    (hA : iSupIndep A) (hB : iSupIndep B) :
    iSupIndep fun i => (A i).prod (B i) := by
  intro i
  have hle : (⨆ (j) (_ : j ≠ i), (A j).prod (B j)) ≤
      (⨆ (j) (_ : j ≠ i), A j).prod (⨆ (j) (_ : j ≠ i), B j) :=
    iSup₂_le fun j hj => Submodule.prod_mono
      (le_iSup₂ (f := fun j (_ : j ≠ i) => A j) j hj)
      (le_iSup₂ (f := fun j (_ : j ≠ i) => B j) j hj)
  have hd : Disjoint ((A i).prod (B i))
      ((⨆ (j) (_ : j ≠ i), A j).prod (⨆ (j) (_ : j ≠ i), B j)) := by
    rw [disjoint_iff, Submodule.prod_inf_prod, disjoint_iff.mp (hA i),
      disjoint_iff.mp (hB i), Submodule.prod_bot]
  exact hd.mono_right hle

/-- Products of two spanning indexed families span the product. -/
theorem iSup_prod_eq_top {A : ι → Submodule R M} {B : ι → Submodule R N}
    (hA : (⨆ i, A i) = ⊤) (hB : (⨆ i, B i) = ⊤) :
    (⨆ i, (A i).prod (B i)) = ⊤ := by
  have h : Submodule.prod (⨆ i, A i) (⨆ i, B i) ≤ ⨆ i, (A i).prod (B i) := by
    rw [LinearMap.prod_eq_sup_map, Submodule.map_iSup, Submodule.map_iSup]
    refine sup_le (iSup_le fun i => ?_) (iSup_le fun i => ?_)
    · rw [Submodule.map_inl]
      exact (Submodule.prod_mono le_rfl bot_le).trans
        (le_iSup (fun i => (A i).prod (B i)) i)
    · rw [Submodule.map_inr]
      exact (Submodule.prod_mono bot_le le_rfl).trans
        (le_iSup (fun i => (A i).prod (B i)) i)
  rw [eq_top_iff]
  calc
    (⊤ : Submodule R (M × N)) = Submodule.prod ⊤ ⊤ := Submodule.prod_top.symm
    _ = Submodule.prod (⨆ i, A i) (⨆ i, B i) := by rw [hA, hB]
    _ ≤ ⨆ i, (A i).prod (B i) := h

/-- `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top` combines independence
and spanning into internality. -/
theorem isInternal_prod [DecidableEq ι] {A : ι → Submodule R M}
    {B : ι → Submodule R N} (hA : DirectSum.IsInternal A)
    (hB : DirectSum.IsInternal B) : DirectSum.IsInternal fun i => (A i).prod (B i) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_prod hA.submodule_iSupIndep hB.submodule_iSupIndep)
    (iSup_prod_eq_top hA.submodule_iSup_eq_top hB.submodule_iSup_eq_top)
end InternalProd

/-- Images under a linear equivalence preserve internal direct sums. -/
theorem _root_.DirectSum.IsInternal.mapEquiv {R M N ι : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [DecidableEq ι] {A : ι → Submodule R M} (hA : DirectSum.IsInternal A)
    (e : M ≃ₗ[R] N) : DirectSum.IsInternal fun i => (A i).map e.toLinearMap := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hA ⊢
  refine ⟨?_, ?_⟩
  · have hmap := hA.1.map_orderIso (Submodule.orderIsoMapComap e)
    have hf : (Submodule.orderIsoMapComap e) ∘ A = fun i => (A i).map (e : M →ₗ[R] N) := by
      funext i
      rw [Function.comp_apply, Submodule.orderIsoMapComap_apply]
    rwa [hf] at hmap
  · rw [← Submodule.map_iSup, hA.2, Submodule.map_top, LinearEquiv.range]

variable (V W : Type*) [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- `TensorProduct.prodRight` (`Mathlib/LinearAlgebra/TensorProduct/Prod.lean`) distributes
scalar extension over a binary product. -/
def prodBaseChange : (ℂ ⊗[ℚ] (V × W)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] V) × (ℂ ⊗[ℚ] W) :=
  TensorProduct.prodRight ℚ ℂ ℂ V W

@[simp] theorem prodBaseChange_tmul (c : ℂ) (v : V) (w : W) :
    prodBaseChange V W (c ⊗ₜ[ℚ] (v, w)) = (c ⊗ₜ[ℚ] v, c ⊗ₜ[ℚ] w) := rfl

theorem prodBaseChange_sigmaQR (x : ℂ ⊗[ℚ] (V × W)) :
    prodBaseChange V W (sigmaQR (V × W) x) =
      LinearMap.prodMap (sigmaQR V) (sigmaQR W) (prodBaseChange V W x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c p => simp only [sigmaQ_tmul, LinearMap.prodMap_apply]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem sigma_prodBaseChange_symm (y : (ℂ ⊗[ℚ] V) × (ℂ ⊗[ℚ] W)) :
    sigmaQ (V × W) ((prodBaseChange V W).symm y) =
      (prodBaseChange V W).symm (sigmaQ V y.1, sigmaQ W y.2) := by
  apply (prodBaseChange V W).injective
  change prodBaseChange V W (sigmaQR (V × W) ((prodBaseChange V W).symm y)) = _
  rw [prodBaseChange_sigmaQR, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, LinearMap.prodMap_apply]
  rfl

theorem map_sigma_prodPiece (P : Submodule ℂ (ℂ ⊗[ℚ] V))
    (Q : Submodule ℂ (ℂ ⊗[ℚ] W)) :
    ((P.prod Q).map (prodBaseChange V W).symm.toLinearMap).map (sigmaQ (V × W)) =
      ((P.map (sigmaQ V)).prod (Q.map (sigmaQ W))).map
        (prodBaseChange V W).symm.toLinearMap := by
  ext x
  constructor
  · rintro ⟨-, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨(sigmaQ V s.1, sigmaQ W s.2),
      ⟨Submodule.mem_map_of_mem hs.1, Submodule.mem_map_of_mem hs.2⟩,
      (sigma_prodBaseChange_symm V W s).symm⟩
  · rintro ⟨⟨t₁, t₂⟩, ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, rfl⟩
    exact ⟨(prodBaseChange V W).symm (a, b),
      ⟨(a, b), Submodule.mem_prod.mpr ⟨ha, hb⟩, rfl⟩,
      sigma_prodBaseChange_symm V W (a, b)⟩

variable {n : ℤ} [Module.Finite ℚ V] [Module.Finite ℚ W]

/-- Binary direct sum of same-weight Hodge structures. `DirectSum.IsInternal.mapEquiv`
transports an internal decomposition across a linear equivalence. -/
def QHodgeStructure.prod (M : QHodgeStructure n V) (N : QHodgeStructure n W) :
    QHodgeStructure n (V × W) where
  H pq := ((M.H pq).prod (N.H pq)).map (prodBaseChange V W).symm.toLinearMap
  supported pq h := by
    rw [M.supported pq h, N.supported pq h, Submodule.prod_bot, Submodule.map_bot]
  isInternal := (isInternal_prod M.isInternal N.isInternal).mapEquiv (prodBaseChange V W).symm
  conj_symm p q := by rw [map_sigma_prodPiece, M.conj_symm p q, N.conj_symm p q]

end HodgeBlocks
