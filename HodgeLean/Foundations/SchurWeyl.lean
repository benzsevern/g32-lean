import HodgeLean.Foundations.Polarization

/-!
# Schur–Weyl duality and the first fundamental theorem for `GL(W)`

Foundations target T7 (`docs/roadmap/foundations.md` §4 T7).

`K` is a field of characteristic zero, `W` a finite-dimensional `K`-vector space and `ι` a finite
index type (`ι = Fin k` for `W^{⊗k}`). `T = ⨂[K] _ : ι, W`; `Equiv.Perm ι` acts on `T` by
permuting the factors (`permRep K W ι`), and `End W` acts diagonally by
`tensorPow ι x = x ⊗ ⋯ ⊗ x`.

## Main results

* `centralizer_permRep_eq_span_tensorPow`: the endomorphisms of `T` commuting with every
  permutation are the span of the `x ⊗ ⋯ ⊗ x`, `x ∈ End W` (by polarization).
* `span_tensorPow_units_eq`, `centralizer_permRep_eq_span_tensorPow_units`: already the span of the
  `g ⊗ ⋯ ⊗ g`, `g ∈ GL(W)` (density of `GL(W)` in `End W` over an infinite field).
* `centralizer_tensorPow_units_eq_span_permRep` (**Schur–Weyl duality**): the endomorphisms of `T`
  commuting with every `g ⊗ ⋯ ⊗ g` are the span of the permutations (double centralizer theorem
  for the semisimple image of `K[S_k]`, `Module.Finite.toModuleEnd_moduleEnd_surjective`).
* `invariants_mixedRep_eq_span_contraction` (**first fundamental theorem for `GL(W)`**): the
  `GL(W)`-invariants of `W^{⊗ι} ⊗ (W^∨)^{⊗ι}` (`mixedRep`) are the span of the permutation
  contractions `contraction K W ι π`, defined as the preimage of `π` under the equivariant
  isomorphism `mixedEquiv : W^{⊗ι} ⊗ (W^∨)^{⊗ι} ≃ End (W^{⊗ι})`; `contraction_eq_sum` gives the
  formula in any basis.
* `invariants_mixedRep_eq_bot`: no invariants in `W^{⊗ι} ⊗ (W^∨)^{⊗κ}` when `|ι| ≠ |κ|`.
* Examples: `invariants_mixedRep_fin_one` (`k = 1`), `contraction_eq_of_finrank_eq_one` (the
  `c_π` coincide when `dim W = 1`, so they are not a basis in general),
  `linearIndependent_contraction_one_swap` (`k = 2`, `dim W ≥ 2`).

## Not formalized here

The Lie-algebra version (`gl(W)`-invariants equal `GL(W)`-invariants) and the `SL(W)` and
exterior-algebra forms (T8).

Relation to the goal: HC no distance; AV milestone no distance; first step toward a Lean proof
of F-1575 (1), the paper's invariant-theory lemma.
-/

open PiTensorProduct Finset Module
open scoped TensorProduct

noncomputable section

namespace HodgeLean.Foundations.SchurWeyl

section TensorPow

variable {K W : Type*} [CommRing K] [AddCommGroup W] [Module K W] (ι : Type*)

/-- The diagonal action `x ↦ x ⊗ ⋯ ⊗ x` of `End W` on `⨂[K] _ : ι, W`.

Source: Goodman–Wallach, *Symmetry, Representations, and Invariants*, GTM 255, Ch. 4 (the
action of `GL(V)` on `⊗^k V`). -/
def tensorPow (x : Module.End K W) : Module.End K (⨂[K] _ : ι, W) :=
  PiTensorProduct.map fun _ => x

variable {ι}

@[simp]
theorem tensorPow_tprod (x : Module.End K W) (v : ι → W) :
    tensorPow ι x (tprod K v) = tprod K fun i => x (v i) :=
  map_tprod _ _

/-- `tensorPow` on `W ⊗ W`. -/
example (x : Module.End K W) (a b : W) :
    tensorPow (Fin 2) x (tprod K ![a, b]) = tprod K ![x a, x b] := by
  rw [tensorPow_tprod]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem tensorPow_mul (x y : Module.End K W) :
    tensorPow ι (x * y) = tensorPow ι x * tensorPow ι y :=
  PiTensorProduct.map_comp _ _

theorem tensorPow_one : tensorPow ι (1 : Module.End K W) = 1 :=
  PiTensorProduct.map_id

/-- Permutations of the factors commute with the diagonal action. -/
theorem permRep_mul_tensorPow (σ : Equiv.Perm ι) (x : Module.End K W) :
    permRep K W ι σ * tensorPow ι x = tensorPow ι x * permRep K W ι σ := by
  ext v
  simp

end TensorPow

section Centralizer

variable {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional K W] [Fintype ι] [DecidableEq ι] in
/-- `piTensorHomMap : ⨂ End W → End (⨂ W)` intertwines the permutation actions: the action on the
source and conjugation on the target. -/
theorem piTensorHomMap_permRep (σ : Equiv.Perm ι) (u : ⨂[K] _ : ι, Module.End K W) :
    piTensorHomMap (permRep K (Module.End K W) ι σ u) =
      permRep K W ι σ * piTensorHomMap u * permRep K W ι σ⁻¹ := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul, permRep_tprod, mul_smul_comm, smul_mul_assoc]
    congr 1
    ext v
    simp only [piTensorHomMap_tprod_eq_map, LinearMap.compMultilinearMap_apply, map_tprod,
      Module.End.mul_apply, permRep_tprod, Equiv.Perm.inv_def, Equiv.symm_symm]
    congr 1
    funext i
    congr 1
    exact congrArg v (σ.apply_symm_apply i).symm
  | add x y hx hy => simp only [map_add, hx, hy, mul_add, add_mul]

/-- In finite dimension, `piTensorHomMap : ⨂ End W → End (⨂ W)` is surjective: it hits every
matrix unit. -/
theorem piTensorHomMap_surjective :
    Function.Surjective
      (piTensorHomMap : (⨂[K] _ : ι, Module.End K W) →ₗ[K] Module.End K (⨂[K] _ : ι, W)) := by
  classical
  let b := Module.finBasis K W
  let bT := Basis.piTensorProduct fun _ : ι => b
  rw [← LinearMap.range_eq_top, eq_top_iff, ← bT.end.span_eq, Submodule.span_le]
  rintro _ ⟨⟨α, γ⟩, rfl⟩
  refine ⟨tprod K fun l => b.end (α l, γ l), ?_⟩
  rw [piTensorHomMap_tprod_eq_map]
  refine bT.ext fun δ => ?_
  rw [Basis.end_apply_apply]
  simp only [bT, Basis.piTensorProduct_apply, map_tprod, Basis.end_apply_apply]
  by_cases h : γ = δ
  · subst h; simp
  · obtain ⟨l, hl⟩ := Function.ne_iff.mp h
    simp only [h, ↓reduceIte]
    exact (PiTensorProduct.tprod K).map_coord_zero l (by simp [hl])

/-- **Polarization form of Schur–Weyl.** The endomorphisms of `⨂[K] _ : ι, W` commuting with every
permutation of the factors are the span of the `x ⊗ ⋯ ⊗ x`, `x ∈ End W`.

Source: Goodman–Wallach, *Symmetry, Representations, and Invariants*, GTM 255, Ch. 4 (Schur–Weyl
duality); Procesi, *Lie Groups*, Ch. 9 §1. -/
theorem centralizer_permRep_eq_span_tensorPow [CharZero K] :
    Subalgebra.toSubmodule (Subalgebra.centralizer K (Set.range (permRep K W ι))) =
      Submodule.span K (Set.range (tensorPow (K := K) (W := W) ι)) := by
  apply le_antisymm
  · intro f hf
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at hf
    obtain ⟨u, rfl⟩ := piTensorHomMap_surjective (K := K) (W := W) (ι := ι) f
    have hconj (σ : Equiv.Perm ι) :
        piTensorHomMap (permRep K (Module.End K W) ι σ u) = piTensorHomMap u := by
      rw [piTensorHomMap_permRep, hf _ ⟨σ, rfl⟩, mul_assoc, ← map_mul, mul_inv_cancel, map_one,
        mul_one]
    have hsum : piTensorHomMap (∑ σ : Equiv.Perm ι, permRep K (Module.End K W) ι σ u) =
        (Fintype.card (Equiv.Perm ι) : K) • piTensorHomMap u := by
      simp [map_sum, hconj, Finset.sum_const, Nat.cast_smul_eq_nsmul]
    have hmem : piTensorHomMap (∑ σ : Equiv.Perm ι, permRep K (Module.End K W) ι σ u) ∈
        Submodule.span K (Set.range (tensorPow (K := K) (W := W) ι)) := by
      have := Submodule.mem_map_of_mem (f := piTensorHomMap) (sum_permRep_mem_span u)
      rw [Submodule.map_span, ← Set.range_comp] at this
      convert this using 3
      ext x : 1
      simp [tensorPow, piTensorHomMap_tprod_eq_map]
    have hcard : (Fintype.card (Equiv.Perm ι) : K) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have := Submodule.smul_mem _ (Fintype.card (Equiv.Perm ι) : K)⁻¹ hmem
    rwa [hsum, smul_smul, inv_mul_cancel₀ hcard, one_smul] at this
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨σ, rfl⟩
    exact permRep_mul_tensorPow σ x

omit [FiniteDimensional K W] in
/-- For `x ∈ End W` and a linear form `ℓ` on `End (⨂ W)`, `t ↦ ℓ (tensorPow (x + t • 1))` is a
polynomial function of `t`. -/
theorem exists_polynomial_tensorPow_add_smul (ℓ : Module.End K (⨂[K] _ : ι, W) →ₗ[K] K)
    (x : Module.End K W) :
    ∃ p : Polynomial K, ∀ t : K, p.eval t = ℓ (tensorPow ι (x + t • 1)) := by
  let F := (ℓ.compMultilinearMap (mapMultilinear K (fun _ : ι => W) fun _ : ι => W))
  refine ⟨∑ s : Finset ι, (∏ i, if i ∈ s then 1 else Polynomial.X) *
      Polynomial.C (F (s.piecewise (fun _ => x) fun _ => 1)), fun t => ?_⟩
  have hF (y : Module.End K W) : ℓ (tensorPow ι y) = F fun _ => y := rfl
  rw [hF]
  have : (fun _ : ι => x + t • (1 : Module.End K W)) = (fun _ => x) + fun _ => t • 1 := rfl
  rw [this, F.map_add_univ]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_C, apply_ite (Polynomial.eval t), Polynomial.eval_one, Polynomial.eval_X]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hpw : s.piecewise (fun _ : ι => x) (fun _ => t • (1 : Module.End K W)) =
      fun i => (if i ∈ s then 1 else t) • s.piecewise (fun _ => x) (fun _ => 1) i := by
    ext1 i
    by_cases hi : i ∈ s <;> simp [hi]
  rw [hpw, F.map_smul_univ, smul_eq_mul]

/-- **Density of `GL(W)` in `End W`.** Over a field of characteristic zero, the span of the
`g ⊗ ⋯ ⊗ g`, `g ∈ GL(W)`, contains every `x ⊗ ⋯ ⊗ x`, `x ∈ End W`: `x + t` is invertible for all
but finitely many `t`, and `t ↦ (x + t)^{⊗k}` is polynomial.

Source: Goodman–Wallach, GTM 255, Ch. 4–5 (Zariski density of `GL(V)` in `End(V)`); Procesi,
*Lie Groups*, Ch. 9. -/
theorem span_tensorPow_units_eq [CharZero K] :
    Submodule.span K (Set.range fun g : LinearMap.GeneralLinearGroup K W =>
        tensorPow ι (g : Module.End K W)) =
      Submodule.span K (Set.range (tensorPow (K := K) (W := W) ι)) := by
  set S := Submodule.span K (Set.range fun g : LinearMap.GeneralLinearGroup K W =>
    tensorPow ι (g : Module.End K W))
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨g, rfl⟩; exact ⟨_, rfl⟩)
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [SetLike.mem_coe, ← Submodule.Quotient.mk_eq_zero,
    ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  let ℓ := φ ∘ₗ S.mkQ
  obtain ⟨p, hp⟩ := exists_polynomial_tensorPow_add_smul ℓ x
  have hroot : {t | ¬ (x + t • 1).HasEigenvalue 0} ⊆ {t | p.IsRoot t} := by
    intro t ht
    have hunit : IsUnit (x + t • (1 : Module.End K W)) := by
      rw [LinearMap.isUnit_iff_ker_eq_bot]
      by_contra hker
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hker
      exact ht (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using hv), hv0⟩)
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, hp]
    have : tensorPow ι (x + t • 1) ∈ S := Submodule.subset_span ⟨hunit.unit, rfl⟩
    simp [ℓ, (Submodule.Quotient.mk_eq_zero S).mpr this]
  have hfin : {t : K | (x + t • 1).HasEigenvalue 0}.Finite := by
    refine (Set.Finite.preimage (f := fun t : K => -t) ?_ (x.finite_hasEigenvalue)).subset ?_
    · exact (neg_injective.injOn)
    · intro t ht
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      obtain ⟨v, hv⟩ := ht.exists_hasEigenvector
      refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hv.2⟩
      have := Module.End.mem_eigenspace_iff.mp hv.1
      rw [Module.End.mem_eigenspace_iff]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        zero_smul] at this
      rw [neg_smul, eq_neg_iff_add_eq_zero, this]
  have hp0 : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p
    ((hfin.infinite_compl).mono hroot)
  have := hp 0
  rw [hp0, Polynomial.eval_zero, zero_smul, add_zero] at this
  exact this.symm

/-- **Schur–Weyl duality, first half.** The endomorphisms of `⨂[K] _ : ι, W` commuting with every
permutation of the factors are the span of the `g ⊗ ⋯ ⊗ g`, `g ∈ GL(W)`.

Source: Goodman–Wallach, *Symmetry, Representations, and Invariants*, GTM 255, Ch. 4 (Schur–Weyl
duality); Weyl, *The Classical Groups*, Ch. IV. -/
theorem centralizer_permRep_eq_span_tensorPow_units [CharZero K] :
    Subalgebra.toSubmodule (Subalgebra.centralizer K (Set.range (permRep K W ι))) =
      Submodule.span K (Set.range fun g : LinearMap.GeneralLinearGroup K W =>
        tensorPow ι (g : Module.End K W)) := by
  rw [centralizer_permRep_eq_span_tensorPow, span_tensorPow_units_eq]

end Centralizer

section DoubleCentralizer

variable {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- The image of the group algebra `K[S_ι]` in `End (⨂ W)` lies in the span of the permutations. -/
theorem asAlgebraHom_permRep_mem_span (a : MonoidAlgebra K (Equiv.Perm ι)) :
    (permRep K W ι).asAlgebraHom a ∈ Submodule.span K (Set.range (permRep K W ι)) := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    rw [Representation.asAlgebraHom_of]
    exact Submodule.subset_span ⟨g, rfl⟩
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

variable [CharZero K] [FiniteDimensional K W]

/-- **Schur–Weyl duality.** Over a field of characteristic zero, the endomorphisms of
`⨂[K] _ : ι, W` commuting with every `g ⊗ ⋯ ⊗ g`, `g ∈ GL(W)`, are the span of the permutations
of the factors (the image of the group algebra `K[S_ι]`).

The proof is the double centralizer theorem: the image `B` of `K[S_ι]` is semisimple (Maschke),
its commutant is the span of the `g ⊗ ⋯ ⊗ g` (`centralizer_permRep_eq_span_tensorPow_units`), and
Jacobson density (`Module.Finite.toModuleEnd_moduleEnd_surjective`) says that `B` is the commutant
of its commutant.

Source: Goodman–Wallach, *Symmetry, Representations, and Invariants*, GTM 255, Ch. 4 (Schur–Weyl
duality, the double commutant theorem); Weyl, *The Classical Groups*, Ch. IV; Procesi,
*Lie Groups*, Ch. 9. -/
theorem centralizer_tensorPow_units_eq_span_permRep :
    Subalgebra.toSubmodule (Subalgebra.centralizer K
        (Set.range fun g : LinearMap.GeneralLinearGroup K W => tensorPow ι (g : Module.End K W))) =
      Submodule.span K (Set.range (permRep K W ι)) := by
  apply le_antisymm
  · intro f hf
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at hf
    let B := (permRep K W ι).asAlgebraHom.range
    have : NeZero (Nat.card (Equiv.Perm ι) : K) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
    have : IsSemisimpleRing B :=
      (permRep K W ι).asAlgebraHom.rangeRestrict.toRingHom.isSemisimpleRing_of_surjective
        (AlgHom.rangeRestrict_surjective _)
    have : Module.Finite (Module.End B (⨂[K] _ : ι, W)) (⨂[K] _ : ι, W) :=
      Module.Finite.of_restrictScalars_finite K _ _
    have hcomm (φ : Module.End B (⨂[K] _ : ι, W)) (m : ⨂[K] _ : ι, W) : f (φ m) = φ (f m) := by
      let φK : Module.End K (⨂[K] _ : ι, W) := φ.restrictScalars K
      have hφK : φK ∈ Subalgebra.toSubmodule
          (Subalgebra.centralizer K (Set.range (permRep K W ι))) := by
        rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
        rintro _ ⟨σ, rfl⟩
        have hσ : permRep K W ι σ ∈ B :=
          ⟨MonoidAlgebra.of K _ σ, Representation.asAlgebraHom_of _ _⟩
        refine LinearMap.ext fun m => ?_
        exact (φ.map_smul ⟨_, hσ⟩ m).symm
      rw [centralizer_permRep_eq_span_tensorPow_units] at hφK
      have hc : φK ∈ Subalgebra.toSubmodule (Subalgebra.centralizer K {f}) := by
        refine (Submodule.span_le.mpr ?_) hφK
        rintro _ ⟨g, rfl⟩
        rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
        rintro _ rfl
        exact (hf _ ⟨g, rfl⟩).symm
      rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at hc
      exact congr($(hc f rfl) m)
    let F : Module.End (Module.End B (⨂[K] _ : ι, W)) (⨂[K] _ : ι, W) :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := hcomm }
    obtain ⟨b, hb⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := B)
      (M := ⨂[K] _ : ι, W) F
    have hfb : f = (b : Module.End K (⨂[K] _ : ι, W)) :=
      LinearMap.ext fun m => (DFunLike.congr_fun hb m).symm
    obtain ⟨a, ha⟩ := b.2
    rw [hfb, ← ha]
    exact asAlgebraHom_permRep_mem_span a
  · rw [Submodule.span_le]
    rintro _ ⟨σ, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    exact (permRep_mul_tensorPow σ _).symm

end DoubleCentralizer

section Mixed

variable (K W : Type*) [Field K] [AddCommGroup W] [Module K W] (ι κ : Type*)

/-- The mixed tensors `W^{⊗ι} ⊗ (W^∨)^{⊗κ}`.

Source: Goodman–Wallach, *Symmetry, Representations, and Invariants*, GTM 255, Ch. 5 (mixed
tensors). -/
abbrev MixedTensor := (⨂[K] _ : ι, W) ⊗[K] (⨂[K] _ : κ, Module.Dual K W)

/-- The action of `GL(W)` on the mixed tensors: `g` acts by `g^{⊗ι} ⊗ ((g⁻¹)^∨)^{⊗κ}`, the
contragredient on the dual factors.

Source: Goodman–Wallach, GTM 255, Ch. 5 (the action of `GL(V)` on mixed tensors). -/
def mixedRep : Representation K (LinearMap.GeneralLinearGroup K W) (MixedTensor K W ι κ) where
  toFun g := TensorProduct.map (tensorPow ι (g : Module.End K W))
    (tensorPow κ ((g⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W).dualMap)
  map_one' := by
    have h1 : (1 : Module.End K W).dualMap = 1 := LinearMap.dualMap_id
    rw [inv_one, Units.val_one, h1, tensorPow_one, tensorPow_one]
    exact TensorProduct.map_one
  map_mul' g h := by
    have hd : (((h⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W) *
        ((g⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W)).dualMap =
        ((g⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W).dualMap *
          ((h⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W).dualMap :=
      (LinearMap.dualMap_comp_dualMap _ _).symm
    rw [← TensorProduct.map_mul, ← tensorPow_mul, ← tensorPow_mul, mul_inv_rev, Units.val_mul,
      Units.val_mul, hd]

variable {K W ι κ}

@[simp]
theorem mixedRep_tmul_tprod (g : LinearMap.GeneralLinearGroup K W) (v : ι → W)
    (φ : κ → Module.Dual K W) :
    mixedRep K W ι κ g (tprod K v ⊗ₜ tprod K φ) =
      tprod K (fun i => (g : Module.End K W) (v i)) ⊗ₜ
        tprod K (fun j => φ j ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W)) := by
  simp [mixedRep, tensorPow_tprod]
  rfl

/-- `GL(W)` acting on `W ⊗ W^∨`. -/
example (g : LinearMap.GeneralLinearGroup K W) (v : W) (φ : Module.Dual K W) :
    mixedRep K W (Fin 1) (Fin 1) g (tprod K (fun _ => v) ⊗ₜ tprod K (fun _ => φ)) =
      tprod K (fun _ => (g : Module.End K W) v) ⊗ₜ
        tprod K (fun _ => φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W)) :=
  mixedRep_tmul_tprod g _ _

variable [FiniteDimensional K W] [Fintype ι]

variable (K W ι) in
/-- The `GL(W)`-equivariant isomorphism `W^{⊗ι} ⊗ (W^∨)^{⊗ι} ≃ End (W^{⊗ι})`: `t ⊗ (φ₁ ⊗ ⋯ ⊗ φₖ)`
goes to `w₁ ⊗ ⋯ ⊗ wₖ ↦ (∏ φᵢ wᵢ) • t` (`mixedEquiv_tmul_tprod`). It is built from
`PiTensorProduct.dualDistribEquiv` and `dualTensorHomEquiv`.

Source: Goodman–Wallach, GTM 255, Ch. 5 (mixed tensors as endomorphisms). -/
def mixedEquiv : MixedTensor K W ι ι ≃ₗ[K] Module.End K (⨂[K] _ : ι, W) :=
  TensorProduct.comm K _ _ ≪≫ₗ
    TensorProduct.congr PiTensorProduct.dualDistribEquiv (LinearEquiv.refl K _) ≪≫ₗ
      dualTensorHomEquiv K (⨂[K] _ : ι, W) (⨂[K] _ : ι, W)

@[simp]
theorem mixedEquiv_tmul_tprod (t : ⨂[K] _ : ι, W) (φ : ι → Module.Dual K W)
    (v : ι → W) :
    mixedEquiv K W ι (t ⊗ₜ tprod K φ) (tprod K v) = (∏ i, φ i (v i)) • t := by
  simp [mixedEquiv]
  convert rfl

/-- `k = 1`: `v ⊗ φ ∈ W ⊗ W^∨` goes to the rank-one map `w ↦ φ w • v`. -/
example (v w : W) (φ : Module.Dual K W) :
    mixedEquiv K W (Fin 1) (tprod K (fun _ => v) ⊗ₜ tprod K (fun _ => φ)) (tprod K fun _ => w) =
      φ w • tprod K (fun _ => v) := by
  simp

/-- `mixedEquiv` is `GL(W)`-equivariant, for conjugation on `End (W^{⊗ι})`. -/
theorem mixedEquiv_mixedRep (g : LinearMap.GeneralLinearGroup K W) (v : MixedTensor K W ι ι) :
    mixedEquiv K W ι (mixedRep K W ι ι g v) =
      tensorPow ι (g : Module.End K W) * mixedEquiv K W ι v *
        tensorPow ι ((g⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W) := by
  have : (mixedEquiv K W ι).toLinearMap ∘ₗ mixedRep K W ι ι g =
      (LinearMap.mulLeft K (tensorPow ι (g : Module.End K W)) ∘ₗ
        LinearMap.mulRight K
          (tensorPow ι ((g⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W))) ∘ₗ
        (mixedEquiv K W ι).toLinearMap := by
    ext t φ v
    simp [mixedEquiv_tmul_tprod, tensorPow_tprod]
  exact congr($this v)

variable (K W ι) in
/-- The permutation contraction `c_π ∈ W^{⊗ι} ⊗ (W^∨)^{⊗ι}`: the mixed tensor corresponding to
the permutation `π` of the factors under `mixedEquiv`. In a basis `(e_j)` of `W` with dual basis
`(e^∨_j)` it is `∑_α e_{α(π⁻¹ 1)} ⊗ ⋯ ⊗ e_{α(π⁻¹ k)} ⊗ e^∨_{α 1} ⊗ ⋯ ⊗ e^∨_{α k}`
(`contraction_eq_sum`), for every basis.

Source: Goodman–Wallach, *Symmetry, Representations, and Invariants*, GTM 255, Ch. 5 (the
complete contractions in the first fundamental theorem for `GL(V)`). -/
def contraction (π : Equiv.Perm ι) : MixedTensor K W ι ι :=
  (mixedEquiv K W ι).symm (permRep K W ι π)

@[simp]
theorem mixedEquiv_contraction (π : Equiv.Perm ι) :
    mixedEquiv K W ι (contraction K W ι π) = permRep K W ι π :=
  LinearEquiv.apply_symm_apply _ _

/-- The basis formula for `c_π`, in any basis of `W`. -/
theorem contraction_eq_sum [DecidableEq ι] {J : Type*} [Fintype J] [DecidableEq J]
    (b : Module.Basis J K W) (π : Equiv.Perm ι) :
    contraction K W ι π = ∑ α : ι → J,
      tprod K (fun i => b (α (π.symm i))) ⊗ₜ tprod K (fun i => b.coord (α i)) := by
  apply (mixedEquiv K W ι).injective
  rw [mixedEquiv_contraction]
  refine (Basis.piTensorProduct fun _ : ι => b).ext fun γ => ?_
  simp only [Basis.piTensorProduct_apply, map_sum, LinearMap.sum_apply, mixedEquiv_tmul_tprod,
    permRep_tprod]
  rw [Finset.sum_eq_single γ]
  · simp [Basis.coord_apply]
  · intro α _ hα
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hα
    rw [Finset.prod_eq_zero (Finset.mem_univ i)
      (by simp [Basis.coord_apply, Ne.symm hi]), zero_smul]
  · exact fun h => absurd (Finset.mem_univ γ) h

/-- `k = 1`: `c_id` is the identity of `W` (the trace tensor `∑ e_j ⊗ e^∨_j`). -/
example : mixedEquiv K W (Fin 1) (contraction K W (Fin 1) 1) = 1 := by
  simp

/-- **The first fundamental theorem of invariant theory for `GL(W)`, mixed tensors.** Over a field
of characteristic zero, the `GL(W)`-invariants of `W^{⊗ι} ⊗ (W^∨)^{⊗ι}` are the span of the
permutation contractions `c_π`.

Source: Goodman–Wallach, *Symmetry, Representations, and Invariants*, GTM 255, Ch. 5 (first
fundamental theorem for `GL(V)`, tensor form); Weyl, *The Classical Groups*, Ch. II–IV; Procesi,
*Lie Groups*, Ch. 9. -/
theorem invariants_mixedRep_eq_span_contraction [CharZero K] [DecidableEq ι] :
    (mixedRep K W ι ι).invariants =
      Submodule.span K (Set.range (contraction K W ι)) := by
  have hspan : Submodule.span K (Set.range (contraction K W ι)) =
      (Submodule.span K (Set.range (permRep K W ι))).map
        ((mixedEquiv K W ι).symm : Module.End K (⨂[K] _ : ι, W) →ₗ[K] MixedTensor K W ι ι) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  ext v
  rw [hspan, Submodule.mem_map_equiv, LinearEquiv.symm_symm,
    ← centralizer_tensorPow_units_eq_span_permRep, Subalgebra.mem_toSubmodule,
    Subalgebra.mem_centralizer_iff, Representation.mem_invariants]
  have hinv (g : LinearMap.GeneralLinearGroup K W) :
      tensorPow ι ((g⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W) *
        tensorPow ι (g : Module.End K W) = 1 := by
    rw [← tensorPow_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, tensorPow_one]
  have hinv' (g : LinearMap.GeneralLinearGroup K W) :
      tensorPow ι (g : Module.End K W) *
        tensorPow ι ((g⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W) = 1 := by
    rw [← tensorPow_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, tensorPow_one]
  constructor
  · rintro h _ ⟨g, rfl⟩
    have := congrArg (mixedEquiv K W ι) (h g)
    rw [mixedEquiv_mixedRep] at this
    calc tensorPow ι (g : Module.End K W) * mixedEquiv K W ι v
        = tensorPow ι (g : Module.End K W) * mixedEquiv K W ι v *
            (tensorPow ι ((g⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W) *
              tensorPow ι (g : Module.End K W)) := by rw [hinv, mul_one]
      _ = mixedEquiv K W ι v * tensorPow ι (g : Module.End K W) := by
        rw [← mul_assoc, this]
  · intro h g
    apply (mixedEquiv K W ι).injective
    rw [mixedEquiv_mixedRep, h _ ⟨g, rfl⟩, mul_assoc, hinv', mul_one]

end Mixed

section Scalars

variable {K W ι κ : Type*} [Field K] [AddCommGroup W] [Module K W] [Fintype ι] [Fintype κ]

/-- A scalar `a` acts on `W^{⊗ι}` by `a ^ |ι|`. -/
theorem tensorPow_smul_one (a : K) :
    tensorPow ι (a • (1 : Module.End K W)) = a ^ Fintype.card ι • 1 := by
  ext v
  simp [tensorPow_tprod, MultilinearMap.map_smul_univ, Finset.prod_const]

/-- The scalar `a ≠ 0` acts on `W^{⊗ι} ⊗ (W^∨)^{⊗κ}` by `a ^ |ι| * a⁻¹ ^ |κ|`. -/
theorem mixedRep_algebraMap (a : Kˣ) :
    mixedRep K W ι κ (Units.map (algebraMap K (Module.End K W) : K →* Module.End K W) a) =
      ((a : K) ^ Fintype.card ι * ((a⁻¹ : Kˣ) : K) ^ Fintype.card κ) • 1 := by
  have hdual : (((a⁻¹ : Kˣ) : K) • (1 : Module.End K W)).dualMap = ((a⁻¹ : Kˣ) : K) • 1 := by
    ext φ w
    simp
  simp only [mixedRep, MonoidHom.coe_mk, OneHom.coe_mk, ← map_inv, Units.coe_map,
    MonoidHom.coe_ofClass, Algebra.algebraMap_eq_smul_one, hdual, tensorPow_smul_one,
    TensorProduct.map_smul_left, TensorProduct.map_smul_right, TensorProduct.map_one, smul_smul]
  rw [mul_comm]

/-- **No invariants in unequal degrees.** If `|ι| ≠ |κ|`, the `GL(W)`-invariants of
`W^{⊗ι} ⊗ (W^∨)^{⊗κ}` are `0`: the scalar `2` acts by `2 ^ (|ι| - |κ|) ≠ 1`.

Source: Goodman–Wallach, *Symmetry, Representations, and Invariants*, GTM 255, Ch. 5 (first
fundamental theorem for `GL(V)`, the case `k ≠ l`). -/
theorem invariants_mixedRep_eq_bot [CharZero K] (h : Fintype.card ι ≠ Fintype.card κ) :
    (mixedRep K W ι κ).invariants = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  let two : Kˣ := Units.mk0 2 two_ne_zero
  have hv2 := hv (Units.map (algebraMap K (Module.End K W) : K →* Module.End K W) two)
  rw [mixedRep_algebraMap, LinearMap.smul_apply, Module.End.one_apply] at hv2
  have hc : ((two : K) ^ Fintype.card ι * (two⁻¹ : K) ^ Fintype.card κ) ≠ 1 := by
    simp only [two, Units.val_mk0, inv_pow]
    rw [Ne, mul_inv_eq_one₀ (pow_ne_zero _ two_ne_zero)]
    intro h2
    apply h
    have : ((2 ^ Fintype.card ι : ℕ) : K) = ((2 ^ Fintype.card κ : ℕ) : K) := by
      push_cast; exact h2
    exact Nat.pow_right_injective le_rfl (Nat.cast_injective this)
  rw [Submodule.mem_bot]
  by_contra hne
  exact hc (smul_left_injective K hne (by simpa using hv2))

/-- `W` itself (`k = 1`, `l = 0`) has no nonzero `GL(W)`-invariant. -/
example [CharZero K] : (mixedRep K W (Fin 1) (Fin 0)).invariants = ⊥ :=
  invariants_mixedRep_eq_bot (by simp)

end Scalars

section Examples

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- `k = 1`: the invariants of `W ⊗ W^∨ ≃ End W` are the line through `c_id`, which is the
identity (`mixedEquiv_contraction`). -/
theorem invariants_mixedRep_fin_one [CharZero K] :
    (mixedRep K W (Fin 1) (Fin 1)).invariants = K ∙ contraction K W (Fin 1) 1 := by
  rw [invariants_mixedRep_eq_span_contraction]
  congr 1
  ext v
  simp only [Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun ⟨σ, hσ⟩ => hσ ▸ by rw [Subsingleton.elim σ 1], fun hv => ⟨1, hv.symm⟩⟩

/-- If `dim W = 1`, every permutation acts trivially on `W^{⊗ι}`. -/
theorem permRep_eq_one_of_finrank_eq_one {ι : Type*} [Fintype ι] (h : finrank K W = 1)
    (π : Equiv.Perm ι) : permRep K W ι π = 1 := by
  let b := Module.finBasisOfFinrankEq K W h
  have hv (w : W) : w = b.repr w 0 • b 0 := by
    conv_lhs => rw [← b.sum_repr w]
    simp
  ext v
  simp only [LinearMap.compMultilinearMap_apply, permRep_tprod, Module.End.one_apply]
  calc tprod K (fun i => v (π.symm i))
      = tprod K (fun i => b.repr (v (π.symm i)) 0 • b 0) := by
        congr 1; funext i; exact hv _
    _ = (∏ i, b.repr (v (π.symm i)) 0) • tprod K (fun _ : ι => b 0) :=
        MultilinearMap.map_smul_univ _ _ _
    _ = (∏ i, b.repr (v i) 0) • tprod K (fun _ : ι => b 0) := by
        rw [Equiv.prod_comp π.symm (fun i => b.repr (v i) 0)]
    _ = tprod K (fun i => b.repr (v i) 0 • b 0) := (MultilinearMap.map_smul_univ _ _ _).symm
    _ = tprod K v := by congr 1; funext i; exact (hv _).symm

/-- If `dim W = 1`, all the contractions `c_π` coincide (so they are not linearly independent in
general). -/
theorem contraction_eq_of_finrank_eq_one {ι : Type*} [Fintype ι] (h : finrank K W = 1)
    (π σ : Equiv.Perm ι) : contraction K W ι π = contraction K W ι σ := by
  simp only [contraction, permRep_eq_one_of_finrank_eq_one h]

/-- `k = 2`, `dim W = 1`: `c_id = c_swap` (both are `e ⊗ e ⊗ e^∨ ⊗ e^∨`). -/
example (h : finrank K W = 1) :
    contraction K W (Fin 2) 1 = contraction K W (Fin 2) (Equiv.swap 0 1) :=
  contraction_eq_of_finrank_eq_one h _ _

/-- `k = 2`, `dim W ≥ 2`: `c_id` and `c_swap` are linearly independent. -/
theorem linearIndependent_contraction_one_swap (h : 2 ≤ finrank K W) :
    LinearIndependent K
      ![contraction K W (Fin 2) 1, contraction K W (Fin 2) (Equiv.swap 0 1)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h' := congrArg (mixedEquiv K W (Fin 2)) hst
  simp only [map_add, map_smul, mixedEquiv_contraction, map_zero] at h'
  let b := Module.finBasis K W
  let j0 : Fin (finrank K W) := ⟨0, by omega⟩
  let j1 : Fin (finrank K W) := ⟨1, by omega⟩
  have hj : j0 ≠ j1 := by simp [j0, j1, Fin.ext_iff]
  let bT := Basis.piTensorProduct fun _ : Fin 2 => b
  have hx := congr($h' (tprod K ![b j0, b j1]))
  simp only [LinearMap.add_apply, LinearMap.smul_apply, permRep_tprod, map_one,
    Module.End.one_apply, LinearMap.zero_apply] at hx
  have h0 := congr(bT.repr $hx ![j0, j1])
  have h1 := congr(bT.repr $hx ![j1, j0])
  simp [bT, Basis.piTensorProduct_repr_tprod_apply, Fin.prod_univ_two, hj,
    hj.symm] at h0 h1
  exact ⟨h0, h1⟩

end Examples

end HodgeLean.Foundations.SchurWeyl
