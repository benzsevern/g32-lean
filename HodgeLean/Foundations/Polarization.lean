import Mathlib

/-!
# Polarization: symmetric tensors are spanned by pure powers

Foundations target T7, item 1 (`docs/roadmap/foundations.md` §4 T7).

For a module `A` over a commutative ring `R` and a finite index type `ι`, the permutation group
`Equiv.Perm ι` acts on the tensor power `⨂[R] _ : ι, A` by permuting the factors
(`permRep R A ι`, built from `PiTensorProduct.reindex`).

## Main results

* `polarization`: for any multilinear map `f` on `A^ι` and any family `x : ι → A`,
  `∑ s, (-1) ^ #sᶜ • f (fun _ ↦ ∑ i ∈ s, x i) = ∑ σ, f (x ∘ σ)` (over any commutative ring).
* `invariants_permRep_eq_span`: over a field of characteristic zero, the tensors fixed by every
  permutation are exactly the span of the pure powers `a ⊗ ⋯ ⊗ a`.

Relation to the goal: HC no distance; AV milestone no distance; first step toward a Lean proof
of F-1575 (1), the paper's invariant-theory lemma.
-/

open PiTensorProduct Finset
open scoped TensorProduct

noncomputable section

namespace HodgeLean.Foundations.SchurWeyl

section Identity

variable {R A N ι : Type*} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup N]
  [Module R N] [Fintype ι] [DecidableEq ι]

/-- Inclusion–exclusion: the signed count `∑ (-1) ^ #sᶜ` over the finsets `s` containing the
range of `r : ι → ι` is `1` if `r` is surjective and `0` otherwise. -/
theorem sum_neg_one_pow_card_compl_range_subset (r : ι → ι) :
    (∑ s : Finset ι, if (∀ j, r j ∈ s) then (-1 : R) ^ sᶜ.card else 0) =
      if Function.Surjective r then 1 else 0 := by
  set T : Finset ι := univ.image r
  have hcompl : (∑ s : Finset ι, if (∀ j, r j ∈ s) then (-1 : R) ^ sᶜ.card else 0) =
      ∑ t : Finset ι, if t ⊆ Tᶜ then (-1 : R) ^ t.card else 0 := by
    refine Fintype.sum_equiv ⟨compl, compl, compl_compl, compl_compl⟩ _ _ fun s => ?_
    have : sᶜ ⊆ Tᶜ ↔ ∀ j, r j ∈ s := by
      rw [subset_compl_comm, compl_compl, image_subset_iff]; simp
    simp only [Equiv.coe_fn_mk, this]
  have hpow : (∑ t : Finset ι, if t ⊆ Tᶜ then (-1 : R) ^ t.card else 0) =
      ((∑ t ∈ Tᶜ.powerset, (-1 : ℤ) ^ t.card : ℤ) : R) := by
    rw [← sum_filter, Int.cast_sum]
    refine sum_congr ?_ fun t _ => by push_cast; rfl
    ext t; simp
  rw [hcompl, hpow, sum_powerset_neg_one_pow_card]
  have hT : Tᶜ = ∅ ↔ Function.Surjective r := by
    rw [compl_eq_empty_iff, eq_univ_iff_forall]
    simp [T, Function.Surjective]
  by_cases h : Function.Surjective r <;> simp [h, hT.mpr, hT.not.mpr]

/-- **The polarization identity.** For a multilinear map `f` on `A^ι` and `x : ι → A`, the
alternating sum of `f` on the constant families `∑ i ∈ s, x i` is the sum of `f` over the
permutations of `x`.

Source: Goodman–Wallach, *Symmetry, Representations, and Invariants*, GTM 255, Ch. 4 (the
polarization of a homogeneous polynomial); Procesi, *Lie Groups*, Ch. 3 (polarization). -/
theorem polarization (f : MultilinearMap R (fun _ : ι => A) N) (x : ι → A) :
    ∑ s : Finset ι, (-1 : R) ^ sᶜ.card • f (fun _ => ∑ i ∈ s, x i) =
      ∑ σ : Equiv.Perm ι, f (fun j => x (σ j)) := by
  have hexp (s : Finset ι) : f (fun _ => ∑ i ∈ s, x i) =
      ∑ r : ι → ι, if (∀ j, r j ∈ s) then f (fun j => x (r j)) else 0 := by
    rw [f.map_sum_finset (fun _ i => x i) (fun _ => s), ← sum_filter]
    congr 1
    ext r; simp [Fintype.mem_piFinset]
  simp_rw [hexp, smul_sum, smul_ite, smul_zero]
  rw [sum_comm]
  have hinner (r : ι → ι) :
      (∑ s : Finset ι, if (∀ j, r j ∈ s) then (-1 : R) ^ sᶜ.card • f (fun j => x (r j)) else 0)
        = if Function.Surjective r then f (fun j => x (r j)) else 0 := by
    have := congrArg (· • f (fun j => x (r j)))
      (sum_neg_one_pow_card_compl_range_subset (R := R) r)
    simp only [sum_smul, ite_smul, zero_smul, one_smul] at this
    exact this
  simp_rw [hinner]
  rw [← sum_filter]
  symm
  refine sum_bij (fun σ _ => ⇑σ) (fun σ _ => by simpa using σ.surjective)
    (fun σ _ τ _ h => Equiv.coe_fn_injective h) (fun r hr => ?_) (fun _ _ => rfl)
  have hs : Function.Surjective r := by simpa using hr
  have hb : Function.Bijective r := ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  exact ⟨Equiv.ofBijective r hb, mem_univ _, rfl⟩

end Identity

section PermRep

variable (R A ι : Type*) [CommRing R] [AddCommGroup A] [Module R A]

/-- The action of `Equiv.Perm ι` on `⨂[R] _ : ι, A` permuting the factors:
`σ • (x₁ ⊗ ⋯ ⊗ xₙ) = x_{σ⁻¹ 1} ⊗ ⋯ ⊗ x_{σ⁻¹ n}` (`permRep_tprod`), so that the factor in slot
`i` moves to slot `σ i`.

Source: Goodman–Wallach, GTM 255, Ch. 4 (the action of `S_k` on `⊗^k V`). -/
def permRep : Representation R (Equiv.Perm ι) (⨂[R] _ : ι, A) where
  toFun σ := (reindex R (fun _ => A) σ).toLinearMap
  map_one' := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe, reindex_tprod]
    rfl
  map_mul' σ τ := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe, Module.End.mul_apply,
      reindex_tprod]
    rfl

variable {R A ι}

@[simp]
theorem permRep_tprod (σ : Equiv.Perm ι) (x : ι → A) :
    permRep R A ι σ (tprod R x) = tprod R fun i => x (σ.symm i) := by
  simp [permRep]

/-- The transposition of two factors of `A ⊗ A`. -/
example (a b : A) :
    permRep R A (Fin 2) (Equiv.swap 0 1) (tprod R ![a, b]) = tprod R ![b, a] := by
  rw [permRep_tprod]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- A pure power is fixed by every permutation. -/
theorem tprod_const_mem_invariants (a : A) :
    tprod R (fun _ : ι => a) ∈ (permRep R A ι).invariants := fun σ => by
  simp

end PermRep

section Invariants

variable {K A ι : Type*} [Field K] [CharZero K] [AddCommGroup A] [Module K A] [Fintype ι]
  [DecidableEq ι]

omit [CharZero K] in
/-- The sum over all permutations of a tensor lies in the span of the pure powers. -/
theorem sum_permRep_mem_span (t : ⨂[K] _ : ι, A) :
    ∑ σ : Equiv.Perm ι, permRep K A ι σ t ∈
      Submodule.span K (Set.range fun a : A => tprod K fun _ : ι => a) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp_rw [map_smul, permRep_tprod, ← smul_sum]
    refine Submodule.smul_mem _ r ?_
    rw [Fintype.sum_equiv (Equiv.inv _) (fun σ : Equiv.Perm ι => tprod K fun i => x (σ.symm i))
      (fun σ : Equiv.Perm ι => tprod K fun i => x (σ i)) (fun σ => rfl)]
    rw [← polarization (tprod K) x]
    exact Submodule.sum_mem _ fun s _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  | add x y hx hy =>
    simp_rw [map_add, sum_add_distrib]
    exact Submodule.add_mem _ hx hy

/-- **Polarization.** Over a field of characteristic zero, the tensors in `⨂[K] _ : ι, A` fixed
by every permutation of the factors are spanned by the pure powers `a ⊗ ⋯ ⊗ a`.

Source: Goodman–Wallach, *Symmetry, Representations, and Invariants*, GTM 255, Ch. 4 (symmetric
tensors and polarization); Procesi, *Lie Groups*, Ch. 9 §1. -/
theorem invariants_permRep_eq_span :
    (permRep K A ι).invariants =
      Submodule.span K (Set.range fun a : A => tprod K fun _ : ι => a) := by
  apply le_antisymm
  · intro t ht
    have hsum : ∑ σ : Equiv.Perm ι, permRep K A ι σ t =
        (Fintype.card (Equiv.Perm ι) : K) • t := by
      simp [ht _, Finset.sum_const, Nat.cast_smul_eq_nsmul]
    have hcard : (Fintype.card (Equiv.Perm ι) : K) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have := Submodule.smul_mem _ (Fintype.card (Equiv.Perm ι) : K)⁻¹ (sum_permRep_mem_span t)
    rwa [hsum, smul_smul, inv_mul_cancel₀ hcard, one_smul] at this
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact tprod_const_mem_invariants a

/-- For `ι = Fin 2`: `a ⊗ b + b ⊗ a` is a combination of pure squares. -/
example (a b : A) :
    tprod K ![a, b] + tprod K ![b, a] ∈
      Submodule.span K (Set.range fun c : A => tprod K fun _ : Fin 2 => c) := by
  rw [← invariants_permRep_eq_span]
  intro σ
  have h2 : ∀ σ : Equiv.Perm (Fin 2), σ = 1 ∨ σ = Equiv.swap 0 1 := by decide
  rcases h2 σ with rfl | rfl
  · simp
  · rw [map_add, permRep_tprod, permRep_tprod, add_comm]
    congr 2 <;> ext i <;> fin_cases i <;> rfl

end Invariants

end HodgeLean.Foundations.SchurWeyl
