import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Trace

/-! # A positive involution of a CM field is complex conjugation

Helpers for `p1_rosati_conj`.

* `p1c_trace_algHom_eq`: if a finite field extension `L / K` acts `K`-linearly on a
  finite-dimensional `K`-vector space `M` through `r : L →ₐ[K] End_K(M)`, then
  `tr_K(r x) = m · Tr_{L/K}(x)` for a fixed `m : ℕ` (`M` is free over `L` of rank `m`).
* `p1c_eq_complexConj`: a ring involution `σ` of a CM field `L` with
  `0 < Tr_{L/ℚ}(x σ(x))` for every `x ≠ 0` is complex conjugation
  (Mumford, *Abelian Varieties*, §21; Birkenhake–Lange, *Complex Abelian Varieties*, §5.5).
  The involution `τ = c ∘ σ` commutes with `c`, and an `x ≠ 0` with `τ x = -x` would give
  `Tr(x σ(x)) = -Tr(x c(x)) = -Σ_ι |ι x|² ≤ 0`.
-/

noncomputable section

open NumberField

namespace HodgeLean.Foundations

section Trace

variable {K L M : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- The `K`-trace of the action of `x ∈ L` on `M` is a fixed multiple of `Tr_{L/K}(x)`. -/
theorem p1c_trace_algHom_eq (r : L →ₐ[K] Module.End K M) :
    ∃ m : ℕ, ∀ x : L, LinearMap.trace K M (r x) = m • Algebra.trace K L x := by
  classical
  let _ : Module L M := Module.compHom M r.toRingHom
  have : IsScalarTower K L M := ⟨fun q x v => by
    change r (q • x) v = q • r x v
    rw [map_smul]; rfl⟩
  have : Module.Finite L M := Module.Finite.of_restrictScalars_finite K L M
  let b := Module.Free.chooseBasis L M
  let c := Module.Free.chooseBasis K L
  let bb := c.smulTower b
  refine ⟨Fintype.card (Module.Free.ChooseBasisIndex L M), fun x => ?_⟩
  have hsmul : ∀ (y : L) (v : M), r y v = y • v := fun _ _ => rfl
  rw [LinearMap.trace_eq_matrix_trace K bb, Algebra.trace_eq_matrix_trace c, Matrix.trace,
    Matrix.trace, Fintype.sum_prod_type, Finset.sum_comm]
  trans ∑ _i : Module.Free.ChooseBasisIndex L M, ∑ k, (Algebra.leftMulMatrix c x).diag k
  swap
  · rw [Finset.sum_const, Finset.card_univ]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag, Matrix.diag, LinearMap.toMatrix_apply, Module.Basis.smulTower_apply,
    Module.Basis.smulTower_repr, hsmul, smul_smul, map_smul, Module.Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
    Algebra.leftMulMatrix_eq_repr_mul]

end Trace

section CM

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]

/-- Every ring endomorphism of a CM field commutes with complex conjugation. -/
theorem p1c_complexConj_comm (σ : L →+* L) (y : L) :
    σ (IsCMField.complexConj L y) = IsCMField.complexConj L (σ y) := by
  let ι : L →+* ℂ := Classical.choice inferInstance
  apply ι.injective
  have h := IsCMField.complexEmbedding_complexConj L (ι.comp σ) y
  rw [RingHom.comp_apply, RingHom.comp_apply] at h
  rw [h, IsCMField.complexEmbedding_complexConj]

/-- `Tr_{L/ℚ}(x c(x)) ≥ 0`: under every complex embedding `x c(x)` maps to `|ι x|²`. -/
theorem p1c_trace_mul_complexConj_nonneg (x : L) :
    0 ≤ Algebra.trace ℚ L (x * IsCMField.complexConj L x) := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := L) (E := ℂ)
    (x := x * IsCMField.complexConj L x)
  have hterm : ∀ φ : L →ₐ[ℚ] ℂ, φ (x * IsCMField.complexConj L x) =
      ((Complex.normSq (φ x) : ℝ) : ℂ) := by
    intro φ
    have hc := IsCMField.complexEmbedding_complexConj L φ.toRingHom x
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hc
    rw [map_mul, hc, Complex.mul_conj]
  simp_rw [hterm] at h
  rw [← Complex.ofReal_sum, eq_ratCast, ← Complex.ofReal_ratCast, Complex.ofReal_inj] at h
  have : (0 : ℝ) ≤ (Algebra.trace ℚ L (x * IsCMField.complexConj L x) : ℝ) := by
    rw [h]; exact Finset.sum_nonneg fun φ _ => Complex.normSq_nonneg _
  exact_mod_cast this

/-- **A positive involution of a CM field is complex conjugation.** A ring involution `σ` of the
CM field `L` with `0 < Tr_{L/ℚ}(x σ(x))` for every `x ≠ 0` is `IsCMField.complexConj L`.
Mumford, *Abelian Varieties*, §21; Birkenhake–Lange, *Complex Abelian Varieties*, §5.5. -/
theorem p1c_eq_complexConj (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x)
    (hpos : ∀ x : L, x ≠ 0 → 0 < Algebra.trace ℚ L (x * σ x)) (a : L) :
    σ a = IsCMField.complexConj L a := by
  by_contra hne
  -- `τ = c ∘ σ` moves `a`; `x = a - τ a` satisfies `σ x = -c x`.
  have hτ : IsCMField.complexConj L (σ a) ≠ a := by
    intro h; apply hne
    have := congrArg (IsCMField.complexConj L) h
    rwa [IsCMField.complexConj_apply_apply] at this
  have hx0 : a - IsCMField.complexConj L (σ a) ≠ 0 := sub_ne_zero.mpr (Ne.symm hτ)
  have hσx : σ (a - IsCMField.complexConj L (σ a)) =
      -IsCMField.complexConj L (a - IsCMField.complexConj L (σ a)) := by
    rw [map_sub, map_sub, p1c_complexConj_comm, hσ, IsCMField.complexConj_apply_apply]
    ring
  have h1 := hpos _ hx0
  rw [hσx, mul_neg, map_neg] at h1
  linarith [p1c_trace_mul_complexConj_nonneg (a - IsCMField.complexConj L (σ a))]

end CM

end HodgeLean.Foundations
