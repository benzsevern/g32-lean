import HodgeLean.Adapters.IntersectionProductBlochRoberts
import HodgeLean.Adapters.IntersectionProductMovingRobertsUnramified
import HodgeLean.Adapters.IntersectionProductMovingRoberts
import Mathlib.RingTheory.Nullstellensatz

/-! # Roberts' main lemma over the line: generic projections `ℓ × id`

Stage A3.3, the third input of Bloch's homotopy. Over `𝔸¹_t` the relative affine cone over
`X × 𝔸¹` lives in `ℂ[x, t]`, and the projection is `ℓ × id : (x, t) ↦ (ℓ x, t)`, the block matrix
`a3h_block a` with blocks `ℓ` and `1`. Its parameters are those of `ℓ` alone, so the generic
hypotheses of Roberts' main lemma (`a3k_roberts_main_rel`) are proved again for block matrices:
* generic secants (`a3h_generic_secant_rel`): pairs `(w, z) ∈ W × Z` off the diagonal with the
  same projection have the expected dimension. The pairs lie over the same `t`, which cuts the
  incidence algebra `ℂ[W] ⊗ ℂ[Z]` by the nonzerodivisor `t ⊗ 1 - 1 ⊗ t` unless `W` and `Z` lie in
  the same fibre `t = c`; on the quotient the relations `ℓ(w - z) = 0` are the linear incidence conditions of
  `a3r_generic_linear`;
* generic unramifiedness (`a3h_generic_isUnramifiedAt_rel`): where the differentials of the
  relative cone over `ℂ[t]` have rank at most `n + 1`, the differentials `dℓ_i` of generic linear
  forms span them;
* `ℓ × id` is finite on the relative cone `I_X[t]` when `ℓ` is finite on the cone
  (`a3h_finite_rel`), and the relative cone has one dimension more (`a3h_IXr_isPrime_dim`);
* `ℓ × id` is unramified where `ℓ` is (`a3h_formallyUnramified_rel`): `(ℂ[x, t]/I_X[t])_f` is a
  quotient of the base change of `(ℂ[x]/I_X)_f` along `ℂ[y] → ℂ[y, t]`.

With these, `a3h_roberts_rel` is Roberts' main lemma over the line for a generic `ℓ`: the
components `Z' ≠ Z` of `(ℓ × id)⁻¹ (ℓ × id)(Z)` meet each `W` with excess one less; for a smooth
projective `X` the smoothness hypothesis is `a3m_roberts_rank` (`a3h_roberts_rel_X`).

Source: J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970* (1972), 89–96,
Main Lemma and §1; S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3
(1994), §2 (the main lemma over a base); Kleiman, *The transversality of a general translate*
(1974), proof of Theorem 2. HC no distance; AV milestone no distance.
-/

noncomputable section

open MvPolynomial TensorProduct

namespace HodgeLean.Adapters

section Block

variable {ρ σ : Type} [Fintype ρ] [Fintype σ]

/-- The block matrix of `ℓ × id`: `y_i ↦ Σ_k ℓ_{ik} x_k`, `t ↦ t`. -/
def a3h_block (a : ρ × σ → ℂ) : Matrix (ρ ⊕ Unit) (σ ⊕ Unit) ℂ :=
  Matrix.fromBlocks (a3r_mat a) 0 0 1

omit [Fintype ρ] [Fintype σ] in
@[simp] theorem a3h_block_inl_inl (a : ρ × σ → ℂ) (i : ρ) (k : σ) :
    a3h_block a (Sum.inl i) (Sum.inl k) = a (i, k) := rfl

omit [Fintype ρ] [Fintype σ] in
@[simp] theorem a3h_block_inl_inr (a : ρ × σ → ℂ) (i : ρ) (u : Unit) :
    a3h_block a (Sum.inl i) (Sum.inr u) = 0 := rfl

omit [Fintype ρ] [Fintype σ] in
@[simp] theorem a3h_block_inr_inl (a : ρ × σ → ℂ) (u : Unit) (k : σ) :
    a3h_block a (Sum.inr u) (Sum.inl k) = 0 := rfl

omit [Fintype ρ] [Fintype σ] in
@[simp] theorem a3h_block_inr_inr (a : ρ × σ → ℂ) (u v : Unit) :
    a3h_block a (Sum.inr u) (Sum.inr v) = 1 := rfl

omit [Fintype ρ] in
theorem a3h_lin_block_inl (a : ρ × σ → ℂ) (i : ρ) :
    a3r_lin (a3h_block a) (X (Sum.inl i)) = ∑ k, C (a (i, k)) * X (Sum.inl k) := by
  rw [a3r_lin_X, Fintype.sum_sum_type]
  simp

omit [Fintype ρ] in
theorem a3h_lin_block_inr (a : ρ × σ → ℂ) (u : Unit) :
    a3r_lin (a3h_block a) (X (Sum.inr u)) = X (Sum.inr u) := by
  rw [a3r_lin_X, Fintype.sum_sum_type]
  simp

end Block

/-! ## Generic secants over the line -/

section Secant

variable {ρ σ : Type} [Fintype ρ] [Fintype σ] [DecidableEq σ]

omit [Fintype ρ] [DecidableEq σ] in
/-- A complex point of `V(P)`, for a proper ideal `P`. -/
theorem a3h_exists_point_quot (P : Ideal (MvPolynomial (σ ⊕ Unit) ℂ)) (hP : P ≠ ⊤) :
    ∃ e : MvPolynomial (σ ⊕ Unit) ℂ ⧸ P →ₐ[ℂ] ℂ, True := by
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal (K := ℂ) hM
  have hPx : ∀ F ∈ P, aeval x F = 0 := by
    intro F hF
    have := hPM hF
    rw [hx, MvPolynomial.mem_vanishingIdeal_singleton_iff] at this
    exact this
  exact ⟨Ideal.Quotient.liftₐ P (aeval x) hPx, trivial⟩

omit [Fintype ρ] [DecidableEq σ] in
/-- `t ⊗ 1 - 1 ⊗ t` is nonzero in `ℂ[W] ⊗ ℂ[Z]` unless `W` and `Z` lie in the same fibre
`t = c`: complex points of `W` and `Z` send it to `c - c'`. -/
theorem a3h_δt_ne_zero (PW PZ : Ideal (MvPolynomial (σ ⊕ Unit) ℂ)) [PW.IsPrime] [PZ.IsPrime]
    (hZW : ∀ c : ℂ, X (Sum.inr ()) - C c ∉ PZ ∨ X (Sum.inr ()) - C c ∉ PW) :
    a3r_δD PW PZ (Sum.inr ()) ≠ 0 := by
  obtain ⟨e, -⟩ := a3h_exists_point_quot PW (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨e', -⟩ := a3h_exists_point_quot PZ (Ideal.IsPrime.ne_top inferInstance)
  intro h0
  set c := e (Ideal.Quotient.mk PW (X (Sum.inr ())))
  set c' := e' (Ideal.Quotient.mk PZ (X (Sum.inr ())))
  -- `t = c` on `Z`
  let Φ : (MvPolynomial (σ ⊕ Unit) ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial (σ ⊕ Unit) ℂ ⧸ PZ) →ₐ[ℂ]
      MvPolynomial (σ ⊕ Unit) ℂ ⧸ PZ :=
    Algebra.TensorProduct.lift ((Algebra.ofId ℂ _).comp e) (AlgHom.id ℂ _)
      fun _ _ => Commute.all _ _
  have h1 := congrArg Φ h0
  rw [map_zero, a3r_δD, map_sub, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.lift_tmul, map_one, map_one, mul_one, one_mul] at h1
  have hZ : X (Sum.inr ()) - C c ∈ PZ := by
    rw [← neg_mem_iff, neg_sub, ← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    convert h1 using 2
    · simp [Algebra.ofId_apply, c]
      rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
    · rfl
  -- `t = c'` on `W`
  let Ψ : (MvPolynomial (σ ⊕ Unit) ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial (σ ⊕ Unit) ℂ ⧸ PZ) →ₐ[ℂ]
      MvPolynomial (σ ⊕ Unit) ℂ ⧸ PW :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ _) ((Algebra.ofId ℂ _).comp e')
      fun _ _ => Commute.all _ _
  have h2 := congrArg Ψ h0
  rw [map_zero, a3r_δD, map_sub, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.lift_tmul, map_one, map_one, mul_one, one_mul] at h2
  have hW : X (Sum.inr ()) - C c' ∈ PW := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    convert h2 using 2
    · simp [Algebra.ofId_apply, c']
    · rfl
  -- `c = c'`, from a point of `W × Z`
  have hcc : c = c' := by
    let χ : (MvPolynomial (σ ⊕ Unit) ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial (σ ⊕ Unit) ℂ ⧸ PZ) →ₐ[ℂ] ℂ :=
      Algebra.TensorProduct.lift e e' fun _ _ => Commute.all _ _
    have h3 := congrArg χ h0
    rw [map_zero, a3r_δD, map_sub, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lift_tmul, map_one, map_one, mul_one, one_mul, sub_eq_zero] at h3
    exact h3
  rcases hZW c with h | h
  · exact h hZ
  · exact h (hcc ▸ hW)

set_option synthInstance.maxHeartbeats 200000 in
/-- **Generic secants for `ℓ × id`.** For generic `ℓ`, pairs `(w, z) ∈ V(P_W) × V(P_Z)` with
`w_j ≠ z_j` and the same image under `ℓ × id` have dimension at most
`dim W + dim Z - (n + 2)`, unless `W` and `Z` lie in one fibre `t = c`: the secant hypothesis of
`a3k_roberts_main_rel` for the block matrix `a3h_block a`.
Source: J. Roberts, *Chow's moving lemma* (1972), proof of the Main Lemma; S. Bloch, *The moving
lemma for higher Chow groups* (1994), §2. -/
theorem a3h_generic_secant_rel (PW PZ : Ideal (MvPolynomial (σ ⊕ Unit) ℂ)) [PW.IsPrime]
    [PZ.IsPrime] (hZW : ∀ c : ℂ, X (Sum.inr ()) - C c ∉ PZ ∨ X (Sum.inr ()) - C c ∉ PW) :
    a3r_Generic {a : ρ × σ → ℂ | ∀ (j : σ ⊕ Unit)
      (𝔓 : Ideal ((MvPolynomial (σ ⊕ Unit) ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial (σ ⊕ Unit) ℂ ⧸ PZ))),
      𝔓.IsPrime → a3r_δD PW PZ j ∉ 𝔓 →
      (∀ i, ∑ k, algebraMap ℂ _ (a3h_block a i k) * a3r_δD PW PZ k - 0 ∈ 𝔓) →
      ringKrullDim (_ ⧸ 𝔓) + Fintype.card (ρ ⊕ Unit) ≤
        ringKrullDim ((MvPolynomial (σ ⊕ Unit) ℂ ⧸ PW) ⊗[ℂ]
          (MvPolynomial (σ ⊕ Unit) ℂ ⧸ PZ))} := by
  classical
  set A := MvPolynomial (σ ⊕ Unit) ℂ
  set D := (A ⧸ PW) ⊗[ℂ] (A ⧸ PZ)
  set δt := a3r_δD PW PZ (Sum.inr ())
  have : Algebra.FiniteType ℂ (A ⧸ PW) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : Algebra.FiniteType ℂ (A ⧸ PZ) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : IsDomain D := hc9k8_isDomain_tensorProduct
  set D' := D ⧸ Ideal.span {δt}
  have : Algebra.FiniteType ℂ D' :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have hδt : δt ∈ nonZeroDivisors D := mem_nonZeroDivisors_of_ne_zero (a3h_δt_ne_zero PW PZ hZW)
  have hdrop : ringKrullDim D' + 1 ≤ ringKrullDim D :=
    ringKrullDim_quotient_succ_le_of_nonZeroDivisor hδt
  refine (a3r_generic_iInter_fintype _ fun j => a3r_generic_linear (ρ := ρ) D'
    (fun k => Ideal.Quotient.mk _ (a3r_δD PW PZ (Sum.inl k))) (fun _ => 0) j).mono
    fun a ha j 𝔓 h𝔓 hj hrel => ?_
  have ht : δt ∈ 𝔓 := by
    have := hrel (Sum.inr ())
    rw [Fintype.sum_sum_type] at this
    simp only [a3h_block_inr_inl, a3h_block_inr_inr, map_zero, zero_mul, Finset.sum_const_zero,
      zero_add, map_one, one_mul, Finset.univ_unique, Finset.sum_singleton, sub_zero] at this
    exact this
  rcases j with j | u
  · have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {δt})) ≤ 𝔓 := by
      rw [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
      exact ht
    set 𝔓' := 𝔓.map (Ideal.Quotient.mk (Ideal.span {δt}))
    have h𝔓' : 𝔓'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    have hmem : ∀ d, Ideal.Quotient.mk _ d ∈ 𝔓' ↔ d ∈ 𝔓 := by
      intro d
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
        sup_eq_left.2 hker]
    have hb := ha j 𝔓' h𝔓' (fun h => hj ((hmem _).1 h)) fun i => by
      rw [sub_zero]
      have := hrel (Sum.inl i)
      rw [Fintype.sum_sum_type, sub_zero] at this
      simp only [a3h_block_inl_inl, a3h_block_inl_inr, map_zero, zero_mul,
        Finset.sum_const_zero, add_zero] at this
      rw [← hmem] at this
      convert this using 1
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul]
      rfl
    have hle : Ideal.span {δt} ≤ 𝔓 := by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact ht
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE (R := D) hle)] at hb
    rw [Fintype.card_sum, Fintype.card_unit, Nat.cast_add, Nat.cast_one, ← add_assoc]
    calc _ ≤ ringKrullDim D' + 1 := by gcongr
      _ ≤ _ := hdrop
  · exact absurd ht hj

end Secant

/-! ## Generic unramifiedness relative to the line -/

section Unramified

set_option synthInstance.maxHeartbeats 400000

variable {ρ σ : Type} [Fintype ρ] [Fintype σ]

/-- `ℂ[x, t]/I` as an algebra over the line `ℂ[t]`. -/
abbrev a3h_algT (I : Ideal (MvPolynomial (σ ⊕ Unit) ℂ)) :
    Algebra (MvPolynomial Unit ℂ) (MvPolynomial (σ ⊕ Unit) ℂ ⧸ I) :=
  ((Ideal.Quotient.mk I).comp (rename Sum.inr).toRingHom).toAlgebra

omit [Fintype σ] in
/-- The differentials of the coordinates `x` span the differentials of `ℂ[x, t]/I` over `ℂ[t]`. -/
theorem a3h_span_D_X_rel (I : Ideal (MvPolynomial (σ ⊕ Unit) ℂ)) :
    letI := a3h_algT I
    Submodule.span (MvPolynomial (σ ⊕ Unit) ℂ ⧸ I)
      (Set.range fun k => KaehlerDifferential.D (MvPolynomial Unit ℂ)
        (MvPolynomial (σ ⊕ Unit) ℂ ⧸ I) (Ideal.Quotient.mk I (X (Sum.inl k)))) = ⊤ := by
  letI := a3h_algT I
  set A := MvPolynomial (σ ⊕ Unit) ℂ ⧸ I
  set T := MvPolynomial Unit ℂ
  set S := Submodule.span A (Set.range fun k =>
    KaehlerDifferential.D T A (Ideal.Quotient.mk I (X (Sum.inl k))))
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation T A, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction F using MvPolynomial.induction_on with
  | C c =>
    have : Ideal.Quotient.mk I (C c : MvPolynomial (σ ⊕ Unit) ℂ) = algebraMap T A (C c) := by
      change _ = Ideal.Quotient.mk I (rename Sum.inr (C c))
      rw [rename_C]
    rw [this, Derivation.map_algebraMap]
    exact zero_mem _
  | add F G hF hG => rw [map_add, map_add]; exact add_mem hF hG
  | mul_X F i hF =>
    rw [map_mul, Derivation.leibniz]
    refine add_mem (S.smul_mem _ ?_) (S.smul_mem _ hF)
    rcases i with k | u
    · exact Submodule.subset_span ⟨k, rfl⟩
    · have : Ideal.Quotient.mk I (X (Sum.inr u) : MvPolynomial (σ ⊕ Unit) ℂ) =
          algebraMap T A (X u) := by
        change _ = Ideal.Quotient.mk I (rename Sum.inr (X u))
        rw [rename_X]
      rw [this, Derivation.map_algebraMap]
      exact zero_mem _

set_option maxHeartbeats 400000 in
/-- **Generic unramifiedness for `ℓ × id`.** At a point `𝔶` of `V(I) ⊆ 𝔸^{N+1} × 𝔸¹` where the
differentials over the line have rank at most `card ρ`, for generic `ℓ` the projection
`ℂ[y, t] → ℂ[x, t]/I`, `y ↦ ℓ x`, `t ↦ t`, is unramified at `𝔶`.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 8.7 and III, Exercise 10.3; J. Roberts,
*Chow's moving lemma* (1972), §1; S. Bloch, *The moving lemma for higher Chow groups* (1994), §2. -/
theorem a3h_generic_isUnramifiedAt_rel [DecidableEq σ] (I : Ideal (MvPolynomial (σ ⊕ Unit) ℂ))
    (𝔶 : Ideal (MvPolynomial (σ ⊕ Unit) ℂ ⧸ I)) [𝔶.IsPrime]
    (hrank : letI := a3h_algT I
      Module.finrank 𝔶.ResidueField (𝔶.ResidueField ⊗[MvPolynomial (σ ⊕ Unit) ℂ ⧸ I]
        Ω[MvPolynomial (σ ⊕ Unit) ℂ ⧸ I⁄MvPolynomial Unit ℂ]) ≤ Fintype.card ρ) :
    a3r_Generic {a : ρ × σ → ℂ |
      letI : Algebra (MvPolynomial (ρ ⊕ Unit) ℂ) (MvPolynomial (σ ⊕ Unit) ℂ ⧸ I) :=
        ((Ideal.Quotient.mk I).comp (a3r_lin (a3h_block a)).toRingHom).toAlgebra
      Algebra.IsUnramifiedAt (MvPolynomial (ρ ⊕ Unit) ℂ) 𝔶} := by
  classical
  letI := a3h_algT I
  set A := MvPolynomial (σ ⊕ Unit) ℂ ⧸ I
  set T := MvPolynomial Unit ℂ
  set K := 𝔶.ResidueField
  have : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : IsScalarTower ℂ T A := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = Ideal.Quotient.mk I (rename Sum.inr (algebraMap ℂ T c))
    rw [MvPolynomial.algebraMap_eq, rename_C, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap]
  have : Algebra.FiniteType T A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ T A
  set v : σ → K ⊗[A] Ω[A⁄T] := fun k =>
    (1 : K) ⊗ₜ KaehlerDifferential.D T A (Ideal.Quotient.mk I (X (Sum.inl k)))
  have h1 : ∀ ω : Ω[A⁄T], (1 : K) ⊗ₜ[A] ω ∈ Submodule.span K (Set.range v) := by
    intro ω
    have hω : ω ∈ Submodule.span A (Set.range fun k =>
        KaehlerDifferential.D T A (Ideal.Quotient.mk I (X (Sum.inl k)))) := by
      rw [a3h_span_D_X_rel]; exact Submodule.mem_top
    induction hω using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => rw [tmul_zero]; exact zero_mem _
    | add y y' _ _ hy hy' => rw [tmul_add]; exact add_mem hy hy'
    | smul r y _ hy =>
      rw [← TensorProduct.smul_tmul, ← algebraMap_smul K r, smul_eq_mul, mul_one,
        show (algebraMap A K r) ⊗ₜ[A] y = (algebraMap A K r) • ((1 : K) ⊗ₜ[A] y) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ hy
  have hv : Submodule.span K (Set.range v) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    clear ‹z ∈ ⊤›
    induction z using TensorProduct.inductionOn with
    | tmul x ω =>
      have : x ⊗ₜ[A] ω = x • ((1 : K) ⊗ₜ[A] ω) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (h1 ω)
    | add y y' hy hy' => exact add_mem hy hy'
  have : Module.Finite A Ω[A⁄T] := inferInstance
  have : FiniteDimensional K (K ⊗[A] Ω[A⁄T]) := inferInstance
  refine (a3r_generic_span (ρ := ρ) v hv hrank).mono fun a ha => ?_
  set R := MvPolynomial (ρ ⊕ Unit) ℂ
  let _ : Algebra R A := ((Ideal.Quotient.mk I).comp (a3r_lin (a3h_block a)).toRingHom).toAlgebra
  let _ : Algebra T R := (rename Sum.inr).toRingHom.toAlgebra
  have : IsScalarTower T R A := IsScalarTower.of_algebraMap_eq fun p => by
    change Ideal.Quotient.mk I (rename Sum.inr p) =
      Ideal.Quotient.mk I (a3r_lin (a3h_block a) (rename Sum.inr p))
    congr 1
    induction p using MvPolynomial.induction_on with
    | C c => simp [a3r_lin_C]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p u hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp only [rename_X, a3h_lin_block_inr]
  have : Algebra.FiniteType R A := Algebra.FiniteType.of_restrictScalars_finiteType T R A
  set L : K ⊗[A] Ω[A⁄T] →ₗ[K] K ⊗[A] Ω[A⁄R] :=
    (KaehlerDifferential.map T R A A).baseChange K
  have hLsurj : Function.Surjective L := by
    rw [show (L : K ⊗[A] Ω[A⁄T] → K ⊗[A] Ω[A⁄R]) = _ from
      LinearMap.baseChange_eq_lTensor (KaehlerDifferential.map T R A A)]
    exact LinearMap.lTensor_surjective _ (KaehlerDifferential.map_surjective T R A)
  have hLv : ∀ k, L (v k) =
      (1 : K) ⊗ₜ KaehlerDifferential.D R A (Ideal.Quotient.mk I (X (Sum.inl k))) := by
    intro k
    simp only [L, v, LinearMap.baseChange_tmul, KaehlerDifferential.map_D]
    rfl
  have hsm : ∀ (c : ℂ) (ω : Ω[A⁄R]), algebraMap ℂ K c • ((1 : K) ⊗ₜ[A] ω) =
      (1 : K) ⊗ₜ[A] (algebraMap ℂ A c • ω) := by
    intro c ω
    rw [IsScalarTower.algebraMap_apply ℂ A K, algebraMap_smul, TensorProduct.tmul_smul]
  have hLw : ∀ i, L (∑ k, algebraMap ℂ K (a (i, k)) • v k) = 0 := by
    intro i
    rw [map_sum]
    simp only [map_smul, hLv, hsm]
    rw [← TensorProduct.tmul_sum]
    have : ∑ k, algebraMap ℂ A (a (i, k)) •
        KaehlerDifferential.D R A (Ideal.Quotient.mk I (X (Sum.inl k))) =
        KaehlerDifferential.D R A (algebraMap R A (X (Sum.inl i))) := by
      change _ = KaehlerDifferential.D R A
        (Ideal.Quotient.mk I (a3r_lin (a3h_block a) (X (Sum.inl i))))
      rw [a3h_lin_block_inl, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have e1 : Ideal.Quotient.mk I (C (a (i, k)) : MvPolynomial (σ ⊕ Unit) ℂ) =
          algebraMap R A (C (a (i, k))) := by
        change _ = Ideal.Quotient.mk I (a3r_lin (a3h_block a) (C (a (i, k))))
        rw [a3r_lin_C]
      have e2 : Ideal.Quotient.mk I (C (a (i, k)) : MvPolynomial (σ ⊕ Unit) ℂ) =
          algebraMap ℂ A (a (i, k)) := by
        rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      rw [map_mul, Derivation.leibniz, e1, Derivation.map_algebraMap, smul_zero, add_zero, ← e1,
        e2]
    rw [this, Derivation.map_algebraMap, tmul_zero]
  have hzero : ∀ z, L z = 0 := by
    intro z
    have hz : z ∈ Submodule.span K (Set.range fun i => ∑ k, algebraMap ℂ K (a (i, k)) • v k) :=
      ha ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hLw i
    | zero => exact map_zero L
    | add y y' _ _ hy hy' => rw [map_add, hy, hy', add_zero]
    | smul r y _ hy => rw [map_smul, hy, smul_zero]
  have hsub : Subsingleton (K ⊗[A] Ω[A⁄R]) := ⟨fun x y => by
    obtain ⟨x', rfl⟩ := hLsurj x
    obtain ⟨y', rfl⟩ := hLsurj y
    rw [hzero, hzero]⟩
  have hnot : (⟨𝔶, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A Ω[A⁄R] := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.2 hsub
  have hloc : (⟨𝔶, inferInstance⟩ : PrimeSpectrum A) ∈ Algebra.unramifiedLocus R A := by
    rw [Algebra.unramifiedLocus_eq_compl_support]
    exact hnot
  exact hloc

end Unramified

/-! ## The relative cone over `X × 𝔸¹` and finiteness of `ℓ × id` -/

section FiniteRel

variable {ρ σ : Type} [Fintype ρ] [Fintype σ]

/-- The ideal `I_X[t]` of the relative affine cone over `X × 𝔸¹`. -/
abbrev a3h_IXr (IX : Ideal (MvPolynomial σ ℂ)) : Ideal (MvPolynomial (σ ⊕ Unit) ℂ) :=
  Ideal.map (rename Sum.inl) IX

/-- `ℓ × id` is finite on the relative cone when `ℓ` is finite on the cone: the coordinates `x_k`
satisfy the integral equations over `ℂ[y]` they satisfy on `X`, and `t` lies in `ℂ[y, t]`.
Source: Atiyah–Macdonald, *Introduction to Commutative Algebra*, Proposition 5.1 and
Corollary 5.2 (integral elements form a ring). -/
theorem a3h_finite_rel (IX : Ideal (MvPolynomial σ ℂ)) (a : ρ × σ → ℂ)
    (hfin : ((Ideal.Quotient.mk IX).comp (a3r_lin (a3r_mat a)).toRingHom).Finite) :
    ((Ideal.Quotient.mk (a3h_IXr IX)).comp (a3r_lin (a3h_block a)).toRingHom).Finite := by
  set f := (Ideal.Quotient.mk (a3h_IXr IX)).comp (a3r_lin (a3h_block a)).toRingHom
  set φ := (Ideal.Quotient.mk IX).comp (a3r_lin (a3r_mat a)).toRingHom
  have hle : IX ≤ (a3h_IXr IX).comap (rename (R := ℂ) (Sum.inl : σ → σ ⊕ Unit)) :=
    Ideal.le_comap_map
  let ψ : MvPolynomial σ ℂ ⧸ IX →+* MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX :=
    Ideal.quotientMap _ (rename Sum.inl).toRingHom hle
  have hcomm : ψ.comp φ = f.comp (rename (R := ℂ) (Sum.inl : ρ → ρ ⊕ Unit)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · simp [ψ, φ, f, a3r_lin_C]
    · simp only [ψ, φ, f, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Ideal.quotientMap_mk, rename_X, a3h_lin_block_inl, a3r_lin_X, map_sum, map_mul,
        rename_C]
      rw [Fintype.sum_sum_type]
      simp [a3r_mat]
  have hgen : ∀ i, f.IsIntegralElem (Ideal.Quotient.mk (a3h_IXr IX) (X i)) := by
    rintro (k | u)
    · obtain ⟨p, hp, hpx⟩ := hfin.to_isIntegral (Ideal.Quotient.mk IX (X k))
      refine ⟨p.map (rename Sum.inl).toRingHom, hp.map _, ?_⟩
      have h := congrArg ψ hpx
      rw [map_zero, Polynomial.hom_eval₂, hcomm] at h
      rw [Polynomial.eval₂_map]
      convert h using 2
      simp [ψ]
    · have : Ideal.Quotient.mk (a3h_IXr IX) (X (Sum.inr u) : MvPolynomial (σ ⊕ Unit) ℂ) =
          f (X (Sum.inr u)) := by
        simp [f, a3h_lin_block_inr]
      rw [this]
      exact f.isIntegralElem_map
  have hint : f.IsIntegral := by
    intro z
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction F using MvPolynomial.induction_on with
    | C c =>
      have : Ideal.Quotient.mk (a3h_IXr IX) (C c : MvPolynomial (σ ⊕ Unit) ℂ) = f (C c) := by
        simp [f, a3r_lin_C]
      rw [this]
      exact f.isIntegralElem_map
    | add F G hF hG => rw [map_add]; exact RingHom.IsIntegralElem.add f hF hG
    | mul_X F i hF => rw [map_mul]; exact RingHom.IsIntegralElem.mul f hF (hgen i)
  have : Algebra.FiniteType ℂ (MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have hft : f.FiniteType := by
    refine RingHom.FiniteType.of_comp_finiteType
      (f := algebraMap ℂ (MvPolynomial (ρ ⊕ Unit) ℂ)) ?_
    have : f.comp (algebraMap ℂ (MvPolynomial (ρ ⊕ Unit) ℂ)) =
        algebraMap ℂ (MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX) := by
      ext c
      simp [f, MvPolynomial.algebraMap_eq, a3r_lin_C]
      rfl
    rw [this]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  exact hint.to_finite hft

/-- The relative cone is prime of dimension `dim (cone over X) + 1`. -/
theorem a3h_IXr_isPrime_dim (IX : Ideal (MvPolynomial σ ℂ)) [IX.IsPrime] :
    (a3h_IXr IX).IsPrime ∧ ringKrullDim (MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX) =
      ringKrullDim (MvPolynomial σ ℂ ⧸ IX) + 1 := by
  obtain ⟨h1, h2⟩ := a3r_map_rename_isPrime (Sum.inl : σ → σ ⊕ Unit) Sum.inl_injective IX
  refine ⟨h1, h2.trans ?_⟩
  rw [Fintype.card_sum, Fintype.card_unit, Nat.add_sub_cancel_left]
  rfl

end FiniteRel

/-! ## Unramifiedness of `ℓ × id` from unramifiedness of `ℓ` -/

section UnramifiedTransfer

/-- If `S` is formally unramified over `R` and `S'` is generated over `R'` by the image of an
`R`-algebra map `S → S'`, then `S'` is formally unramified over `R'`: it is a quotient of the
base change `R' ⊗[R] S`.
Source: Stacks Project, Tag 00UR (unramified ring maps are stable under base change and
quotients). -/
theorem a3h_formallyUnramified_of_adjoin {R R' S S' : Type*} [CommRing R] [CommRing R']
    [CommRing S] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra R' S']
    [Algebra.FormallyUnramified R S] (γ : S →+* S')
    (hγ : ∀ r : R, γ (algebraMap R S r) = algebraMap R' S' (algebraMap R R' r))
    (h : ∀ z : S', z ∈ Algebra.adjoin R' (Set.range γ)) : Algebra.FormallyUnramified R' S' := by
  letI : Algebra R S' := ((algebraMap R' S').comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' rfl
  let γa : S →ₐ[R] S' := { γ with commutes' := hγ }
  let Φ : R' ⊗[R] S →ₐ[R'] S' :=
    Algebra.TensorProduct.lift (Algebra.ofId R' S') γa fun _ _ => Commute.all _ _
  have hle : Algebra.adjoin R' (Set.range γ) ≤ Φ.range := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp [Φ, γa]⟩
  exact Algebra.FormallyUnramified.of_surjective Φ fun z => hle (h z)

variable {ρ σ : Type} [Fintype ρ] [Fintype σ]

omit [Fintype ρ] in
/-- `rename ∘ ℓ = (ℓ × id) ∘ rename`. -/
theorem a3h_rename_lin (a : ρ × σ → ℂ) (r : MvPolynomial ρ ℂ) :
    rename Sum.inl (a3r_lin (a3r_mat a) r) =
      a3r_lin (a3h_block a) (rename (Sum.inl : ρ → ρ ⊕ Unit) r) := by
  induction r using MvPolynomial.induction_on with
  | C c => simp [a3r_lin_C]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp, rename_X, a3h_lin_block_inl, a3r_lin_X,
      map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [a3r_mat]


/-- The map `(ℂ[x]/I_X)_f → (ℂ[x, t]/I_X[t])_f` induced by `x ↦ x`. -/
def a3h_γ (IX : Ideal (MvPolynomial σ ℂ)) (f₀ : MvPolynomial σ ℂ) :
    Localization.Away (Ideal.Quotient.mk IX f₀) →+*
      Localization.Away (Ideal.Quotient.mk (a3h_IXr IX) (rename Sum.inl f₀)) :=
  IsLocalization.map (M := Submonoid.powers (Ideal.Quotient.mk IX f₀))
    (T := Submonoid.powers (Ideal.Quotient.mk (a3h_IXr IX) (rename Sum.inl f₀))) _
    (Ideal.quotientMap (a3h_IXr IX) (rename Sum.inl).toRingHom
      (Ideal.le_comap_map : IX ≤ (a3h_IXr IX).comap (rename (R := ℂ) (Sum.inl : σ → σ ⊕ Unit))))
    (by
      rintro _ ⟨m, rfl⟩
      exact ⟨m, by rw [map_pow]; rfl⟩)

omit [Fintype σ] in
theorem a3h_γ_algebraMap (IX : Ideal (MvPolynomial σ ℂ)) (f₀ : MvPolynomial σ ℂ)
    (F : MvPolynomial σ ℂ) :
    a3h_γ IX f₀ (algebraMap _ _ (Ideal.Quotient.mk IX F)) =
      algebraMap _ _ (Ideal.Quotient.mk (a3h_IXr IX) (rename Sum.inl F)) := by
  rw [a3h_γ, IsLocalization.map_eq]
  rfl

omit [Fintype σ] in
theorem a3h_γ_inv (IX : Ideal (MvPolynomial σ ℂ)) (f₀ : MvPolynomial σ ℂ) :
    a3h_γ IX f₀ (IsLocalization.mk' _ (1 : MvPolynomial σ ℂ ⧸ IX)
      (⟨Ideal.Quotient.mk IX f₀, 1, pow_one _⟩ : Submonoid.powers _)) =
    IsLocalization.mk' _ (1 : MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX)
      (⟨Ideal.Quotient.mk (a3h_IXr IX) (rename Sum.inl f₀), 1, pow_one _⟩ :
        Submonoid.powers _) := by
  rw [a3h_γ, IsLocalization.map_mk']
  congr 1
  exact map_one _

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- `(ℂ[x, t]/I_X[t])_f` is generated over `ℂ[y, t]` by the image of `(ℂ[x]/I_X)_f`. -/
theorem a3h_adjoin_rel (IX : Ideal (MvPolynomial σ ℂ)) (a : ρ × σ → ℂ) (f₀ : MvPolynomial σ ℂ) :
    letI : Algebra (MvPolynomial (ρ ⊕ Unit) ℂ) (MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX) :=
      ((Ideal.Quotient.mk (a3h_IXr IX)).comp (a3r_lin (a3h_block a)).toRingHom).toAlgebra
    ∀ z : Localization.Away (Ideal.Quotient.mk (a3h_IXr IX) (rename Sum.inl f₀)),
      z ∈ Algebra.adjoin (MvPolynomial (ρ ⊕ Unit) ℂ) (Set.range (a3h_γ IX f₀)) := by
  letI : Algebra (MvPolynomial (ρ ⊕ Unit) ℂ) (MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX) :=
    ((Ideal.Quotient.mk (a3h_IXr IX)).comp (a3r_lin (a3h_block a)).toRingHom).toAlgebra
  set T := Algebra.adjoin (MvPolynomial (ρ ⊕ Unit) ℂ) (Set.range (a3h_γ IX f₀))
  set S' := Localization.Away (Ideal.Quotient.mk (a3h_IXr IX) (rename Sum.inl f₀))
  have hγT : ∀ x, a3h_γ IX f₀ x ∈ T := fun x => Algebra.subset_adjoin ⟨x, rfl⟩
  have hR'T : ∀ r : MvPolynomial (ρ ⊕ Unit) ℂ, algebraMap _ S' r ∈ T := fun r => T.algebraMap_mem r
  have hbase : ∀ r : MvPolynomial (ρ ⊕ Unit) ℂ, algebraMap _ S' r =
      algebraMap (MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX) S'
        (Ideal.Quotient.mk (a3h_IXr IX) (a3r_lin (a3h_block a) r)) := fun r => rfl
  have hA' : ∀ F : MvPolynomial (σ ⊕ Unit) ℂ,
      algebraMap (MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX) S'
        (Ideal.Quotient.mk (a3h_IXr IX) F) ∈ T := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C c =>
      have := hR'T (C c)
      rwa [hbase, a3r_lin_C] at this
    | add p q hp hq => rw [map_add, map_add]; exact T.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, map_mul]
      refine T.mul_mem hp ?_
      rcases i with k | u
      · have := hγT (algebraMap _ _ (Ideal.Quotient.mk IX (X k)))
        rwa [a3h_γ_algebraMap, rename_X] at this
      · have := hR'T (X (Sum.inr u))
        rwa [hbase, a3h_lin_block_inr] at this
  intro z
  obtain ⟨⟨a', ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (Ideal.Quotient.mk (a3h_IXr IX) (rename Sum.inl f₀))) z
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a'
  have hinv := hγT (IsLocalization.mk' _ (1 : MvPolynomial σ ℂ ⧸ IX)
    (⟨Ideal.Quotient.mk IX f₀, 1, pow_one _⟩ : Submonoid.powers _))
  rw [a3h_γ_inv] at hinv
  have hmk : IsLocalization.mk' S' (Ideal.Quotient.mk (a3h_IXr IX) F)
      (⟨Ideal.Quotient.mk (a3h_IXr IX) (rename Sum.inl f₀) ^ m, m, rfl⟩ : Submonoid.powers _) =
      algebraMap _ S' (Ideal.Quotient.mk (a3h_IXr IX) F) *
        IsLocalization.mk' S' (1 : MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX)
          (⟨Ideal.Quotient.mk (a3h_IXr IX) (rename Sum.inl f₀), 1, pow_one _⟩ :
            Submonoid.powers _) ^ m := by
    rw [← IsLocalization.mk'_pow, IsLocalization.mul_mk'_eq_mk'_of_mul, one_pow, mul_one]
    rfl
  dsimp only
  rw [hmk]
  exact T.mul_mem (hA' F) (T.pow_mem hinv m)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- If `ℂ[y] → (ℂ[x]/I_X)_f` is formally unramified, so is `ℂ[y, t] → (ℂ[x, t]/I_X[t])_f`: the
latter is generated over `ℂ[y, t]` by the image of the former
(`a3h_formallyUnramified_of_adjoin`).
Source: Stacks Project, Tags 00UR and 02FL (unramified ring maps are stable under base change
and quotients); Hartshorne, *Algebraic Geometry*, III, Exercise 10.3. -/
theorem a3h_formallyUnramified_rel (IX : Ideal (MvPolynomial σ ℂ)) (a : ρ × σ → ℂ)
    (f₀ : MvPolynomial σ ℂ)
    (h : letI : Algebra (MvPolynomial ρ ℂ) (MvPolynomial σ ℂ ⧸ IX) :=
        ((Ideal.Quotient.mk IX).comp (a3r_lin (a3r_mat a)).toRingHom).toAlgebra
      Algebra.FormallyUnramified (MvPolynomial ρ ℂ) (Localization.Away (Ideal.Quotient.mk IX f₀))) :
    letI : Algebra (MvPolynomial (ρ ⊕ Unit) ℂ) (MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX) :=
      ((Ideal.Quotient.mk (a3h_IXr IX)).comp (a3r_lin (a3h_block a)).toRingHom).toAlgebra
    Algebra.FormallyUnramified (MvPolynomial (ρ ⊕ Unit) ℂ)
      (Localization.Away (Ideal.Quotient.mk (a3h_IXr IX) (rename Sum.inl f₀))) := by
  classical
  letI : Algebra (MvPolynomial ρ ℂ) (MvPolynomial σ ℂ ⧸ IX) :=
    ((Ideal.Quotient.mk IX).comp (a3r_lin (a3r_mat a)).toRingHom).toAlgebra
  letI : Algebra (MvPolynomial (ρ ⊕ Unit) ℂ) (MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX) :=
    ((Ideal.Quotient.mk (a3h_IXr IX)).comp (a3r_lin (a3h_block a)).toRingHom).toAlgebra
  letI : Algebra (MvPolynomial ρ ℂ) (MvPolynomial (ρ ⊕ Unit) ℂ) :=
    (rename (R := ℂ) (Sum.inl : ρ → ρ ⊕ Unit)).toRingHom.toAlgebra
  refine a3h_formallyUnramified_of_adjoin (R := MvPolynomial ρ ℂ)
    (S := Localization.Away (Ideal.Quotient.mk IX f₀)) (a3h_γ IX f₀) (fun r => ?_)
    (a3h_adjoin_rel IX a f₀)
  rw [IsScalarTower.algebraMap_apply (MvPolynomial ρ ℂ) (MvPolynomial σ ℂ ⧸ IX)]
  change a3h_γ IX f₀ (algebraMap _ _ (Ideal.Quotient.mk IX (a3r_lin (a3r_mat a) r))) = _
  rw [a3h_γ_algebraMap, a3h_rename_lin]
  rfl

end UnramifiedTransfer

/-! ## Roberts' main lemma over the line for a generic projection -/

section MainRel

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 400000

variable {σ : Type} [Fintype σ] [DecidableEq σ]

set_option maxHeartbeats 400000 in
/-- **Roberts' main lemma over the line.** Let `X = V(I_X)` have affine cone of dimension `n + 1`,
with differentials of rank at most `n + 1` at its relevant points (`X` smooth, `a3m_roberts_rank`),
and let `Z = V(P_Z) ⊂ X × 𝔸¹` dominate the line and meet the finitely many
`W = V(P_W)` with excess at most `k + 1` at their relevant components. For a generic `ℓ`,
`ℓ × id` is finite on the relative cone and every component `Z' ≠ Z` of `(ℓ × id)⁻¹ (ℓ × id)(Z)`
meets each `W` with excess at most `k` at its relevant points.
Source: J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970* (1972), 89–96,
Main Lemma; S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
§2 (the main lemma over a base); Fulton, *Intersection Theory*, second edition,
Example 11.4.1. -/
theorem a3h_roberts_rel (IX : Ideal (MvPolynomial σ ℂ)) [IX.IsPrime]
    (hIXh : IX.IsHomogeneous (homogeneousSubmodule σ ℂ)) (n : ℕ)
    (hIX : ringKrullDim (MvPolynomial σ ℂ ⧸ IX) = (n + 1 : ℕ))
    (PZ : Ideal (MvPolynomial (σ ⊕ Unit) ℂ)) [PZ.IsPrime] (hXZ : a3h_IXr IX ≤ PZ)
    (SW : Finset (Ideal (MvPolynomial (σ ⊕ Unit) ℂ))) (hSW : ∀ W ∈ SW, W.IsPrime)
    (hZW : ∀ W ∈ SW, ∀ c : ℂ, X (Sum.inr ()) - C c ∉ PZ ∨ X (Sum.inr ()) - C c ∉ W) (k : ℕ)
    (hexc : ∀ W ∈ SW, ∀ 𝔶 ∈ (PZ ⊔ W).minimalPrimes, (∃ j, X (Sum.inl j) ∉ 𝔶) →
      ringKrullDim (MvPolynomial (σ ⊕ Unit) ℂ ⧸ 𝔶) +
          ringKrullDim (MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX) ≤
        ringKrullDim (MvPolynomial (σ ⊕ Unit) ℂ ⧸ PZ) +
          ringKrullDim (MvPolynomial (σ ⊕ Unit) ℂ ⧸ W) + (k + 1 : ℕ))
    (hsm : ∀ (𝔶 : Ideal (MvPolynomial σ ℂ ⧸ IX)) [𝔶.IsPrime],
      (∃ j, Ideal.Quotient.mk IX (X j) ∉ 𝔶) →
      Module.finrank 𝔶.ResidueField
        (𝔶.ResidueField ⊗[MvPolynomial σ ℂ ⧸ IX] Ω[MvPolynomial σ ℂ ⧸ IX⁄ℂ]) ≤ n + 1) :
    a3r_Generic {a : Fin (n + 1) × σ → ℂ |
      ((Ideal.Quotient.mk (a3h_IXr IX)).comp (a3r_lin (a3h_block a)).toRingHom).Finite ∧
      ∀ Q' : Ideal (MvPolynomial (σ ⊕ Unit) ℂ), Q'.IsPrime → a3h_IXr IX ≤ Q' →
        Q'.comap (a3r_lin (a3h_block a)) = PZ.comap (a3r_lin (a3h_block a)) → Q' ≠ PZ →
        ∀ W ∈ SW, ∀ Y : Ideal (MvPolynomial (σ ⊕ Unit) ℂ), Y.IsPrime → Q' ⊔ W ≤ Y →
          (∃ j, X (Sum.inl j) ∉ Y) →
          ringKrullDim (MvPolynomial (σ ⊕ Unit) ℂ ⧸ Y) +
              ringKrullDim (MvPolynomial (σ ⊕ Unit) ℂ ⧸ a3h_IXr IX) ≤
            ringKrullDim (MvPolynomial (σ ⊕ Unit) ℂ ⧸ PZ) +
              ringKrullDim (MvPolynomial (σ ⊕ Unit) ℂ ⧸ W) + k} := by
  classical
  set B := MvPolynomial (σ ⊕ Unit) ℂ
  set IXr := a3h_IXr IX
  set R := MvPolynomial (Fin (n + 1) ⊕ Unit) ℂ
  obtain ⟨hIXr, hdimr⟩ := a3h_IXr_isPrime_dim IX
  have hdimX : ringKrullDim (B ⧸ IXr) = Fintype.card (Fin (n + 1) ⊕ Unit) := by
    rw [hdimr, hIX, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    rfl
  -- the generic conditions
  set G : Set (Fin (n + 1) × σ → ℂ) :=
    {a | ((Ideal.Quotient.mk IX).comp (a3r_lin (a3r_mat a)).toRingHom).Finite} ∩
    {a | ∀ W ∈ (SW : Set (Ideal B)), ∀ (j : σ ⊕ Unit) (𝔓 : Ideal ((B ⧸ W) ⊗[ℂ] (B ⧸ PZ))),
      𝔓.IsPrime → a3r_δD W PZ j ∉ 𝔓 →
      (∀ i, ∑ k, algebraMap ℂ _ (a3h_block a i k) * a3r_δD W PZ k - 0 ∈ 𝔓) →
      ringKrullDim (_ ⧸ 𝔓) + Fintype.card (Fin (n + 1) ⊕ Unit) ≤
        ringKrullDim ((B ⧸ W) ⊗[ℂ] (B ⧸ PZ))} ∩
    {a | ∀ W ∈ (SW : Set (Ideal B)), ∀ 𝔶 ∈ (PZ ⊔ W).minimalPrimes,
      (∃ j, X (Sum.inl j) ∉ 𝔶) →
      ((Ideal.Quotient.mk IX).comp (a3r_lin (a3r_mat a)).toRingHom).Finite → ∃ f ∉ 𝔶,
      letI : Algebra R (B ⧸ IXr) :=
        ((Ideal.Quotient.mk IXr).comp (a3r_lin (a3h_block a)).toRingHom).toAlgebra
      Algebra.FormallyUnramified R (Localization.Away (Ideal.Quotient.mk IXr f))}
  have hG : a3r_Generic G := by
    have hfinX : a3r_Generic {a : Fin (n + 1) × σ → ℂ |
        ((Ideal.Quotient.mk IX).comp (a3r_lin (a3r_mat a)).toRingHom).Finite} := by
      exact a3r_generic_finite IX hIXh hIX
    refine (hfinX.inter (a3r_generic_biInter _ SW.finite_toSet _ fun W hW => ?_)).inter
      (a3r_generic_biInter _ SW.finite_toSet _ fun W hW => ?_)
    · have := hSW W hW
      exact a3h_generic_secant_rel W PZ (hZW W hW)
    · have := hSW W hW
      refine a3r_generic_biInter _ (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _) _
        fun 𝔶 h𝔶 => a3r_generic_of_imp _ _ fun hrel => ?_
      have h𝔶p : 𝔶.IsPrime := h𝔶.1.1
      have hX𝔶 : IXr ≤ 𝔶 := hXZ.trans (le_sup_left.trans h𝔶.1.2)
      set 𝔶₀ := 𝔶.comap (rename (R := ℂ) (Sum.inl : σ → σ ⊕ Unit))
      have h𝔶₀ : 𝔶₀.IsPrime := Ideal.comap_isPrime _ _
      have hX₀ : IX ≤ 𝔶₀ := fun F hF => hX𝔶 (Ideal.mem_map_of_mem _ hF)
      obtain ⟨j, hj⟩ := hrel
      have hj₀ : X j ∉ 𝔶₀ := by rw [Ideal.mem_comap, rename_X]; exact hj
      have hmap : (𝔶₀.map (Ideal.Quotient.mk IX)).IsPrime := Ideal.map_isPrime_of_surjective
        Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
      have hcomap : (𝔶₀.map (Ideal.Quotient.mk IX)).comap (Ideal.Quotient.mk IX) = 𝔶₀ := by
        rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
          sup_eq_left.2 hX₀]
      have hj' : Ideal.Quotient.mk IX (X j) ∉ 𝔶₀.map (Ideal.Quotient.mk IX) := by
        rw [← Ideal.mem_comap, hcomap]; exact hj₀
      refine (a3r_generic_isUnramifiedAt (ρ := Fin (n + 1)) IX _
        ((hsm _ ⟨j, hj'⟩).trans (by simp))).mono fun a ha hfin => ?_
      let _ : Algebra (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial σ ℂ ⧸ IX) :=
        ((Ideal.Quotient.mk IX).comp (a3r_lin (a3r_mat a)).toRingHom).toAlgebra
      have : Algebra.IsUnramifiedAt (MvPolynomial (Fin (n + 1)) ℂ)
        (𝔶₀.map (Ideal.Quotient.mk IX)) := ha
      have : Module.Finite (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial σ ℂ ⧸ IX) := hfin
      have : Algebra.EssFiniteType (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial σ ℂ ⧸ IX) :=
        Algebra.EssFiniteType.of_finiteType _ _
      obtain ⟨f', hf', hunr⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt
        (R := MvPolynomial (Fin (n + 1)) ℂ) (𝔶₀.map (Ideal.Quotient.mk IX))
      obtain ⟨f₀, rfl⟩ := Ideal.Quotient.mk_surjective f'
      refine ⟨rename Sum.inl f₀, fun h => hf' ?_, a3h_formallyUnramified_rel IX a f₀ hunr⟩
      rw [← Ideal.mem_comap, hcomap]
      exact h
  refine hG.mono fun a ⟨⟨hfin, hsec⟩, hunr⟩ => ?_
  have hfinr := a3h_finite_rel IX a hfin
  refine ⟨hfinr, fun Q' hQ' hXQ hcomap hne W hW Y hY hWY hYrel => ?_⟩
  have := hSW W hW
  exact a3k_roberts_main_rel IXr PZ W hXZ (a3h_block a) (fun P => ∃ j, X (Sum.inl j) ∉ P)
    (fun _ _ hPQ ⟨j, hj⟩ => ⟨j, fun h => hj (hPQ h)⟩) hdimX hfinr (hsec W hW)
    (fun 𝔶 h𝔶 hrel => hunr W hW 𝔶 h𝔶 hrel hfin) k (hexc W hW) Q' hXQ hcomap hne Y hWY hYrel

end MainRel

/-! ## Roberts' main lemma over the line for `X` -/

section MainRelX

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- **Roberts' main lemma over the line for a smooth projective `X ⊂ ℙᴺ`**, of dimension `n`:
`a3h_roberts_rel` for the relative cone `I_X[t]`, the rank hypothesis being the smoothness of `X`
(`a3m_roberts_rank`).
Source: J. Roberts, *Chow's moving lemma* (1972), Main Lemma; S. Bloch, *The moving lemma for
higher Chow groups*, J. Algebraic Geom. 3 (1994), §2. -/
theorem a3h_roberts_rel_X (n : ℕ) (hn : Order.height (genericPoint X.left) = n)
    (PZ : Ideal (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ)) [PZ.IsPrime]
    (hXZ : a3h_IXr (a3s_IX X) ≤ PZ)
    (SW : Finset (Ideal (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ))) (hSW : ∀ W ∈ SW, W.IsPrime)
    (hZW : ∀ W ∈ SW, ∀ c : ℂ, MvPolynomial.X (Sum.inr ()) - MvPolynomial.C c ∉ PZ ∨
      MvPolynomial.X (Sum.inr ()) - MvPolynomial.C c ∉ W)
    (k : ℕ)
    (hexc : ∀ W ∈ SW, ∀ 𝔶 ∈ (PZ ⊔ W).minimalPrimes, (∃ j, MvPolynomial.X (Sum.inl j) ∉ 𝔶) →
      ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ 𝔶) +
          ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_IXr (a3s_IX X)) ≤
        ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ PZ) +
          ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ W) + (k + 1 : ℕ)) :
    a3r_Generic {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ |
      ((Ideal.Quotient.mk (a3h_IXr (a3s_IX X))).comp (a3r_lin (a3h_block a)).toRingHom).Finite ∧
      ∀ Q' : Ideal (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ), Q'.IsPrime →
        a3h_IXr (a3s_IX X) ≤ Q' →
        Q'.comap (a3r_lin (a3h_block a)) = PZ.comap (a3r_lin (a3h_block a)) → Q' ≠ PZ →
        ∀ W ∈ SW, ∀ Y : Ideal (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ), Y.IsPrime →
          Q' ⊔ W ≤ Y → (∃ j, MvPolynomial.X (Sum.inl j) ∉ Y) →
          ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ Y) +
              ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_IXr (a3s_IX X)) ≤
            ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ PZ) +
              ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ W) + k} := by
  have hdim : ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) = (n + 1 : ℕ) := by
    rw [← a3s_height_add_one X (genericPoint X.left), hn]
    rfl
  exact a3h_roberts_rel (a3s_IX X) (a3s_IX_isHomogeneous X) n hdim PZ hXZ SW hSW hZW k hexc
    fun 𝔶 _ hrel => a3m_roberts_rank X n hn 𝔶 hrel

end MainRelX

end HodgeLean.Adapters
