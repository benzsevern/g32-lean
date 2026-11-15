import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Length

/-! # Reformulated bridge of A3-B4a: lengths of slices of filtered modules

Weakly regular sequences and the lengths of the quotients by them are additive in short exact
sequences whose last term carries the sequence weakly regularly; along a finite filtration the
length of the quotient of a module is the sum over the graded pieces.
Source: Bruns–Herzog, *Cohen–Macaulay Rings*, §1.1; Matsumura, *Commutative Ring Theory*, §16. -/

noncomputable section
namespace HodgeLean.Adapters
open RingTheory.Sequence Submodule Pointwise

variable {A : Type*} [CommRing A]

/-- Every sequence is weakly regular on a subsingleton module. -/
theorem a3b4g_isWeaklyRegular_of_subsingleton {M : Type*} [AddCommGroup M] [Module A M]
    [Subsingleton M] (rs : List A) : IsWeaklyRegular M rs := by
  induction rs generalizing M with
  | nil => exact IsWeaklyRegular.nil A M
  | cons r rs ih =>
    exact (isWeaklyRegular_cons_iff M r rs).mpr ⟨fun x y _ => Subsingleton.elim x y, ih⟩

/-- A sequence weakly regular on the outer terms of a short exact sequence is weakly regular on
the middle term. Source: Bruns–Herzog, *Cohen–Macaulay Rings*, Proposition 1.1.4. -/
theorem a3b4g_isWeaklyRegular_of_exact {M' M M'' : Type*} [AddCommGroup M'] [Module A M']
    [AddCommGroup M] [Module A M] [AddCommGroup M''] [Module A M''] (rs : List A) :
    ∀ {f : M' →ₗ[A] M} {g : M →ₗ[A] M''}, Function.Injective f → Function.Exact f g →
      Function.Surjective g → IsWeaklyRegular M' rs → IsWeaklyRegular M'' rs →
        IsWeaklyRegular M rs := by
  induction rs generalizing M' M M'' with
  | nil => intros; exact IsWeaklyRegular.nil A M
  | cons r rs ih =>
    intro f g hf hfg hg h' h''
    rw [isWeaklyRegular_cons_iff] at h' h'' ⊢
    refine ⟨isSMulRegular_of_range_eq_ker hf (LinearMap.exact_iff.mp hfg).symm h'.1 h''.1, ?_⟩
    have hinj : Function.Injective (QuotSMulTop.map r f) := by
      have h4 := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
        (f₁ := (0 : PUnit.{1} →ₗ[A] M')) (f₂ := f) (f₃ := g)
        ((LinearMap.exact_zero_iff_injective _ _).mpr hf) hfg h''.1
      rw [map_zero] at h4
      exact (LinearMap.exact_zero_iff_injective _ _).mp h4
    exact ih hinj (QuotSMulTop.map_exact r hfg hg) (QuotSMulTop.map_surjective r hg) h'.2 h''.2

/-- The quotient of a short exact sequence by a sequence weakly regular on its last term is
again short exact; in particular the lengths of the quotients add.
Source: Bruns–Herzog, *Cohen–Macaulay Rings*, Proposition 1.1.4. -/
theorem a3b4g_length_quot_of_exact {M' M M'' : Type*} [AddCommGroup M'] [Module A M']
    [AddCommGroup M] [Module A M] [AddCommGroup M''] [Module A M''] (rs : List A)
    {f : M' →ₗ[A] M} {g : M →ₗ[A] M''} (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (h'' : IsWeaklyRegular M'' rs) :
    Module.length A (M ⧸ (Ideal.ofList rs • ⊤ : Submodule A M)) =
      Module.length A (M' ⧸ (Ideal.ofList rs • ⊤ : Submodule A M')) +
        Module.length A (M'' ⧸ (Ideal.ofList rs • ⊤ : Submodule A M'')) := by
  have h1 := map_first_exact_on_four_term_right_exact_of_isSMulRegular_last (rs := rs)
    (f₁ := (0 : PUnit.{1} →ₗ[A] M')) (f₂ := f) (f₃ := g)
    ((LinearMap.exact_zero_iff_injective _ _).mpr hf) hfg hg h''
  have h2 := map_first_exact_on_four_term_right_exact_of_isSMulRegular_last (rs := rs)
    (f₁ := f) (f₂ := g) (f₃ := (0 : M'' →ₗ[A] PUnit.{1})) hfg
    ((LinearMap.exact_zero_iff_surjective _ _).mpr hg) (fun _ => ⟨0, Subsingleton.elim _ _⟩)
    (a3b4g_isWeaklyRegular_of_subsingleton rs)
  refine Module.length_eq_add_of_exact _ _ ?_ ?_ h2
  · rw [← LinearMap.ker_eq_bot, LinearMap.exact_iff.mp h1, eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx, map_zero]
    exact Submodule.zero_mem _
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      obtain ⟨x, rfl⟩ := hg y
      exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- The graded piece `F k / F (k + 1)` of a descending chain of submodules. -/
abbrev a3b4g_gradedPiece {M : Type*} [AddCommGroup M] [Module A M] (F : ℕ → Submodule A M)
    (k : ℕ) : Type _ :=
  ↥(F k) ⧸ (F (k + 1)).comap (F k).subtype

/-- Along a finite descending filtration whose graded pieces carry a sequence weakly regularly,
the sequence is weakly regular on the module and the length of the quotient is the sum of the
lengths of the quotients of the graded pieces. Source: Bruns–Herzog, *Cohen–Macaulay Rings*,
Proposition 1.1.4, by induction along the filtration. -/
theorem a3b4g_length_quot_of_filtration {M : Type*} [AddCommGroup M] [Module A M]
    (F : ℕ → Submodule A M) (hF : Antitone F) (N : ℕ) (hN : F N = ⊥) (rs : List A)
    (hreg : ∀ k < N, IsWeaklyRegular (a3b4g_gradedPiece F k) rs) :
    IsWeaklyRegular ↥(F 0) rs ∧
      Module.length A (↥(F 0) ⧸ (Ideal.ofList rs • ⊤ : Submodule A ↥(F 0))) =
        ∑ k ∈ Finset.range N, Module.length A (a3b4g_gradedPiece F k ⧸
          (Ideal.ofList rs • ⊤ : Submodule A (a3b4g_gradedPiece F k))) := by
  have key : ∀ d ≤ N, IsWeaklyRegular ↥(F (N - d)) rs ∧
      Module.length A (↥(F (N - d)) ⧸ (Ideal.ofList rs • ⊤ : Submodule A ↥(F (N - d)))) =
        ∑ k ∈ Finset.Ico (N - d) N, Module.length A (a3b4g_gradedPiece F k ⧸
          (Ideal.ofList rs • ⊤ : Submodule A (a3b4g_gradedPiece F k))) := by
    intro d
    induction d with
    | zero =>
      intro _
      simp only [Nat.sub_zero, Finset.Ico_self, Finset.sum_empty]
      have : Subsingleton ↥(F N) := by rw [hN]; infer_instance
      refine ⟨a3b4g_isWeaklyRegular_of_subsingleton rs, ?_⟩
      exact Module.length_eq_zero
    | succ d ih =>
      intro hd
      obtain ⟨ihr, ihl⟩ := ih (Nat.le_of_succ_le hd)
      set j := N - (d + 1) with hj
      have hj1 : j + 1 = N - d := by omega
      have hjN : j < N := by omega
      have hle : F (j + 1) ≤ F j := hF (Nat.le_succ j)
      let f : ↥(F (j + 1)) →ₗ[A] ↥(F j) := Submodule.inclusion hle
      let g : ↥(F j) →ₗ[A] a3b4g_gradedPiece F j := Submodule.mkQ _
      have hf : Function.Injective f := Submodule.inclusion_injective hle
      have hfg : Function.Exact f g := by
        rw [LinearMap.exact_iff]
        ext x
        simp only [g, Submodule.ker_mkQ, Submodule.mem_comap, Submodule.subtype_apply,
          LinearMap.mem_range, f]
        constructor
        · intro hx
          exact ⟨⟨x, hx⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact y.2
      have hg : Function.Surjective g := Submodule.mkQ_surjective _
      rw [← hj1] at ihr ihl
      refine ⟨a3b4g_isWeaklyRegular_of_exact rs hf hfg hg ihr (hreg j hjN), ?_⟩
      rw [a3b4g_length_quot_of_exact rs hf hfg hg (hreg j hjN), ihl,
        Finset.sum_eq_sum_Ico_succ_bot hjN, add_comm]
  have := key N le_rfl
  rw [Nat.sub_self] at this
  rwa [Finset.range_eq_Ico]

/-- A linear equivalence induces an equivalence of the quotients by `J • ⊤`. -/
def a3b4g_quotSMulTopEquiv {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (e : M ≃ₗ[A] M') (J : Ideal A) :
    (M ⧸ (J • ⊤ : Submodule A M)) ≃ₗ[A] (M' ⧸ (J • ⊤ : Submodule A M')) :=
  Submodule.Quotient.equiv _ _ e (by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])

/-- On a finite free module over a module carrying a weakly regular sequence, the sequence is
weakly regular and the length of the quotient is the rank times the length for one summand. -/
theorem a3b4g_pi_length_quot (X : Type*) [AddCommGroup X] [Module A X] (rs : List A)
    (hX : IsWeaklyRegular X rs) (r : ℕ) :
    IsWeaklyRegular (Fin r → X) rs ∧
      Module.length A ((Fin r → X) ⧸ (Ideal.ofList rs • ⊤ : Submodule A (Fin r → X))) =
        r * Module.length A (X ⧸ (Ideal.ofList rs • ⊤ : Submodule A X)) := by
  induction r with
  | zero =>
    refine ⟨a3b4g_isWeaklyRegular_of_subsingleton rs, ?_⟩
    rw [Nat.cast_zero, zero_mul]
    exact Module.length_eq_zero
  | succ r ih =>
    let e := Fin.consLinearEquiv A (fun _ : Fin (r + 1) => X)
    have hf : Function.Injective (LinearMap.inl A X (Fin r → X)) := LinearMap.inl_injective
    have hg : Function.Surjective (LinearMap.snd A X (Fin r → X)) := LinearMap.snd_surjective
    have hfg : Function.Exact (LinearMap.inl A X (Fin r → X)) (LinearMap.snd A X (Fin r → X)) :=
      Function.Exact.inl_snd
    have hreg := a3b4g_isWeaklyRegular_of_exact rs hf hfg hg hX ih.1
    refine ⟨(e.isWeaklyRegular_congr rs).mp hreg, ?_⟩
    rw [← (a3b4g_quotSMulTopEquiv e (Ideal.ofList rs)).length_eq,
      a3b4g_length_quot_of_exact rs hf hfg hg ih.1, ih.2]
    push_cast
    ring

/-- The length of a slice of a ring filtered by the powers of a nilpotent ideal `I` whose graded
pieces are free over `A ⧸ I`: the sum of the ranks times the length of the slice of `A ⧸ I`.
Source: Bruns–Herzog, *Cohen–Macaulay Rings*, Proposition 1.1.4; Fulton, *Intersection Theory*,
Lemma A.2. -/
theorem a3b4g_length_quot_of_free_graded (I : Ideal A) (N : ℕ) (hN : I ^ N = ⊥) (r : ℕ → ℕ)
    (e : ∀ k < N, a3b4g_gradedPiece (fun k => I ^ k) k ≃ₗ[A] (Fin (r k) → A ⧸ I))
    (rs : List A) (hreg : IsWeaklyRegular (A ⧸ I) rs) :
    Module.length A (A ⧸ Ideal.ofList rs) =
      (∑ k ∈ Finset.range N, (r k : ℕ∞)) *
        Module.length A ((A ⧸ I) ⧸ (Ideal.ofList rs • ⊤ : Submodule A (A ⧸ I))) := by
  have hF : Antitone (fun k => (I ^ k : Submodule A A)) := fun _ _ h => Ideal.pow_le_pow_right h
  obtain ⟨-, hlen⟩ := a3b4g_length_quot_of_filtration (fun k => (I ^ k : Submodule A A)) hF N hN
    rs (fun k hk => ((e k hk).isWeaklyRegular_congr rs).mpr
      (a3b4g_pi_length_quot (A ⧸ I) rs hreg (r k)).1)
  have e0 : ↥((I ^ 0 : Ideal A) : Submodule A A) ≃ₗ[A] A :=
    LinearEquiv.ofEq _ ⊤ (by rw [pow_zero, Ideal.one_eq_top]) ≪≫ₗ Submodule.topEquiv
  have hq : (Ideal.ofList rs • ⊤ : Submodule A A) = Ideal.ofList rs := by
    rw [smul_eq_mul, Ideal.mul_top]
  rw [← (Submodule.quotEquivOfEq _ _ hq).length_eq,
    ← (a3b4g_quotSMulTopEquiv e0 (Ideal.ofList rs)).length_eq, hlen, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [(a3b4g_quotSMulTopEquiv (e k (Finset.mem_range.mp hk)) (Ideal.ofList rs)).length_eq,
    (a3b4g_pi_length_quot (A ⧸ I) rs hreg (r k)).2]

end HodgeLean.Adapters
