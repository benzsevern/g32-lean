import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
# Generic flatness of finite type algebras over a Noetherian domain

For a Noetherian domain `A` and a finite type `A`-algebra `B`, there is a nonzero `a : A` such
that `B` becomes flat over `A` after inverting any multiple of `a`. The argument follows
Matsumura, *Commutative Ring Theory*, Theorem 24.1: a prime filtration reduces finite modules over
a polynomial ring to quotients `A[X₀, …, Xₙ] ⧸ p`, and a shear of the variables makes such a
quotient finite over `A[X₁, …, Xₙ]` once the leading coefficient of a relation is inverted.
-/

noncomputable section

open TensorProduct LinearMap

namespace HodgeLean.GenericFreeness

universe u v w

section Extension

variable {A : Type u} [CommRing A]
variable {N₁ N₂ N₃ : Type*} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module A N₂]
  [AddCommGroup N₃] [Module A N₃]

/-- An extension of flat modules is flat. -/
theorem flat_of_exact {f : N₁ →ₗ[A] N₂} {g : N₂ →ₗ[A] N₃} (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.Flat A N₁] [Module.Flat A N₃] : Module.Flat A N₂ := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h3 : (I.subtype.rTensor N₃) ((g.lTensor I) x) = 0 := by
    rw [← LinearMap.comp_apply, rTensor_comp_lTensor, ← lTensor_comp_rTensor, comp_apply, hx,
      map_zero]
  have h3' : (g.lTensor I) x = 0 :=
    (injective_iff_map_eq_zero _).1
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective) _ h3
  obtain ⟨z, rfl⟩ := (lTensor_exact I hfg hg _).1 h3'
  have h1 : (f.lTensor A) ((I.subtype.rTensor N₁) z) = 0 := by
    rw [← LinearMap.comp_apply, lTensor_comp_rTensor, ← rTensor_comp_lTensor, comp_apply, hx]
  have h1' := (injective_iff_map_eq_zero _).1
    (Module.Flat.lTensor_preserves_injective_linearMap (M := A) f hf) _ h1
  rw [(injective_iff_map_eq_zero _).1
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective) _ h1', map_zero]

end Extension

section GenFlat

variable (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]

/-- `M` becomes flat over `A` after inverting any multiple of some nonzero `a : A`. -/
def GenFlat : Prop :=
  ∃ a : A, a ≠ 0 ∧ ∀ b : A, a ∣ b → Module.Flat A (LocalizedModule (Submonoid.powers b) M)

variable {A M}

/-- The localization map of `M` at the powers of `b`. -/
noncomputable abbrev locMap (b : A) (M : Type*) [AddCommGroup M] [Module A M] :
    M →ₗ[A] LocalizedModule (Submonoid.powers b) M :=
  LocalizedModule.mkLinearMap (Submonoid.powers b) M

theorem flat_localizedModule [Module.Flat A M] (S : Submonoid A) :
    Module.Flat A (LocalizedModule S M) :=
  Module.Flat.trans A (Localization S) _

theorem GenFlat.of_flat [Nontrivial A] [Module.Flat A M] : GenFlat A M :=
  ⟨1, one_ne_zero, fun _ _ ↦ flat_localizedModule _⟩

theorem GenFlat.of_map [IsDomain A] {M' : Type w} [AddCommGroup M'] [Module A M']
    (g : M →ₗ[A] M') {c : A} (hc : c ≠ 0)
    (h : ∀ b : A, c ∣ b → Function.Bijective
      (IsLocalizedModule.map (Submonoid.powers b) (locMap b M) (locMap b M') g))
    (hM : GenFlat A M) : GenFlat A M' := by
  obtain ⟨a, ha, hM⟩ := hM
  refine ⟨a * c, mul_ne_zero ha hc, fun b hb ↦ ?_⟩
  have := hM b (dvd_trans (dvd_mul_right a c) hb)
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective
    ((IsLocalizedModule.map (Submonoid.powers b) (locMap b M) (locMap b M') g))
    (h b (dvd_trans (dvd_mul_left c a) hb))).symm

theorem GenFlat.of_linearEquiv [IsDomain A] {M' : Type w} [AddCommGroup M'] [Module A M']
    (e : M ≃ₗ[A] M') (hM : GenFlat A M) : GenFlat A M' :=
  hM.of_map e.toLinearMap one_ne_zero fun _ _ ↦
    ⟨IsLocalizedModule.map_injective _ _ _ _ e.injective,
      IsLocalizedModule.map_surjective _ _ _ _ e.surjective⟩

theorem GenFlat.of_exact [IsDomain A] {N₁ N₂ N₃ : Type*} [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃] [Module A N₃]
    {f : N₁ →ₗ[A] N₂} {g : N₂ →ₗ[A] N₃} (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (h₁ : GenFlat A N₁) (h₃ : GenFlat A N₃) : GenFlat A N₂ := by
  obtain ⟨a₁, ha₁, h₁⟩ := h₁
  obtain ⟨a₃, ha₃, h₃⟩ := h₃
  refine ⟨a₁ * a₃, mul_ne_zero ha₁ ha₃, fun b hb ↦ ?_⟩
  have := h₁ b (dvd_trans (dvd_mul_right _ _) hb)
  have := h₃ b (dvd_trans (dvd_mul_left _ _) hb)
  let S := Submonoid.powers b
  exact flat_of_exact
    (f := (IsLocalizedModule.map S (locMap b N₁) (locMap b N₂) f))
    (g := (IsLocalizedModule.map S (locMap b N₂) (locMap b N₃) g))
    (IsLocalizedModule.map_injective _ _ _ _ hf)
    (IsLocalizedModule.map_surjective _ _ _ _ hg)
    (IsLocalizedModule.map_exact S _ _ _ _ _ hfg)

theorem GenFlat.of_injective [IsDomain A] {M' : Type w} [AddCommGroup M'] [Module A M']
    (ι : M' →ₗ[A] M) (hι : Function.Injective ι) {c : A} (hc : c ≠ 0)
    (h : ∀ z : M, ∃ k : ℕ, ∃ y : M', ι y = c ^ k • z) (hM' : GenFlat A M') : GenFlat A M := by
  refine hM'.of_map ι hc fun b hb ↦ ⟨IsLocalizedModule.map_injective _ _ _ _ hι, ?_⟩
  intro y
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers b) (locMap b M) y
  obtain ⟨k, y, hy⟩ := h z
  obtain ⟨d, hd⟩ := pow_dvd_pow_of_dvd hb k
  let t : Submonoid.powers b := ⟨b ^ k, pow_mem (Submonoid.mem_powers b) k⟩
  refine ⟨IsLocalizedModule.mk' (locMap b M') (d • y) (t * s), ?_⟩
  rw [IsLocalizedModule.map_mk']
  simp only [Function.uncurry_apply_pair, map_smul, hy]
  rw [smul_smul, mul_comm d, ← hd]
  exact IsLocalizedModule.mk'_cancel_left _ _ t s

end GenFlat


open Polynomial in
theorem exists_pow_leadingCoeff_mul_sub_mem {R : Type*} [CommRing R] (F : R[X]) (P : R[X]) :
    ∃ k : ℕ, ∃ G : R[X], C F.leadingCoeff ^ k * P - F * G ∈
      Submodule.span R (Set.range fun i : Fin F.natDegree ↦ (X : R[X]) ^ (i : ℕ)) := by
  set V := Submodule.span R (Set.range fun i : Fin F.natDegree ↦ (X : R[X]) ^ (i : ℕ))
  set N := F.natDegree
  set ℓ := F.leadingCoeff
  have hV : ∀ Q : R[X], Q.natDegree < N → Q ∈ V := by
    intro Q hQ
    rw [Q.as_sum_range' N hQ]
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    rw [← smul_X_eq_monomial]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, Finset.mem_range.1 hi⟩, rfl⟩)
  suffices H : ∀ d : ℕ, ∀ Q : R[X], Q.natDegree < N + d →
      ∃ k : ℕ, ∃ G : R[X], C ℓ ^ k * Q - F * G ∈ V from H (P.natDegree + 1) P (by lia)
  intro d
  induction d with
  | zero => exact fun Q hQ ↦ ⟨0, 0, by simpa using hV Q hQ⟩
  | succ d ih =>
    intro Q hQ
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hQ) with hQ' | hQ'
    · exact ih Q hQ'
    set a := Q.leadingCoeff
    set Q' := C ℓ * Q - F * (C a * X ^ d) with hQ'def
    have key : Q'.natDegree < N + d ∨ Q' = 0 := by
      by_cases h0 : Q' = 0
      · exact Or.inr h0
      left
      rw [natDegree_lt_iff_degree_lt h0, degree_lt_iff_coeff_zero]
      intro j hj
      have e : F * (C a * X ^ d) = C a * F * X ^ d := by ring
      rw [hQ'def, e, coeff_sub, coeff_C_mul, coeff_mul_X_pow', ite_eq_left_of_eq_true _ _ (eq_true (show d ≤ j by lia)), coeff_C_mul]
      rcases lt_or_eq_of_le hj with hj | rfl
      · rw [Q.coeff_eq_zero_of_natDegree_lt (by lia),
          F.coeff_eq_zero_of_natDegree_lt (by lia)]
        ring
      · have hQ'' : Q.natDegree = N + d := hQ'
        rw [← hQ'', show Q.natDegree - d = N by lia]
        simp only [coeff_natDegree, ℓ, a, N]
        ring
    obtain ⟨k, G, hG⟩ : ∃ k : ℕ, ∃ G : R[X], C ℓ ^ k * Q' - F * G ∈ V := by
      rcases key with key | key
      · exact ih Q' key
      · exact ⟨0, 0, by simp [key]⟩
    refine ⟨k + 1, G + C ℓ ^ k * (C a * X ^ d), ?_⟩
    convert hG using 1
    rw [hQ'def]
    ring

section Shear


open MvPolynomial

theorem map_finSuccEquiv {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ}
    (g : MvPolynomial (Fin (n + 1)) A) :
    Polynomial.map (MvPolynomial.map φ) (finSuccEquiv A n g) = finSuccEquiv B n (map φ g) := by
  ext i m
  rw [Polynomial.coeff_map, coeff_map, finSuccEquiv_coeff_coeff, finSuccEquiv_coeff_coeff,
    coeff_map]

/-- Shear of the variables `X_i ↦ X_i + e • X_0 ^ (u ^ i)` for `i ≠ 0`. -/
noncomputable abbrev shear {A : Type*} [CommRing A] {n : ℕ} (u : ℕ) (e : A) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  aeval fun i ↦ if i = 0 then X 0 else X i + e • X 0 ^ (u ^ i.1)

theorem shear_comp_shear_neg {A : Type*} [CommRing A] {n : ℕ} (u : ℕ) (e : A) :
    (shear (n := n) u e).comp (shear u (-e)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

theorem exists_shear_leadingCoeff {A : Type u} [CommRing A] [IsDomain A] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) A) (hf : f ≠ 0) :
    ∃ T T' : MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A,
      T'.comp T = AlgHom.id _ _ ∧ ∃ c : A, c ≠ 0 ∧
        (finSuccEquiv A n (T f)).leadingCoeff = MvPolynomial.C c := by
  let K := FractionRing A
  let φ : A →+* K := algebraMap A K
  have hφ : Function.Injective φ := IsFractionRing.injective A K
  set fK := map φ f
  have hfK : fK ≠ 0 := fun h ↦ hf (map_injective φ hφ (by rw [map_zero]; exact h))
  let u := 2 + fK.totalDegree
  refine ⟨shear u 1, shear u (-1), by simpa using shear_comp_shear_neg (n := n) u (-1 : A), ?_⟩
  have hT : map φ (shear u 1 f) = NoetherNormalization.varChange fK fK := by
    have : (map φ).comp (shear u 1 : MvPolynomial (Fin (n + 1)) A →ₐ[A] _).toRingHom =
        (NoetherNormalization.varChange fK).toRingHom.comp (map φ) := by
      refine ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
      · simp [φ]
      · cases i using Fin.cases <;> simp [u, fK]
    exact RingHom.congr_fun this f
  have hU := NoetherNormalization.varChange_leadingCoeff_isUnit fK hfK
  rw [← hT, ← map_finSuccEquiv, Polynomial.leadingCoeff_map_of_injective (map_injective φ hφ),
    isUnit_iff_eq_C_of_isReduced] at hU
  obtain ⟨r, hr, hU⟩ := hU
  set ℓ := (finSuccEquiv A n (shear u 1 f)).leadingCoeff
  refine ⟨ℓ.coeff 0, ?_, ?_⟩
  · intro h0
    apply hr.ne_zero
    have := congrArg (fun p : MvPolynomial (Fin n) K ↦ p.coeff 0) hU
    simp only [coeff_map, h0, map_zero, coeff_C, ↓reduceIte] at this
    exact this.symm
  · ext m
    apply hφ
    rw [← coeff_map, hU, coeff_C, coeff_C]
    split_ifs with hm
    · subst hm
      have := congrArg (fun p : MvPolynomial (Fin n) K ↦ p.coeff 0) hU
      simp only [coeff_map, coeff_C, ↓reduceIte] at this
      exact this.symm
    · rw [map_zero]

end Shear

section Induction

open MvPolynomial

/-- Generic flatness of the quotients of a polynomial ring in `n` variables. -/
def QuotientStatement (n : ℕ) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (p : Ideal (MvPolynomial (Fin n) A)), GenFlat A (MvPolynomial (Fin n) A ⧸ p)

/-- Generic flatness of the finite modules over a polynomial ring in `n` variables. -/
def ModuleStatement (n : ℕ) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module (MvPolynomial (Fin n) A) M]
    [IsScalarTower A (MvPolynomial (Fin n) A) M] [Module.Finite (MvPolynomial (Fin n) A) M],
    GenFlat A M

theorem moduleStatement_of_quotientStatement {n : ℕ} (hQ : QuotientStatement.{u} n) :
    ModuleStatement.{u} n := by
  intro A _ _ _ M _ _ _ _ hfin
  let R := MvPolynomial (Fin n) A
  revert ‹Module A M› ‹IsScalarTower A R M›
  induction hfin using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N => intro _ _; exact GenFlat.of_flat
  | quotient N p e =>
    intro _ _
    exact (hQ A p.1).of_linearEquiv (e.symm.restrictScalars A)
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro _ _
    let : Module A N₁ := Module.compHom N₁ (algebraMap A R)
    have : IsScalarTower A R N₁ := ⟨fun a r x ↦ by
      change (a • r) • x = algebraMap A R a • (r • x)
      rw [Algebra.smul_def, mul_smul]⟩
    let : Module A N₃ := Module.compHom N₃ (algebraMap A R)
    have : IsScalarTower A R N₃ := ⟨fun a r x ↦ by
      change (a • r) • x = algebraMap A R a • (r • x)
      rw [Algebra.smul_def, mul_smul]⟩
    exact GenFlat.of_exact (f := f.restrictScalars A) (g := g.restrictScalars A) hf hg hfg
      h₁ h₃

theorem genFlat_quotient_bot {n : ℕ} {A : Type u} [CommRing A] [IsDomain A]
    (p : Ideal (MvPolynomial (Fin n) A)) (hp : p = ⊥) :
    GenFlat A (MvPolynomial (Fin n) A ⧸ p) :=
  (GenFlat.of_flat (M := MvPolynomial (Fin n) A)).of_linearEquiv
    ((Submodule.quotEquivOfEqBot p hp).symm.restrictScalars A)

theorem quotientStatement_zero : QuotientStatement.{u} 0 := by
  intro A _ _ _ p
  by_cases hp : p = ⊥
  · exact genFlat_quotient_bot p hp
  obtain ⟨f, hfp, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  have hc : f.coeff 0 ≠ 0 := by
    intro h; apply hf; rw [eq_C_of_isEmpty f, h, map_zero]
  refine GenFlat.of_injective (M' := PUnit.{u + 1}) 0 (Function.injective_of_subsingleton _) hc
    (fun z ↦ ⟨1, 0, ?_⟩) GenFlat.of_flat
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [pow_one, LinearMap.zero_apply, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap,
    ← map_mul, eq_comm,
    Ideal.Quotient.eq_zero_iff_mem]
  refine p.mul_mem_right _ ?_
  rw [MvPolynomial.algebraMap_eq, ← eq_C_of_isEmpty f]
  exact hfp

theorem genFlat_of_polynomial_quotient {n : ℕ} (hM : ModuleStatement.{u} n)
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {Q : Type u} [CommRing Q] [Algebra A Q]
    (Φ : Polynomial (MvPolynomial (Fin n) A) →ₐ[A] Q) (hΦ : Function.Surjective Φ)
    (F : Polynomial (MvPolynomial (Fin n) A)) (hF : Φ F = 0) {c : A} (hc : c ≠ 0)
    (hℓ : F.leadingCoeff = C c) : GenFlat A Q := by
  let Rn := MvPolynomial (Fin n) A
  let ψ : Rn →ₐ[A] Q := Φ.comp (IsScalarTower.toAlgHom A Rn (Polynomial Rn))
  let _ : Algebra Rn Q := ψ.toRingHom.toAlgebra
  have : IsScalarTower A Rn Q := IsScalarTower.of_algebraMap_eq fun a ↦ (ψ.commutes a).symm
  let L : Polynomial Rn →ₗ[Rn] Q :=
    { toFun := Φ
      map_add' := map_add Φ
      map_smul' := fun r P ↦ by
        rw [Polynomial.smul_eq_C_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
        rfl }
  let N : Submodule Rn Q :=
    Submodule.span Rn (Set.range fun i : Fin F.natDegree ↦ Φ (Polynomial.X ^ (i : ℕ)))
  have : Module.Finite Rn N := Module.Finite.span_of_finite Rn (Set.finite_range _)
  have hN := hM A N
  refine GenFlat.of_injective ((N.subtype).restrictScalars A) Subtype.val_injective hc
    (fun z ↦ ?_) hN
  obtain ⟨P, rfl⟩ := hΦ z
  obtain ⟨k, G, hG⟩ := exists_pow_leadingCoeff_mul_sub_mem F P
  have hle : Submodule.span Rn
      (Set.range fun i : Fin F.natDegree ↦ (Polynomial.X : Polynomial Rn) ^ (i : ℕ)) ≤
      N.comap L := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨k, ⟨_, hle hG⟩, ?_⟩
  simp only [LinearMap.restrictScalars_apply, Submodule.subtype_apply]
  change Φ _ = _
  have hC : Polynomial.C F.leadingCoeff = algebraMap A (Polynomial Rn) c := by
    rw [hℓ, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  rw [map_sub, map_mul, map_mul, hF, zero_mul, sub_zero, map_pow, hC, AlgHom.commutes,
    Algebra.smul_def, map_pow]

theorem quotientStatement_succ {n : ℕ} (hM : ModuleStatement.{u} n) :
    QuotientStatement.{u} (n + 1) := by
  intro A _ _ _ p
  by_cases hp : p = ⊥
  · exact genFlat_quotient_bot p hp
  obtain ⟨f, hfp, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  obtain ⟨T, T', hTT', c, hc, hℓ⟩ := exists_shear_leadingCoeff f hf
  let Φ : Polynomial (MvPolynomial (Fin n) A) →ₐ[A] MvPolynomial (Fin (n + 1)) A ⧸ p :=
    (Ideal.Quotient.mkₐ A p).comp (T'.comp (finSuccEquiv A n).symm.toAlgHom)
  have hΦ : ∀ q, Φ (finSuccEquiv A n (T q)) = Ideal.Quotient.mk p q := by
    intro q
    change Ideal.Quotient.mk p (T' ((finSuccEquiv A n).symm (finSuccEquiv A n (T q)))) = _
    rw [AlgEquiv.symm_apply_apply, ← AlgHom.comp_apply T' T, hTT', AlgHom.id_apply]
  refine genFlat_of_polynomial_quotient hM Φ (fun z ↦ ?_) (finSuccEquiv A n (T f)) ?_ hc hℓ
  · obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨_, hΦ q⟩
  · rw [hΦ, Ideal.Quotient.eq_zero_iff_mem]; exact hfp

theorem moduleStatement (n : ℕ) : ModuleStatement.{u} n := by
  induction n with
  | zero => exact moduleStatement_of_quotientStatement quotientStatement_zero
  | succ n ih => exact moduleStatement_of_quotientStatement (quotientStatement_succ ih)

end Induction

section Algebra

/-- **Generic freeness**, flat form: a finite type algebra over a Noetherian domain becomes flat
after inverting any multiple of some nonzero element. -/
theorem genFlat_of_finiteType {A B : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B] : GenFlat A B := by
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType A B›
  let _ : Algebra (MvPolynomial (Fin n) A) B := g.toRingHom.toAlgebra
  have : IsScalarTower A (MvPolynomial (Fin n) A) B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : Module.Finite (MvPolynomial (Fin n) A) B :=
    Module.Finite.of_surjective (Algebra.linearMap (MvPolynomial (Fin n) A) B) hg
  exact moduleStatement n A B

/-- Flatness of a localized algebra over the localized base. -/
theorem flat_localization_of_flat_localizedModule {A B A' B' : Type*} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B']
    [Algebra A B'] [IsScalarTower A B B'] [IsScalarTower A A' B'] (a : A)
    [IsLocalization.Away a A'] [IsLocalization.Away (algebraMap A B a) B']
    (h : Module.Flat A (LocalizedModule (Submonoid.powers a) B)) : Module.Flat A' B' := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers a)) B' := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  have := (isLocalizedModule_iff_isLocalization (S := Submonoid.powers a) (A := B)
    (Aₛ := B')).mpr this
  have : Module.Flat A B' := Module.Flat.of_linearEquiv
    (IsLocalizedModule.iso (Submonoid.powers a)
      (IsScalarTower.toAlgHom A B B').toLinearMap).symm
  exact (Module.flat_iff_of_isLocalization A' (Submonoid.powers a) B').mpr this

end Algebra

end HodgeLean.GenericFreeness
