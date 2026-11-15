import HodgeLean.Adapters.IntersectionProductHerbrand
import HodgeLean.Adapters.IntersectionProductCMQuotient

/-! # Herbrand differences of modules of dimension at most one

Over a Noetherian local ring `(A, 𝔪)`, let `Φ` be a finite set of primes `𝔭 ≠ 𝔪` with nothing
between `𝔭` and `𝔪`, and `r` an element outside every `𝔭 ∈ Φ`. For a finitely generated module
`N` whose support lies in `Φ ∪ {𝔪}`,
`e_r(N) = Σ_{𝔭 ∈ Φ} length_{A_𝔭}(N_𝔭) · e_r(A ⧸ 𝔭)` (`a3e_herbrand_eq_sum`).
The proof runs along a prime filtration of `N`: both sides are additive on short exact sequences
(the snake lemma, exactness of localization), vanish on `A ⧸ 𝔪`, and agree on `A ⧸ 𝔭`,
`𝔭 ∈ Φ`, where `(A ⧸ 𝔭)_𝔭` is the residue field of `A_𝔭`.

Applied to `N = Tor_i(A ⧸ 𝔭_W, A ⧸ 𝔭_V)` at a point of a proper intersection, `Φ` is the set of
components of `W ∩ V` through the point, and the formula splits Serre's computation of
`[div r] · V` into the multiplicities `i(Z; W · V)` and the orders of `r` along the curves `Z`.

Source: Fulton, *Intersection Theory*, second edition, Lemma A.2.2 and Example A.2.1
(`e_M(r) = Σ ℓ(M_𝔭) e_{A/𝔭}(r)`); Serre, *Algèbre locale, multiplicités*, Chapitre I, §2 and
Chapitre V, B.2. HC no distance; AV milestone no distance.
-/

open CategoryTheory IsLocalRing Pointwise

noncomputable section
namespace HodgeLean.Adapters
universe u

section loc
variable {A : Type u} [CommRing A] (S : Submonoid A)

theorem a3e_localizedModule_map_coe {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (g : M →ₗ[A] N) :
    ⇑(LocalizedModule.map S g) = ⇑(IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S N) g) := by
  funext x
  induction x using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.map_mk, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk',
      IsLocalizedModule.map_mk']

/-- Localization of modules is exact, for the `Localization S`-linear maps. -/
theorem a3e_localizedModule_map_exact {M₀ M₁ M₂ : Type u} [AddCommGroup M₀] [Module A M₀]
    [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂] (g : M₀ →ₗ[A] M₁)
    (h : M₁ →ₗ[A] M₂) (ex : Function.Exact g h) :
    Function.Exact (LocalizedModule.map S g) (LocalizedModule.map S h) := by
  rw [a3e_localizedModule_map_coe, a3e_localizedModule_map_coe]
  exact LocalizedModule.map_exact S g h ex

/-- The length of `N_𝔭` over `A_𝔭`.
Source: Fulton, *Intersection Theory*, second edition, Example A.2.1 (`ℓ(M_𝔭)`); Mathlib,
`LocalizedModule` and `Module.length`. -/
def a3e_locLen (𝔭 : PrimeSpectrum A) (N : Type u) [AddCommGroup N] [Module A N] : ℕ∞ :=
  Module.length (Localization.AtPrime 𝔭.asIdeal) (LocalizedModule 𝔭.asIdeal.primeCompl N)

example (𝔭 : PrimeSpectrum A) : a3e_locLen 𝔭 (PUnit : Type u) = 0 :=
  Module.length_eq_zero

theorem a3e_locLen_ses (𝔭 : PrimeSpectrum A) {N₁ N₂ N₃ : Type u} [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃] [Module A N₃] (f : N₁ →ₗ[A] N₂)
    (g : N₂ →ₗ[A] N₃) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    a3e_locLen 𝔭 N₂ = a3e_locLen 𝔭 N₁ + a3e_locLen 𝔭 N₃ :=
  Module.length_eq_add_of_exact _ _ (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) (a3e_localizedModule_map_exact _ f g hfg)

theorem a3e_locLen_congr (𝔭 : PrimeSpectrum A) {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (e : N ≃ₗ[A] N') : a3e_locLen 𝔭 N = a3e_locLen 𝔭 N' :=
  le_antisymm
    (Module.length_le_of_injective _ (LocalizedModule.map_injective _ e.toLinearMap e.injective))
    (Module.length_le_of_injective _
      (LocalizedModule.map_injective _ e.symm.toLinearMap e.symm.injective))

/-- `N_𝔭 = 0` when an element outside `𝔭` kills `N`. -/
theorem a3e_locLen_eq_zero (𝔭 : PrimeSpectrum A) (N : Type u) [AddCommGroup N] [Module A N]
    (s : A) (hs : s ∉ 𝔭.asIdeal) (h : ∀ n : N, s • n = 0) : a3e_locLen 𝔭 N = 0 := by
  have : Subsingleton (LocalizedModule 𝔭.asIdeal.primeCompl N) :=
    LocalizedModule.subsingleton_iff.mpr fun n => ⟨s, hs, h n⟩
  exact Module.length_eq_zero

/-- `(A ⧸ 𝔭)_𝔭` is a simple `A_𝔭`-module: the residue field. -/
theorem a3e_locLen_quotient_self (𝔭 : PrimeSpectrum A) : a3e_locLen 𝔭 (A ⧸ 𝔭.asIdeal) = 1 := by
  unfold a3e_locLen
  set S := 𝔭.asIdeal.primeCompl
  have hz : ∀ (a : A) (s : S), LocalizedModule.mk (Ideal.Quotient.mk 𝔭.asIdeal a) s = 0 ↔
      a ∈ 𝔭.asIdeal := by
    intro a s
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    constructor
    · rintro ⟨t, ht⟩
      have hm : (t : A) * ((s : A) * a) ∈ 𝔭.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simpa only [Submonoid.smul_def, smul_zero, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.mk_eq_mk, map_mul] using ht
      rcases 𝔭.isPrime.mem_or_mem hm with h | h
      · exact absurd h t.2
      · rcases 𝔭.isPrime.mem_or_mem h with h | h
        · exact absurd h s.2
        · exact h
    · intro ha
      refine ⟨1, ?_⟩
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr ha]
  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨⟨LocalizedModule.mk (Ideal.Quotient.mk 𝔭.asIdeal 1) 1, 0, fun h0 => ?_⟩, ?_⟩
  · exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ((hz 1 1).mp h0))
  · intro x hx y
    induction x using LocalizedModule.induction_on with
    | h a s =>
    induction y using LocalizedModule.induction_on with
    | h b t =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have ha : a ∉ 𝔭.asIdeal := fun h => hx ((hz a s).mpr h)
    refine ⟨Localization.mk (b * s) ⟨a * t, 𝔭.asIdeal.primeCompl.mul_mem ha t.2⟩, ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, ← map_mul, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq]
    congr 1
    ring

end loc

section dim
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- A finite module supported only at the maximal ideal has finite length. -/
theorem a3e_length_ne_top_of_support (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N]
    (h : Module.support A N ⊆ {closedPoint A}) : Module.length A N ≠ ⊤ := by
  rw [Module.length_ne_top_iff]
  refine a3c_isFiniteLength_of_supportDim_le_zero N ?_
  have : Subsingleton (Module.support A N) :=
    ⟨fun a b => Subtype.ext ((h a.2).trans (h b.2).symm)⟩
  exact Order.krullDim_nonpos_of_subsingleton

variable (r : A)

/-- If `r` lies in no prime of the support of `N` other than `𝔪`, then `N ⧸ r N` and `0 :_N r`
have finite length. -/
theorem a3e_finite_of_support (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N]
    (h : ∀ 𝔭 ∈ Module.support A N, r ∈ 𝔭.asIdeal → 𝔭 = closedPoint A) :
    Module.length A (QuotSMulTop r N) ≠ ⊤ ∧ Module.length A (a3e_kerSMul r N) ≠ ⊤ := by
  have hrq : r ∈ Module.annihilator A (QuotSMulTop r N) := by
    rw [Module.mem_annihilator]
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  have hrk : r ∈ Module.annihilator A (a3e_kerSMul r N) := by
    rw [Module.mem_annihilator]
    intro x
    exact Subtype.ext x.2
  refine ⟨a3e_length_ne_top_of_support _ fun 𝔭 h𝔭 => ?_,
    a3e_length_ne_top_of_support _ fun 𝔭 h𝔭 => ?_⟩
  · refine h 𝔭 (Module.support_subset_of_surjective (r • (⊤ : Submodule A N)).mkQ
      (Submodule.mkQ_surjective _) h𝔭) ?_
    exact (Module.mem_support_iff_of_finite.mp h𝔭) hrq
  · refine h 𝔭 (Module.support_subset_of_injective (a3e_kerSMul r N).subtype
      Subtype.val_injective h𝔭) ?_
    exact (Module.mem_support_iff_of_finite.mp h𝔭) hrk

variable (Φ : Finset (PrimeSpectrum A)) (hΦm : ∀ 𝔭 ∈ Φ, 𝔭 ≠ closedPoint A)
  (hΦdim : ∀ 𝔭 ∈ Φ, ∀ 𝔮 : PrimeSpectrum A, 𝔭 < 𝔮 → 𝔮 = closedPoint A)
  (hΦr : ∀ 𝔭 ∈ Φ, r ∉ 𝔭.asIdeal)

omit [IsNoetherianRing A] in
include hΦr in
theorem a3e_support_condition {N : Type u} [AddCommGroup N] [Module A N]
    (hN : Module.support A N ⊆ insert (closedPoint A) (Φ : Set (PrimeSpectrum A))) :
    ∀ 𝔭 ∈ Module.support A N, r ∈ 𝔭.asIdeal → 𝔭 = closedPoint A := by
  intro 𝔭 h𝔭 hr
  rcases hN h𝔭 with h | h
  · exact h
  · exact absurd hr (hΦr 𝔭 h)

include hΦm hΦdim hΦr in
/-- The Herbrand difference of a module of dimension at most one, along its one-dimensional
primes: `e_r(N) = Σ_{𝔭 ∈ Φ} ℓ(N_𝔭) e_r(A ⧸ 𝔭)`.
Source: Fulton, *Intersection Theory*, second edition, Lemma A.2.2 and Example A.2.1. -/
theorem a3e_herbrand_eq_sum (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hN : Module.support A N ⊆ insert (closedPoint A) (Φ : Set (PrimeSpectrum A))) :
    a3e_herbrand r N =
      ∑ 𝔭 ∈ Φ, ((a3e_locLen 𝔭 N).toNat : ℤ) * a3e_herbrand r (A ⧸ 𝔭.asIdeal) ∧
    ∀ 𝔭 ∈ Φ, a3e_locLen 𝔭 N ≠ ⊤ := by
  revert hN
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A ‹Module.Finite A N›
    (motive := fun N _ _ _ => Module.support A N ⊆ insert (closedPoint A) (Φ : Set _) →
      a3e_herbrand r N =
        ∑ 𝔭 ∈ Φ, ((a3e_locLen 𝔭 N).toNat : ℤ) * a3e_herbrand r (A ⧸ 𝔭.asIdeal) ∧
      ∀ 𝔭 ∈ Φ, a3e_locLen 𝔭 N ≠ ⊤) ?_ ?_ ?_
  · intro N _ _ _ _ _
    have h0 : ∀ 𝔭 : PrimeSpectrum A, a3e_locLen 𝔭 N = 0 := fun 𝔭 => Module.length_eq_zero
    refine ⟨?_, fun 𝔭 _ => by rw [h0]; exact ENat.zero_ne_top⟩
    rw [a3e_herbrand_finiteLength r N (by rw [Module.length_eq_zero]; exact ENat.zero_ne_top)]
    simp [h0]
  · intro N _ _ _ 𝔮 e hN
    have h𝔮 : 𝔮 ∈ Module.support A N := by
      rw [e.support_eq]
      rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
    rw [a3e_herbrand_congr r e]
    simp only [a3e_locLen_congr _ e]
    rcases hN h𝔮 with h | h
    · subst h
      have hfin : Module.length A (A ⧸ (closedPoint A).asIdeal) ≠ ⊤ := by
        show Module.length A (A ⧸ maximalIdeal A) ≠ ⊤
        rw [Module.length_eq_one_iff.mpr (isSimpleModule_iff_isCoatom.mpr
          (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal A)))]
        exact ENat.one_ne_top
      have h0 : ∀ 𝔭 ∈ Φ, a3e_locLen 𝔭 (A ⧸ (closedPoint A).asIdeal) = 0 := by
        intro 𝔭 h𝔭
        have hlt : 𝔭.asIdeal < maximalIdeal A := lt_of_le_of_ne
          (le_maximalIdeal 𝔭.isPrime.ne_top) fun h => hΦm 𝔭 h𝔭 (PrimeSpectrum.ext h)
        obtain ⟨s, hs, hs'⟩ := IsConcreteLE.exists_of_lt hlt
        refine a3e_locLen_eq_zero 𝔭 _ s hs' fun n => ?_
        obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective n
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
          Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ hs
      refine ⟨?_, fun 𝔭 h𝔭 => by rw [h0 𝔭 h𝔭]; exact ENat.zero_ne_top⟩
      rw [a3e_herbrand_finiteLength r _ hfin, Finset.sum_eq_zero]
      intro 𝔭 h𝔭
      rw [h0 𝔭 h𝔭]
      simp
    · have hother : ∀ 𝔭 ∈ Φ, 𝔭 ≠ 𝔮 → a3e_locLen 𝔭 (A ⧸ 𝔮.asIdeal) = 0 := by
        intro 𝔭 h𝔭 hne
        have hnle : ¬ 𝔮 ≤ 𝔭 := fun hle =>
          hΦm 𝔭 h𝔭 (hΦdim 𝔮 h 𝔭 (lt_of_le_of_ne hle (Ne.symm hne)))
        obtain ⟨s, hs, hs'⟩ := Set.not_subset.mp hnle
        refine a3e_locLen_eq_zero 𝔭 _ s hs' fun n => ?_
        obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective n
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
          Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ hs
      refine ⟨?_, fun 𝔭 h𝔭 => ?_⟩
      · rw [Finset.sum_eq_single 𝔮 (fun 𝔭 h𝔭 hne => by rw [hother 𝔭 h𝔭 hne]; simp)
          (fun h' => absurd h h'), a3e_locLen_quotient_self]
        simp
      · by_cases hne : 𝔭 = 𝔮
        · rw [hne, a3e_locLen_quotient_self]
          exact ENat.one_ne_top
        · rw [hother 𝔭 h𝔭 hne]
          exact ENat.zero_ne_top
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg ih₁ ih₃ hN₂
    have hsupp := Module.support_of_exact hfg hf hg
    have hN₁ : Module.support A N₁ ⊆ insert (closedPoint A) (Φ : Set _) :=
      (Set.subset_union_left.trans hsupp.symm.subset).trans hN₂
    have hN₃ : Module.support A N₃ ⊆ insert (closedPoint A) (Φ : Set _) :=
      (Set.subset_union_right.trans hsupp.symm.subset).trans hN₂
    obtain ⟨e₁, l₁⟩ := ih₁ hN₁
    obtain ⟨e₃, l₃⟩ := ih₃ hN₃
    have hl : ∀ 𝔭, a3e_locLen 𝔭 N₂ = a3e_locLen 𝔭 N₁ + a3e_locLen 𝔭 N₃ := fun 𝔭 =>
      a3e_locLen_ses 𝔭 f g hf hg hfg
    refine ⟨?_, fun 𝔭 h𝔭 => by
      rw [hl]
      exact WithTop.add_ne_top.mpr ⟨l₁ 𝔭 h𝔭, l₃ 𝔭 h𝔭⟩⟩
    obtain ⟨c₁, k₁⟩ := a3e_finite_of_support r N₁ (a3e_support_condition r Φ hΦr hN₁)
    obtain ⟨c₂, k₂⟩ := a3e_finite_of_support r N₂ (a3e_support_condition r Φ hΦr hN₂)
    obtain ⟨c₃, k₃⟩ := a3e_finite_of_support r N₃ (a3e_support_condition r Φ hΦr hN₃)
    rw [a3e_herbrand_ses r f g hf hg hfg k₁ k₂ k₃ c₁ c₂ c₃, e₁, e₃, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun 𝔭 h𝔭 => ?_
    rw [hl, ENat.toNat_add (l₁ 𝔭 h𝔭) (l₃ 𝔭 h𝔭)]
    push_cast
    ring

end dim

end HodgeLean.Adapters
