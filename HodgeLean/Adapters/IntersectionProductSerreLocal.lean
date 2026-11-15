import HodgeLean.Adapters.IntersectionProductSerreGeneral
import HodgeLean.Adapters.IntersectionProductMovingDimension

/-! # Serre's vanishing theorem in the local rings of a smooth variety

Let `A` be the local ring at a point of a smooth variety over `ℂ`. For finite `A`-modules `M`, `N`
whose supports meet only at the closed point (so `M ⊗ N` has finite length) and with
`dim A/P + dim A/Q < dim A` for all primes `P` of the support of `M` and `Q` of that of `N` (that
is, `dim M + dim N < dim A`), `Σ_{i ≤ m} (-1)^i ℓ Tor_i^A(M, N) = 0` for every `m ≥ dim A`
(`a3w_vanishing_stalk`).

The steps:
* `a3w_length_tor_localization`: for a localization `A = S_R`, the lengths of
  `Tor_i^A(A/𝔭A, A/𝔮A)` are the localized lengths at `R` of `Tor_i^S(S/𝔭, S/𝔮)`;
* `a3w_vanishing_atPrime`: the case `M = A/P`, `N = A/Q` for a localization of a smooth affine
  variety with étale coordinates, from `a3w_vanishing_affine`;
* `a3w_chi_devissage` and `a3w_vanishing_module`: prime filtrations of `M` and `N`;
* `a3w_vanishing_stalk`: an affine chart with étale coordinates around the point.

Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.3, Théorème 1 (the case of a regular
local ring containing a field); Hartshorne, *Algebraic Geometry*, II, Proposition 2.2 (stalks as
localizations). HC no distance; AV milestone no distance.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory TensorProduct IsLocalRing

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace HodgeLean.Adapters

section loc
variable {S : Type} [CommRing S] (R : Ideal S) [R.IsPrime] (A : Type) [CommRing A] [Algebra S A]
  [IsLocalization.AtPrime A R]

/-- Lengths of `Tor` over a localization `A = S_R` are localized lengths of `Tor` over `S`. -/
theorem a3w_length_tor_localization (𝔭 𝔮 : Ideal S) (i : ℕ) :
    Module.length A (((Tor (ModuleCat.{0} A) i).obj
      (ModuleCat.of A (A ⧸ 𝔭.map (algebraMap S A)))).obj
        (ModuleCat.of A (A ⧸ 𝔮.map (algebraMap S A)))) =
    a3e_locLen ⟨R, inferInstance⟩ (((Tor (ModuleCat.{0} S) i).obj
      (ModuleCat.of S (S ⧸ 𝔭))).obj (ModuleCat.of S (S ⧸ 𝔮))) := by
  let f := algebraMap S A
  have hf : f.Flat := RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A R.primeCompl)
  obtain ⟨eb⟩ := a3q_tor_baseChange f hf (ModuleCat.of S (S ⧸ 𝔭)) (ModuleCat.of S (S ⧸ 𝔮)) i
  let e := (((Tor (ModuleCat.{0} A) i).mapIso (a3w_extQuot 𝔭)).app _ ≪≫
    ((Tor (ModuleCat.{0} A) i).obj _).mapIso (a3w_extQuot 𝔮)).symm ≪≫ eb
  rw [e.toLinearEquiv.length_eq, a3w_length_extendScalars]
  exact (a3q_locLen_eq_length ⟨R, inferInstance⟩ _ _ (TensorProduct.mk S A _ 1)).symm

end loc

section locVanishing
variable (k : Type) [Field k] [IsAlgClosed k] {S : Type} [CommRing S] [IsDomain S] [Algebra k S]
  [Algebra.FiniteType k S] (d : ℕ) [Algebra (MvPolynomial (Fin d) k) S]
  [IsScalarTower k (MvPolynomial (Fin d) k) S] [Algebra.Etale (MvPolynomial (Fin d) k) S]
  (R : Ideal S) [R.IsPrime] (A : Type) [CommRing A] [Algebra S A] [IsLocalization.AtPrime A R]
  [IsLocalRing A]

include k R in
/-- Serre's vanishing theorem for two primes of a local ring `A = S_R` of a smooth affine variety
with étale coordinates: if `P + Q` is primary to the maximal ideal and
`dim A/P + dim A/Q < dim A`, then `Σ_{i ≤ m} (-1)^i ℓ Tor_i^A(A/P, A/Q) = 0` for `m ≥ d`.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.3, Théorème 1. -/
theorem a3w_vanishing_atPrime (hdim : ringKrullDim S = d) (P Q : Ideal A) [P.IsPrime] [Q.IsPrime]
    (hPQ : ∀ 𝔓 : Ideal A, 𝔓.IsPrime → P ⊔ Q ≤ 𝔓 → 𝔓 = maximalIdeal A)
    (hlt : ringKrullDim (A ⧸ P) + ringKrullDim (A ⧸ Q) < ringKrullDim A) (m : ℕ) (hm : d ≤ m) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
      ((Module.length A (((Tor (ModuleCat.{0} A) i).obj
        (ModuleCat.of A (A ⧸ P))).obj (ModuleCat.of A (A ⧸ Q)))).toNat : ℤ) = 0 := by
  set 𝔭 := P.comap (algebraMap S A)
  set 𝔮 := Q.comap (algebraMap S A)
  have hP : 𝔭.map (algebraMap S A) = P := IsLocalization.map_under R.primeCompl A P
  have hQ : 𝔮.map (algebraMap S A) = Q := IsLocalization.map_under R.primeCompl A Q
  have hRmax : (maximalIdeal A).comap (algebraMap S A) = R :=
    IsLocalization.AtPrime.under_maximalIdeal A R
  have hR : R ∈ (𝔭 ⊔ 𝔮).minimalPrimes := by
    refine ⟨⟨inferInstance, sup_le ?_ ?_⟩, fun R' hR' hR'R => ?_⟩
    · rw [← hRmax]; exact Ideal.comap_mono (le_maximalIdeal Ideal.IsPrime.ne_top')
    · rw [← hRmax]; exact Ideal.comap_mono (le_maximalIdeal Ideal.IsPrime.ne_top')
    obtain ⟨hR'p, hle⟩ := hR'
    have hd : Disjoint (R.primeCompl : Set S) R' :=
      Set.disjoint_left.2 fun x hx hx' => hx (hR'R hx')
    have hprime := IsLocalization.isPrime_of_isPrime_disjoint R.primeCompl A R' hR'p hd
    have hmax : R'.map (algebraMap S A) = maximalIdeal A := by
      refine hPQ _ hprime (sup_le ?_ ?_)
      · rw [← hP]; exact Ideal.map_mono (le_sup_left.trans hle)
      · rw [← hQ]; exact Ideal.map_mono (le_sup_right.trans hle)
    have := IsLocalization.under_map_of_isPrime_disjoint R.primeCompl A hR'p hd
    rw [← this, Ideal.under, hmax, hRmax]
  -- dimensions
  have hRd := hc9k8_height_add_ringKrullDim_quotient (k := k) R
  rw [hdim] at hRd
  obtain ⟨r, e, hr, -, -⟩ := a3m_withBot_add_eq_nat hRd
  have hA : ringKrullDim A = (r : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height R A, hr]; rfl
  have hPd := a3c_height_add_ringKrullDim_quotient_of_isLocalization (k := k) R A P
  have hQd := a3c_height_add_ringKrullDim_quotient_of_isLocalization (k := k) R A Q
  rw [hA] at hPd hQd
  rw [← IsLocalization.height_under R.primeCompl P] at hPd
  rw [← IsLocalization.height_under R.primeCompl Q] at hQd
  obtain ⟨p, a, hp, ha, hpa⟩ := a3m_withBot_add_eq_nat hPd
  obtain ⟨q, b, hq, hb, hqb⟩ := a3m_withBot_add_eq_nat hQd
  rw [ha, hb, hA] at hlt
  have hlt' : a + b < r := by exact_mod_cast hlt
  have hheight : R.height < 𝔭.height + 𝔮.height := by
    change R.height < (P.under S).height + (Q.under S).height
    rw [hr, hp, hq]
    exact_mod_cast (by omega : r < p + q)
  have key := a3w_vanishing_affine k d 𝔭 𝔮 R hdim hR hheight m hm
  rw [← key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← a3w_length_tor_localization R A 𝔭 𝔮 i, hP, hQ]

end locVanishing

section devissage
variable {B : Type} [CommRing B] [IsRegularLocalRing B]

/-- Dévissage in the first variable: if the Euler characteristic against `N` vanishes on the
quotients `B ⧸ P` for `P` in a set `Z` of primes meeting the support of `N` only at the closed
point, it vanishes on every finite module supported in `Z`. -/
theorem a3w_chi_devissage (m : ℕ) (hm : ringKrullDim B < (m + 1 : ℕ)) (N : ModuleCat.{0} B)
    [Module.Finite B N] (Z : Set (PrimeSpectrum B))
    (hfin : ∀ P ∈ Z, Module.annihilator B N ≤ P.asIdeal → P = closedPoint B)
    (hprime : ∀ P ∈ Z, a3s_chi m (ModuleCat.of B (B ⧸ P.asIdeal)) N = 0)
    (M : Type) [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hM : Module.support B M ⊆ Z) : a3s_chi m (ModuleCat.of B M) N = 0 := by
  revert hM
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime B (inferInstance : Module.Finite B M)
    (motive := fun X _ _ _ => Module.support B X ⊆ Z → a3s_chi m (ModuleCat.of B X) N = 0) ?_ ?_ ?_
  · intro X _ _ _ _ _
    unfold a3s_chi
    refine Finset.sum_eq_zero fun i _ => ?_
    have : Subsingleton (ModuleCat.of B X) := inferInstanceAs (Subsingleton X)
    rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
      (a3c_isZero_tor_of_subsingleton _ _ i))]
    simp
  · intro X _ _ _ p e hX
    have hp : p ∈ Module.support B X := by
      rw [e.support_eq, Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
    rw [a3s_chi_congr e.toModuleIso]
    exact hprime p (hX hp)
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ hX
    have s₁ := Module.support_subset_of_injective f hf
    have s₃ := Module.support_subset_of_surjective g hg
    let S : ShortComplex (ModuleCat.{0} B) :=
      ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (by ext x; exact hfg.apply_apply_eq_zero x)
    have hS : S.ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hfg
        mono_f := (ModuleCat.mono_iff_injective _).2 hf
        epi_g := (ModuleCat.epi_iff_surjective _).2 hg }
    have fin : ∀ (Y : Type) [AddCommGroup Y] [Module B Y] [Module.Finite B Y],
        Module.support B Y ⊆ Module.support B N₂ → ∀ i,
        Module.length B (((Tor (ModuleCat.{0} B) i).obj (ModuleCat.of B Y)).obj N) ≠ ⊤ := by
      intro Y _ _ _ hY i
      have : Module.Finite B (ModuleCat.of B Y) := ‹Module.Finite B Y›
      refine a3s_length_tor_ne_top _ _ i fun 𝔮 h1 h2 => hfin 𝔮 (hX (hY ?_)) h2
      exact (Module.mem_support_iff_of_finite (M := Y)).2 h1
    have e := a3s_chi_ses S hS N m
      (fun i _ => fin N₁ s₁ i) (fun i _ => fin N₂ subset_rfl i) (fun i _ => fin N₃ s₃ i)
      (a3e_isZero_tor_regular _ _ (m + 1) hm)
    change a3s_chi m (ModuleCat.of B N₂) _ =
      a3s_chi m (ModuleCat.of B N₁) _ + a3s_chi m (ModuleCat.of B N₃) _ at e
    rw [e, h₁ (s₁.trans hX), h₃ (s₃.trans hX), add_zero]

end devissage


section moduleVanishing
variable (k : Type) [Field k] [IsAlgClosed k] {S : Type} [CommRing S] [IsDomain S] [Algebra k S]
  [Algebra.FiniteType k S] (d : ℕ) [Algebra (MvPolynomial (Fin d) k) S]
  [IsScalarTower k (MvPolynomial (Fin d) k) S] [Algebra.Etale (MvPolynomial (Fin d) k) S]
  (R : Ideal S) [R.IsPrime] (A : Type) [CommRing A] [Algebra S A] [IsLocalization.AtPrime A R]
  [IsLocalRing A]

omit [IsAlgClosed k] [IsScalarTower k (MvPolynomial (Fin d) k) S] [IsLocalRing A] in
include k R in
/-- A localization `S_R` of a smooth affine variety with étale coordinates is a regular local ring
of dimension at most `d`. -/
theorem a3w_isRegular_dim_le (hdim : ringKrullDim S = d) :
    IsRegularLocalRing A ∧ ringKrullDim A ≤ d := by
  have hreg : IsRegularLocalRing (Localization.AtPrime R) :=
    a3c_isRegularLocalRing_atPrime_of_etale (R := MvPolynomial (Fin d) k) R
  refine ⟨@IsRegularLocalRing.of_ringEquiv (Localization.AtPrime R) _ hreg A _
    (IsLocalization.algEquiv R.primeCompl (Localization.AtPrime R) A).toRingEquiv, ?_⟩
  have hRd := hc9k8_height_add_ringKrullDim_quotient (k := k) R
  rw [hdim] at hRd
  obtain ⟨r, e, hr, -, hre⟩ := a3m_withBot_add_eq_nat hRd
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height R A, hr]
  exact_mod_cast (by omega : r ≤ d)

include k R in
/-- Serre's vanishing theorem for finite modules over a local ring `A = S_R` of a smooth affine
variety with étale coordinates: if the supports of `M` and `N` meet only at the closed point and
`dim A/P + dim A/Q < dim A` for all `P` in the support of `M` and `Q` in that of `N` (that is,
`dim M + dim N < dim A`), then `Σ_{i ≤ m} (-1)^i ℓ Tor_i^A(M, N) = 0` for `m ≥ d`.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.3, Théorème 1. -/
theorem a3w_vanishing_module (hdim : ringKrullDim S = d) (M N : Type) [AddCommGroup M]
    [Module A M] [Module.Finite A M] [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hsupp : ∀ P ∈ Module.support A M, ∀ Q ∈ Module.support A N, ∀ 𝔓 : PrimeSpectrum A,
      P ≤ 𝔓 → Q ≤ 𝔓 → 𝔓 = closedPoint A)
    (hdimMN : ∀ P ∈ Module.support A M, ∀ Q ∈ Module.support A N,
      ringKrullDim (A ⧸ P.asIdeal) + ringKrullDim (A ⧸ Q.asIdeal) < ringKrullDim A)
    (m : ℕ) (hm : d ≤ m) : a3s_chi m (ModuleCat.of A M) (ModuleCat.of A N) = 0 := by
  obtain ⟨hreg, hAd⟩ := a3w_isRegular_dim_le k d R A hdim
  have hm' : ringKrullDim A < (m + 1 : ℕ) :=
    lt_of_le_of_lt hAd (by exact_mod_cast (by omega : d < m + 1))
  have : Module.Finite A (ModuleCat.of A N) := ‹Module.Finite A N›
  refine a3w_chi_devissage m hm' (ModuleCat.of A N) (Module.support A M) ?_ ?_ M subset_rfl
  · intro P hP hPN
    have hPN' : P ∈ Module.support A N := (Module.mem_support_iff_of_finite (M := N)).2 hPN
    exact hsupp P hP P hPN' P le_rfl le_rfl
  intro P hP
  rw [a3s_chi_symm]
  have : Module.Finite A (ModuleCat.of A (A ⧸ P.asIdeal)) :=
    inferInstanceAs (Module.Finite A (A ⧸ P.asIdeal))
  refine a3w_chi_devissage m hm' (ModuleCat.of A (A ⧸ P.asIdeal)) (Module.support A N) ?_ ?_
    N subset_rfl
  · intro Q hQ hPQ
    change Module.annihilator A (A ⧸ P.asIdeal) ≤ Q.asIdeal at hPQ
    rw [Ideal.annihilator_quotient] at hPQ
    exact hsupp P hP Q hQ Q hPQ le_rfl
  intro Q hQ
  unfold a3s_chi
  refine a3w_vanishing_atPrime k d R A hdim Q.asIdeal P.asIdeal ?_ ?_ m hm
  · intro 𝔓 h𝔓 hle
    have := hsupp P hP Q hQ ⟨𝔓, h𝔓⟩ (le_sup_right.trans hle) (le_sup_left.trans hle)
    exact congrArg PrimeSpectrum.asIdeal this
  · rw [add_comm]; exact hdimMN P hP Q hQ

end moduleVanishing


/-- Over a regular local ring the truncated Euler characteristic of `Tor` stabilises from the
dimension on. -/
theorem a3w_chi_eq_of_le {B : Type} [CommRing B] [IsRegularLocalRing B] (M N : ModuleCat.{0} B)
    [Module.Finite B N] {m m' : ℕ} (hm : ringKrullDim B ≤ m) (hmm' : m ≤ m') :
    a3s_chi m M N = a3s_chi m' M N := by
  induction m', hmm' using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [ih]
    unfold a3s_chi
    rw [Finset.sum_range_succ (n := n + 1)]
    have hz := a3e_isZero_tor_regular M N (n + 1)
      (lt_of_le_of_lt hm (by exact_mod_cast (by omega : m < n + 1)))
    rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hz)]
    simp

open AlgebraicGeometry

attribute [local instance] overSpecAlgebra

/-- Serre's vanishing theorem on a smooth variety over `ℂ`: for finite modules `M`, `N` over a
local ring `A = 𝒪_{X,T}` whose supports meet only at the closed point, with
`dim A/P + dim A/Q < dim A` for all `P` in the support of `M` and `Q` in that of `N`,
`Σ_{i ≤ m} (-1)^i ℓ Tor_i^A(M, N) = 0` for every `m ≥ dim A`.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.3, Théorème 1 (the case of a regular
local ring containing a field, by reduction to the diagonal). -/
theorem a3w_vanishing_stalk (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (T : X.left) (M N : Type) [AddCommGroup M] [Module (X.left.presheaf.stalk T) M]
    [Module.Finite (X.left.presheaf.stalk T) M] [AddCommGroup N]
    [Module (X.left.presheaf.stalk T) N] [Module.Finite (X.left.presheaf.stalk T) N]
    (hsupp : ∀ P ∈ Module.support (X.left.presheaf.stalk T) M,
      ∀ Q ∈ Module.support (X.left.presheaf.stalk T) N,
      ∀ 𝔓 : PrimeSpectrum (X.left.presheaf.stalk T), P ≤ 𝔓 → Q ≤ 𝔓 →
        𝔓 = IsLocalRing.closedPoint (X.left.presheaf.stalk T))
    (hdimMN : ∀ P ∈ Module.support (X.left.presheaf.stalk T) M,
      ∀ Q ∈ Module.support (X.left.presheaf.stalk T) N,
      ringKrullDim (X.left.presheaf.stalk T ⧸ P.asIdeal) +
          ringKrullDim (X.left.presheaf.stalk T ⧸ Q.asIdeal) <
        ringKrullDim (X.left.presheaf.stalk T))
    (m : ℕ) (hm : ringKrullDim (X.left.presheaf.stalk T) ≤ m) :
    a3s_chi m (ModuleCat.of (X.left.presheaf.stalk T) M)
      (ModuleCat.of (X.left.presheaf.stalk T) N) = 0 := by
  obtain ⟨d, hd⟩ := Smooth.exists_smoothOfRelativeDimension X.hom
  obtain ⟨V, hV, hTV, hf⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension (d := d) X.hom T
  have hf' := algebraMap_isStandardSmoothOfRelativeDimension (d := d) X hf
  have : Nonempty V := ⟨⟨T, hTV⟩⟩
  have hdim : ringKrullDim Γ(X.left, V) = d := hf'.ringKrullDim_eq_complex
  obtain ⟨g, hgC, hg⟩ := hf'.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin d) ℂ) Γ(X.left, V) := g.toAlgebra
  have : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) Γ(X.left, V) :=
    IsScalarTower.of_algebraMap_eq' hgC.symm
  have : Algebra.Etale (MvPolynomial (Fin d) ℂ) Γ(X.left, V) := RingHom.etale_algebraMap.mp hg
  have : Algebra.FiniteType ℂ Γ(X.left, V) :=
    Algebra.FiniteType.trans (S := MvPolynomial (Fin d) ℂ) inferInstance inferInstance
  let P : Ideal Γ(X.left, V) := (hV.primeIdealOf ⟨T, hTV⟩).asIdeal
  let : Algebra Γ(X.left, V) (X.left.presheaf.stalk T) :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨T, hTV⟩
  have : IsLocalization.AtPrime (X.left.presheaf.stalk T) P := hV.isLocalization_stalk ⟨T, hTV⟩
  have hreg := a3c_isRegularLocalRing_stalk X T
  have : Module.Finite (X.left.presheaf.stalk T) (ModuleCat.of (X.left.presheaf.stalk T) N) := ‹_›
  rw [a3w_chi_eq_of_le (ModuleCat.of (X.left.presheaf.stalk T) M)
    (ModuleCat.of (X.left.presheaf.stalk T) N) hm (le_max_left m d)]
  exact a3w_vanishing_module ℂ d P (X.left.presheaf.stalk T) hdim M N hsupp hdimMN (max m d)
    (le_max_right m d)

end HodgeLean.Adapters
