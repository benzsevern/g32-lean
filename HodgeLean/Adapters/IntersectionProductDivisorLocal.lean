import HodgeLean.Adapters.IntersectionProductSerreLocal

/-! # Serre's multiplicity and principal divisors: the local identity at a point

At a point `T` of a smooth variety over `ℂ`, let `A = 𝒪_{X,T}`, `W`, `V` subvarieties through `T`
meeting properly in curves near `T`, and `a` a function on `W` vanishing on none of these curves.
Then `Σ_D ord_D(a|_W) · i(T; D · V) = Σ_Z i(Z; W · V) · ord_T(a|_Z)`, the sums over the
components `D` of `div(a|_W)` and `Z` of `W ∩ V` through `T` (`a3w_principal_stalk`): the local
form of `div(a|_W) · V = div(a|_{W · V})` (Fulton, Theorem 2.4) for Serre's multiplicities.

The proof filters `A ⧸ (𝔭_W + a)` by primes (`a3w_chi_devissage_top`): the primes of dimension
below that of the `D` contribute nothing by Serre's vanishing theorem (`a3w_vanishing_stalk`), and
the left side of `a3e_principal_local` is then the left side above.

Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.3 and C; Fulton, *Intersection
Theory*, second edition, Theorem 2.4, Example 7.1.10 and Lemma A.2.2.
HC no distance; AV milestone no distance.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory TensorProduct IsLocalRing

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace HodgeLean.Adapters

section devissageTop
variable {B : Type} [CommRing B] [IsRegularLocalRing B]

/-- Dévissage onto the minimal primes: if the Euler characteristic against `N` vanishes on the
quotients `B ⧸ 𝔮` for the primes `𝔮` of a set `Z` outside a finite set `F` of primes minimal in
`Z`, then `χ(M, N) = Σ_{𝔇 ∈ F} ℓ(M_𝔇) χ(B ⧸ 𝔇, N)` for every finite `M` supported in `Z`. -/
theorem a3w_chi_devissage_top (m : ℕ) (hm : ringKrullDim B < (m + 1 : ℕ)) (N : ModuleCat.{0} B)
    [Module.Finite B N] (Z : Set (PrimeSpectrum B)) (F : Finset (PrimeSpectrum B))
    (hfin : ∀ P ∈ Z, Module.annihilator B N ≤ P.asIdeal → P = closedPoint B)
    (hFZ : ∀ 𝔮 ∈ Z, ∀ 𝔇 ∈ F, 𝔮 ≤ 𝔇 → 𝔮 = 𝔇)
    (hlow : ∀ 𝔮 ∈ Z, 𝔮 ∉ F → a3s_chi m (ModuleCat.of B (B ⧸ 𝔮.asIdeal)) N = 0)
    (M : Type) [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hM : Module.support B M ⊆ Z) :
    a3s_chi m (ModuleCat.of B M) N =
        ∑ 𝔇 ∈ F, ((a3e_locLen 𝔇 M).toNat : ℤ) * a3s_chi m (ModuleCat.of B (B ⧸ 𝔇.asIdeal)) N ∧
      ∀ 𝔇 ∈ F, a3e_locLen 𝔇 M ≠ ⊤ := by
  revert hM
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime B
    (inferInstance : Module.Finite B M)
    (motive := fun X _ _ _ => Module.support B X ⊆ Z →
      a3s_chi m (ModuleCat.of B X) N =
        ∑ 𝔇 ∈ F, ((a3e_locLen 𝔇 X).toNat : ℤ) * a3s_chi m (ModuleCat.of B (B ⧸ 𝔇.asIdeal)) N ∧
      ∀ 𝔇 ∈ F, a3e_locLen 𝔇 X ≠ ⊤) ?_ ?_ ?_
  · intro X _ _ _ _ _
    have h0 : ∀ 𝔇 : PrimeSpectrum B, a3e_locLen 𝔇 X = 0 := fun 𝔇 => Module.length_eq_zero
    refine ⟨?_, fun 𝔇 _ => by rw [h0]; exact ENat.zero_ne_top⟩
    simp only [h0, ENat.toNat_zero, Nat.cast_zero, zero_mul, Finset.sum_const_zero]
    unfold a3s_chi
    refine Finset.sum_eq_zero fun i _ => ?_
    have : Subsingleton (ModuleCat.of B X) := inferInstanceAs (Subsingleton X)
    rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
      (a3c_isZero_tor_of_subsingleton _ _ i))]
    simp
  · intro X _ _ _ 𝔮 e hX
    have h𝔮 : 𝔮 ∈ Module.support B X := by
      rw [e.support_eq, Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
    rw [a3s_chi_congr e.toModuleIso]
    simp only [a3e_locLen_congr _ e]
    have hother : ∀ 𝔇 ∈ F, 𝔇 ≠ 𝔮 → a3e_locLen 𝔇 (B ⧸ 𝔮.asIdeal) = 0 := by
      intro 𝔇 h𝔇 hne
      have hnle : ¬ 𝔮 ≤ 𝔇 := fun hle => hne (hFZ 𝔮 (hX h𝔮) 𝔇 h𝔇 hle).symm
      obtain ⟨s, hs, hs'⟩ := Set.not_subset.mp hnle
      refine a3e_locLen_eq_zero 𝔇 _ s hs' fun n => ?_
      obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective n
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ hs
    by_cases hF : 𝔮 ∈ F
    · refine ⟨?_, fun 𝔇 h𝔇 => ?_⟩
      · rw [Finset.sum_eq_single 𝔮 (fun 𝔇 h𝔇 hne => by rw [hother 𝔇 h𝔇 hne]; simp)
          (fun h' => absurd hF h'), a3e_locLen_quotient_self]
        simp
      · by_cases hne : 𝔇 = 𝔮
        · rw [hne, a3e_locLen_quotient_self]; exact ENat.one_ne_top
        · rw [hother 𝔇 h𝔇 hne]; exact ENat.zero_ne_top
    · refine ⟨?_, fun 𝔇 h𝔇 => ?_⟩
      · rw [hlow 𝔮 (hX h𝔮) hF, Finset.sum_eq_zero]
        intro 𝔇 h𝔇
        rw [hother 𝔇 h𝔇 (fun h => hF (h ▸ h𝔇))]
        simp
      · rw [hother 𝔇 h𝔇 (fun h => hF (h ▸ h𝔇))]; exact ENat.zero_ne_top
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ hX
    have s₁ := Module.support_subset_of_injective f hf
    have s₃ := Module.support_subset_of_surjective g hg
    obtain ⟨e₁, l₁⟩ := h₁ (s₁.trans hX)
    obtain ⟨e₃, l₃⟩ := h₃ (s₃.trans hX)
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
    have hl : ∀ 𝔇, a3e_locLen 𝔇 N₂ = a3e_locLen 𝔇 N₁ + a3e_locLen 𝔇 N₃ := fun 𝔇 =>
      a3e_locLen_ses 𝔇 f g hf hg hfg
    refine ⟨?_, fun 𝔇 h𝔇 => by
      rw [hl]
      exact WithTop.add_ne_top.mpr ⟨l₁ 𝔇 h𝔇, l₃ 𝔇 h𝔇⟩⟩
    rw [e, e₁, e₃, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun 𝔇 h𝔇 => ?_
    rw [hl, ENat.toNat_add (l₁ 𝔇 h𝔇) (l₃ 𝔇 h𝔇)]
    push_cast
    ring

end devissageTop

section principalStalk
open AlgebraicGeometry

/-- In a local ring of a variety, `dim A/𝔮` is a natural number for every prime `𝔮`. -/
theorem a3w_dim_quot_nat (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (T : X.left)
    (𝔮 : Ideal (X.left.presheaf.stalk T)) [𝔮.IsPrime] :
    ∃ n : ℕ, ringKrullDim (X.left.presheaf.stalk T ⧸ 𝔮) = n ∧
      ∃ r : ℕ, ringKrullDim (X.left.presheaf.stalk T) = r ∧ n ≤ r := by
  have hreg := a3c_isRegularLocalRing_stalk X T
  have hA : ringKrullDim (X.left.presheaf.stalk T) =
      ((Submodule.spanFinrank (maximalIdeal (X.left.presheaf.stalk T)) : ℕ) : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := X.left.presheaf.stalk T)).symm
  set r := Submodule.spanFinrank (maximalIdeal (X.left.presheaf.stalk T))
  have h := a3c_height_add_ringKrullDim_quotient_stalk X T 𝔮
  rw [hA] at h
  obtain ⟨p, n, -, hn, hpn⟩ := a3m_withBot_add_eq_nat h
  exact ⟨n, hn, r, hA, by omega⟩

/-- Commutativity of Serre's multiplicity with a principal divisor, at a point `T` of a smooth
variety over `ℂ`. Let `A = 𝒪_{X,T}`, `P = 𝔭_W` and `Q = 𝔭_V` primes with `W ∩ V` proper of
dimension one at `T`, `dim A/P + dim A/Q = dim A + 1`, whose components through `T` form `Φ`,
and `a ∉ P` lying in no `Z ∈ Φ`. Let `F` be the set of primes `𝔇 ⊇ P + (a)` with
`dim A/𝔇 = dim A/P - 1`: the components `D` of `div(a|_W)` through `T`. Then
`Σ_{D ∈ F} ord_D(a|_W) · i(T; D · V) = Σ_{Z ∈ Φ} i(Z; W · V) · ord_T(a|_Z)`,
with `ord_D(a|_W) = ℓ((A ⧸ (P + a))_D)`, `ord_T(a|_Z) = e_a(A ⧸ Z)` and Serre's multiplicities
`i = Σ (-1)^i ℓ Tor_i`.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, C, and Chapitre V, B.3, Théorème 1;
Fulton, *Intersection Theory*, second edition, Theorem 2.4 and Example 7.1.10. -/
theorem a3w_principal_stalk (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (T : X.left)
    (P Q : Ideal (X.left.presheaf.stalk T)) [P.IsPrime] [Q.IsPrime] (a : X.left.presheaf.stalk T)
    (ha : a ∉ P) (Φ : Finset (PrimeSpectrum (X.left.presheaf.stalk T)))
    (hΦm : ∀ Z ∈ Φ, Z ≠ closedPoint (X.left.presheaf.stalk T))
    (hΦdim : ∀ Z ∈ Φ, ∀ 𝔮 : PrimeSpectrum (X.left.presheaf.stalk T), Z < 𝔮 →
      𝔮 = closedPoint (X.left.presheaf.stalk T))
    (hΦa : ∀ Z ∈ Φ, a ∉ Z.asIdeal)
    (hPQ : ∀ 𝔮 : PrimeSpectrum (X.left.presheaf.stalk T), P ≤ 𝔮.asIdeal → Q ≤ 𝔮.asIdeal →
      𝔮 = closedPoint (X.left.presheaf.stalk T) ∨ 𝔮 ∈ Φ)
    (hprop : ringKrullDim (X.left.presheaf.stalk T ⧸ P) +
        ringKrullDim (X.left.presheaf.stalk T ⧸ Q) = ringKrullDim (X.left.presheaf.stalk T) + 1)
    (F : Finset (PrimeSpectrum (X.left.presheaf.stalk T)))
    (hF : ∀ 𝔇 : PrimeSpectrum (X.left.presheaf.stalk T), 𝔇 ∈ F ↔
      (P ≤ 𝔇.asIdeal ∧ a ∈ 𝔇.asIdeal ∧
        ringKrullDim (X.left.presheaf.stalk T ⧸ 𝔇.asIdeal) + 1 =
          ringKrullDim (X.left.presheaf.stalk T ⧸ P)))
    (m : ℕ) (hm : ringKrullDim (X.left.presheaf.stalk T) ≤ m) :
    ∑ 𝔇 ∈ F, ((a3e_locLen 𝔇 (QuotSMulTop a (X.left.presheaf.stalk T ⧸ P))).toNat : ℤ) *
        a3s_chi m (ModuleCat.of (X.left.presheaf.stalk T) (X.left.presheaf.stalk T ⧸ 𝔇.asIdeal))
          (ModuleCat.of (X.left.presheaf.stalk T) (X.left.presheaf.stalk T ⧸ Q)) =
      ∑ Z ∈ Φ, (∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        ((a3e_locLen Z (((Tor (ModuleCat.{0} (X.left.presheaf.stalk T)) i).obj
          (ModuleCat.of (X.left.presheaf.stalk T) (X.left.presheaf.stalk T ⧸ P))).obj
            (ModuleCat.of (X.left.presheaf.stalk T) (X.left.presheaf.stalk T ⧸ Q)))).toNat : ℤ)) *
        a3e_herbrand a (X.left.presheaf.stalk T ⧸ Z.asIdeal) := by
  have hreg := a3c_isRegularLocalRing_stalk X T
  have hm' : ringKrullDim (X.left.presheaf.stalk T) < (m + 1 : ℕ) :=
    lt_of_le_of_lt hm (by exact_mod_cast Nat.lt_succ_self m)
  let M := QuotSMulTop a ((X.left.presheaf.stalk T) ⧸ P)
  have hannM : ∀ 𝔮 ∈ Module.support (X.left.presheaf.stalk T) M, P ≤ 𝔮.asIdeal ∧ a ∈ 𝔮.asIdeal := by
    intro 𝔮 h𝔮
    rw [Module.support_quotSMulTop] at h𝔮
    obtain ⟨h1, h2⟩ := h𝔮
    rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] at h1
    exact ⟨h1, by simpa using h2⟩
  -- dimensions as natural numbers
  obtain ⟨p, hp, r, hr, -⟩ := a3w_dim_quot_nat X T P
  obtain ⟨q, hq, -, -, -⟩ := a3w_dim_quot_nat X T Q
  rw [hp, hq, hr] at hprop
  have hpq : p + q = r + 1 := by exact_mod_cast hprop
  have hdims : ∀ 𝔮 ∈ Module.support (X.left.presheaf.stalk T) M, ∃ n : ℕ,
      ringKrullDim ((X.left.presheaf.stalk T) ⧸ 𝔮.asIdeal) = n ∧ n + 1 ≤ p := by
    intro 𝔮 h𝔮
    obtain ⟨hP𝔮, ha𝔮⟩ := hannM 𝔮 h𝔮
    obtain ⟨n, hn, -⟩ := a3w_dim_quot_nat X T 𝔮.asIdeal
    have hlt : P < 𝔮.asIdeal := lt_of_le_of_ne hP𝔮 fun h => ha (h ▸ ha𝔮)
    have := a3s_ringKrullDim_quotient_add_one_le hlt
    rw [hn, hp] at this
    exact ⟨n, hn, by exact_mod_cast this⟩
  have hclosed : ∀ 𝔮 ∈ Module.support (X.left.presheaf.stalk T) M,
      ∀ 𝔓 : PrimeSpectrum (X.left.presheaf.stalk T), 𝔮 ≤ 𝔓 → Q ≤ 𝔓.asIdeal →
      𝔓 = closedPoint (X.left.presheaf.stalk T) := by
    intro 𝔮 h𝔮 𝔓 h1 h2
    obtain ⟨hP𝔮, ha𝔮⟩ := hannM 𝔮 h𝔮
    rcases hPQ 𝔓 (hP𝔮.trans h1) h2 with h | h
    · exact h
    · exact absurd (h1 ha𝔮) (hΦa 𝔓 h)
  have : Module.Finite (X.left.presheaf.stalk T)
      (ModuleCat.of (X.left.presheaf.stalk T) ((X.left.presheaf.stalk T) ⧸ Q)) :=
    inferInstanceAs (Module.Finite (X.left.presheaf.stalk T) ((X.left.presheaf.stalk T) ⧸ Q))
  have hdev := a3w_chi_devissage_top m hm'
    (ModuleCat.of (X.left.presheaf.stalk T) ((X.left.presheaf.stalk T) ⧸ Q))
    (Module.support (X.left.presheaf.stalk T) M) F
    (fun 𝔓 h𝔓 hQ => by
      change Module.annihilator (X.left.presheaf.stalk T) ((X.left.presheaf.stalk T) ⧸ Q) ≤ _ at hQ
      rw [Ideal.annihilator_quotient] at hQ
      exact hclosed 𝔓 h𝔓 𝔓 le_rfl hQ)
    (fun 𝔮 h𝔮 𝔇 h𝔇 hle => by
      obtain ⟨n, hn, hnp⟩ := hdims 𝔮 h𝔮
      obtain ⟨-, -, h𝔇d⟩ := (hF 𝔇).1 h𝔇
      rcases eq_or_lt_of_le hle with h | h
      · exact h
      · exfalso
        have := a3s_ringKrullDim_quotient_add_one_le (show 𝔮.asIdeal < 𝔇.asIdeal from h)
        rw [hn] at this
        rw [hp] at h𝔇d
        obtain ⟨e, he, -⟩ := a3w_dim_quot_nat X T 𝔇.asIdeal
        rw [he] at this h𝔇d
        have h1 : e + 1 = p := by exact_mod_cast h𝔇d
        have h2 : e + 1 ≤ n := by exact_mod_cast this
        omega)
    (fun 𝔮 h𝔮 h𝔮F => by
      obtain ⟨n, hn, hnp⟩ := hdims 𝔮 h𝔮
      obtain ⟨hP𝔮, ha𝔮⟩ := hannM 𝔮 h𝔮
      have hn' : n + 1 ≠ p := fun h => h𝔮F ((hF 𝔮).2 ⟨hP𝔮, ha𝔮, by rw [hn, hp]; exact_mod_cast h⟩)
      refine a3w_vanishing_stalk X T ((X.left.presheaf.stalk T) ⧸ 𝔮.asIdeal)
        ((X.left.presheaf.stalk T) ⧸ Q) ?_ ?_ m hm
      · intro P' hP' Q' hQ' 𝔓 h1 h2
        rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] at hP' hQ'
        exact hclosed 𝔮 h𝔮 𝔓 (fun x hx => h1 (hP' hx)) (hQ'.trans h2)
      · intro P' hP' Q' hQ'
        rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] at hP' hQ'
        obtain ⟨n', hn', -⟩ := a3w_dim_quot_nat X T P'.asIdeal
        obtain ⟨q', hq', -⟩ := a3w_dim_quot_nat X T Q'.asIdeal
        have h1 : n' ≤ n := by
          have := ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP')
            (Ideal.Quotient.factor_surjective hP')
          rw [hn', hn] at this; exact_mod_cast this
        have h2 : q' ≤ q := by
          have := ringKrullDim_le_of_surjective (Ideal.Quotient.factor hQ')
            (Ideal.Quotient.factor_surjective hQ')
          rw [hq', hq] at this; exact_mod_cast this
        rw [hn', hq', hr]
        exact_mod_cast (by omega : n' + q' < r))
    M (subset_rfl)
  have hloc := a3e_principal_local P Q a ha m hm Φ hΦm hΦdim hΦa hPQ
  rw [← hloc, ← hdev.1]
  rfl

end principalStalk

end HodgeLean.Adapters
