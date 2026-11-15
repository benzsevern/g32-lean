import HodgeLean.Adapters.IntersectionProductTorLocal

/-! # Serre's vanishing theorem: the Euler characteristic of `Tor`

For modules `M`, `N` over a commutative ring, `a3s_chi m M N = Σ_{i ≤ m} (-1)^i ℓ Tor_i(M, N)`.
It is additive along short exact sequences in `M` when the lengths involved are finite and
`Tor_{m+1}` of the quotient vanishes (`a3s_chi_ses`).

HC no distance; AV milestone no distance.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory IsLocalRing

noncomputable section
namespace HodgeLean.Adapters
universe u

section chi
variable {R : Type u} [CommRing R]

/-- The truncated Euler characteristic `Σ_{i ≤ m} (-1)^i ℓ Tor_i(M, N)`, each length read
through `ENat.toNat`.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, A.1 (the Euler–Poincaré
characteristic `χ(M, N)`). -/
def a3s_chi (m : ℕ) (M N : ModuleCat.{u} R) : ℤ :=
  ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
    ((Module.length R (((Tor (ModuleCat.{u} R) i).obj M).obj N)).toNat : ℤ)

example (M N : ModuleCat.{u} R) : a3s_chi 0 M N =
    ((Module.length R (((Tor (ModuleCat.{u} R) 0).obj M).obj N)).toNat : ℤ) := by
  simp [a3s_chi]

/-- The alternating-sum bookkeeping of a long exact sequence truncated at `m`. -/
theorem a3s_alt_sum3 (a b c k p q : ℕ → ℤ) (m : ℕ) (ha : ∀ i ≤ m, a i = k i + p i)
    (hb : ∀ i ≤ m, b i = p i + q i) (hc0 : c 0 = q 0)
    (hc : ∀ i, i + 1 ≤ m → c (i + 1) = q (i + 1) + k i) :
    ∀ m' ≤ m, ∑ i ∈ Finset.range (m' + 1), (-1 : ℤ) ^ i * b i =
      ∑ i ∈ Finset.range (m' + 1), (-1 : ℤ) ^ i * a i +
        ∑ i ∈ Finset.range (m' + 1), (-1 : ℤ) ^ i * c i - (-1) ^ m' * k m' := by
  intro m' hm'
  induction m' with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul]
    rw [ha 0 hm', hb 0 hm', hc0]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (n := n + 1),
      Finset.sum_range_succ (n := n + 1), ih (by omega), ha (n + 1) hm', hb (n + 1) hm',
      hc n hm', pow_succ]
    ring

variable {N : ModuleCat.{u} R} (Q : ProjectiveResolution N)

/-- `H_0(- ⊗ Q)` sends an epimorphism to a surjection. -/
theorem a3s_surjective_homologyMap_zero {X Y : ModuleCat.{u} R} (g : X ⟶ Y) [Epi g] :
    Function.Surjective (HomologicalComplex.homologyMap (a3c_tensMap g Q.complex) 0).hom := by
  rw [← ModuleCat.epi_iff_surjective]
  have h := a3c_H0Iso_naturality Q g
  rw [← Iso.eq_comp_inv, Category.assoc] at h
  rw [h]
  infer_instance

theorem a3s_toNat_add {a x y : ℕ∞} (h : a = x + y) (ha : a ≠ ⊤) :
    (a.toNat : ℤ) = (x.toNat : ℤ) + (y.toNat : ℤ) := by
  have hx : x ≠ ⊤ := fun hx => ha (by rw [h, hx, top_add])
  have hy : y ≠ ⊤ := fun hy => ha (by rw [h, hy, add_top])
  rw [h, ENat.toNat_add hx hy]
  push_cast
  rfl

/-- Additivity of the truncated Euler characteristic along `0 → X₁ → X₂ → X₃ → 0`, in the
homology of `- ⊗ Q`. -/
theorem a3s_chi_ses_homology (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (m : ℕ)
    (h₁ : ∀ i ≤ m, Module.length R ((a3c_tensC S.X₁ Q.complex).homology i) ≠ ⊤)
    (h₂ : ∀ i ≤ m, Module.length R ((a3c_tensC S.X₂ Q.complex).homology i) ≠ ⊤)
    (h₃ : ∀ i ≤ m, Module.length R ((a3c_tensC S.X₃ Q.complex).homology i) ≠ ⊤)
    (htop : IsZero ((a3c_tensC S.X₃ Q.complex).homology (m + 1))) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        ((Module.length R ((a3c_tensC S.X₂ Q.complex).homology i)).toNat : ℤ) =
      ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
          ((Module.length R ((a3c_tensC S.X₁ Q.complex).homology i)).toNat : ℤ) +
        ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
          ((Module.length R ((a3c_tensC S.X₃ Q.complex).homology i)).toNat : ℤ) := by
  have hT := a3c_sesC_shortExact S hS Q.complex Q.projective
  have : Epi S.g := hS.epi_g
  let f := fun i : ℕ => (HomologicalComplex.homologyMap (a3c_tensMap S.f Q.complex) i).hom
  let g := fun i : ℕ => (HomologicalComplex.homologyMap (a3c_tensMap S.g Q.complex) i).hom
  let δ := fun i : ℕ => (hT.δ (i + 1) i (by simp)).hom
  have ex₁ : ∀ i, LinearMap.range (δ i) = LinearMap.ker (f i) := fun i =>
    (hT.homology_exact₁ (i + 1) i (by simp)).moduleCat_range_eq_ker
  have ex₂ : ∀ i, LinearMap.range (f i) = LinearMap.ker (g i) := fun i =>
    (hT.homology_exact₂ i).moduleCat_range_eq_ker
  have ex₃ : ∀ i, LinearMap.range (g (i + 1)) = LinearMap.ker (δ i) := fun i =>
    (hT.homology_exact₃ (i + 1) i (by simp)).moduleCat_range_eq_ker
  let k : ℕ → ℤ := fun i => ((Module.length R (LinearMap.ker (f i))).toNat : ℤ)
  let p : ℕ → ℤ := fun i => ((Module.length R (LinearMap.range (f i))).toNat : ℤ)
  let q : ℕ → ℤ := fun i => ((Module.length R (LinearMap.range (g i))).toNat : ℤ)
  have key := a3s_alt_sum3
    (fun i => ((Module.length R ((a3c_tensC S.X₁ Q.complex).homology i)).toNat : ℤ))
    (fun i => ((Module.length R ((a3c_tensC S.X₂ Q.complex).homology i)).toNat : ℤ))
    (fun i => ((Module.length R ((a3c_tensC S.X₃ Q.complex).homology i)).toNat : ℤ))
    k p q m
    (fun i hi => a3s_toNat_add (a3e_length_eq_ker_add_range (f i)) (h₁ i hi))
    (fun i hi => by
      have := a3s_toNat_add (a3e_length_eq_ker_add_range (g i)) (h₂ i hi)
      rw [this, ← ex₂ i])
    (by
      have hsurj := a3s_surjective_homologyMap_zero Q S.g
      change _ = ((Module.length R (LinearMap.range (g 0))).toNat : ℤ)
      rw [LinearMap.range_eq_top.mpr hsurj, Module.length_top])
    (fun i hi => by
      refine (a3s_toNat_add (a3e_length_eq_ker_add_range (δ i)) (h₃ (i + 1) hi)).trans ?_
      rw [← ex₃ i, ex₁ i]
      rfl)
    m le_rfl
  have hk : k m = 0 := by
    have hδ : hT.δ (m + 1) m (by simp) = 0 := htop.eq_of_src _ _
    have : LinearMap.ker (f m) = ⊥ := by
      rw [← ex₁ m]
      change LinearMap.range (hT.δ (m + 1) m (by simp)).hom = ⊥
      rw [hδ, ModuleCat.hom_zero, LinearMap.range_zero]
    have h0 : Module.length R (LinearMap.ker (f m)) = 0 := by
      rw [this]
      exact Module.length_bot
    simp only [k, h0, ENat.toNat_zero, Nat.cast_zero]
  rw [key, hk, mul_zero, sub_zero]

/-- Additivity of the truncated Euler characteristic of `Tor(-, N)` along a short exact
sequence, given finite lengths up to `m` and `Tor_{m+1}(X₃, N) = 0`.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, A.1 (additivity of `χ`). -/
theorem a3s_chi_ses (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (N : ModuleCat.{u} R) (m : ℕ)
    (h₁ : ∀ i ≤ m, Module.length R (((Tor (ModuleCat.{u} R) i).obj S.X₁).obj N) ≠ ⊤)
    (h₂ : ∀ i ≤ m, Module.length R (((Tor (ModuleCat.{u} R) i).obj S.X₂).obj N) ≠ ⊤)
    (h₃ : ∀ i ≤ m, Module.length R (((Tor (ModuleCat.{u} R) i).obj S.X₃).obj N) ≠ ⊤)
    (htop : IsZero (((Tor (ModuleCat.{u} R) (m + 1)).obj S.X₃).obj N)) :
    a3s_chi m S.X₂ N = a3s_chi m S.X₁ N + a3s_chi m S.X₃ N := by
  let Q := ProjectiveResolution.of N
  have e := fun (X : ModuleCat.{u} R) i => (a3c_torIso X N Q i).toLinearEquiv
  unfold a3s_chi
  simp only [(e _ _).length_eq] at h₁ h₂ h₃ ⊢
  exact a3s_chi_ses_homology Q S hS m h₁ h₂ h₃ (htop.of_iso (a3c_torIso _ N Q (m + 1)).symm)

theorem a3s_chi_symm (m : ℕ) (M N : ModuleCat.{u} R) : a3s_chi m M N = a3s_chi m N M := by
  unfold a3s_chi
  simp only [a3c_length_tor_symm M N]

theorem a3s_chi_congr {M M' : ModuleCat.{u} R} (e : M ≅ M') (N : ModuleCat.{u} R) (m : ℕ) :
    a3s_chi m M N = a3s_chi m M' N := by
  unfold a3s_chi
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(((Tor (ModuleCat.{u} R) i).mapIso e).app N).toLinearEquiv.length_eq]

/-- A point of the support of `Tor_i(M, N)` contains the annihilators of `M` and of `N`. -/
theorem a3s_annihilator_le_of_mem_support_tor (M N : ModuleCat.{u} R) (i : ℕ)
    (𝔮 : PrimeSpectrum R)
    (h : 𝔮 ∈ Module.support R (((Tor (ModuleCat.{u} R) i).obj M).obj N)) :
    Module.annihilator R M ≤ 𝔮.asIdeal ∧ Module.annihilator R N ≤ 𝔮.asIdeal := by
  have hann := Module.annihilator_le_of_mem_support h
  exact ⟨fun p hp => hann (Module.mem_annihilator.mpr fun t =>
      a3c_smul_tor_eq_zero_of_mem_annihilator_left M N p hp i t),
    fun q hq => hann (Module.mem_annihilator.mpr fun t =>
      a3c_smul_tor_eq_zero_of_mem_annihilator_right M N q hq i t)⟩

/-- `M ⧸ (x₁, …, xₖ) M` as `QuotSMulTop` of the last element. -/
theorem a3s_iterQuot_append (xs : List R) (y : R) (M : ModuleCat.{u} R) :
    a3c_iterQuot (xs ++ [y]) M = ModuleCat.of R (QuotSMulTop y (a3c_iterQuot xs M)) := by
  induction xs generalizing M with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem a3s_ofList_le_annihilator_iterQuot (xs : List R) (M : ModuleCat.{u} R) :
    Ideal.ofList xs ≤ Module.annihilator R (a3c_iterQuot xs M) := by
  intro x hx
  rw [Module.mem_annihilator]
  intro t
  apply (a3c_iterQuotEquiv xs M).injective
  rw [LinearEquiv.map_smul, LinearEquiv.map_zero]
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (a3c_iterQuotEquiv xs M t)
  rw [← hm, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hx Submodule.mem_top

/-- `Tor_n(M, R ⧸ (x₁, …, xₖ)) = 0` for `n > k` and a weakly regular sequence. -/
theorem a3s_isZero_tor_iterQuot (xs : List R)
    (hxs : RingTheory.Sequence.IsWeaklyRegular R xs) (M : ModuleCat.{u} R) (n : ℕ)
    (hn : xs.length < n) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj (a3c_iterQuot xs (ModuleCat.of R R))) := by
  refine a3e_isZero_tor_symm _ _ n ?_
  refine a3c_isZero_tor_iterQuot M xs (ModuleCat.of R R) 0 hxs (fun k hk => ?_) n (by omega)
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact a3c_isZero_tor_self M k

end chi

section vanishing
variable {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

/-- `Tor_i(M, N)` has finite length when the annihilators of `M` and `N` cut out only the
closed point. -/
theorem a3s_length_tor_ne_top (M N : ModuleCat.{u} B) [Module.Finite B M] [Module.Finite B N]
    (i : ℕ) (h : ∀ 𝔮 : PrimeSpectrum B, Module.annihilator B M ≤ 𝔮.asIdeal →
      Module.annihilator B N ≤ 𝔮.asIdeal → 𝔮 = closedPoint B) :
    Module.length B (((Tor (ModuleCat.{u} B) i).obj M).obj N) ≠ ⊤ := by
  have := a3e_tor_finite i M N
  refine a3e_length_ne_top_of_support _ fun 𝔮 h𝔮 => ?_
  obtain ⟨h1, h2⟩ := a3s_annihilator_le_of_mem_support_tor M N i 𝔮 h𝔮
  exact h 𝔮 h1 h2

/-- The kernel and cokernel of `y` on `Tor_i(M, N)` have finite length when the annihilators of
`M` and `N` and `y` cut out only the closed point. -/
theorem a3s_finite_tor (M N : ModuleCat.{u} B) [Module.Finite B M] [Module.Finite B N]
    (y : B) (i : ℕ) (h : ∀ 𝔮 : PrimeSpectrum B, Module.annihilator B M ≤ 𝔮.asIdeal →
      Module.annihilator B N ≤ 𝔮.asIdeal → y ∈ 𝔮.asIdeal → 𝔮 = closedPoint B) :
    Module.length B (QuotSMulTop y (((Tor (ModuleCat.{u} B) i).obj M).obj N)) ≠ ⊤ ∧
      Module.length B (a3e_kerSMul y (((Tor (ModuleCat.{u} B) i).obj M).obj N)) ≠ ⊤ := by
  have := a3e_tor_finite i M N
  refine a3e_finite_of_support y _ fun 𝔮 h𝔮 hy => ?_
  obtain ⟨h1, h2⟩ := a3s_annihilator_le_of_mem_support_tor M N i 𝔮 h𝔮
  exact h 𝔮 h1 h2 hy

omit [IsLocalRing B] [IsNoetherianRing B] in
/-- A proper specialization of a prime drops the dimension of the quotient. -/
theorem a3s_ringKrullDim_quotient_add_one_le {𝔮 𝔭 : Ideal B} [𝔮.IsPrime] (hlt : 𝔮 < 𝔭) :
    ringKrullDim (B ⧸ 𝔭) + 1 ≤ ringKrullDim (B ⧸ 𝔮) := by
  obtain ⟨y, hy𝔭, hy𝔮⟩ := IsConcreteLE.exists_of_lt hlt
  have hne : Ideal.Quotient.mk 𝔮 y ≠ 0 := fun h => hy𝔮 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hnzd : Ideal.Quotient.mk 𝔮 y ∈ nonZeroDivisors (B ⧸ 𝔮) := mem_nonZeroDivisors_of_ne_zero hne
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd)
  gcongr
  have hle : Ideal.span {Ideal.Quotient.mk 𝔮 y} ≤ 𝔭.map (Ideal.Quotient.mk 𝔮) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hy𝔭
  have e : (B ⧸ 𝔮) ⧸ 𝔭.map (Ideal.Quotient.mk 𝔮) ≃+* B ⧸ 𝔭 :=
    DoubleQuot.quotQuotEquivQuotOfLE hlt.le
  rw [← ringKrullDim_eq_of_ringEquiv e]
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)

theorem a3s_lt_of_add_one_lt {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 < (n : WithBot ℕ∞) + 1) :
    a < n := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 < (n : ℕ∞) + 1 := by exact_mod_cast h
    induction e using ENat.recTopCoe with
    | top => simp at h'
    | coe k =>
      have : k + 1 < n + 1 := by exact_mod_cast h'
      exact_mod_cast (by omega : k < n)

/-- The statement of Serre's vanishing for a weakly regular sequence of length `n`: for a finite
module `M` whose support meets `V(x₁, …, xₙ)` only at the closed point and has dimension below
`n`, `χ(M, B ⧸ (x₁, …, xₙ)) = 0`. -/
def a3s_VanishingStatement (B : Type u) [CommRing B] [IsLocalRing B] (n : ℕ) : Prop :=
  ∀ xs : List B, xs.length = n → RingTheory.Sequence.IsWeaklyRegular B xs →
    (∀ x ∈ xs, x ∈ maximalIdeal B) →
    ∀ (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M],
      (∀ 𝔮 ∈ Module.support B M, Ideal.ofList xs ≤ 𝔮.asIdeal → 𝔮 = closedPoint B) →
      (∀ 𝔮 ∈ Module.support B M, ringKrullDim (B ⧸ 𝔮.asIdeal) < n) →
      ∀ m, n ≤ m → a3s_chi m (ModuleCat.of B M) (a3c_iterQuot xs (ModuleCat.of B B)) = 0

/-- The prime filtration reduces the vanishing to the modules `B ⧸ 𝔮`. -/
theorem a3s_vanishing_of_prime (n : ℕ)
    (hprime : ∀ xs : List B, xs.length = n → RingTheory.Sequence.IsWeaklyRegular B xs →
      (∀ x ∈ xs, x ∈ maximalIdeal B) → ∀ 𝔮 : PrimeSpectrum B,
      (∀ 𝔭 : PrimeSpectrum B, 𝔮 ≤ 𝔭 → Ideal.ofList xs ≤ 𝔭.asIdeal → 𝔭 = closedPoint B) →
      ringKrullDim (B ⧸ 𝔮.asIdeal) < n → ∀ m, n ≤ m →
        a3s_chi m (ModuleCat.of B (B ⧸ 𝔮.asIdeal)) (a3c_iterQuot xs (ModuleCat.of B B)) = 0) :
    a3s_VanishingStatement B n := by
  intro xs hlen hreg hmem M _ _ hfin hsupp hdim m hm
  have : Module.Finite B (a3c_iterQuot xs (ModuleCat.of B B)) := by
    have : Module.Finite B (ModuleCat.of B B) := inferInstanceAs (Module.Finite B B)
    exact a3c_finite_iterQuot xs (ModuleCat.of B B)
  revert hsupp hdim
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime B hfin
    (motive := fun N _ _ _ => (∀ 𝔮 ∈ Module.support B N, Ideal.ofList xs ≤ 𝔮.asIdeal →
        𝔮 = closedPoint B) → (∀ 𝔮 ∈ Module.support B N, ringKrullDim (B ⧸ 𝔮.asIdeal) < n) →
      a3s_chi m (ModuleCat.of B N) (a3c_iterQuot xs (ModuleCat.of B B)) = 0) ?_ ?_ ?_
  · intro N _ _ _ _ _ _
    unfold a3s_chi
    refine Finset.sum_eq_zero fun i _ => ?_
    have : Subsingleton (ModuleCat.of B N) := inferInstanceAs (Subsingleton N)
    rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
      (a3c_isZero_tor_of_subsingleton _ _ i))]
    simp
  · intro N _ _ _ p e hs hd
    have hp : p ∈ Module.support B N := by
      rw [e.support_eq, Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
    rw [a3s_chi_congr e.toModuleIso]
    refine hprime xs hlen hreg hmem p (fun 𝔭 h𝔭 hx => hs 𝔭 (Module.mem_support_mono h𝔭 hp) hx)
      (hd p hp) m hm
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ hs hd
    have s₁ := Module.support_subset_of_injective f hf
    have s₃ := Module.support_subset_of_surjective g hg
    let S : ShortComplex (ModuleCat.{u} B) :=
      ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (by ext x; exact hfg.apply_apply_eq_zero x)
    have hS : S.ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hfg
        mono_f := (ModuleCat.mono_iff_injective _).2 hf
        epi_g := (ModuleCat.epi_iff_surjective _).2 hg }
    have hK := a3s_ofList_le_annihilator_iterQuot xs (ModuleCat.of B B)
    have fin : ∀ (X : Type u) [AddCommGroup X] [Module B X] [Module.Finite B X],
        Module.support B X ⊆ Module.support B N₂ → ∀ i,
        Module.length B (((Tor (ModuleCat.{u} B) i).obj (ModuleCat.of B X)).obj
          (a3c_iterQuot xs (ModuleCat.of B B))) ≠ ⊤ := by
      intro X _ _ _ hX i
      have : Module.Finite B (ModuleCat.of B X) := ‹Module.Finite B X›
      refine a3s_length_tor_ne_top _ _ i fun 𝔮 h1 h2 => hs 𝔮 (hX ?_) (hK.trans h2)
      exact (Module.mem_support_iff_of_finite (M := X)).2 h1
    have e := a3s_chi_ses S hS (a3c_iterQuot xs (ModuleCat.of B B)) m
      (fun i _ => fin N₁ s₁ i) (fun i _ => fin N₂ subset_rfl i) (fun i _ => fin N₃ s₃ i)
      (a3s_isZero_tor_iterQuot xs hreg _ (m + 1) (by omega))
    change a3s_chi m (ModuleCat.of B N₂) _ =
      a3s_chi m (ModuleCat.of B N₁) _ + a3s_chi m (ModuleCat.of B N₃) _ at e
    rw [e, h₁ (fun 𝔮 h => hs 𝔮 (s₁ h)) (fun 𝔮 h => hd 𝔮 (s₁ h)),
      h₃ (fun 𝔮 h => hs 𝔮 (s₃ h)) (fun 𝔮 h => hd 𝔮 (s₃ h)), add_zero]

/-- The case `B ⧸ 𝔮` of Serre's vanishing for a regular sequence `xs ++ [y]`, given the vanishing
for `xs`: if `y ∈ 𝔮`, `y` kills every `Tor_i(B ⧸ (xs), B ⧸ 𝔮)` and the Herbrand differences
vanish; otherwise both sides are the Euler characteristic of `B ⧸ (𝔮 + y)` against
`B ⧸ (xs)`. -/
theorem a3s_vanishing_prime_succ (n : ℕ) (ih : a3s_VanishingStatement B n) (xs : List B)
    (hlen : xs.length = n + 1) (hreg : RingTheory.Sequence.IsWeaklyRegular B xs)
    (hmem : ∀ x ∈ xs, x ∈ maximalIdeal B) (𝔮 : PrimeSpectrum B)
    (hs : ∀ 𝔭 : PrimeSpectrum B, 𝔮 ≤ 𝔭 → Ideal.ofList xs ≤ 𝔭.asIdeal → 𝔭 = closedPoint B)
    (hd : ringKrullDim (B ⧸ 𝔮.asIdeal) < (n + 1 : ℕ)) (m : ℕ) (hm : n + 1 ≤ m) :
    a3s_chi m (ModuleCat.of B (B ⧸ 𝔮.asIdeal)) (a3c_iterQuot xs (ModuleCat.of B B)) = 0 := by
  obtain ⟨xs', y, rfl⟩ : ∃ xs' y, xs = xs' ++ [y] := by
    rcases List.eq_nil_or_concat' xs with h | h
    · subst h; simp at hlen
    · exact h
  have hlen' : xs'.length = n := by simpa using hlen
  rw [RingTheory.Sequence.isWeaklyRegular_append_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hreg
  obtain ⟨hreg', hy⟩ := hreg
  set K' := a3c_iterQuot xs' (ModuleCat.of B B)
  have hyK : IsSMulRegular K' y :=
    ((a3c_iterQuotEquiv xs' (ModuleCat.of B B)).isSMulRegular_congr y).2 hy
  have hmem' : ∀ x ∈ xs', x ∈ maximalIdeal B := fun x hx => hmem x (by simp [hx])
  have : Module.Finite B (ModuleCat.of B B) := inferInstanceAs (Module.Finite B B)
  have : Module.Finite B K' := a3c_finite_iterQuot xs' (ModuleCat.of B B)
  set P := ModuleCat.of B (B ⧸ 𝔮.asIdeal)
  have : Module.Finite B P := inferInstanceAs (Module.Finite B (B ⧸ 𝔮.asIdeal))
  have hannP : Module.annihilator B P = 𝔮.asIdeal := Ideal.annihilator_quotient
  have hK' := a3s_ofList_le_annihilator_iterQuot xs' (ModuleCat.of B B)
  have hxs : ∀ 𝔭 : PrimeSpectrum B, Ideal.ofList xs' ≤ 𝔭.asIdeal → y ∈ 𝔭.asIdeal →
      Ideal.ofList (xs' ++ [y]) ≤ 𝔭.asIdeal := by
    intro 𝔭 h1 h2
    rw [Ideal.ofList_append, Ideal.ofList_singleton]
    exact sup_le h1 ((Ideal.span_singleton_le_iff_mem _).2 h2)
  have hcond : ∀ 𝔭 : PrimeSpectrum B, Module.annihilator B K' ≤ 𝔭.asIdeal →
      Module.annihilator B P ≤ 𝔭.asIdeal → y ∈ 𝔭.asIdeal → 𝔭 = closedPoint B := by
    intro 𝔭 h1 h2 h3
    rw [hannP] at h2
    exact hs 𝔭 h2 (hxs 𝔭 (hK'.trans h1) h3)
  rw [a3s_iterQuot_append, a3s_chi_symm]
  have htop : IsZero (((Tor (ModuleCat.{u} B) (m + 1)).obj
      (ModuleCat.of B (QuotSMulTop y K'))).obj P) := by
    refine a3e_isZero_tor_symm _ _ _ ?_
    have := a3s_isZero_tor_iterQuot (xs' ++ [y])
      ((RingTheory.Sequence.isWeaklyRegular_append_iff B xs' [y]).2
        ⟨hreg', (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ y).2 hy⟩) P (m + 1)
      (by simp; omega)
    rwa [a3s_iterQuot_append] at this
  have heuler := a3e_euler_tor K' P y hyK m (fun i _ => (a3s_finite_tor K' P y i hcond).2)
    (fun i _ => (a3s_finite_tor K' P y i hcond).1) htop
  unfold a3s_chi
  rw [heuler]
  by_cases hy𝔮 : y ∈ 𝔮.asIdeal
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [a3e_herbrand_finiteLength y _ (a3s_length_tor_ne_top K' P i fun 𝔭 h1 h2 =>
      hcond 𝔭 h1 h2 (by rw [hannP] at h2; exact h2 hy𝔮)), mul_zero]
  · have hyP : IsSMulRegular P y := by
      intro a b hab
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      change Ideal.Quotient.mk 𝔮.asIdeal (y * a) = Ideal.Quotient.mk 𝔮.asIdeal (y * b) at hab
      rw [Ideal.Quotient.eq, ← mul_sub] at hab
      rw [Ideal.Quotient.eq]
      exact (𝔮.isPrime.mem_or_mem hab).resolve_left hy𝔮
    have hcond' : ∀ 𝔭 : PrimeSpectrum B, Module.annihilator B P ≤ 𝔭.asIdeal →
        Module.annihilator B K' ≤ 𝔭.asIdeal → y ∈ 𝔭.asIdeal → 𝔭 = closedPoint B :=
      fun 𝔭 h1 h2 h3 => hcond 𝔭 h2 h1 h3
    have htop' : IsZero (((Tor (ModuleCat.{u} B) (m + 1)).obj
        (ModuleCat.of B (QuotSMulTop y P))).obj K') :=
      a3s_isZero_tor_iterQuot xs' hreg' _ (m + 1) (by omega)
    have heuler' := a3e_euler_tor P K' y hyP m (fun i _ => (a3s_finite_tor P K' y i hcond').2)
      (fun i _ => (a3s_finite_tor P K' y i hcond').1) htop'
    have hsymm : ∀ i, a3e_herbrand y (((Tor (ModuleCat.{u} B) i).obj K').obj P) =
        a3e_herbrand y (((Tor (ModuleCat.{u} B) i).obj P).obj K') := fun i =>
      let ⟨e⟩ := a3c_tor_symm P i K'
      a3e_herbrand_congr y e.toLinearEquiv
    simp only [hsymm]
    rw [← heuler']
    have hsupp : ∀ 𝔭 ∈ Module.support B (QuotSMulTop y (B ⧸ 𝔮.asIdeal)),
        𝔮 ≤ 𝔭 ∧ y ∈ 𝔭.asIdeal := by
      intro 𝔭 h𝔭
      rw [Module.support_quotSMulTop] at h𝔭
      obtain ⟨h1, h2⟩ := h𝔭
      rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] at h1
      exact ⟨h1, by simpa using h2⟩
    exact ih xs' hlen' hreg' hmem' (QuotSMulTop y (B ⧸ 𝔮.asIdeal))
      (fun 𝔭 h𝔭 hx => hs 𝔭 (hsupp 𝔭 h𝔭).1 (hxs 𝔭 hx (hsupp 𝔭 h𝔭).2))
      (fun 𝔭 h𝔭 => by
        have hlt : 𝔮.asIdeal < 𝔭.asIdeal :=
          lt_of_le_of_ne (hsupp 𝔭 h𝔭).1 fun h => hy𝔮 (h ▸ (hsupp 𝔭 h𝔭).2)
        have h1 := a3s_ringKrullDim_quotient_add_one_le hlt
        have h2 : ringKrullDim (B ⧸ 𝔭.asIdeal) + 1 < (n : WithBot ℕ∞) + 1 :=
          lt_of_le_of_lt h1 (by exact_mod_cast hd)
        exact a3s_lt_of_add_one_lt h2)
      m (by omega)

/-- Serre's vanishing theorem for a weakly regular sequence `x₁, …, xₙ` in the maximal ideal of a
Noetherian local ring: if the support of a finite module `M` meets `V(x)` only at the closed point
and has dimension below `n`, then `Σ_{i ≤ m} (-1)^i ℓ Tor_i(M, B ⧸ (x)) = 0` for `m ≥ n`.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre IV, A, Théorème 1 and Appendice II (the
Euler characteristic `χ(x, M)` of the Koszul complex vanishes when `dim M < n`), and
Chapitre V, B.3 (reduction to the diagonal). -/
theorem a3s_vanishing (n : ℕ) : a3s_VanishingStatement B n := by
  induction n with
  | zero =>
    refine a3s_vanishing_of_prime 0 fun xs _ _ _ 𝔮 _ hd _ _ => ?_
    have : Nontrivial (B ⧸ 𝔮.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr 𝔮.isPrime.ne_top
    exact absurd hd (not_lt.mpr (by exact_mod_cast ringKrullDim_nonneg_of_nontrivial))
  | succ n ih =>
    exact a3s_vanishing_of_prime (n + 1) fun xs hlen hreg hmem 𝔮 hs hd m hm =>
      a3s_vanishing_prime_succ n ih xs hlen hreg hmem 𝔮 hs hd m hm

end vanishing

end HodgeLean.Adapters
