import HodgeLean.Adapters.IntersectionProductHerbrandDim
import HodgeLean.Adapters.IntersectionProductTorDim

/-! # Serre's multiplicity of a principal divisor against a subvariety: the local identity

Let `A` be a regular local ring of dimension at most `d`, `𝔭_W`, `𝔭_V` ideals with `𝔭_W` prime,
and `a ∉ 𝔭_W`. Suppose the primes containing `𝔭_W + 𝔭_V` are the maximal ideal and a finite set
`Φ` of primes of dimension one, none containing `a` (the components through the point of a
proper intersection `W ∩ V`, none of them inside `div a`). Then
`Σ_i (-1)^i ℓ Tor_i(A ⧸ (𝔭_W + a), A ⧸ 𝔭_V) =`
`Σ_{Z ∈ Φ} (Σ_i (-1)^i ℓ_{A_Z} Tor_i(A ⧸ 𝔭_W, A ⧸ 𝔭_V)_Z) · e_a(A ⧸ Z)`
(`a3e_principal_local`): the multiplicity of `div a|_W` against `V` at the point is the sum over
the components `Z` of `W ∩ V` of the local multiplicity along `Z` times the order of `a` on the
curve `Z`. The inputs are the Euler characteristic along a nonzerodivisor (`a3e_euler_tor`), the
vanishing of `Tor` above the dimension (`a3e_isZero_tor_regular`), and the decomposition of
Herbrand differences in dimension one (`a3e_herbrand_eq_sum`).

Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.2 and C (the proof of
`i(Z; V · W) = Σ ...` for a divisor), Chapitre IV, Théorème 9; Fulton, *Intersection Theory*,
second edition, Proposition 2.3 and Example 7.1.10, Lemma A.2.2.
HC no distance; AV milestone no distance.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory IsLocalRing

noncomputable section
namespace HodgeLean.Adapters
universe u

section finite
variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- `Tor` of finitely generated modules over a Noetherian ring is finitely generated: by
induction, `Tor_{n+1}(M, N)` embeds in `Tor_n(K, N)` for a syzygy `0 → K → F → M → 0`.
Source: Weibel, *An Introduction to Homological Algebra*, §2.4 and Exercise 3.3.1 (finitely
generated resolutions over a Noetherian ring). -/
theorem a3e_tor_finite (n : ℕ) :
    ∀ (M N : ModuleCat.{u} A) [Module.Finite A M] [Module.Finite A N],
      Module.Finite A (((Tor (ModuleCat.{u} A) n).obj M).obj N) := by
  induction n with
  | zero =>
    intro M N _ _
    have : Module.Finite A (M ⊗ N : ModuleCat.{u} A) :=
      inferInstanceAs (Module.Finite A (TensorProduct A M N))
    exact Module.Finite.equiv (a3c_tor0Iso M N).toLinearEquiv.symm
  | succ n ih =>
    intro M N _ _
    obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' A M
    let S := a3e_kerSES f
    have hS : S.ShortExact := a3e_kerSES_shortExact f hf
    have : Module.Projective A (Fin m → A) := Module.Projective.of_free
    have : Projective S.X₂ := (IsProjective.iff_projective (R := A) S.X₂).1 this
    have : Module.Flat A S.X₂ := a3c_flat_of_projective S.X₂
    have : Module.Finite A (LinearMap.ker f) := Module.Finite.of_injective
      (LinearMap.ker f).subtype Subtype.val_injective
    have : Module.Finite A S.X₁ := this
    let Q := ProjectiveResolution.of N
    have hT := a3c_sesC_shortExact S hS Q.complex Q.projective
    have hz : IsZero ((a3c_tensC S.X₂ Q.complex).homology (n + 1)) :=
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
        (a3c_exactAt_tensC S.X₂ _ n (Q.complex_exactAt_succ n))
    have hm := hT.mono_δ (n + 1) n (by simp) hz
    have := ih S.X₁ N
    have : Module.Finite A ((a3c_tensC S.X₁ Q.complex).homology n) :=
      Module.Finite.equiv (a3c_torIso S.X₁ N Q n).toLinearEquiv
    have : Module.Finite A ((a3c_sesC S Q.complex).X₁.homology n) := this
    have : IsNoetherian A ((a3c_sesC S Q.complex).X₁.homology n) :=
      isNoetherian_of_isNoetherianRing_of_finite A _
    have hinj : Function.Injective (hT.δ (n + 1) n (by simp)).hom :=
      (ModuleCat.mono_iff_injective _).mp hm
    have : Module.Finite A ((a3c_tensC S.X₃ Q.complex).homology (n + 1)) :=
      Module.Finite.of_injective _ hinj
    exact Module.Finite.equiv (a3c_torIso S.X₃ N Q (n + 1)).toLinearEquiv.symm

end finite

section principal
variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- The local identity for the intersection of `div a|_W` with `V`.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.2 and C; Fulton, *Intersection
Theory*, second edition, Proposition 2.3, Example 7.1.10 and Lemma A.2.2. -/
theorem a3e_principal_local (P Q : Ideal A) [P.IsPrime] (a : A) (ha : a ∉ P) (d : ℕ)
    (hd : ringKrullDim A ≤ d) (Φ : Finset (PrimeSpectrum A))
    (hΦm : ∀ Z ∈ Φ, Z ≠ closedPoint A)
    (hΦdim : ∀ Z ∈ Φ, ∀ 𝔮 : PrimeSpectrum A, Z < 𝔮 → 𝔮 = closedPoint A)
    (hΦa : ∀ Z ∈ Φ, a ∉ Z.asIdeal)
    (hPQ : ∀ 𝔮 : PrimeSpectrum A, P ≤ 𝔮.asIdeal → Q ≤ 𝔮.asIdeal → 𝔮 = closedPoint A ∨ 𝔮 ∈ Φ) :
    ∑ i ∈ Finset.range (d + 1), (-1 : ℤ) ^ i *
        ((Module.length A (((Tor (ModuleCat.{u} A) i).obj
          (ModuleCat.of A (QuotSMulTop a (A ⧸ P)))).obj (ModuleCat.of A (A ⧸ Q)))).toNat : ℤ) =
      ∑ Z ∈ Φ, (∑ i ∈ Finset.range (d + 1), (-1 : ℤ) ^ i *
        ((a3e_locLen Z (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ P))).obj
          (ModuleCat.of A (A ⧸ Q)))).toNat : ℤ)) * a3e_herbrand a (A ⧸ Z.asIdeal) := by
  let M := ModuleCat.of A (A ⧸ P)
  let N := ModuleCat.of A (A ⧸ Q)
  have hr : IsSMulRegular M a := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk P (a * x) = Ideal.Quotient.mk P (a * y) at hxy
    rw [Ideal.Quotient.eq, ← mul_sub] at hxy
    rw [Ideal.Quotient.eq]
    exact (‹P.IsPrime›.mem_or_mem hxy).resolve_left ha
  have htop : IsZero (((Tor (ModuleCat.{u} A) (d + 1)).obj
      (ModuleCat.of A (QuotSMulTop a M))).obj N) :=
    a3e_isZero_tor_regular _ N (d + 1) (lt_of_le_of_lt hd (by exact_mod_cast Nat.lt_succ_self d))
  have hsupp : ∀ i, Module.support A (((Tor (ModuleCat.{u} A) i).obj M).obj N) ⊆
      insert (closedPoint A) (Φ : Set (PrimeSpectrum A)) := by
    intro i 𝔮 h𝔮
    have hann := Module.annihilator_le_of_mem_support h𝔮
    have hP : P ≤ 𝔮.asIdeal := fun p hp => hann (Module.mem_annihilator.mpr fun t =>
      a3c_smul_tor_eq_zero_of_mem_annihilator_left M N p (Module.mem_annihilator.mpr fun x => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        change Ideal.Quotient.mk P (p * x) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact P.mul_mem_right x hp) i t)
    have hQ : Q ≤ 𝔮.asIdeal := fun q hq => hann (Module.mem_annihilator.mpr fun t =>
      a3c_smul_tor_eq_zero_of_mem_annihilator_right M N q (Module.mem_annihilator.mpr fun x => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        change Ideal.Quotient.mk Q (q * x) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Q.mul_mem_right x hq) i t)
    exact hPQ 𝔮 hP hQ
  have hfin : ∀ i, Module.Finite A (((Tor (ModuleCat.{u} A) i).obj M).obj N) := fun i =>
    a3e_tor_finite i M N
  have hcond := fun i => a3e_support_condition a Φ hΦa (hsupp i)
  have heuler := a3e_euler_tor M N a hr d
    (fun i _ => (a3e_finite_of_support a _ (hcond i)).2)
    (fun i _ => (a3e_finite_of_support a _ (hcond i)).1) htop
  change _ = _ at heuler
  rw [heuler]
  have hdec : ∀ i, a3e_herbrand a (((Tor (ModuleCat.{u} A) i).obj M).obj N) =
      ∑ Z ∈ Φ, ((a3e_locLen Z (((Tor (ModuleCat.{u} A) i).obj M).obj N)).toNat : ℤ) *
        a3e_herbrand a (A ⧸ Z.asIdeal) := fun i =>
    (a3e_herbrand_eq_sum a Φ hΦm hΦdim hΦa _ (hsupp i)).1
  simp only [hdec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Z _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end principal

end HodgeLean.Adapters
