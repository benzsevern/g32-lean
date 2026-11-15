import HodgeLean.Adapters.NormalConeB4aGysinBridge2FreeTransport
import HodgeLean.Adapters.NormalConeB4aGysinBridge2LocalLength
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Noetherian.Nilpotent

/-! # Reformulated bridge of A3-B4a: exact slice lengths near a generic point

For a minimal prime `P` of a Noetherian ring `S` there is `g ∉ P` such that at every prime `Q`
with `g ∉ Q`, every list of `dim S_Q` elements generating the maximal ideal of `S_Q` together
with the nilradical has slice length equal to the length of the Artinian ring `S_P`.
Source: Fulton, *Intersection Theory*, Lemma A.2 and Example 7.1.10; Matsumura, *Commutative Ring
Theory*, Theorem 4.10 and Theorem 17.4. -/

noncomputable section
namespace HodgeLean.Adapters
open IsLocalRing RingTheory.Sequence

universe u

/-- The Krull dimension is unchanged modulo an ideal of nilpotents. -/
theorem a3b4g_ringKrullDim_quotient_of_le_nilradical {A : Type*} [CommRing A] (I : Ideal A)
    (hI : I ≤ nilradical A) : ringKrullDim (A ⧸ I) = ringKrullDim A := by
  have hz : PrimeSpectrum.zeroLocus (I : Set A) = Set.univ :=
    Set.eq_univ_of_forall fun p => hI.trans (nilradical_le_prime p.asIdeal)
  rw [ringKrullDim_quotient, hz, Order.krullDim_eq_of_orderIso (OrderIso.Set.univ)]
  rfl

/-- For a minimal prime `P` of a Noetherian ring there is an element outside `P` lying in every
other minimal prime. -/
theorem a3b4g_exists_mem_other_minimalPrimes {S : Type*} [CommRing S] [IsNoetherianRing S]
    (P : Ideal S) (hP : P ∈ minimalPrimes S) :
    ∃ a : S, a ∉ P ∧ ∀ P' ∈ minimalPrimes S, P' ≠ P → a ∈ P' := by
  classical
  have hPp : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  let F := (minimalPrimes.finite_of_isNoetherianRing S).toFinset.erase P
  have hx : ∀ P' ∈ F, ∃ x, x ∈ P' ∧ x ∉ P := by
    intro P' hP'
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hP'
    have hP'min : P' ∈ minimalPrimes S := (Set.Finite.mem_toFinset _).mp hmem
    by_contra h
    push_neg at h
    exact hne (le_antisymm h (hP.2 ⟨Ideal.minimalPrimes_isPrime hP'min, bot_le⟩ h))
  choose! x hxP' hxP using hx
  refine ⟨∏ P' ∈ F, x P', ?_, ?_⟩
  · intro h
    obtain ⟨P', hP', hmem⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hxP P' hP' hmem
  · intro P' hP' hne
    have hF : P' ∈ F := Finset.mem_erase.mpr ⟨hne, (Set.Finite.mem_toFinset _).mpr hP'⟩
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem x hF) (hxP' P' hF)

/-- Near a minimal prime `P` of a Noetherian ring, every slice by `dim` many elements generating
the maximal ideal together with the nilradical has length equal to the length of `S_P`.
Source: Fulton, *Intersection Theory*, Lemma A.2; Matsumura, *Commutative Ring Theory*,
Theorem 4.10 and Theorem 17.4. -/
theorem a3b4g_exists_basicOpen_slice_length {S : Type*} [CommRing S] [IsNoetherianRing S]
    (P : Ideal S) [P.IsPrime] (hP : P ∈ minimalPrimes S) :
    ∃ g : S, g ∉ P ∧
      (∀ (Q : Ideal S) [Q.IsPrime], g ∉ Q → ∀ P' ∈ minimalPrimes S, P' ≤ Q → P' = P) ∧
      ∃ m : ℕ,
      (∀ (A₀ : Type u) [CommRing A₀] [Algebra S A₀] [IsLocalization.AtPrime A₀ P],
        Module.length A₀ A₀ = m) ∧
      ∀ (Q : Ideal S) [Q.IsPrime] (A : Type u) [CommRing A] [IsLocalRing A] [Algebra S A]
        [IsLocalization.AtPrime A Q], g ∉ Q → ∀ rs : List A, ringKrullDim A = rs.length →
        Ideal.ofList rs ⊔ nilradical A = maximalIdeal A →
        Module.length A (A ⧸ Ideal.ofList rs) = m := by
  classical
  obtain ⟨a, haP, ha⟩ := a3b4g_exists_mem_other_minimalPrimes P hP
  obtain ⟨N, hN⟩ := IsNoetherianRing.isNilpotent_nilradical S
  have haP' : Ideal.span {a} * P ≤ nilradical S := by
    rw [Ideal.mul_le]
    intro y hy x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [nilradical, ← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro P' hP'
    by_cases h : P' = P
    · subst h
      exact Ideal.mul_mem_left _ _ hx
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (ha P' hP' h))
  have hpow : ∀ x ∈ P ^ N, a ^ N * x = 0 := by
    intro x hx
    have hle : (Ideal.span {a} * P) ^ N ≤ ⊥ := by
      rw [← Ideal.zero_eq_bot, ← hN]
      exact Ideal.pow_right_mono haP' N
    rw [mul_pow, Ideal.span_singleton_pow] at hle
    exact hle (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hx)
  let M : ℕ → Type _ := fun k => a3b4g_gradedPiece (fun j => ((P ^ j : Ideal S) : Submodule S S)) k
  have htor : ∀ k, Module.IsTorsionBySet S (M k) (P : Set S) := by
    intro k x y
    induction x using Submodule.Quotient.induction_on with
    | _ z =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      change (y : S) * (z : S) ∈ P ^ (k + 1)
      rw [pow_succ']
      exact Ideal.mul_mem_mul y.2 z.2
  choose r hrP n hfree using fun k => a3b4g_free_atPrime_of_torsion P (M k) (htor k)
  let g := a * ∏ k ∈ Finset.range N, r k
  have hgP : g ∉ P := by
    intro h
    rcases (Ideal.IsPrime.mem_or_mem ‹P.IsPrime› h) with h | h
    · exact haP h
    · obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hrP k hk
  have hPQ_of : ∀ (Q : Ideal S) [Q.IsPrime], g ∉ Q → P ≤ Q := by
    intro Q _ hgQ
    have haQ : a ∉ Q := fun h => hgQ (Ideal.mul_mem_right _ _ h)
    obtain ⟨P', hP', hP'Q⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal S) ≤ Q)
    by_cases h : P' = P
    · exact h ▸ hP'Q
    · exact absurd (hP'Q (ha P' hP' h)) haQ
  have hIN_of : ∀ (Q : Ideal S) [Q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
      [IsLocalization.AtPrime A Q], g ∉ Q → (P.map (algebraMap S A)) ^ N = ⊥ := by
    intro Q _ A _ _ _ hgQ
    have haQ : a ∉ Q := fun h => hgQ (Ideal.mul_mem_right _ _ h)
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker]
    have hu : IsUnit (algebraMap S A (a ^ N)) :=
      IsLocalization.map_units A (⟨a ^ N, fun h => haQ (‹Q.IsPrime›.mem_of_pow_mem N h)⟩ :
        Q.primeCompl)
    have h0 : algebraMap S A (a ^ N * x) = 0 := by
      rw [hpow x hx, map_zero]
    rw [map_mul] at h0
    exact (hu.mul_right_eq_zero).mp h0
  have key : ∀ (Q : Ideal S) [Q.IsPrime] (A : Type u) [CommRing A] [IsLocalRing A] [Algebra S A]
      [IsLocalization.AtPrime A Q], g ∉ Q → ∀ rs : List A,
      IsWeaklyRegular (A ⧸ P.map (algebraMap S A)) rs →
      Ideal.ofList rs ⊔ P.map (algebraMap S A) = maximalIdeal A →
      Module.length A (A ⧸ Ideal.ofList rs) = ((∑ k ∈ Finset.range N, n k : ℕ) : ℕ∞) := by
    intro Q _ A _ _ _ _ hgQ rs hreg hgen
    have hrQ : ∀ k < N, r k ∉ Q := fun k hk h => hgQ (Ideal.mul_mem_left _ _
      (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem r (Finset.mem_range.mpr hk)) h))
    have hPQ := hPQ_of Q hgQ
    set I := P.map (algebraMap S A) with hI
    have hIN : I ^ N = ⊥ := hIN_of Q A hgQ
    have e : ∀ k < N, a3b4g_gradedPiece (fun j => ((I ^ j : Ideal _) : Submodule _ _)) k ≃ₗ[A]
        (Fin (n k) → A ⧸ I) := by
      intro k hk
      let φ := a3b4g_gradedLocalizationMap (T := S) (T' := A) (P ^ k)
        (P ^ (k + 1)) (I ^ k) (I ^ (k + 1)) (Ideal.map_pow _ _ _).symm (Ideal.map_pow _ _ _).symm
      have hφ : IsLocalizedModule Q.primeCompl φ :=
        a3b4g_gradedLocalizationMap_isLocalizedModule Q.primeCompl _ _ _ _ _ _
      exact (hfree k Q A hPQ (hrQ k hk) _ φ hφ).some
    rw [a3b4g_local_length A I N hIN n e rs hreg hgen, Nat.cast_sum]
  refine ⟨g, hgP, ?_, ∑ k ∈ Finset.range N, n k, ?_, ?_⟩
  · intro Q _ hgQ P' hP' hP'Q
    by_contra h
    exact hgQ (Ideal.mul_mem_right _ _ (hP'Q (ha P' hP' h)))
  · intro A₀ _ _ _
    haveI : IsLocalRing A₀ := IsLocalization.AtPrime.isLocalRing A₀ P
    have h := key P A₀ hgP [] (IsWeaklyRegular.nil _ _) (by
      rw [Ideal.ofList_nil, bot_sup_eq]
      exact IsLocalization.AtPrime.map_eq_maximalIdeal P A₀)
    rw [← h]
    exact ((Submodule.quotEquivOfEqBot _ Ideal.ofList_nil).length_eq).symm
  · intro Q _ A _ _ _ _ hgQ rs hdim hgen
    haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing Q.primeCompl A inferInstance
    have hPQ := hPQ_of Q hgQ
    set I := P.map (algebraMap S A) with hI
    have hIN : I ^ N = ⊥ := hIN_of Q A hgQ
    have hIprime : I.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl _ P
      ‹_› (by
        rw [Set.disjoint_left]
        intro x hx hxP
        exact hx (hPQ hxP))
    have hnil : nilradical A = I := by
      refine le_antisymm (nilradical_le_prime I) ?_
      intro x hx
      refine ⟨N, ?_⟩
      have := Ideal.pow_mem_pow hx N
      rw [hIN] at this
      exact this
    rw [hnil] at hgen
    haveI : Nontrivial (A ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr hIprime.ne_top
    haveI : IsLocalRing (A ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hdim' : ringKrullDim (A ⧸ I) = rs.length := by
      rw [a3b4g_ringKrullDim_quotient_of_le_nilradical I hnil.ge, hdim]
    haveI : IsRegularLocalRing (A ⧸ I) := by
      apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
      have hm : maximalIdeal (A ⧸ I) =
          Ideal.ofList (rs.map (Ideal.Quotient.mk I)) := by
        rw [← Ideal.map_ofList, ← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
          Ideal.Quotient.mk_surjective, ← hgen, Ideal.map_sup, Ideal.map_quotient_self,
          sup_bot_eq]
      rw [hm, hdim']
      have h1 := Submodule.spanFinrank_span_le_ncard_of_finite
        (R := A ⧸ I) (List.finite_toSet (rs.map (Ideal.Quotient.mk I)))
      have h2 : {x | x ∈ rs.map (Ideal.Quotient.mk I)}.ncard ≤ rs.length := by
        have : {x | x ∈ rs.map (Ideal.Quotient.mk I)} =
            ((rs.map (Ideal.Quotient.mk I)).toFinset : Set _) := by ext; simp
        rw [this, Set.ncard_coe_finset]
        exact (List.toFinset_card_le _).trans (by simp)
      exact_mod_cast h1.trans h2
    have hreg := a3b4g_isWeaklyRegular_quotient A I rs.length hdim' rs rfl hgen
    exact key Q A hgQ rs hreg hgen

end HodgeLean.Adapters
