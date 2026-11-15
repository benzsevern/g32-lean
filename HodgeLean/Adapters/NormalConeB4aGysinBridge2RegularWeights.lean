import HodgeLean.Adapters.NormalConeB4aGysinBridge2Weights

/-! # Reformulated bridge of A3-B4a: regular generic slices

Near a generic point, every list of `dim 𝒪_w` elements generating the maximal ideal of `𝒪_w`
together with the nilradical is weakly regular on `𝒪_w`, in addition to having the generic slice
length; away from a closed set containing no generic point, the slice sequence of the shifted
sections is therefore weakly regular and its exact length is the multiplicity of the cycle.
Source: Bruns–Herzog, *Cohen–Macaulay Rings*, Proposition 1.1.4; Fulton, *Intersection Theory*,
Lemma A.2 and Example 7.1.10; Matsumura, *Commutative Ring Theory*, Theorem 17.4. -/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry IsLocalRing RingTheory.Sequence

universe u

/-- A sequence weakly regular on `A ⧸ I`, for a nilpotent ideal `I` with free graded pieces, is
weakly regular on `A`. -/
theorem a3b4g_isWeaklyRegular_of_free_graded {A : Type*} [CommRing A] (I : Ideal A) (N : ℕ)
    (hN : I ^ N = ⊥) (r : ℕ → ℕ)
    (e : ∀ k < N, a3b4g_gradedPiece (fun k => ((I ^ k : Ideal A) : Submodule A A)) k ≃ₗ[A]
      (Fin (r k) → A ⧸ I))
    (rs : List A) (hreg : IsWeaklyRegular (A ⧸ I) rs) : IsWeaklyRegular A rs := by
  have hF : Antitone (fun k => (I ^ k : Submodule A A)) := fun _ _ h => Ideal.pow_le_pow_right h
  obtain ⟨h0, -⟩ := a3b4g_length_quot_of_filtration (fun k => (I ^ k : Submodule A A)) hF N hN
    rs (fun k hk => ((e k hk).isWeaklyRegular_congr rs).mpr
      (a3b4g_pi_length_quot (A ⧸ I) rs hreg (r k)).1)
  have e0 : ↥((I ^ 0 : Ideal A) : Submodule A A) ≃ₗ[A] A :=
    LinearEquiv.ofEq _ ⊤ (by rw [pow_zero, Ideal.one_eq_top]) ≪≫ₗ Submodule.topEquiv
  exact (e0.isWeaklyRegular_congr rs).mp h0

theorem a3b4g_exists_basicOpen_slice_regular {S : Type*} [CommRing S] [IsNoetherianRing S]
    (P : Ideal S) [P.IsPrime] (hP : P ∈ minimalPrimes S) :
    ∃ g : S, g ∉ P ∧
      (∀ (Q : Ideal S) [Q.IsPrime], g ∉ Q → ∀ P' ∈ minimalPrimes S, P' ≤ Q → P' = P) ∧
      ∃ m : ℕ,
      (∀ (A₀ : Type u) [CommRing A₀] [Algebra S A₀] [IsLocalization.AtPrime A₀ P],
        Module.length A₀ A₀ = m) ∧
      ∀ (Q : Ideal S) [Q.IsPrime] (A : Type u) [CommRing A] [IsLocalRing A] [Algebra S A]
        [IsLocalization.AtPrime A Q], g ∉ Q → ∀ rs : List A, ringKrullDim A = rs.length →
        Ideal.ofList rs ⊔ nilradical A = maximalIdeal A →
        Module.length A (A ⧸ Ideal.ofList rs) = m ∧ IsWeaklyRegular A rs := by
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
      Module.length A (A ⧸ Ideal.ofList rs) = ((∑ k ∈ Finset.range N, n k : ℕ) : ℕ∞) ∧
        IsWeaklyRegular A rs := by
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
    refine ⟨?_, a3b4g_isWeaklyRegular_of_free_graded I N hIN n e rs hreg⟩
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
    rw [← h.1]
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

/-- A generic point of a locally Noetherian scheme has a neighbourhood on which every slice of
`dim 𝒪_w` elements generating the maximal ideal modulo the nilradical has the generic length and is weakly regular.
Source: Fulton, *Intersection Theory*, Lemma A.2. -/
theorem a3b4g_exists_good_open_regular {K : Scheme.{0}} [IsLocallyNoetherian K] (η : K)
    (hη : η ∈ genericPoints K) :
    ∃ W : K.Opens, η ∈ W ∧ ∃ m : ℕ,
      Module.length (K.presheaf.stalk η) (K.presheaf.stalk η) = m ∧
      ∀ w ∈ W, ∀ rs : List (K.presheaf.stalk w), ringKrullDim (K.presheaf.stalk w) = rs.length →
        Ideal.ofList rs ⊔ nilradical (K.presheaf.stalk w) = maximalIdeal (K.presheaf.stalk w) →
        Module.length (K.presheaf.stalk w) (K.presheaf.stalk w ⧸ Ideal.ofList rs) = m ∧
          IsWeaklyRegular (K.presheaf.stalk w) rs := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ :=
    K.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  haveI : IsNoetherianRing Γ(K, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  set P := (hV.primeIdealOf ⟨η, hηV⟩).asIdeal with hPdef
  letI := K.presheaf.algebra_section_stalk ⟨η, hηV⟩
  haveI hlocη : IsLocalization.AtPrime (K.presheaf.stalk η) P := hV.isLocalization_stalk ⟨η, hηV⟩
  have hP : P ∈ minimalPrimes Γ(K, V) := by
    rw [← Ideal.height_eq_zero_iff]
    have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height P (K.presheaf.stalk η)
    rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr
      (a3b4g_isMax_of_mem_genericPoints η hη)] at h1
    exact_mod_cast h1.symm
  obtain ⟨g, hgP, -, m, hlen0, hslice⟩ := a3b4g_exists_basicOpen_slice_regular P hP
  refine ⟨K.basicOpen g, ?_, m, hlen0 (K.presheaf.stalk η), ?_⟩
  · rw [Scheme.mem_basicOpen K g η hηV]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (K.presheaf.stalk η) P g).mpr hgP
  · intro w hw rs hdim hgen
    have hwV : w ∈ V := K.basicOpen_le g hw
    letI := K.presheaf.algebra_section_stalk ⟨w, hwV⟩
    haveI : IsLocalization.AtPrime (K.presheaf.stalk w) (hV.primeIdealOf ⟨w, hwV⟩).asIdeal :=
      hV.isLocalization_stalk ⟨w, hwV⟩
    have hgQ : g ∉ (hV.primeIdealOf ⟨w, hwV⟩).asIdeal := by
      have hu := (Scheme.mem_basicOpen K g w hwV).mp hw
      exact (IsLocalization.AtPrime.isUnit_to_map_iff (K.presheaf.stalk w) _ g).mp hu
    exact hslice _ (K.presheaf.stalk w) hgQ rs hdim hgen

/-- Generic component weights: away from a closed set containing no generic point, exact slice
lengths of `dim 𝒪_{K,w}` elements generating the maximal ideal modulo the nilradical are the
multiplicities of the cycle of `K`, and the slice sequences are weakly regular. Source: Fulton, *Intersection Theory*, Lemma A.2 and
Example 7.1.10. -/
theorem a3b4g_generic_component_weights_regular
    {Z K : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)} [IsNoetherian Z]
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (i : K ⟶ Z) (hi : IsClosedImmersion i) :
    ∃ B : Set K, IsClosed B ∧ (∀ x ∈ B, closure {x} ∉ irreducibleComponents K) ∧
      ∀ w : ComplexPoint (Over.mk (i ≫ q)), w.underlying ∉ B →
      ∀ (U : Z.Opens) {n : ℕ} (g : Fin n → Γ(Z, U)) (a : Fin n → ℂ)
        (hw : i.base w.underlying ∈ U),
        ringKrullDim (K.presheaf.stalk w.underlying) = n →
        a3b4g_sliceIdeal q i U g a w.underlying hw ⊔ nilradical (K.presheaf.stalk w.underlying) =
          IsLocalRing.maximalIdeal (K.presheaf.stalk w.underlying) →
        IsWeaklyRegular (K.presheaf.stalk w.underlying)
          (a3b4a_gysin_sliceSequence q i U g a w.underlying hw) ∧
        ∃ k : ℕ, a3b4a_gysin_sliceLength q i U g a w = k ∧
          a3b4_multiplicity q (a3b3_imageCycle i inferInstance) (a3b4_anMap (q := i ≫ q) (q' := q)
            i rfl w) = k := by
  classical
  haveI : IsClosedImmersion i := hi
  haveI : IsLocallyNoetherian K := LocallyOfFiniteType.isLocallyNoetherian i
  haveI : CompactSpace K := (quasiCompact_iff_compactSpace i).1 inferInstance
  haveI : IsNoetherian K := {}
  have hfin : (genericPoints K).Finite := by
    refine Set.Finite.preimage ?_ (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents)
    intro x _ y _ hxy
    exact (inseparable_iff_closure_eq.mpr hxy).eq
  choose! W hηW m hm hsl using fun η (hη : η ∈ genericPoints K) =>
    a3b4g_exists_good_open_regular η hη
  let W' : K → Set K := fun η =>
    (W η : Set K) ∩ ⋂ η' ∈ genericPoints K \ {η}, (closure ({η'} : Set K))ᶜ
  have hW' : ∀ η, IsOpen (W' η) := fun η =>
    (W η).2.inter ((hfin.diff).isOpen_biInter fun _ _ => isClosed_closure.isOpen_compl)
  have hηW' : ∀ η ∈ genericPoints K, η ∈ W' η := by
    intro η hη
    refine ⟨hηW η hη, Set.mem_iInter₂.mpr fun η' hη' => ?_⟩
    exact a3b4g_not_mem_closure_of_genericPoints hη hη'.2
  refine ⟨(⋃ η ∈ genericPoints K, W' η)ᶜ, (isOpen_biUnion fun η _ => hW' η).isClosed_compl,
    ?_, ?_⟩
  · intro x hx hcomp
    exact hx (Set.mem_iUnion₂.mpr ⟨x, hcomp, hηW' x hcomp⟩)
  · intro w hwB U n g a hw hdim hgen
    obtain ⟨η, hη, hwW⟩ := Set.mem_iUnion₂.mp (not_not.mp hwB)
    let rs := a3b4a_gysin_sliceSequence q i U g a w.underlying hw
    have hlen : rs.length = n := List.length_ofFn
    have hL := hsl η hη w.underlying hwW.1 rs (by rw [hdim, hlen]) hgen
    have hwη : w.underlying ∈ closure ({η} : Set K) := by
      obtain ⟨ζ, hζ, hwζ⟩ := a3b4g_exists_genericPoint_specializes w.underlying
      by_cases h : ζ = η
      · exact h ▸ hwζ
      · exact absurd hwζ (Set.mem_iInter₂.mp hwW.2 ζ ⟨hζ, h⟩)
    refine ⟨hL.2, m η, ?_, ?_⟩
    · simp only [a3b4a_gysin_sliceLength, hw, ↓reduceDIte]
      exact hL.1
    · have hx : (a3b4_anMap (q := i ≫ q) (q' := q) i rfl w).underlying ∈
          closure ({i η} : Set Z) := by
        change i.base w.underlying ∈ _
        exact specializes_iff_mem_closure.mp
          ((specializes_iff_mem_closure.mpr hwη).map i.continuous)
      have hother : ∀ ξ ∈ (a3b3_imageCycle i inferInstance).support, ξ ≠ i η →
          (a3b4_anMap (q := i ≫ q) (q' := q) i rfl w).underlying ∉ closure ({ξ} : Set Z) := by
        intro ξ hξ hne
        rw [a3b3_imageCycle, a3b4a_gysin_idealCycle_support] at hξ
        obtain ⟨y', hy', rfl⟩ := hξ
        let y := (Scheme.homeoOfIso (asIso i.toImage)).symm y'
        have hyy : i.toImage y = y' := (Scheme.homeoOfIso (asIso i.toImage)).apply_symm_apply y'
        have hpt : i.ker.subschemeι y' = i y := by
          rw [← hyy, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
        have hyg : y ∈ genericPoints K := by
          rw [← a3b2_homeomorph_mem_genericPoints (Scheme.homeoOfIso (asIso i.toImage)) y]
          change i.toImage y ∈ _
          rw [hyy]
          exact hy'
        have hyη : y ≠ η := by
          rintro rfl
          exact hne hpt
        rw [hpt]
        change i.base w.underlying ∉ _
        intro hcl
        have hsp : i y ⤳ i w.underlying := specializes_iff_mem_closure.mpr hcl
        rw [(IsClosedImmersion.isClosedEmbedding i).isInducing.specializes_iff] at hsp
        exact (Set.mem_iInter₂.mp hwW.2 y ⟨hyg, hyη⟩) (specializes_iff_mem_closure.mp hsp)
      rw [a3b4a_gysin_multiplicity_eq_source_stalkLength q i η hη _ hx hother, hm η hη]
      simp

end HodgeLean.Adapters
