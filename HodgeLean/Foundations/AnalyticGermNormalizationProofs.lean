import HodgeLean.Foundations.AnalyticGermProjection
import Mathlib.RingTheory.Ideal.HasGoingUp

/-! # Analytic prime normalization primitives

Implication from preparation to finite parameter maps compatible with linear projection,
and from distinguished equations to proper finite-fibre neighbourhood projections.
Parameter dimension calibration and neighbourhood surjectivity remain deferred.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

private theorem ringKrullDim_eq_of_finite_injective {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Finite)
    (hinj : Function.Injective f) : ringKrullDim R = ringKrullDim S := by
  letI : Algebra R S := f.toAlgebra
  have hint : Algebra.IsIntegral R S := ⟨hf.to_isIntegral⟩
  apply le_antisymm
  · rw [ringKrullDim, Order.krullDim]
    apply iSup_le
    intro l
    obtain ⟨Q, -, hQ, hQo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
      (⊥ : Ideal S) (by
        change RingHom.ker f ≤ l.head.asIdeal
        rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
        exact bot_le)
    have : Q.LiesOver l.head.asIdeal := ⟨hQo.symm⟩
    obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
    rw [← hL]
    exact Order.LTSeries.length_le_krullDim L
  · exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) fun I J hIJ ↦ by
      change Ideal.under R I.asIdeal < Ideal.under R J.asIdeal
      exact Ideal.IsIntegral.under_lt_under hIJ
private theorem adim5_power_mem_map_maximalIdeal {R S : Type*}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) (hf : f.IsIntegral)
    {x : S} (hx : x ∈ IsLocalRing.maximalIdeal S) :
    ∃ k : ℕ, x ^ k ∈ (IsLocalRing.maximalIdeal R).map f := by
  rw [← Ideal.mem_radical_iff]
  rw [Ideal.radical_eq_sInf]
  rw [Ideal.mem_sInf]
  intro Q hQ
  have hle : IsLocalRing.maximalIdeal R ≤ Q.comap f :=
    Ideal.map_le_iff_le_comap.mp hQ.1
  have hcomapQ : Q.comap f = IsLocalRing.maximalIdeal R := by
    apply le_antisymm (IsLocalRing.le_maximalIdeal (hQ.2.comap f).ne_top)
    exact hle
  letI : Q.IsPrime := hQ.2
  have hQmax : Q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap f hf Q
      (hcomapQ ▸ IsLocalRing.maximalIdeal.isMaximal R)
  have hQeq : Q = IsLocalRing.maximalIdeal S := IsLocalRing.eq_maximalIdeal hQmax
  simpa [hQeq] using hx

private theorem adim5_analyticGerm_isLocalRing (n : ℕ) : IsLocalRing (AnalyticGerm n) := by
  apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
  intro a b hab
  rw [analyticGerm_isUnit_iff] at hab
  simp only [map_add] at hab
  by_cases ha : analyticGermValue n a = 0
  · right
    rw [analyticGerm_isUnit_iff]
    simpa [ha] using hab
  · left
    rwa [analyticGerm_isUnit_iff]

private theorem adim5_analyticGerm_maximalIdeal_eq (n : ℕ) [IsLocalRing (AnalyticGerm n)] :
    IsLocalRing.maximalIdeal (AnalyticGerm n) = analyticGermMaximalIdeal n := by
  symm
  apply IsLocalRing.eq_maximalIdeal
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  refine ⟨⟨Filter.Germ.ofFun (fun _ ↦ c), fun _ ↦ c, analyticAt_const, rfl⟩, ?_⟩
  rfl

/-- Source: Gunning--Rossi, III.B--C, local parametrization; de Jong--Pfister, Chapter 3, finite analytic algebras. -/
theorem adim5_prime_step_aux (n : ℕ) (P : Ideal (AnalyticGerm (n + 1)))
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ∃ (L : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ))
      (e : AnalyticGerm (n + 1) ≃+* AnalyticGerm (n + 1))
      (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
      (W : Polynomial (AnalyticGerm n)),
      (∀ (a : AnalyticGerm (n + 1)) (f : (Fin (n + 1) → ℂ) → ℂ),
        AnalyticAt ℂ f 0 → Germ.ofFun f = a.val →
        Germ.ofFun (fun z ↦ f (L z)) = (e a).val) ∧
      IsWeierstrassEmbedding ι ∧ IsWeierstrassPolynomial W ∧
      ι W ∈ P.map e.toRingHom ∧
      ((P.map e.toRingHom).comap (ι.comp C)).IsPrime ∧
      (Ideal.quotientMap (P.map e.toRingHom) (ι.comp C) (le_refl _)).Finite ∧
      Function.Injective
        (Ideal.quotientMap (P.map e.toRingHom) (ι.comp C) (le_refl _)) ∧
      ringKrullDim (AnalyticGerm n ⧸ (P.map e.toRingHom).comap (ι.comp C)) =
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) := by
  obtain ⟨g, hgP, hg0⟩ : ∃ g ∈ P, g ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hgu : ¬ IsUnit g := fun hg ↦ hP.ne_top (P.eq_top_of_isUnit_mem hgP hg)
  obtain ⟨L, e, he, hreg⟩ := spec_exists_linearChange_regular hg0 hgu
  have hegu : ¬ IsUnit (e g) := fun hg ↦ hgu (by simpa using hg.map e.symm)
  obtain ⟨ι, W, hι, hW, hassoc⟩ := spec_preparation_transfer hreg hegu
  let J : Ideal (AnalyticGerm (n + 1)) := P.map e.toRingHom
  have hegJ : e g ∈ J := Ideal.mem_map_of_mem e.toRingHom hgP
  have hιWJ : ι W ∈ J := by
    obtain ⟨c, hc⟩ := hassoc.dvd
    rw [hc]
    exact J.mul_mem_right c hegJ
  have hJ : J.IsPrime := by
    apply Ideal.map_isPrime_of_surjective e.surjective
    simpa using hP
  letI : J.IsPrime := hJ
  let q : AnalyticGerm n ⧸ J.comap (ι.comp C) →+* AnalyticGerm (n + 1) ⧸ J :=
    Ideal.quotientMap J (ι.comp C) (le_refl _)
  have hqf : q.Finite := adim4_contraction_finite n ι hι W hW J hιWJ
  have hqi : Function.Injective q := Ideal.quotientMap_injective
  have hdimJ : ringKrullDim (AnalyticGerm n ⧸ J.comap (ι.comp C)) =
      ringKrullDim (AnalyticGerm (n + 1) ⧸ J) :=
    ringKrullDim_eq_of_finite_injective q hqf hqi
  have hdimP : ringKrullDim (AnalyticGerm (n + 1) ⧸ J) =
      ringKrullDim (AnalyticGerm (n + 1) ⧸ P) := by
    exact ringKrullDim_eq_of_ringEquiv
      (Ideal.quotientEquiv P J e rfl).symm
  refine ⟨L, e, ι, W, he, hι, hW, hιWJ, ?_, hqf, hqi, ?_⟩
  · exact (inferInstance : (J.comap (ι.comp C)).IsPrime)
  · exact hdimJ.trans hdimP

/-- Source: Gunning--Rossi, III.B--C, local parametrization; Grauert--Remmert, Coherent Analytic Sheaves, Chapter 3. -/
theorem adim5_finite_parameters_aux (n : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) :
    ∃ (d : ℕ) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
      (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)),
      d ≤ n ∧ θ.Finite ∧ Function.Injective θ ∧
      (∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ), AnalyticAt ℂ f 0 →
        Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
        Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b) ∧
      ringKrullDim (AnalyticGerm d) = ringKrullDim (AnalyticGerm n ⧸ P) := by
  induction n with
  | zero =>
      have hvalue : Function.Bijective (analyticGermValue 0) := by
        constructor
        · rintro ⟨g, f, hf, rfl⟩ ⟨h, k, hk, rfl⟩ hv
          apply Subtype.ext
          rw [Filter.Germ.coe_eq]
          filter_upwards [] with z
          have hz : z = 0 := Subsingleton.elim _ _
          change f 0 = k 0 at hv
          simpa [hz] using hv
        · intro c
          refine ⟨⟨@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) (fun _ ↦ c),
            ⟨fun _ ↦ c, analyticAt_const, rfl⟩⟩, ?_⟩
          change (@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) (fun _ ↦ c)).value = c
          simpa using (Filter.Germ.value_ofFun (fun _ : Fin 0 → ℂ ↦ c) (0 : Fin 0 → ℂ))
      let e : AnalyticGerm 0 ≃+* ℂ := RingEquiv.ofBijective (analyticGermValue 0) hvalue
      letI : Field (AnalyticGerm 0) :=
        (e.toMulEquiv.isField (Field.toIsField ℂ)).toField
      letI : P.IsPrime := hP
      have hP0 : P = ⊥ := by
        apply le_antisymm
        · intro x hx
          rw [Ideal.mem_bot]
          by_contra hx0
          exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P
            hx ((isUnit_iff_ne_zero).2 hx0))
        · exact bot_le
      subst P
      refine ⟨0, ContinuousLinearMap.id ℂ _, Ideal.Quotient.mk ⊥, le_rfl,
        RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective,
        (RingEquiv.quotientBot (AnalyticGerm 0)).symm.injective, ?_, ?_⟩
      · intro a f hf hfa b hfb
        apply (RingEquiv.quotientBot (AnalyticGerm 0)).injective
        simpa only [RingEquiv.quotientBot_mk, ContinuousLinearMap.id_apply] using
          Subtype.ext (hfa.symm.trans hfb)
      · exact (RingEquiv.quotientBot (AnalyticGerm 0)).ringKrullDim.symm
  | succ n ih =>
      by_cases hP0 : P = ⊥
      · subst P
        refine ⟨n + 1, ContinuousLinearMap.id ℂ _, Ideal.Quotient.mk ⊥, le_rfl,
          RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective,
          (RingEquiv.quotientBot (AnalyticGerm (n + 1))).symm.injective, ?_, ?_⟩
        · intro a f hf hfa b hfb
          apply (RingEquiv.quotientBot (AnalyticGerm (n + 1))).injective
          simpa only [RingEquiv.quotientBot_mk, ContinuousLinearMap.id_apply] using
            Subtype.ext (hfa.symm.trans hfb)
        · exact (RingEquiv.quotientBot (AnalyticGerm (n + 1))).ringKrullDim.symm
      · obtain ⟨L, e, ι, W, he, hι, hW, hWP, hQ, hfinite, hinjective, hdim⟩ :=
          adim5_prime_step_aux n P hP hP0
        let Q : Ideal (AnalyticGerm n) := (P.map e.toRingHom).comap (ι.comp C)
        let q : AnalyticGerm n ⧸ Q →+* AnalyticGerm (n + 1) ⧸ (P.map e.toRingHom) :=
          Ideal.quotientMap (P.map e.toRingHom) (ι.comp C) (le_refl _)
        let E : (AnalyticGerm (n + 1) ⧸ P) ≃+*
            (AnalyticGerm (n + 1) ⧸ (P.map e.toRingHom)) :=
          Ideal.quotientEquiv P (P.map e.toRingHom) e rfl
        obtain ⟨d, π0, θ0, hd, hf0, hi0, hrep0, hdim0⟩ := ih Q hQ
        let drop : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
          ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj i.castSucc
        let π : (Fin (n + 1) → ℂ) →L[ℂ] (Fin d → ℂ) :=
          π0.comp (drop.comp L.symm.toContinuousLinearMap)
        let θ : AnalyticGerm d →+* AnalyticGerm (n + 1) ⧸ P :=
          E.symm.toRingHom.comp (q.comp θ0)
        refine ⟨d, π, θ, hd.trans (Nat.le_succ n), ?_, ?_, ?_, hdim0.trans hdim⟩
        · exact (RingHom.Finite.of_surjective E.symm.toRingHom E.symm.surjective).comp
            (hfinite.comp hf0)
        · exact E.symm.injective.comp (hinjective.comp hi0)
        · intro a f hfa hfa' b hfb
          let c : AnalyticGerm n :=
            ⟨Germ.ofFun (fun z ↦ f (π0 z)),
              ⟨fun z ↦ f (π0 z),
                hfa.comp_of_eq (π0.analyticAt 0) (map_zero π0), rfl⟩⟩
          have hfc : Germ.ofFun (fun z ↦ f (π0 z)) = c.val := rfl
          have hrec := hrep0 a f hfa hfa' c hfc
          apply E.injective
          change E (E.symm (q (θ0 a))) = E (Ideal.Quotient.mk P b)
          rw [E.apply_symm_apply]
          rw [hrec]
          simp only [q, E, Ideal.quotientMap_mk, RingHom.comp_apply,
            Ideal.quotientEquiv_mk]
          apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
          have heb : e b = ι (C c) := by
            obtain ⟨g, hg, hgc, hgext⟩ := hι.2.1 c
            have hext : Germ.ofFun (fun z : Fin (n + 1) → ℂ ↦
                f (π0 (drop z))) = (ι (C c)).val := by
              rw [← hgext, Filter.Germ.coe_eq]
              have ht : Tendsto (fun z : Fin (n + 1) → ℂ ↦ drop z)
                  (nhds 0) (nhds 0) := by
                rw [← map_zero drop]
                exact drop.continuous.continuousAt
              exact ht.eventually (Filter.Germ.coe_eq.mp (hfc.trans hgc.symm))
            apply Subtype.ext
            rw [← he b (fun z ↦ f (π z))
              (hfa.comp_of_eq (π.analyticAt 0) (map_zero π)) hfb]
            simpa only [π, drop, ContinuousLinearMap.comp_apply,
              ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using hext
          change ι (C c) - e b ∈ P.map e.toRingHom
          rw [heb, sub_self]
          exact Ideal.zero_mem _

/-- Source: de Jong--Pfister, Local Analytic Geometry, Chapters 3--4, finite local analytic algebras; Grauert--Remmert, Coherent Analytic Sheaves, Chapter 3. -/
theorem adim5_distinguished_relation_aux (n d : ℕ) (P : Ideal (AnalyticGerm n)) (hP : P ≠ ⊤)
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (hθ : θ.Finite)
    (hlocal : ∀ (a : AnalyticGerm d) (b : AnalyticGerm n),
      θ a = Ideal.Quotient.mk P b → analyticGermValue d a = analyticGermValue n b)
    (g : AnalyticGerm n) (hg : analyticGermValue n g = 0) :
    ∃ W : Polynomial (AnalyticGerm d), IsWeierstrassPolynomial W ∧
      W.eval₂ θ (Ideal.Quotient.mk P g) = 0 := by
  letI := adim5_analyticGerm_isLocalRing n
  letI := adim5_analyticGerm_isLocalRing d
  letI : Nontrivial (AnalyticGerm n ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
  letI : IsLocalRing (AnalyticGerm n ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let x : AnalyticGerm n ⧸ P := Ideal.Quotient.mk P g
  have hx : x ∈ IsLocalRing.maximalIdeal (AnalyticGerm n ⧸ P) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective]
    apply Ideal.mem_map_of_mem
    rw [adim5_analyticGerm_maximalIdeal_eq n]
    exact hg
  obtain ⟨k, hk⟩ := adim5_power_mem_map_maximalIdeal θ hθ.to_isIntegral hx
  have hk' : x ^ (k + 1) ∈ (IsLocalRing.maximalIdeal (AnalyticGerm d)).map θ := by
    rw [pow_succ]
    exact ((IsLocalRing.maximalIdeal (AnalyticGerm d)).map θ).mul_mem_right x hk
  letI : Algebra (AnalyticGerm d) (AnalyticGerm n ⧸ P) := θ.toAlgebra
  letI : Algebra.IsIntegral (AnalyticGerm d) (AnalyticGerm n ⧸ P) := ⟨hθ.to_isIntegral⟩
  obtain ⟨Q, hQmonic, hQroot, hQcoeff⟩ :=
    Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map hk'
  have hQdeg : 0 < Q.natDegree := by
    by_contra hn
    have hQone : Q = 1 := hQmonic.natDegree_eq_zero.mp (Nat.eq_zero_of_not_pos hn)
    subst Q
    simp at hQroot
  let W : Polynomial (AnalyticGerm d) := Polynomial.expand (AnalyticGerm d) (k + 1) Q
  refine ⟨W, ?_, ?_⟩
  · refine ⟨hQmonic.expand (Nat.succ_pos k), ?_, ?_⟩
    · simp only [W, Polynomial.natDegree_expand]
      positivity
    · intro j hj
      simp only [W, Polynomial.coeff_expand (Nat.succ_pos k)]
      split_ifs with hjdiv
      · rw [← adim5_analyticGerm_maximalIdeal_eq d]
        apply hQcoeff
        apply ne_of_lt
        apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos k)).2
        simpa only [W, Polynomial.natDegree_expand] using hj
      · exact (analyticGermMaximalIdeal d).zero_mem
  · simp only [W, Polynomial.expand_eq_comp_X_pow, Polynomial.eval₂_comp]
    change Q.eval₂ θ (x ^ (k + 1)) = 0 at hQroot
    simpa [x] using hQroot

/-- Source: Gunning--Rossi, III.B--C, distinguished polynomials and finite projection; Chirka, Complex Analytic Sets, §§3--4. -/
theorem adim5_closed_projection_aux (n m : ℕ) (k : Fin m → ℕ) (hk : ∀ j, 0 < k j)
    (a : (j : Fin m) → Fin (k j) → (Fin n → ℂ) → ℂ)
    (ha : ∀ j i, AnalyticAt ℂ (a j i) 0) (ha0 : ∀ j i, a j i 0 = 0)
    (U S : Set ((Fin n → ℂ) × (Fin m → ℂ)))
    (hU : IsOpen U) (hU0 : (0 : (Fin n → ℂ) × (Fin m → ℂ)) ∈ U)
    (hS : IsClosed {z : U | z.val ∈ S})
    (hS0 : (0 : (Fin n → ℂ) × (Fin m → ℂ)) ∈ S)
    (heq : ∀ z ∈ U ∩ S, ∀ j,
      z.2 j ^ k j + ∑ i : Fin (k j), a j i z.1 * z.2 j ^ (i : ℕ) = 0) :
    ∃ (V : Set (Fin n → ℂ)) (W : Set ((Fin n → ℂ) × (Fin m → ℂ))),
      IsOpen V ∧ (0 : Fin n → ℂ) ∈ V ∧ IsOpen W ∧
      (0 : (Fin n → ℂ) × (Fin m → ℂ)) ∈ W ∧ W ⊆ U ∧
      ∃ p : {z : (Fin n → ℂ) × (Fin m → ℂ) // z ∈ W ∩ S} → V,
        (∀ z, (p z).val = z.val.1) ∧ IsProperMap p ∧
        (∀ w : V, (p ⁻¹' {w}).Finite) ∧
        ∀ z, (p z).val = 0 → z.val = 0 := by
  classical
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp (hU.mem_nhds hU0)
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.mp hB
  let R : ℝ := r / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hroot : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ j w,
      w ^ k j + ∑ i : Fin (k j), a j i z * w ^ (i : ℕ) = 0 → ‖w‖ < R := by
    rw [Filter.eventually_all]
    exact fun j ↦ AnalyticDivisorAlgebraic4.spec_monicInLast_roots_small
      (fun i ↦ (ha j i).continuousAt)
      (ha0 j) hR
  let V : Set (Fin n → ℂ) := interior (A ∩ {z | ∀ j w,
    w ^ k j + ∑ i : Fin (k j), a j i z * w ^ (i : ℕ) = 0 → ‖w‖ < R})
  let W : Set ((Fin n → ℂ) × (Fin m → ℂ)) := V ×ˢ Metric.ball 0 r
  have hVopen : IsOpen V := isOpen_interior
  have hV0 : (0 : Fin n → ℂ) ∈ V := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.inter_mem hA hroot
  have hWopen : IsOpen W := hVopen.prod Metric.isOpen_ball
  have hW0 : (0 : (Fin n → ℂ) × (Fin m → ℂ)) ∈ W := by
    exact ⟨hV0, by simpa using hr⟩
  have hWU : W ⊆ U := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    apply hAB
    refine ⟨(interior_subset hz).1, hrB ?_⟩
    simpa [Metric.mem_ball, dist_zero_right] using hw
  refine ⟨V, W, hVopen, hV0, hWopen, hW0, hWU, ?_⟩
  let p : {z : (Fin n → ℂ) × (Fin m → ℂ) // z ∈ W ∩ S} → V :=
    fun z ↦ ⟨z.val.1, z.property.1.1⟩
  have hrootV (z : V) (w : Fin m → ℂ)
      (hw : ∀ j, w j ^ k j + ∑ i : Fin (k j), a j i z.val * w j ^ (i : ℕ) = 0) :
      ∀ j, ‖w j‖ < R := by
    exact fun j ↦ (interior_subset z.property).2 j (w j) (hw j)
  refine ⟨p, fun z ↦ rfl, ?_, ?_, ?_⟩
  · refine isProperMap_iff_isCompact_preimage.mpr ⟨by fun_prop, ?_⟩
    intro K hK
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    let C : Set (Fin m → ℂ) := Metric.closedBall 0 R
    have hC : IsCompact C := isCompact_closedBall 0 R
    let D : Set (V × (Fin m → ℂ)) := K ×ˢ C
    have hD : IsCompact D := hK.prod hC
    let q : D → U := fun y ↦ ⟨(y.val.1.val, y.val.2), hAB ⟨
      (interior_subset y.val.1.property).1,
      hrB (by
        have hyR : ‖y.val.2‖ ≤ R := by
          have hy := y.property.2
          change y.val.2 ∈ Metric.closedBall (0 : Fin m → ℂ) R at hy
          rw [Metric.mem_closedBall] at hy
          simpa [dist_zero_left] using hy
        have hRr : R < r := by dsimp [R]; linarith
        simpa [Metric.mem_ball, dist_zero_right] using hyR.trans_lt hRr)⟩⟩
    have hq : Continuous q := by
      apply Continuous.subtype_mk
      exact (continuous_fst.comp continuous_subtype_val).subtype_val.prodMk
        (continuous_snd.comp continuous_subtype_val)
    let T : Set D := q ⁻¹' {z : U | z.val ∈ S}
    have hDu : IsCompact (Set.univ : Set D) := by
      rw [IsEmbedding.subtypeVal.isCompact_iff]
      simpa using hD
    have hT : IsCompact T := by
      simpa [T] using hDu.inter_right (hS.preimage hq)
    let e : D → (Fin n → ℂ) × (Fin m → ℂ) := fun y ↦ (y.val.1.val, y.val.2)
    have he : Continuous e :=
      ((continuous_fst.comp continuous_subtype_val).subtype_val.prodMk
        (continuous_snd.comp continuous_subtype_val))
    have himg := hT.image he
    have himage : Subtype.val '' (p ⁻¹' K) = e '' T := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hypK : p y ∈ K := by simpa using hy
        have hyeq : ∀ j, y.val.2 j ^ k j +
            ∑ i : Fin (k j), a j i y.val.1 * y.val.2 j ^ (i : ℕ) = 0 :=
          heq y.val ⟨hWU y.property.1, y.property.2⟩
        let d : D := ⟨(p y, y.val.2), ⟨hypK, by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact (pi_norm_le_iff_of_nonneg hR.le).2
            (fun j ↦ (hrootV (p y) y.val.2 hyeq j).le)⟩⟩
        refine ⟨d, ?_, rfl⟩
        exact y.property.2
      · rintro ⟨y, hy, rfl⟩
        have hyS : (y.val.1.val, y.val.2) ∈ S := hy
        have hyR : ‖y.val.2‖ ≤ R := by
          have hyC := y.property.2
          change y.val.2 ∈ Metric.closedBall (0 : Fin m → ℂ) R at hyC
          rw [Metric.mem_closedBall] at hyC
          simpa [dist_zero_left] using hyC
        have hyr : ‖y.val.2‖ < r := hyR.trans_lt (by dsimp [R]; linarith)
        let d : {z : (Fin n → ℂ) × (Fin m → ℂ) // z ∈ W ∩ S} :=
          ⟨(y.val.1.val, y.val.2), ⟨⟨y.val.1.property, by
            simpa [Metric.mem_ball, dist_zero_right] using hyr⟩, hyS⟩⟩
        refine ⟨d, ?_, rfl⟩
        change p d ∈ K
        simpa [d, p] using y.property.1
    rw [himage]
    exact himg
  · intro z
    let roots : Fin m → Set ℂ := fun j ↦ {w | w ^ k j +
      ∑ i : Fin (k j), a j i z.val * w ^ (i : ℕ) = 0}
    have hroots : ∀ j, (roots j).Finite := by
      intro j
      let q : ℂ[X] := X ^ k j + ∑ i : Fin (k j), C (a j i z.val) * X ^ (i : ℕ)
      have hq0 : q ≠ 0 :=
        (monic_X_pow_add (degree_sum_fin_lt (fun i ↦ a j i z.val))).ne_zero
      exact (Polynomial.finite_setOfPred_isRoot hq0).subset (by
        intro w hw
        simpa [q, roots, IsRoot, eval_add, eval_finset_sum] using hw)
    refine Set.Finite.of_finite_image (s := p ⁻¹' {z})
      (f := fun x : {y : (Fin n → ℂ) × (Fin m → ℂ) // y ∈ W ∩ S} ↦ x.val.2)
      ((Set.Finite.pi hroots).subset ?_) ?_
    · rintro w ⟨x, hx, rfl⟩ j hj
      have he := heq x.val ⟨hWU x.property.1, x.property.2⟩ j
      have hxz : x.val.1 = z.val := by
        have : p x = z := by simpa using hx
        exact congrArg Subtype.val this
      rw [hxz] at he
      simpa [roots] using he
    · intro x hx y hy hxy
      apply Subtype.ext
      apply Prod.ext
      · have hxz : p x = z := by simpa using hx
        have hyz : p y = z := by simpa using hy
        exact congrArg Subtype.val (hxz.trans hyz.symm)
      · exact hxy
  · intro z hz
    apply Prod.ext
    · exact hz
    · funext j
      have he := heq z.val ⟨hWU z.property.1, z.property.2⟩ j
      have hz1 : z.val.1 = 0 := hz
      rw [hz1] at he
      simpa [ha0, (hk j).ne'] using he

end HodgeLean.Foundations
