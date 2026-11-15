import HodgeLean.Foundations.AnalyticDivisorAlgebraic12Defs

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic12

open Filter Polynomial Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic10
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11

theorem spec_polynomialAt_coeff_aux {n : ℕ} (P : Polynomial (AnalyticGerm n))
    (a : ℕ → (Fin n → ℂ) → ℂ) (p : Fin n → ℂ) (ha : ∀ j, AnalyticAt ℂ (a j) p) (j : ℕ) :
    ((gaga12_polynomialAt P a p ha).coeff j).1 =
      if j ∈ P.support then @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (a j) else 0 := by
  classical
  rw [gaga12_polynomialAt, Polynomial.sum, finsetSum_coeff]
  simp only [coeff_monomial]
  split_ifs with hj
  · rw [Finset.sum_eq_single_of_mem j hj fun k _ hk ↦ ite_eq_right_iff.mpr fun h ↦ absurd h hk,
      ite_eq_left_iff.mpr fun h ↦ absurd rfl h]
  · rw [Finset.sum_eq_zero fun k hk ↦ ite_eq_right_iff.mpr fun (hkj : k = j) ↦ absurd (hkj ▸ hk) hj]
    rfl

theorem spec_resultant_map_ringEquiv_aux {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P Q : Polynomial R) :
    (P.map e.toRingHom).resultant (Q.map e.toRingHom) = e (P.resultant Q) := by
  have h := resultant_map_map P Q P.natDegree Q.natDegree e.toRingHom
  rw [natDegree_map_eq_of_injective e.injective, natDegree_map_eq_of_injective e.injective]
  exact h

theorem gaga12a_sylvester_congr_apply {R : Type*} [Semiring R] (f g : Polynomial R)
    {m n m' n' : ℕ} (hm : m = m') (hn : n = n') (i j : ℕ) (hi : i < m + n) (hj : j < m + n)
    (hi' : i < m' + n') (hj' : j < m' + n') :
    sylvester f g m n ⟨i, hi⟩ ⟨j, hj⟩ = sylvester f g m' n' ⟨i, hi'⟩ ⟨j, hj'⟩ := by
  subst hm hn; rfl

theorem gaga12a_sylvesterDeriv_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : Polynomial R) (hd : (f.map φ).natDegree = f.natDegree) :
    (f.map φ).sylvesterDeriv = (φ.mapMatrix f.sylvesterDeriv).reindex
      (finCongr (by rw [hd])) (finCongr (by rw [hd])) := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  by_cases hn : f.natDegree = 0
  · simp [sylvesterDeriv, hn, hd]
  · simp only [sylvesterDeriv, hd, hn, ↓reduceDIte, Matrix.reindex_apply, Matrix.submatrix_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, finCongr_symm, finCongr_apply, Fin.cast_mk,
      Matrix.updateRow_apply, Fin.mk.injEq, derivative_map]
    split_ifs
    · simp
    · simp
    · simp
    · rw [sylvester_map_map, RingHom.mapMatrix_apply, Matrix.map_apply,
        gaga12a_sylvester_congr_apply _ _ (by rw [hd]) hd]

theorem gaga12a_discr_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : Polynomial R) (hd : (f.map φ).natDegree = f.natDegree) :
    (f.map φ).discr = φ f.discr := by
  rw [discr, discr, gaga12a_sylvesterDeriv_map φ f hd, Matrix.det_reindex_self,
    ← RingHom.map_det, hd, map_mul, map_pow, map_neg, map_one]

theorem spec_discr_map_ringEquiv_aux {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P : Polynomial R) :
    (P.map e.toRingHom).discr = e P.discr :=
  gaga12a_discr_map e.toRingHom P (natDegree_map_eq_of_injective e.injective P)

theorem spec_germ_translation_resultant_discr_aux (n : ℕ) (p : Fin n → ℂ) :
    ∃ e : AnalyticGermAt n p ≃+* AnalyticGerm n,
      (∀ g : AnalyticGermAt n p,
        analyticGermValue n (e g) = analyticGermAtValue n p g) ∧
      (∀ (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
          (ht : AnalyticAt ℂ (fun z ↦ f (p + z)) 0),
        e ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) f, ⟨f, hf, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun z ↦ f (p + z)),
            ⟨fun z ↦ f (p + z), ht, rfl⟩⟩) ∧
      (∀ A B : Polynomial (AnalyticGermAt n p),
        (A.map e.toRingHom).resultant (B.map e.toRingHom) = e (A.resultant B)) ∧
      ∀ A : Polynomial (AnalyticGermAt n p), (A.map e.toRingHom).discr = e A.discr := by
  obtain ⟨e, hvalue, hrep⟩ := spec_germ_translation_equiv n p
  exact ⟨e, hvalue, hrep, fun A B ↦ spec_resultant_map_ringEquiv_aux e A B,
    fun A ↦ spec_discr_map_ringEquiv_aux e A⟩

theorem gaga12a_sum_monomial_coeff {S T : Type*} [Semiring S] [Semiring T] (P : Polynomial S)
    (c : ℕ → T) (k : ℕ) :
    (P.sum fun j _ ↦ monomial j (c j)).coeff k = if k ∈ P.support then c k else 0 := by
  classical
  rw [Polynomial.sum, finsetSum_coeff]
  simp only [coeff_monomial]
  split_ifs with hk
  · rw [Finset.sum_eq_single_of_mem k hk fun j _ hj ↦ ite_eq_right_iff.mpr fun h ↦ absurd h hj,
      ite_eq_left_iff.mpr fun h ↦ absurd rfl h]
  · exact Finset.sum_eq_zero fun j hj ↦
      ite_eq_right_iff.mpr fun (hjk : j = k) ↦ absurd (hjk ▸ hj) hk

theorem gaga12a_sum_monomial_map {S T U : Type*} [Semiring S] [Semiring T] [Semiring U]
    (P : Polynomial S) (c : ℕ → T) (φ : T →+* U) :
    (P.sum fun j _ ↦ monomial j (c j)).map φ = P.sum fun j _ ↦ monomial j (φ (c j)) := by
  ext k
  rw [coeff_map, gaga12a_sum_monomial_coeff, gaga12a_sum_monomial_coeff]
  split_ifs <;> simp

theorem gaga12a_monic_natDegree {T : Type*} [Semiring T] [Nontrivial T] (Q : Polynomial T) (d : ℕ)
    (h1 : Q.coeff d = 1) (h0 : ∀ k, d < k → Q.coeff k = 0) : Q.Monic ∧ Q.natDegree = d := by
  have hle : Q.natDegree ≤ d :=
    natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ h0 k (by exact_mod_cast hk)
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one d hle h1,
    natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [h1]; exact one_ne_zero)⟩

/-- Fibres of a monic polynomial with leading representative one. -/
theorem gaga12a_fibre_monic {n : ℕ} (P : Polynomial (AnalyticGerm n)) (hP : P.Monic)
    (a : ℕ → (Fin n → ℂ) → ℂ) (x : Fin n → ℂ) (hlead : a P.natDegree x = 1) :
    (P.sum fun j _ ↦ monomial j (a j x)).Monic ∧
      (P.sum fun j _ ↦ monomial j (a j x)).natDegree = P.natDegree := by
  have hmem : P.natDegree ∈ P.support := natDegree_mem_support_of_nonzero hP.ne_zero
  refine gaga12a_monic_natDegree _ _ ?_ fun k hk ↦ ?_
  · rw [gaga12a_sum_monomial_coeff, ite_eq_left hmem, hlead]
  · rw [gaga12a_sum_monomial_coeff, ite_eq_right]
    rw [mem_support_iff, not_not]
    exact coeff_eq_zero_of_natDegree_lt hk

theorem gaga12a_polynomialAt_map {n : ℕ} (P : Polynomial (AnalyticGerm n))
    (a : ℕ → (Fin n → ℂ) → ℂ) (p : Fin n → ℂ)
    (hap : ∀ j, AnalyticAt ℂ (a j) p) :
    (gaga12_polynomialAt P a p hap).map (analyticGermAtSubring n p).subtype =
      (P.sum fun j _ ↦ monomial j (a j)).map (Filter.Germ.coeRingHom (nhds p)) := by
  rw [gaga12_polynomialAt, gaga12a_sum_monomial_map, gaga12a_sum_monomial_map]
  rfl

theorem gaga12a_polynomialAt_monic {n : ℕ} (P : Polynomial (AnalyticGerm n)) (hP : P.Monic)
    (a : ℕ → (Fin n → ℂ) → ℂ) (p : Fin n → ℂ) (hap : ∀ j, AnalyticAt ℂ (a j) p)
    (U : Set (Fin n → ℂ)) (hU : U ∈ nhds p) (hlead : ∀ x ∈ U, a P.natDegree x = 1) :
    (gaga12_polynomialAt P a p hap).Monic ∧
      (gaga12_polynomialAt P a p hap).natDegree = P.natDegree := by
  have hmem : P.natDegree ∈ P.support := natDegree_mem_support_of_nonzero hP.ne_zero
  refine gaga12a_monic_natDegree _ _ ?_ fun k hk ↦ ?_
  · apply Subtype.ext
    rw [gaga12_polynomialAt, gaga12a_sum_monomial_coeff, ite_eq_left hmem]
    exact Filter.Germ.coe_eq.mpr (Filter.eventually_of_mem hU hlead)
  · apply Subtype.ext
    rw [gaga12_polynomialAt, gaga12a_sum_monomial_coeff, ite_eq_right]
    rw [mem_support_iff, not_not]
    exact coeff_eq_zero_of_natDegree_lt hk

theorem spec_resultant_germ_at_nearby_point_aux {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) (hP : P.Monic)
    (a b : ℕ → (Fin n → ℂ) → ℂ) (R : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ))
    (p : Fin n → ℂ) (hU : U ∈ nhds p)
    (hap : ∀ j, AnalyticAt ℂ (a j) p) (hbp : ∀ j, AnalyticAt ℂ (b j) p)
    (hlead : ∀ x ∈ U, a P.natDegree x = 1)
    (hR : ∀ x ∈ U, R x = (P.sum fun j _ ↦ monomial j (a j x)).resultant
      (g.sum fun j _ ↦ monomial j (b j x))) :
    ((gaga12_polynomialAt P a p hap).resultant (gaga12_polynomialAt g b p hbp)).1 =
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) R := by
  classical
  obtain ⟨-, hAd⟩ := gaga12a_polynomialAt_monic P hP a p hap U hU hlead
  set B := gaga12_polynomialAt g b p hbp with hBdef
  set m := B.natDegree
  set Pf := P.sum fun j _ ↦ monomial j (a j)
  set Gf := g.sum fun j _ ↦ monomial j (b j)
  have hvan : ∀ᶠ x in nhds p, ∀ j ∈ g.support, m < j → b j x = 0 := by
    rw [eventually_all_finset]
    intro j hj
    by_cases hjm : m < j
    · have hc : (B.coeff j).1 = @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (b j) := by
        rw [hBdef, gaga12_polynomialAt, gaga12a_sum_monomial_coeff, ite_eq_left hj]
      rw [coeff_eq_zero_of_natDegree_lt hjm] at hc
      have h0 : (b j) =ᶠ[nhds p] fun _ ↦ (0 : ℂ) := Filter.Germ.coe_eq.mp hc.symm
      filter_upwards [h0] with x hx _
      exact hx
    · exact Eventually.of_forall fun x h ↦ absurd h hjm
  have hev : ∀ᶠ x in nhds p, Pf.resultant Gf P.natDegree m x = R x := by
    filter_upwards [hvan, hU] with x hx hxU
    obtain ⟨hfm, hfd⟩ := gaga12a_fibre_monic P hP a x (hlead x hxU)
    have hGle : (g.sum fun j _ ↦ monomial j (b j x)).natDegree ≤ m := by
      refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_
      rw [gaga12a_sum_monomial_coeff]
      split_ifs with h
      · exact hx k h (by exact_mod_cast hk)
      · rfl
    rw [hR x hxU,
      ← AnalyticDivisorAlgebraic10.spec_resultant_fixed_degree_of_monic _ _ hfm m hGle, hfd]
    have := resultant_map_map Pf Gf P.natDegree m (Pi.evalRingHom (fun _ ↦ ℂ) x)
    rw [gaga12a_sum_monomial_map, gaga12a_sum_monomial_map] at this
    exact this.symm
  have h1 : ((gaga12_polynomialAt P a p hap).resultant B).1 =
      ((gaga12_polynomialAt P a p hap).map (analyticGermAtSubring n p).subtype).resultant
        (B.map (analyticGermAtSubring n p).subtype) P.natDegree m := by
    rw [resultant_map_map, ← hAd]
    rfl
  rw [h1, gaga12a_polynomialAt_map, hBdef, gaga12a_polynomialAt_map, resultant_map_map]
  exact Filter.Germ.coe_eq.mpr hev

theorem spec_discriminant_germ_at_nearby_point_aux {n : ℕ}
    (P : Polynomial (AnalyticGerm n)) (hP : P.Monic)
    (a : ℕ → (Fin n → ℂ) → ℂ) (D : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ))
    (p : Fin n → ℂ) (hU : U ∈ nhds p) (hap : ∀ j, AnalyticAt ℂ (a j) p)
    (hlead : ∀ x ∈ U, a P.natDegree x = 1)
    (hD : ∀ x ∈ U, D x = (P.sum fun j _ ↦ monomial j (a j x)).discr) :
    (gaga12_polynomialAt P a p hap).discr.1 =
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) D := by
  classical
  obtain ⟨-, hAd⟩ := gaga12a_polynomialAt_monic P hP a p hap U hU hlead
  set A := gaga12_polynomialAt P a p hap with hAdef
  set Pf := P.sum fun j _ ↦ monomial j (a j)
  have hAι : (A.map (analyticGermAtSubring n p).subtype).natDegree = A.natDegree :=
    natDegree_map_eq_of_injective Subtype.val_injective A
  have hPfd : Pf.natDegree = P.natDegree := by
    have hmem : P.natDegree ∈ P.support := natDegree_mem_support_of_nonzero hP.ne_zero
    refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_
      rw [gaga12a_sum_monomial_coeff, ite_eq_right]
      rw [mem_support_iff, not_not]
      exact coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hk)
    · rw [gaga12a_sum_monomial_coeff, ite_eq_left hmem]
      intro h0
      have h1 := hlead p (mem_of_mem_nhds hU)
      rw [h0] at h1
      exact zero_ne_one h1
  have hγ : (Pf.map (Filter.Germ.coeRingHom (nhds p))).natDegree = Pf.natDegree := by
    rw [← gaga12a_polynomialAt_map P a p hap, ← hAdef, hAι, hAd, hPfd]
  have hev : ∀ᶠ x in nhds p, Pf.discr x = D x := by
    filter_upwards [hU] with x hxU
    obtain ⟨-, hfd⟩ := gaga12a_fibre_monic P hP a x (hlead x hxU)
    have hd : (Pf.map (Pi.evalRingHom (fun _ ↦ ℂ) x)).natDegree = Pf.natDegree := by
      rw [gaga12a_sum_monomial_map, hPfd]
      exact hfd
    have := gaga12a_discr_map (Pi.evalRingHom (fun _ ↦ ℂ) x) Pf hd
    rw [gaga12a_sum_monomial_map] at this
    rw [hD x hxU]
    exact this.symm
  have h1 : A.discr.1 = (A.map (analyticGermAtSubring n p).subtype).discr :=
    (gaga12a_discr_map _ A hAι).symm
  rw [h1, hAdef, gaga12a_polynomialAt_map, gaga12a_discr_map _ Pf hγ]
  exact Filter.Germ.coe_eq.mpr hev

theorem spec_resultant_representative_nearby_aux {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a b : ℕ → (Fin n → ℂ) → ℂ) (R : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      IsOpen U ∧ IsPreconnected U ∧ (0 : Fin n → ℂ) ∈ U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧ (∀ j, AnalyticOnNhd ℂ (b j) U) ∧
      AnalyticOnNhd ℂ R U ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (b j) = (g.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) R = (P.resultant g).1 ∧
      (∀ x ∈ U, a P.natDegree x = 1) ∧
      (∀ x ∈ U, R x = (P.sum fun j _ ↦ monomial j (a j x)).resultant
        (g.sum fun j _ ↦ monomial j (b j x))) ∧
      ∀ p ∈ U, ∀ (hap : ∀ j, AnalyticAt ℂ (a j) p) (hbp : ∀ j, AnalyticAt ℂ (b j) p),
        ((gaga12_polynomialAt P a p hap).resultant (gaga12_polynomialAt g b p hbp)).1 =
          @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) R := by
  obtain ⟨a, b, R, W, hW, ha, hb, hR, ha0, hb0, hR0, hres, _⟩ :=
    spec_resultant_representative P g hP
  have hleadGerm :
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a P.natDegree) =
        @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun _ ↦ (1 : ℂ)) := by
    calc
      _ = (P.coeff P.natDegree).1 := ha0 P.natDegree
      _ = (1 : AnalyticGerm n).1 := congrArg Subtype.val hP.coeff_natDegree
      _ = _ := rfl
  have hleadEventually : ∀ᶠ x in nhds (0 : Fin n → ℂ), a P.natDegree x = 1 :=
    Filter.Germ.coe_eq.mp hleadGerm
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hW hleadEventually)
  let U := Metric.ball (0 : Fin n → ℂ) ε
  have hUW : U ⊆ W := fun x hx ↦ (hball hx).1
  have hUlead : ∀ x ∈ U, a P.natDegree x = 1 := fun x hx ↦ (hball hx).2
  refine ⟨a, b, R, U, Metric.isOpen_ball, (convex_ball 0 ε).isPreconnected,
    Metric.mem_ball_self hε, fun j ↦ (ha j).mono hUW, fun j ↦ (hb j).mono hUW,
    hR.mono hUW, ha0, hb0, hR0, hUlead, fun x hx ↦ hres x (hUW hx), ?_⟩
  intro p hp hap hbp
  exact spec_resultant_germ_at_nearby_point_aux P g hP a b R U p
    (Metric.isOpen_ball.mem_nhds hp) hap hbp hUlead (fun x hx ↦ hres x (hUW hx))

theorem spec_discriminant_representative_nearby_aux {n : ℕ}
    (P : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a : ℕ → (Fin n → ℂ) → ℂ) (D : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)),
      IsOpen U ∧ IsPreconnected U ∧ (0 : Fin n → ℂ) ∈ U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧ AnalyticOnNhd ℂ D U ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) D = P.discr.1 ∧
      (∀ x ∈ U, a P.natDegree x = 1) ∧
      (∀ x ∈ U, D x = (P.sum fun j _ ↦ monomial j (a j x)).discr) ∧
      ∀ p ∈ U, ∀ hap : ∀ j, AnalyticAt ℂ (a j) p,
        (gaga12_polynomialAt P a p hap).discr.1 =
          @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) D := by
  obtain ⟨a, D, W, hW, ha, hD, ha0, hD0, hdiscr, _⟩ :=
    spec_discriminant_representative P hP
  have hleadGerm :
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a P.natDegree) =
        @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun _ ↦ (1 : ℂ)) := by
    calc
      _ = (P.coeff P.natDegree).1 := ha0 P.natDegree
      _ = (1 : AnalyticGerm n).1 := congrArg Subtype.val hP.coeff_natDegree
      _ = _ := rfl
  have hleadEventually : ∀ᶠ x in nhds (0 : Fin n → ℂ), a P.natDegree x = 1 :=
    Filter.Germ.coe_eq.mp hleadGerm
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hW hleadEventually)
  let U := Metric.ball (0 : Fin n → ℂ) ε
  have hUW : U ⊆ W := fun x hx ↦ (hball hx).1
  have hUlead : ∀ x ∈ U, a P.natDegree x = 1 := fun x hx ↦ (hball hx).2
  refine ⟨a, D, U, Metric.isOpen_ball, (convex_ball 0 ε).isPreconnected,
    Metric.mem_ball_self hε, fun j ↦ (ha j).mono hUW, hD.mono hUW, ha0, hD0, hUlead,
    fun x hx ↦ hdiscr x (hUW hx), ?_⟩
  intro p hp hap
  exact spec_discriminant_germ_at_nearby_point_aux P hP a D U p
    (Metric.isOpen_ball.mem_nhds hp) hap hUlead (fun x hx ↦ hdiscr x (hUW hx))

theorem spec_germ_ne_zero_of_preconnected_aux {n : ℕ}
    (R : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hR : AnalyticOnNhd ℂ R U)
    (q p : Fin n → ℂ) (hq : q ∈ U) (hp : p ∈ U)
    (hne : @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds q) R ≠ 0) :
    @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) R ≠ 0 := by
  intro hz
  apply hne
  change (↑R : Filter.Germ (nhds q) ℂ) = ↑(0 : (Fin n → ℂ) → ℂ)
  rw [Filter.Germ.coe_eq]
  rw [← Filter.Germ.coe_zero] at hz
  have hpz : R =ᶠ[nhds p] 0 := Filter.Germ.coe_eq.mp hz
  have hall := hR.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hp hpz
  filter_upwards [hU.mem_nhds hq] with x hx
  exact hall hx

theorem spec_resultant_ne_zero_nearby_aux {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) (hP : P.Monic) (hres : P.resultant g ≠ 0) :
    ∃ (a b : ℕ → (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)),
      IsOpen U ∧ IsPreconnected U ∧ (0 : Fin n → ℂ) ∈ U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧ (∀ j, AnalyticOnNhd ℂ (b j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (b j) = (g.coeff j).1) ∧
      ∀ p ∈ U, ∀ (hap : ∀ j, AnalyticAt ℂ (a j) p) (hbp : ∀ j, AnalyticAt ℂ (b j) p),
        (gaga12_polynomialAt P a p hap).resultant (gaga12_polynomialAt g b p hbp) ≠ 0 := by
  obtain ⟨a, b, R, U, hU, hconn, h0, ha, hb, hR, ha0, hb0, hR0, hlead, hRfibre,
    hnear⟩ := spec_resultant_representative_nearby_aux P g hP
  refine ⟨a, b, U, hU, hconn, h0, ha, hb, ha0, hb0, fun p hp hap hbp ↦ ?_⟩
  have hR0ne : @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) R ≠ 0 := by
    intro hz
    apply hres
    apply Subtype.ext
    exact hR0.symm.trans hz
  have hRpne := spec_germ_ne_zero_of_preconnected_aux R U hU hconn hR 0 p h0 hp hR0ne
  intro hz
  apply hRpne
  rw [← hnear p hp hap hbp]
  exact congrArg Subtype.val hz

theorem spec_discriminant_ne_zero_nearby_aux {n : ℕ}
    (P : Polynomial (AnalyticGerm n)) (hP : P.Monic) (hdiscr : P.discr ≠ 0) :
    ∃ (a : ℕ → (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)),
      IsOpen U ∧ IsPreconnected U ∧ (0 : Fin n → ℂ) ∈ U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      ∀ p ∈ U, ∀ hap : ∀ j, AnalyticAt ℂ (a j) p,
        (gaga12_polynomialAt P a p hap).discr ≠ 0 := by
  obtain ⟨a, D, U, hU, hconn, h0, ha, hD, ha0, hD0, hlead, hDfibre, hnear⟩ :=
    spec_discriminant_representative_nearby_aux P hP
  refine ⟨a, U, hU, hconn, h0, ha, ha0, fun p hp hap ↦ ?_⟩
  have hD0ne : @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) D ≠ 0 := by
    intro hz
    apply hdiscr
    apply Subtype.ext
    exact hD0.symm.trans hz
  have hDpne := spec_germ_ne_zero_of_preconnected_aux D U hU hconn hD 0 p h0 hp hD0ne
  intro hz
  apply hDpne
  rw [← hnear p hp hap]
  exact congrArg Subtype.val hz

theorem spec_resultant_nonzero_fibre_avoids_common_root_at_aux {n : ℕ}
    (p : Fin n → ℂ) (A B : Polynomial (AnalyticGermAt n p)) (hA : A.Monic) :
    ∃ (a b : ℕ → (Fin n → ℂ) → ℂ) (R : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      U ∈ nhds p ∧ AnalyticOnNhd ℂ R U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧
      (∀ j, AnalyticOnNhd ℂ (b j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (a j) = (A.coeff j).1) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (b j) = (B.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) R = (A.resultant B).1 ∧
      ∀ x ∈ U, R x ≠ 0 → ∀ w : ℂ,
        (A.sum fun j _ ↦ monomial j (a j x)).eval w ≠ 0 ∨
          (B.sum fun j _ ↦ monomial j (b j x)).eval w ≠ 0 := by
  classical
  obtain ⟨e, _hvalue, hrep, hresult, _hdiscr⟩ :=
    spec_germ_translation_resultant_discr_aux n p
  let P := A.map e.toRingHom
  let Q := B.map e.toRingHom
  have hP : P.Monic := (spec_polynomial_translation_monic_degree e A).1.mpr hA
  obtain ⟨a₀, b₀, R₀, U₀, hU₀, hR₀, ha₀, hb₀, haP, hbQ, hres, hroot⟩ :=
    AnalyticDivisorAlgebraic10.spec_resultant_nonzero_fibre_avoids_common_root P Q hP
  let τ : (Fin n → ℂ) → (Fin n → ℂ) := fun x ↦ x - p
  let a : ℕ → (Fin n → ℂ) → ℂ := fun j x ↦ a₀ j (τ x)
  let b : ℕ → (Fin n → ℂ) → ℂ := fun j x ↦ b₀ j (τ x)
  let R : (Fin n → ℂ) → ℂ := fun x ↦ R₀ (τ x)
  let U : Set (Fin n → ℂ) := τ ⁻¹' U₀
  have hτ : AnalyticOnNhd ℂ τ Set.univ := fun x _ ↦ analyticAt_id.sub analyticAt_const
  have hτp : τ p = 0 := by simp [τ]
  have hU : U ∈ nhds p := by
    exact (hτ p (Set.mem_univ p)).continuousAt.preimage_mem_nhds (hτp ▸ hU₀)
  have ha : ∀ j, AnalyticOnNhd ℂ (a j) U := by
    intro j
    exact (ha₀ j).comp (hτ.mono (Set.subset_univ U)) (fun _ hx ↦ hx)
  have hb : ∀ j, AnalyticOnNhd ℂ (b j) U := by
    intro j
    exact (hb₀ j).comp (hτ.mono (Set.subset_univ U)) (fun _ hx ↦ hx)
  have hRa : AnalyticOnNhd ℂ R U :=
    hR₀.comp (hτ.mono (Set.subset_univ U)) (fun _ hx ↦ hx)
  have htranslate (f₀ : (Fin n → ℂ) → ℂ) (hf₀ : AnalyticOnNhd ℂ f₀ U₀) :
      e ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (fun x ↦ f₀ (τ x)),
          ⟨fun x ↦ f₀ (τ x),
            by
              change AnalyticAt ℂ (f₀ ∘ τ) p
              exact (hf₀ (τ p) (hτp ▸ mem_of_mem_nhds hU₀)).comp
                (hτ p (Set.mem_univ p)), rfl⟩⟩ =
        ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) f₀,
          ⟨f₀, hf₀ 0 (mem_of_mem_nhds hU₀), rfl⟩⟩ := by
    have hfback : AnalyticAt ℂ (fun x ↦ f₀ (τ x)) p := by
      change AnalyticAt ℂ (f₀ ∘ τ) p
      exact (hf₀ (τ p) (hτp ▸ mem_of_mem_nhds hU₀)).comp
        (hτ p (Set.mem_univ p))
    have htback : AnalyticAt ℂ (fun z ↦ f₀ (τ (p + z))) 0 := by
      convert hf₀ 0 (mem_of_mem_nhds hU₀) using 1 <;> simp [τ]
    calc
      e ⟨_, ⟨_, hfback, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0)
            (fun z ↦ f₀ (τ (p + z))), ⟨_, htback, rfl⟩⟩ :=
        hrep _ hfback htback
      _ = _ := Subtype.ext (Filter.EventuallyEq.germ_eq
        (Filter.Eventually.of_forall fun z ↦ by simp [τ]))
  refine ⟨a, b, R, U, hU, hRa, ha, hb, ?_, ?_, ?_, ?_⟩
  · intro j
    change (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (fun x ↦ a₀ j (τ x)),
      ⟨_, ha j p (mem_of_mem_nhds hU), rfl⟩⟩ : AnalyticGermAt n p).1 = _
    apply congrArg Subtype.val
    apply e.injective
    rw [htranslate (a₀ j) (ha₀ j)]
    exact Subtype.ext (by simpa [P, spec_polynomial_translation_coeff] using haP j)
  · intro j
    change (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (fun x ↦ b₀ j (τ x)),
      ⟨_, hb j p (mem_of_mem_nhds hU), rfl⟩⟩ : AnalyticGermAt n p).1 = _
    apply congrArg Subtype.val
    apply e.injective
    rw [htranslate (b₀ j) (hb₀ j)]
    exact Subtype.ext (by simpa [Q, spec_polynomial_translation_coeff] using hbQ j)
  · change (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (fun x ↦ R₀ (τ x)),
      ⟨_, hRa p (mem_of_mem_nhds hU), rfl⟩⟩ : AnalyticGermAt n p).1 = _
    apply congrArg Subtype.val
    apply e.injective
    rw [htranslate R₀ hR₀]
    have hres' :
        (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) R₀,
          ⟨R₀, hR₀ 0 (mem_of_mem_nhds hU₀), rfl⟩⟩ : AnalyticGerm n) =
            P.resultant Q := Subtype.ext hres
    exact hres'.trans (hresult A B)
  · intro x hx hRx w
    have hz := hroot (τ x) hx hRx w
    dsimp only [P, Q] at hz
    rw [Polynomial.sum, Polynomial.sum,
      Polynomial.support_map_of_injective A e.injective,
      Polynomial.support_map_of_injective B e.injective] at hz
    exact hz

theorem spec_discriminant_nonzero_fibre_simple_roots_at_aux {n : ℕ}
    (p : Fin n → ℂ) (A : Polynomial (AnalyticGermAt n p)) (hA : A.Monic) :
    ∃ (a : ℕ → (Fin n → ℂ) → ℂ) (D : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      U ∈ nhds p ∧ AnalyticOnNhd ℂ D U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (a j) = (A.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) D = A.discr.1 ∧
      ∀ x ∈ U, D x ≠ 0 → ∀ w : ℂ,
        (A.sum fun j _ ↦ monomial j (a j x)).eval w = 0 →
          (A.sum fun j _ ↦ monomial j (a j x)).derivative.eval w ≠ 0 := by
  classical
  obtain ⟨e, _hvalue, hrep, _hresult, hdiscr⟩ :=
    spec_germ_translation_resultant_discr_aux n p
  let P := A.map e.toRingHom
  have hP : P.Monic := (spec_polynomial_translation_monic_degree e A).1.mpr hA
  obtain ⟨a₀, D₀, U₀, hU₀, hD₀, ha₀, haP, hdisc, hroot⟩ :=
    AnalyticDivisorAlgebraic10.spec_discriminant_nonzero_fibre_simple_roots P hP
  let τ : (Fin n → ℂ) → (Fin n → ℂ) := fun x ↦ x - p
  let a : ℕ → (Fin n → ℂ) → ℂ := fun j x ↦ a₀ j (τ x)
  let D : (Fin n → ℂ) → ℂ := fun x ↦ D₀ (τ x)
  let U : Set (Fin n → ℂ) := τ ⁻¹' U₀
  have hτ : AnalyticOnNhd ℂ τ Set.univ := fun x _ ↦ analyticAt_id.sub analyticAt_const
  have hτp : τ p = 0 := by simp [τ]
  have hU : U ∈ nhds p := by
    exact (hτ p (Set.mem_univ p)).continuousAt.preimage_mem_nhds (hτp ▸ hU₀)
  have ha : ∀ j, AnalyticOnNhd ℂ (a j) U := by
    intro j
    exact (ha₀ j).comp (hτ.mono (Set.subset_univ U)) (fun _ hx ↦ hx)
  have hDa : AnalyticOnNhd ℂ D U :=
    hD₀.comp (hτ.mono (Set.subset_univ U)) (fun _ hx ↦ hx)
  have htranslate (f₀ : (Fin n → ℂ) → ℂ) (hf₀ : AnalyticOnNhd ℂ f₀ U₀) :
      e ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (fun x ↦ f₀ (τ x)),
          ⟨fun x ↦ f₀ (τ x),
            by
              change AnalyticAt ℂ (f₀ ∘ τ) p
              exact (hf₀ (τ p) (hτp ▸ mem_of_mem_nhds hU₀)).comp
                (hτ p (Set.mem_univ p)), rfl⟩⟩ =
        ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) f₀,
          ⟨f₀, hf₀ 0 (mem_of_mem_nhds hU₀), rfl⟩⟩ := by
    have hfback : AnalyticAt ℂ (fun x ↦ f₀ (τ x)) p := by
      change AnalyticAt ℂ (f₀ ∘ τ) p
      exact (hf₀ (τ p) (hτp ▸ mem_of_mem_nhds hU₀)).comp
        (hτ p (Set.mem_univ p))
    have htback : AnalyticAt ℂ (fun z ↦ f₀ (τ (p + z))) 0 := by
      convert hf₀ 0 (mem_of_mem_nhds hU₀) using 1 <;> simp [τ]
    calc
      e ⟨_, ⟨_, hfback, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0)
            (fun z ↦ f₀ (τ (p + z))), ⟨_, htback, rfl⟩⟩ :=
        hrep _ hfback htback
      _ = _ := Subtype.ext (Filter.EventuallyEq.germ_eq
        (Filter.Eventually.of_forall fun z ↦ by simp [τ]))
  refine ⟨a, D, U, hU, hDa, ha, ?_, ?_, ?_⟩
  · intro j
    change (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (fun x ↦ a₀ j (τ x)),
      ⟨_, ha j p (mem_of_mem_nhds hU), rfl⟩⟩ : AnalyticGermAt n p).1 = _
    apply congrArg Subtype.val
    apply e.injective
    rw [htranslate (a₀ j) (ha₀ j)]
    exact Subtype.ext (by simpa [P, spec_polynomial_translation_coeff] using haP j)
  · change (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (fun x ↦ D₀ (τ x)),
      ⟨_, hDa p (mem_of_mem_nhds hU), rfl⟩⟩ : AnalyticGermAt n p).1 = _
    apply congrArg Subtype.val
    apply e.injective
    rw [htranslate D₀ hD₀]
    have hdisc' :
        (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) D₀,
          ⟨D₀, hD₀ 0 (mem_of_mem_nhds hU₀), rfl⟩⟩ : AnalyticGerm n) = P.discr :=
      Subtype.ext hdisc
    exact hdisc'.trans (hdiscr A)
  · intro x hx hDx w hw
    have hz := hroot (τ x) hx hDx w
    dsimp only [P] at hz
    rw [Polynomial.sum, Polynomial.support_map_of_injective A e.injective] at hz
    exact hz hw

end HodgeLean.Foundations.AnalyticDivisorAlgebraic12
