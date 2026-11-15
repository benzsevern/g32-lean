import HodgeLean.Foundations.AnalyticDivisorAlgebraic11Defs

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic11

open Filter Polynomial Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6

private theorem gaga11_tendsto_add (n : ℕ) (p : Fin n → ℂ) :
    Tendsto (fun z : Fin n → ℂ ↦ p + z) (nhds 0) (nhds p) := by
  exact (continuous_const.add continuous_id).tendsto' 0 p (by simp)

private theorem gaga11_tendsto_sub (n : ℕ) (p : Fin n → ℂ) :
    Tendsto (fun z : Fin n → ℂ ↦ z - p) (nhds p) (nhds 0) := by
  exact (continuous_id.sub continuous_const).tendsto' p 0 (by simp)

/-- The translation ring equivalence between germs at `p` and germs at the origin.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
private def gaga11_translationEquiv (n : ℕ) (p : Fin n → ℂ) :
    AnalyticGermAt n p ≃+* AnalyticGerm n where
  toFun g := ⟨g.1.compTendsto (fun z ↦ p + z) (gaga11_tendsto_add n p), by
    obtain ⟨f, hf, hfg⟩ := g.2
    refine ⟨fun z ↦ f (p + z), ?_, ?_⟩
    · exact AnalyticAt.comp_of_eq (g := f) (f := fun z ↦ p + z) hf
        (analyticAt_const.add analyticAt_id) (by simp)
    · rw [← hfg]; rfl⟩
  invFun g := ⟨g.1.compTendsto (fun z ↦ z - p) (gaga11_tendsto_sub n p), by
    obtain ⟨f, hf, hfg⟩ := g.2
    refine ⟨fun z ↦ f (z - p), ?_, ?_⟩
    · exact AnalyticAt.comp_of_eq (g := f) (f := fun z ↦ z - p) hf
        (analyticAt_id.sub analyticAt_const) (by simp)
    · rw [← hfg]; rfl⟩
  left_inv g := by
    obtain ⟨g, f, hf, rfl⟩ := g
    apply Subtype.ext
    change (@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (fun z ↦ f (p + (z - p)))) = _
    simp only [add_sub_cancel]
  right_inv g := by
    obtain ⟨g, f, hf, rfl⟩ := g
    apply Subtype.ext
    change (@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun z ↦ f (p + z - p))) = _
    simp only [add_sub_cancel_left]
  map_mul' g h := by
    obtain ⟨g, f, hf, rfl⟩ := g
    obtain ⟨h, k, hk, rfl⟩ := h
    rfl
  map_add' g h := by
    obtain ⟨g, f, hf, rfl⟩ := g
    obtain ⟨h, k, hk, rfl⟩ := h
    rfl

theorem spec_germ_translation_equiv_aux (n : ℕ) (p : Fin n → ℂ) :
    ∃ e : AnalyticGermAt n p ≃+* AnalyticGerm n,
      (∀ g : AnalyticGermAt n p,
        analyticGermValue n (e g) = analyticGermAtValue n p g) ∧
      ∀ (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
          (ht : AnalyticAt ℂ (fun z ↦ f (p + z)) 0),
        e ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) f, ⟨f, hf, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun z ↦ f (p + z)),
            ⟨fun z ↦ f (p + z), ht, rfl⟩⟩ := by
  refine ⟨gaga11_translationEquiv n p, ?_, fun f hf ht ↦ rfl⟩
  rintro ⟨g, f, hf, rfl⟩
  change (@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun z ↦ f (p + z))).value =
    (@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) f).value
  simp only [Filter.Germ.value_ofFun, add_zero]

theorem spec_germ_translation_zero_aux (n : ℕ) :
    ∃ e : AnalyticGermAt n 0 ≃+* AnalyticGerm n,
      ∀ g : AnalyticGermAt n 0, (e g).1 = g.1 := by
  obtain ⟨e, -, he⟩ := spec_germ_translation_equiv_aux n 0
  refine ⟨e, ?_⟩
  rintro ⟨g, f, hf, rfl⟩
  have ht : AnalyticAt ℂ (fun z ↦ f (0 + z)) 0 := by simpa only [zero_add] using hf
  rw [he f hf ht]
  simp only [zero_add]

theorem spec_polynomial_translation_coeff_aux {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P : Polynomial R) (j : ℕ) :
    (P.map e.toRingHom).coeff j = e (P.coeff j) := by
  exact coeff_map e.toRingHom j

theorem spec_polynomial_translation_monic_degree_aux {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P : Polynomial R) :
    ((P.map e.toRingHom).Monic ↔ P.Monic) ∧
      (P.map e.toRingHom).natDegree = P.natDegree := by
  exact ⟨e.injective.monic_map_iff.symm, natDegree_map_eq_of_injective e.injective P⟩

theorem spec_polynomial_translation_coprime_aux {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P Q : Polynomial R) :
    IsCoprime (P.map e.toRingHom) (Q.map e.toRingHom) ↔ IsCoprime P Q := by
  constructor
  · intro h
    change IsCoprime ((Polynomial.mapEquiv e) P) ((Polynomial.mapEquiv e) Q) at h
    convert h.map (Polynomial.mapEquiv e).symm.toRingHom using 1 <;>
      exact ((Polynomial.mapEquiv e).symm_apply_apply _).symm
  · intro h
    exact h.map (Polynomial.mapEquiv e).toRingHom

theorem spec_polynomial_translation_irreducible_aux {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P : Polynomial R) :
    Irreducible (P.map e.toRingHom) ↔ Irreducible P := by
  exact MulEquiv.irreducible_iff (f := (Polynomial.mapEquiv e).toMulEquiv)

theorem spec_polynomial_translation_units_aux {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (x : R) : IsUnit (e x) ↔ IsUnit x := by
  constructor
  · intro h
    convert h.map e.symm.toMonoidHom using 1
    exact (e.symm_apply_apply x).symm
  · intro h
    exact h.map e.toMonoidHom

theorem spec_translated_representative_aux {n : ℕ} (p : Fin n → ℂ)
    (f : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ))
    (hp : p ∈ U) (hU : U ∈ nhds p) (hf : AnalyticOnNhd ℂ f U) :
    gaga11_translatedSet p U ∈ nhds (0 : Fin n → ℂ) ∧
      AnalyticOnNhd ℂ (fun z ↦ f (p + z)) (gaga11_translatedSet p U) ∧
      ∀ z ∈ gaga11_translatedSet p U, (fun y ↦ f (p + y)) z = f (p + z) := by
  have ht : AnalyticOnNhd ℂ (fun z : Fin n → ℂ ↦ p + z) (gaga11_translatedSet p U) := by
    fun_prop
  refine ⟨?_, ?_, ?_⟩
  · show (fun z : Fin n → ℂ ↦ p + z) ⁻¹' U ∈ nhds 0
    apply (by fun_prop : ContinuousAt (fun z : Fin n → ℂ ↦ p + z) 0).preimage_mem_nhds
    simpa using hU
  · simpa only [Function.comp_def] using hf.comp ht (by
      intro z hz
      exact hz)
  · intros
    rfl

theorem spec_simultaneous_representatives_translate_aux {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) (a b : ℕ → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (p : Fin n → ℂ) (hUp : U ∈ nhds p)
    (ha : ∀ j, AnalyticOnNhd ℂ (a j) U) (hb : ∀ j, AnalyticOnNhd ℂ (b j) U) :
    ∃ (e : AnalyticGermAt n p ≃+* AnalyticGerm n)
        (A B : Polynomial (AnalyticGermAt n p)),
      A = P.sum (fun j _ ↦ monomial j
        ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (a j),
          ⟨a j, ha j p (mem_of_mem_nhds hUp), rfl⟩⟩) ∧
      B = g.sum (fun j _ ↦ monomial j
        ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (b j),
          ⟨b j, hb j p (mem_of_mem_nhds hUp), rfl⟩⟩) ∧
      (∀ j ∈ P.support, (e (A.coeff j)).1 =
        @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun z ↦ a j (p + z))) ∧
      (∀ j ∈ g.support, (e (B.coeff j)).1 =
        @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun z ↦ b j (p + z))) := by
  obtain ⟨e, _, he⟩ := spec_germ_translation_equiv_aux n p
  let ca : ℕ → AnalyticGermAt n p := fun j ↦
    ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (a j),
      ⟨a j, ha j p (mem_of_mem_nhds hUp), rfl⟩⟩
  let cb : ℕ → AnalyticGermAt n p := fun j ↦
    ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds p) (b j),
      ⟨b j, hb j p (mem_of_mem_nhds hUp), rfl⟩⟩
  let A := P.sum (fun j _ ↦ monomial j (ca j))
  let B := g.sum (fun j _ ↦ monomial j (cb j))
  refine ⟨e, A, B, rfl, rfl, ?_, ?_⟩
  · intro j hj
    have hcoeff : A.coeff j = ca j := by
      simp [A, Polynomial.sum, coeff_monomial, hj, ca]
    rw [hcoeff]
    have haj : AnalyticAt ℂ (a j) (p + 0) := by
      simpa using ha j p (mem_of_mem_nhds hUp)
    have h := he (a j) (ha j p (mem_of_mem_nhds hUp)) (haj.comp (by fun_prop))
    change e (ca j) = _ at h
    exact congrArg (fun x ↦ x.1) h
  · intro j hj
    have hcoeff : B.coeff j = cb j := by
      simp [B, Polynomial.sum, coeff_monomial, hj, cb]
    rw [hcoeff]
    have hbj : AnalyticAt ℂ (b j) (p + 0) := by
      simpa using hb j p (mem_of_mem_nhds hUp)
    have h := he (b j) (hb j p (mem_of_mem_nhds hUp)) (hbj.comp (by fun_prop))
    change e (cb j) = _ at h
    exact congrArg (fun x ↦ x.1) h

theorem spec_weierstrass_translation_falsification_aux : ∀ ε : ℝ, 0 < ε →
    ∃ p : Fin 1 → ℂ, ‖p‖ < ε ∧
      IsWeierstrassPolynomialAt
        (X + C (gaga11_coordinateGermAt 0) : Polynomial (AnalyticGermAt 1 0)) ∧
      ¬ IsWeierstrassPolynomialAt
        (X + C (gaga11_coordinateGermAt p) : Polynomial (AnalyticGermAt 1 p)) := by
  intro ε hε
  have hval : ∀ q : Fin 1 → ℂ, analyticGermAtValue 1 q (gaga11_coordinateGermAt q) = q 0 := by
    intro q
    change (@Filter.Germ.ofFun (Fin 1 → ℂ) ℂ (nhds q) (fun z ↦ z 0)).value = q 0
    simp only [Filter.Germ.value_ofFun]
  refine ⟨fun _ ↦ ((ε / 2 : ℝ) : ℂ), ?_, ?_, ?_⟩
  · rw [pi_norm_const, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  · refine ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; exact one_pos, ?_⟩
    intro j hj
    rw [natDegree_X_add_C] at hj
    obtain rfl : j = 0 := by omega
    rw [coeff_add, coeff_X_zero, coeff_C_zero, zero_add, hval]
    rfl
  · rintro ⟨-, -, h⟩
    have h0 := h 0 (by rw [natDegree_X_add_C]; exact one_pos)
    rw [coeff_add, coeff_X_zero, coeff_C_zero, zero_add, hval] at h0
    have : (ε / 2 : ℝ) ≠ 0 := by positivity
    exact this (by exact_mod_cast h0)

end HodgeLean.Foundations.AnalyticDivisorAlgebraic11
