import HodgeLean.Foundations.AnalyticGermLyingOverProofs

/-! # Finite analytic images and component comparison

Implication from finite proper representatives to analytic images, from faithful finite parameters to
neighbourhood surjectivity. Component dimensions use calibrated parameters.
Coefficient continuation, exact equations and point extension remain deferred.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

/-- Primitive linear coordinate, distinguished minimal relation and a common denominator.
The Bezout identity includes the branch locus in the denominator's zero germ.
Source: Gunning--Rossi, III.B--C, local parametrization; Nicolaescu, Notes on the Topology of Complex Singularities, Theorem 9.2.11 and Remark 9.2.12(b). -/
theorem adim7_primitive_form (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i)) :
    ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n)
      (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
      (R : Fin n → Polynomial (AnalyticGerm d))
      (B C : Polynomial (AnalyticGerm d)),
      v.val = Germ.ofFun (fun z ↦ ℓ z) ∧
      (d < n → ∃ z, π z = 0 ∧ ℓ z ≠ 0) ∧
      IsWeierstrassPolynomial Q ∧ δ ≠ 0 ∧
      B * Q + C * Q.derivative = Polynomial.C δ ∧
      (∀ T : Polynomial (AnalyticGerm d),
        T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T) ∧
      ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
        (R i).eval₂ θ (Ideal.Quotient.mk P v) :=
  adim7_primitive_form_aux n d P hP π θ hfinite hinj hcomp c hc

/-- Roots of one primitive relation realize the simultaneous analytic equations.
Coefficient representatives and the common denominator are explicit data.
Source: Gunning--Rossi, III.C, local parametrization; Nicolaescu, Theorem 9.2.11 and Remark 9.2.12(b). -/
theorem adim7_roots_off_discriminant (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n)
    (hv : v.val = Germ.ofFun (fun z ↦ ℓ z))
    (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hQ : IsWeierstrassPolynomial Q) (hδ : δ ≠ 0)
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧
      Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : AnalyticAt ℂ Δ 0) (hΔrep : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, AnalyticAt ℂ ((r j).coeff i) 0 ∧
      Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (m : ℕ) (g : Fin m → AnalyticGerm n) (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val) :
    ∃ V : Set (Fin d → ℂ), IsOpen V ∧ (0 : Fin d → ℂ) ∈ V ∧
      ∀ w ∈ V, Δ w ≠ 0 → ∃ t : ℂ,
        q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 ∧
        let z : Fin n → ℂ := fun i ↦
          (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w
        z ∈ U ∧ π z = w ∧ ℓ z = t ∧ ∀ j, f j z = 0 :=
  adim7_roots_off_discriminant_aux n d P hP π θ hfinite hinj hcomp c hc ℓ v hv Q δ R hQ hδ hmin hcoord q Δ r hq hΔ hΔrep hr m g hgen f U hU hU0 hf hrep

/-- A proper image containing the complement of a nonzero analytic discriminant
fills a connected parameter neighbourhood.
Source: Gunning--Rossi, I.A, identity theorem, and III.C, proper finite representatives. -/
theorem adim7_close_across_discriminant (d : ℕ)
    (V : Set (Fin d → ℂ)) (hV : IsOpen V) (hV0 : (0 : Fin d → ℂ) ∈ V)
    (hconn : IsPreconnected V) (Δ : (Fin d → ℂ) → ℂ)
    (hΔ : AnalyticOnNhd ℂ Δ V) (hne : ¬ (Δ =ᶠ[𝓝 (0 : Fin d → ℂ)] fun _ ↦ 0))
    (Z : Type*) [TopologicalSpace Z] (p : Z → V) (hproper : IsProperMap p)
    (hroot : ∀ w : V, Δ w.val ≠ 0 → ∃ z, p z = w) :
    Function.Surjective p :=
  adim7_close_across_discriminant_aux d V hV hV0 hconn Δ hΔ hne Z p hproper hroot

/-- Source: Gunning--Rossi, III.B--C, local parametrization; Grauert--Remmert, Coherent Analytic Sheaves, Chapter 3. -/
theorem adim7_surjective_projection (n d m : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
      Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (g : Fin m → AnalyticGerm n) (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val) :
    ∃ (W : Set (Fin n → ℂ)) (V : Set (Fin d → ℂ)),
      IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
      IsOpen V ∧ (0 : Fin d → ℂ) ∈ V ∧
      ∃ p : {z : Fin n → ℂ // z ∈ W ∧ ∀ j, f j z = 0} → V,
        (∀ z, (p z).val = π z.val) ∧ IsProperMap p ∧
        (∀ w : V, (p ⁻¹' {w}).Finite) ∧ Function.Surjective p ∧
        ∀ z, (p z).val = 0 → z.val = 0 :=
  adim7_surjective_projection_aux n d m P hP π θ hfinite hinj hcomp g hgen f U hU hU0 hf hrep

/-- Source: Gunning--Rossi, III.B--C, irreducible components and dimension; de Jong--Pfister, Chapters 3--4. -/
theorem adim7_component_comparison (n : ℕ) (A : Set (Fin (n + 1) → ℂ))
    (x : Fin (n + 1) → ℂ) (hx : x ∈ A)
    (U : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U) (hxU : x ∈ U)
    (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hA : ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0))
    (hdim : ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A x)).minimalPrimes,
      (1 : WithBot ℕ∞) ≤ ringKrullDim (AnalyticGerm (n + 1) ⧸ P)) :
    ∃ F : Finset (Ideal (AnalyticGerm (n + 1))),
      (F : Set (Ideal (AnalyticGerm (n + 1)))) =
        (adim2_ideal (n + 1) (adim2_germ (n + 1) A x)).minimalPrimes ∧
      adim2_germ (n + 1) A x = F.sup (adim2_zeroSet (n + 1)) ∧
      ∀ P ∈ F, adim2_zeroSet (n + 1) P ≤ adim2_germ (n + 1) A x ∧
        ∃ (d : ℕ) (π : (Fin (n + 1) → ℂ) →L[ℂ] (Fin d → ℂ))
          (θ : AnalyticGerm d →+* (AnalyticGerm (n + 1) ⧸ P)),
          1 ≤ d ∧ d ≤ n + 1 ∧ θ.Finite ∧ Function.Injective θ ∧
          (∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
            AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (n + 1),
            Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b) ∧
          ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (d : WithBot ℕ∞) :=
  adim7_component_comparison_aux n A x hx U hU hxU m f hf hA hdim

/-- W2: the faithful identity projection of the full line.
Source: Gunning--Rossi, III.C, finite parametrization. -/
example : ∃ (W V : Set (Fin 1 → ℂ)),
    IsOpen W ∧ (0 : Fin 1 → ℂ) ∈ W ∧ W ⊆ univ ∧
    IsOpen V ∧ (0 : Fin 1 → ℂ) ∈ V ∧
    ∃ p : {z : Fin 1 → ℂ // z ∈ W ∧
      ∀ j : Fin 0, (Fin.elim0 j : (Fin 1 → ℂ) → ℂ) z = 0} → V,
      (∀ z, (p z).val = z.val) ∧ IsProperMap p ∧
      (∀ w : V, (p ⁻¹' {w}).Finite) ∧ Function.Surjective p ∧
      ∀ z, (p z).val = 0 → z.val = 0 := by
  let : NoZeroDivisors (AnalyticGerm 1) := analyticGerm_noZeroDivisors_succ
  let : IsDomain (AnalyticGerm 1) := {}
  have hcomp : ∀ (a : AnalyticGerm 1) (h : (Fin 1 → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm 1,
      Germ.ofFun (fun z ↦ h ((ContinuousLinearMap.id ℂ (Fin 1 → ℂ)) z)) = b.val →
        Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1)) a = Ideal.Quotient.mk ⊥ b := by
    intro a h _ ha b hb
    rw [show a = b from Subtype.ext (ha.symm.trans hb)]
  have hinj : Function.Injective (Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1))) := by
    intro a b hab
    simpa only [Ideal.mem_bot, sub_eq_zero] using
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp hab
  simpa using adim7_surjective_projection 1 1 0 ⊥ inferInstance
    (ContinuousLinearMap.id ℂ (Fin 1 → ℂ)) (Ideal.Quotient.mk ⊥)
    (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hinj hcomp
    (fun j : Fin 0 ↦ Fin.elim0 j) (by simp) (fun j : Fin 0 ↦ Fin.elim0 j)
    univ isOpen_univ (mem_univ _) (by intro j; exact Fin.elim0 j)
    (by intro j; exact Fin.elim0 j)

/-- W3: a nonzero ambient coordinate is killed modulo a nonzero prime.
Source: Gunning--Rossi, III.B, the maximal ideal of the analytic local ring. -/
example : (analyticGermMaximalIdeal 2).IsPrime ∧ analyticGermMaximalIdeal 2 ≠ ⊥ ∧
    adim_coordinate 1 ≠ 0 ∧
    Ideal.Quotient.mk (analyticGermMaximalIdeal 2) (adim_coordinate 1) = 0 := by
  have hne : adim_coordinate 1 ≠ 0 := by
    intro h
    have he : (fun z : Fin 2 → ℂ ↦ z (Fin.last 1)) =ᶠ[𝓝 0] fun _ ↦ 0 :=
      Germ.coe_eq.mp (congrArg Subtype.val h)
    have hd := he.fderiv_eq (𝕜 := ℂ)
    have hv := congrArg (fun f : (Fin 2 → ℂ) →L[ℂ] ℂ ↦ f (fun _ ↦ 1)) hd
    rw [fderiv_apply (𝕜 := ℂ) differentiableAt_id, fderiv_fun_id] at hv
    simp at hv
  have hm : adim_coordinate 1 ∈ analyticGermMaximalIdeal 2 := rfl
  refine ⟨RingHom.ker_isPrime (analyticGermValue 2), ?_, hne,
    Ideal.Quotient.eq_zero_iff_mem.mpr hm⟩
  intro h
  rw [h, Ideal.mem_bot] at hm
  exact hne hm

/-- W5: component comparison at the crossing point of the plane node.
The positive dimension premise is derived from the axis through the origin.
Source: Gunning--Rossi, III.C, dimension of analytic components. -/
example : ∃ F : Finset (Ideal (AnalyticGerm 2)),
    (F : Set (Ideal (AnalyticGerm 2))) =
      (adim2_ideal 2 (adim2_germ 2 {z : Fin 2 → ℂ | z 0 * z 1 = 0} 0)).minimalPrimes ∧
    adim2_germ 2 {z : Fin 2 → ℂ | z 0 * z 1 = 0} 0 = F.sup (adim2_zeroSet 2) ∧
    ∀ P ∈ F, ∃ d : ℕ, 1 ≤ d ∧
      ringKrullDim (AnalyticGerm 2 ⧸ P) = (d : WithBot ℕ∞) := by
  let A : Set (Fin 2 → ℂ) := {z | z 0 * z 1 = 0}
  let S := adim2_germ 2 A 0
  let I := adim2_ideal 2 S
  let : IsLocalRing (AnalyticGerm 2) := by
    apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
    intro a b hab
    rw [analyticGerm_isUnit_iff] at hab
    simp only [map_add] at hab
    by_cases ha : analyticGermValue 2 a = 0
    · right
      rw [analyticGerm_isUnit_iff]
      simpa [ha] using hab
    · left
      rwa [analyticGerm_isUnit_iff]
  have hdim : ∀ P ∈ I.minimalPrimes,
      (1 : WithBot ℕ∞) ≤ ringKrullDim (AnalyticGerm 2 ⧸ P) := by
    intro P hP
    apply le_of_not_gt
    intro hdim
    let : P.IsPrime := hP.isPrime
    have hPm : P.IsMaximal := by
      apply (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mpr
      let : Ring.KrullDimLE 0 (AnalyticGerm 2 ⧸ P) := Ring.krullDimLE_iff.mpr <|
        le_of_not_gt (fun hpos ↦
          not_lt_of_ge ((WithBot.one_le_iff_pos _).mpr hpos) hdim)
      exact Ring.KrullDimLE.isField_of_isDomain
    have hPeq : P = IsLocalRing.maximalIdeal (AnalyticGerm 2) :=
      IsLocalRing.eq_maximalIdeal hPm
    have hIP : I = P := by
      have hunique : ∀ Q ∈ I.minimalPrimes, Q = P := by
        intro Q hQ
        have hQP : Q ≤ P := hPeq.symm ▸ IsLocalRing.le_maximalIdeal hQ.isPrime.ne_top
        exact hQP.antisymm (hP.2 hQ.1 hQP)
      have hrad : I.radical = I := adim2_radical 2 S
      rw [← hrad, ← Ideal.sInf_minimalPrimes]
      apply le_antisymm (sInf_le hP)
      exact le_sInf fun Q hQ ↦ (hunique Q hQ).ge
    have hmax : (analyticGermMaximalIdeal 2).IsMaximal := by
      apply RingHom.ker_isMaximal_of_surjective
      intro c
      exact ⟨⟨Germ.ofFun (fun _ ↦ c), fun _ ↦ c, analyticAt_const, rfl⟩, rfl⟩
    have hPval : P = analyticGermMaximalIdeal 2 :=
      hPeq.trans (IsLocalRing.eq_maximalIdeal hmax).symm
    have hcoord : adim_coordinate 1 ∈ I := by
      rw [hIP, hPval]
      rfl
    have he : ∀ᶠ z in 𝓝 (0 : Fin 2 → ℂ), z 0 * z 1 = 0 → z 1 = 0 := by
      change ∀ᶠ z in 𝓝 (0 : Fin 2 → ℂ), (0 + z) ∈ A → z (Fin.last 1) = 0 at hcoord
      simpa [A, Fin.last] using hcoord
    have hc : ContinuousAt (fun t : ℂ ↦ (![0, t] : Fin 2 → ℂ)) 0 := by fun_prop
    have he' : ∀ᶠ t in 𝓝 (0 : ℂ), t = 0 := by
      have hz : (![0, 0] : Fin 2 → ℂ) = 0 := by ext i; fin_cases i <;> rfl
      have ht := hc.eventually (show ∀ᶠ z in 𝓝 (![0, 0] : Fin 2 → ℂ),
        z 0 * z 1 = 0 → z 1 = 0 from hz.symm ▸ he)
      filter_upwards [ht] with t ht
      exact ht (by simp)
    have hopen : IsOpen ({0} : Set ℂ) := by
      rw [isOpen_iff_mem_nhds]
      rintro y rfl
      exact he'
    exact not_isOpen_singleton (0 : ℂ) hopen
  have hf : AnalyticOnNhd ℂ (fun z : Fin 2 → ℂ ↦ z 0 * z 1) univ :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticOnNhd _).mul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticOnNhd _)
  obtain ⟨F, hprimes, hcover, hF⟩ := adim7_component_comparison 1 A 0 (by simp [A])
    univ isOpen_univ (mem_univ _) 1 (fun _ z ↦ z 0 * z 1) (fun _ ↦ hf)
    (fun z _ ↦ ⟨fun h _ ↦ h, fun h ↦ h 0⟩) hdim
  refine ⟨F, hprimes, hcover, ?_⟩
  intro P hP
  obtain ⟨_, d, π, θ, hd, _, _, _, _, he⟩ := hF P hP
  exact ⟨d, hd, he⟩

/-- The two distinct axes meet at the anchor used in W5.
Source: Gunning--Rossi, III.A, reducible analytic germs. -/
example : adim2_germ 2 {z : Fin 2 → ℂ | z 0 * z 1 = 0} 0 =
    adim2_germ 2 {z : Fin 2 → ℂ | z 0 = 0} 0 ⊔
      adim2_germ 2 {z : Fin 2 → ℂ | z 1 = 0} 0 := by
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall (fun z ↦ propext (by simp [mul_eq_zero]))

/-- The faithful full-line parameter algebra supplies primitive-form data.
Source: Gunning--Rossi, III.C, local parametrization. -/
example :
    ∃ (ℓ : (Fin 1 → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm 1)
      (Q : Polynomial (AnalyticGerm 1)) (δ : AnalyticGerm 1)
      (R : Fin 1 → Polynomial (AnalyticGerm 1))
      (B C : Polynomial (AnalyticGerm 1)),
      v.val = Germ.ofFun (fun z ↦ ℓ z) ∧
      (1 < 1 → ∃ z, (ContinuousLinearMap.id ℂ (Fin 1 → ℂ)) z = 0 ∧ ℓ z ≠ 0) ∧
      IsWeierstrassPolynomial Q ∧ δ ≠ 0 ∧
      B * Q + C * Q.derivative = Polynomial.C δ ∧
      (∀ T : Polynomial (AnalyticGerm 1),
        T.eval₂ (Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1))) (Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1)) v) = 0 ↔ Q ∣ T) ∧
      ∀ i : Fin 1, (Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1))) δ * Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1)) (adim_coordinate 0) =
        (R i).eval₂ (Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1))) (Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1)) v) := by
  let : NoZeroDivisors (AnalyticGerm 1) := analyticGerm_noZeroDivisors_succ
  let : IsDomain (AnalyticGerm 1) := {}
  have hcomp : ∀ (a : AnalyticGerm 1) (h : (Fin 1 → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm 1,
      Germ.ofFun (fun z ↦ h ((ContinuousLinearMap.id ℂ (Fin 1 → ℂ)) z)) = b.val →
        Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1)) a = Ideal.Quotient.mk ⊥ b := by
    intro a h _ ha b hb
    rw [show a = b from Subtype.ext (ha.symm.trans hb)]
  have hinj : Function.Injective (Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1))) := by
    intro a b hab
    simpa only [Ideal.mem_bot, sub_eq_zero] using
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp hab
  exact adim7_primitive_form 1 1 ⊥ inferInstance
    (ContinuousLinearMap.id ℂ _) (Ideal.Quotient.mk ⊥)
    (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hinj hcomp
    (fun _ ↦ adim_coordinate 0) (by intro i; fin_cases i; rfl)

/-- A constant discriminant and the identity map test closure on the full line.
Source: Gunning--Rossi, I.A, identity theorem. -/
example : Function.Surjective (fun w : {w : Fin 1 → ℂ // w ∈ (univ : Set (Fin 1 → ℂ))} ↦ w) := by
  apply adim7_close_across_discriminant 1 univ isOpen_univ (mem_univ _)
    isPreconnected_univ (fun _ ↦ 1) analyticOnNhd_const
    (by intro h; have := h.self_of_nhds; norm_num at this)
    (univ : Set (Fin 1 → ℂ)) id isProperMap_id
  intro w _
  exact ⟨w, rfl⟩

/-- The identity parameter algebra realizes a shared root and its coordinate.
Source: Gunning--Rossi, III.C, local parametrization. -/
example : ∃ V : Set (Fin 1 → ℂ), IsOpen V ∧ (0 : Fin 1 → ℂ) ∈ V ∧
    ∀ w ∈ V, ∃ t : ℂ, t = 0 ∧ (fun _ : Fin 1 ↦ w 0) = w := by
  let : NoZeroDivisors (AnalyticGerm 1) := analyticGerm_noZeroDivisors_succ
  let : IsDomain (AnalyticGerm 1) := {}
  have hinj : Function.Injective (Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1))) := by
    intro a b hab
    simpa only [Ideal.mem_bot, sub_eq_zero] using
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp hab
  have H := adim7_roots_off_discriminant 1 1 ⊥ inferInstance
    (ContinuousLinearMap.id ℂ _) (Ideal.Quotient.mk ⊥)
    (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hinj
    (fun a h _ ha b hb ↦ congrArg (Ideal.Quotient.mk ⊥)
      (Subtype.ext (ha.symm.trans hb)))
    (fun _ ↦ adim_coordinate 0) (by intro i; fin_cases i; rfl)
    0 0 rfl X 1 (fun _ ↦ C (adim_coordinate 0))
    (by exact ⟨monic_X, by simp [analyticGermMaximalIdeal]⟩) one_ne_zero
    (by intro T; simp only [map_zero, eval₂_at_zero, X_dvd_iff,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot])
    (by intro i; simp)
    X (fun _ ↦ 1) (fun _ ↦ C (fun w : Fin 1 → ℂ ↦ w 0))
    (by intro i; simp only [coeff_X]; split_ifs <;> exact ⟨analyticAt_const, rfl⟩)
    analyticAt_const rfl
    (by
      intro j i
      simp only [coeff_C]
      split_ifs
      · exact ⟨(ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0, rfl⟩
      · exact ⟨analyticAt_const, rfl⟩)
    0 (fun j ↦ Fin.elim0 j) (by simp) (fun j ↦ Fin.elim0 j)
    univ isOpen_univ (mem_univ _) (by intro j; exact Fin.elim0 j)
    (by intro j; exact Fin.elim0 j)
  obtain ⟨V, hV, hV0, hroot⟩ := H
  refine ⟨V, hV, hV0, ?_⟩
  intro w hw
  obtain ⟨t, ht, _, hp, _⟩ := hroot w hw one_ne_zero
  exact ⟨t, by simpa using ht, by simpa using hp⟩

/-- W6: a cusp has distinct points over the same parameter, arbitrarily near zero.
Source: Chirka, Complex Analytic Sets, §3, branched finite projections. -/
example (t : ℂ) (ht : t ≠ 0) :
    (t ^ 3) ^ 2 = (t ^ 2) ^ 3 ∧ ((-t) ^ 3) ^ 2 = ((-t) ^ 2) ^ 3 ∧
    (t ^ 2 = (-t) ^ 2) ∧
    (![t ^ 2, t ^ 3] : Fin 2 → ℂ) ≠ ![(-t) ^ 2, (-t) ^ 3] := by
  refine ⟨by ring, by ring, by ring, ?_⟩
  intro he
  have h := congrFun he 1
  have hneg : t ^ 3 = -(t ^ 3) := by
    calc
      t ^ 3 = (-t) ^ 3 := h
      _ = -(t ^ 3) := by ring
  have hz : t ^ 3 = 0 := by linear_combination (1 / 2 : ℂ) * hneg
  exact (pow_ne_zero 3 ht) hz

/-- W7: the explicit cusp parametrization tends to its branching point.
Source: Chirka, Complex Analytic Sets, §3, local branched projections. -/
example : Tendsto (fun t : ℂ ↦ (![t ^ 2, t ^ 3] : Fin 2 → ℂ)) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun t : ℂ ↦ (![t ^ 2, t ^ 3] : Fin 2 → ℂ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hz : (![0, 0] : Fin 2 → ℂ) = 0 := by
    ext i
    fin_cases i <;> rfl
  simpa only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), hz]
    using hc.tendsto 0

end HodgeLean.Foundations
