import HodgeLean.Foundations.AnalyticGermNormalizationProofs

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

/-- Source: Gunning--Rossi, III.B--C, local parametrization; de Jong--Pfister, Chapter 3, finite analytic algebras. -/
theorem adim5_prime_step (n : ℕ) (P : Ideal (AnalyticGerm (n + 1)))
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
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) :=
  adim5_prime_step_aux n P hP hP0

/-- Source: Gunning--Rossi, III.B--C, local parametrization; Grauert--Remmert, Coherent Analytic Sheaves, Chapter 3. -/
theorem adim5_finite_parameters (n : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) :
    ∃ (d : ℕ) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
      (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)),
      d ≤ n ∧ θ.Finite ∧ Function.Injective θ ∧
      (∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ), AnalyticAt ℂ f 0 →
        Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
        Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b) ∧
      ringKrullDim (AnalyticGerm d) = ringKrullDim (AnalyticGerm n ⧸ P) :=
  adim5_finite_parameters_aux n P hP

/-- Source: de Jong--Pfister, Local Analytic Geometry, Chapters 3--4, finite local analytic algebras; Grauert--Remmert, Coherent Analytic Sheaves, Chapter 3. -/
theorem adim5_distinguished_relation (n d : ℕ) (P : Ideal (AnalyticGerm n)) (hP : P ≠ ⊤)
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (hθ : θ.Finite)
    (hlocal : ∀ (a : AnalyticGerm d) (b : AnalyticGerm n),
      θ a = Ideal.Quotient.mk P b → analyticGermValue d a = analyticGermValue n b)
    (g : AnalyticGerm n) (hg : analyticGermValue n g = 0) :
    ∃ W : Polynomial (AnalyticGerm d), IsWeierstrassPolynomial W ∧
      W.eval₂ θ (Ideal.Quotient.mk P g) = 0 :=
  adim5_distinguished_relation_aux n d P hP θ hθ hlocal g hg

/-- Source: Gunning--Rossi, III.B--C, distinguished polynomials and finite projection; Chirka, Complex Analytic Sets, §§3--4. -/
theorem adim5_closed_projection (n m : ℕ) (k : Fin m → ℕ) (hk : ∀ j, 0 < k j)
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
        ∀ z, (p z).val = 0 → z.val = 0 :=
  adim5_closed_projection_aux n m k hk a ha ha0 U S hU hU0 hS hS0 heq

/-- W1: the maximal ideal of the two-variable germ ring supplies a nonzero prime.
Source: Gunning--Rossi, III.B, prime analytic germs. -/
example : ∃ (e : AnalyticGerm 2 ≃+* AnalyticGerm 2)
    (ι : Polynomial (AnalyticGerm 1) →+* AnalyticGerm 2),
    ringKrullDim (AnalyticGerm 1 ⧸
      ((analyticGermMaximalIdeal 2).map e.toRingHom).comap (ι.comp C)) =
      ringKrullDim (AnalyticGerm 2 ⧸ analyticGermMaximalIdeal 2) := by
  have hne : adim_coordinate 1 ≠ 0 := by
    intro h
    have he : (fun z : Fin 2 → ℂ ↦ z (Fin.last 1)) =ᶠ[𝓝 0] fun _ ↦ 0 :=
      Germ.coe_eq.mp (congrArg Subtype.val h)
    have hd := he.fderiv_eq (𝕜 := ℂ)
    have hv := congrArg (fun f : (Fin 2 → ℂ) →L[ℂ] ℂ ↦ f (fun _ ↦ 1)) hd
    rw [fderiv_apply (𝕜 := ℂ) differentiableAt_id, fderiv_fun_id] at hv
    simp at hv
  have hP0 : analyticGermMaximalIdeal 2 ≠ ⊥ := by
    intro h
    have hm : adim_coordinate 1 ∈ analyticGermMaximalIdeal 2 := rfl
    rw [h, Ideal.mem_bot] at hm
    exact hne hm
  obtain ⟨L, e, ι, W, _, _, _, _, _, _, _, hdim⟩ :=
    adim5_prime_step 1 (analyticGermMaximalIdeal 2)
      (RingHom.ker_isPrime (analyticGermValue 2)) hP0
  exact ⟨e, ι, hdim⟩

/-- W2: the full two-dimensional germ exercises the zero-prime stopping case.
Source: Gunning--Rossi, III.B--C, local parametrization. -/
example : ∃ d : ℕ, d ≤ 2 ∧ ∃ θ : AnalyticGerm d →+*
    (AnalyticGerm 2 ⧸ (⊥ : Ideal (AnalyticGerm 2))),
    θ.Finite ∧ Function.Injective θ := by
  let : NoZeroDivisors (AnalyticGerm 2) := analyticGerm_noZeroDivisors_succ
  let : IsDomain (AnalyticGerm 2) := {}
  obtain ⟨d, π, θ, hd, hf, hi, _, _⟩ := adim5_finite_parameters 2 ⊥ inferInstance
  exact ⟨d, hd, θ, hf, hi⟩

/-- W3: the identity finite map and a nonconstant coordinate supply a distinguished relation.
Source: de Jong--Pfister, Chapters 3--4, finite local analytic algebras. -/
example : ∃ W : Polynomial (AnalyticGerm 1), IsWeierstrassPolynomial W ∧
    W.eval₂ (Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1)))
      (Ideal.Quotient.mk ⊥ (adim_coordinate 0)) = 0 := by
  apply adim5_distinguished_relation 1 1 ⊥ bot_ne_top (Ideal.Quotient.mk ⊥)
    (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)
  · intro a b h
    have hab : a = b := by
      simpa only [Ideal.mem_bot, sub_eq_zero] using
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp h
    exact congrArg (analyticGermValue 1) hab
  · rfl



/-- W4: simultaneous equations with two vertical coordinates and branching.
Source: Chirka, Complex Analytic Sets, §§3--4, local projection. -/
example : ∃ (V : Set (Fin 1 → ℂ)) (W : Set ((Fin 1 → ℂ) × (Fin 2 → ℂ))),
    IsOpen V ∧ (0 : Fin 1 → ℂ) ∈ V ∧ IsOpen W ∧
    (0 : (Fin 1 → ℂ) × (Fin 2 → ℂ)) ∈ W ∧ W ⊆ univ ∧
    ∃ p : {z : (Fin 1 → ℂ) × (Fin 2 → ℂ) //
      z ∈ W ∩ {z | ∀ j : Fin 2, z.2 j ^ 2 = z.1 0 ^ ((j : ℕ) + 2)}} → V,
      (∀ z, (p z).val = z.val.1) ∧ IsProperMap p ∧
      (∀ w : V, (p ⁻¹' {w}).Finite) ∧
      ∀ z, (p z).val = 0 → z.val = 0 := by
  let a : (j : Fin 2) → Fin 2 → (Fin 1 → ℂ) → ℂ :=
    fun j i x ↦ if i = 0 then -(x 0) ^ ((j : ℕ) + 2) else 0
  have ha : ∀ j i, AnalyticAt ℂ (a j i) 0 := by
    intro j i
    fin_cases i
    · exact ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).pow ((j : ℕ) + 2) |>.neg
    · exact analyticAt_const
  have ha0 : ∀ j i, a j i 0 = 0 := by
    intro j i
    fin_cases i <;> simp [a]
  have hS : IsClosed {z : (univ : Set ((Fin 1 → ℂ) × (Fin 2 → ℂ))) |
      ∀ j : Fin 2, z.val.2 j ^ 2 = z.val.1 0 ^ ((j : ℕ) + 2)} := by
    have he : {z : (univ : Set ((Fin 1 → ℂ) × (Fin 2 → ℂ))) |
        ∀ j : Fin 2, z.val.2 j ^ 2 = z.val.1 0 ^ ((j : ℕ) + 2)} =
        ⋂ j : Fin 2, {z | z.val.2 j ^ 2 = z.val.1 0 ^ ((j : ℕ) + 2)} := by
      ext z
      simp
    rw [he]
    exact isClosed_iInter fun j ↦ isClosed_eq (by fun_prop) (by fun_prop)
  exact adim5_closed_projection 1 2 (fun _ ↦ 2) (by intro j; norm_num) a ha ha0
    univ {z | ∀ j : Fin 2, z.2 j ^ 2 = z.1 0 ^ ((j : ℕ) + 2)}
    isOpen_univ (mem_univ _) hS (by simp)
    (by intro z hz j; simp [a, hz.2 j])

end HodgeLean.Foundations
