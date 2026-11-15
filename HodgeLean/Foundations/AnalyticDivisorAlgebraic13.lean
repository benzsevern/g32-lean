import HodgeLean.Foundations.AnalyticDivisorAlgebraic13Proofs

/-! # Re-centred Weierstrass preparation and clean loci: frozen specification

This stage states preparation after translating a germ at an arbitrary point to the origin,
transports polynomial factor hypotheses, and transports the clean regular locus back to that
point. It does not construct a sheaf of local divisors or glue local equations.

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic13

open Filter Polynomial Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11

/-- A nonunit germ at `p` whose translate is regular in the last variable is a unit times the
image of a Weierstrass polynomial over the germs in the first `n` coordinates of `p`.
Source: Gunning--Rossi, II.B, Theorem 2; de Jong--Pfister, §3. -/
theorem spec_preparation_at {n : ℕ} (p : Fin (n + 1) → ℂ)
    (g : AnalyticGermAt (n + 1) p)
    (hreg : ∃ e : AnalyticGermAt (n + 1) p ≃+* AnalyticGerm (n + 1),
      (∀ a, analyticGermValue (n + 1) (e a) = analyticGermAtValue (n + 1) p a) ∧
      (∀ (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
          (ht : AnalyticAt ℂ (fun z ↦ f (p + z)) 0),
        e ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds p) f, ⟨f, hf, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) (fun z ↦ f (p + z)),
            ⟨fun z ↦ f (p + z), ht, rfl⟩⟩) ∧
      IsRegularInLast (e g)) (hnu : ¬ IsUnit g) :
    ∃ (eFull : AnalyticGermAt (n + 1) p ≃+* AnalyticGerm (n + 1))
        (eBase : AnalyticGermAt n (gaga13_basePoint p) ≃+* AnalyticGerm n)
        (ι₀ : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
        (ι : Polynomial (AnalyticGermAt n (gaga13_basePoint p)) →+* AnalyticGermAt (n + 1) p)
        (P : Polynomial (AnalyticGermAt n (gaga13_basePoint p)))
        (u : AnalyticGermAt (n + 1) p),
      (∀ a, analyticGermValue (n + 1) (eFull a) =
        analyticGermAtValue (n + 1) p a) ∧
      (∀ (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
          (ht : AnalyticAt ℂ (fun z ↦ f (p + z)) 0),
        eFull ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds p) f, ⟨f, hf, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) (fun z ↦ f (p + z)),
            ⟨fun z ↦ f (p + z), ht, rfl⟩⟩) ∧
      (∀ a, analyticGermValue n (eBase a) =
        analyticGermAtValue n (gaga13_basePoint p) a) ∧
      (∀ (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f (gaga13_basePoint p))
          (ht : AnalyticAt ℂ (fun z ↦ f (gaga13_basePoint p + z)) 0),
        eBase ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds (gaga13_basePoint p)) f,
            ⟨f, hf, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0)
              (fun z ↦ f (gaga13_basePoint p + z)),
            ⟨fun z ↦ f (gaga13_basePoint p + z), ht, rfl⟩⟩) ∧
      IsWeierstrassEmbedding ι₀ ∧
      (∀ Q, eFull (ι Q) = ι₀ (Q.map eBase.toRingHom)) ∧
      IsWeierstrassPolynomialAt P ∧ IsUnit u ∧ g = u * ι P :=
  spec_preparation_at_aux p g hreg hnu

/-- The first coordinate germ in two variables has no transported coordinate Weierstrass
factorization in the last variable. Source: Gunning--Rossi, II.B, Theorem 2. -/
theorem spec_first_coordinate_no_transported_preparation :
    let g : AnalyticGermAt 2 0 :=
      ⟨@Filter.Germ.ofFun (Fin 2 → ℂ) ℂ (nhds 0) (fun z ↦ z 0),
        ⟨fun z ↦ z 0,
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt 0, rfl⟩⟩
    ¬ ∃ (eFull : AnalyticGermAt 2 0 ≃+* AnalyticGerm 2)
        (eBase : AnalyticGermAt 1 0 ≃+* AnalyticGerm 1)
        (ι₀ : Polynomial (AnalyticGerm 1) →+* AnalyticGerm 2)
        (ι : Polynomial (AnalyticGermAt 1 0) →+* AnalyticGermAt 2 0)
        (P : Polynomial (AnalyticGermAt 1 0)) (u : AnalyticGermAt 2 0),
      (∀ a, (eFull a).1 = a.1) ∧ (∀ a, (eBase a).1 = a.1) ∧
      IsWeierstrassEmbedding ι₀ ∧
      (∀ Q, eFull (ι Q) = ι₀ (Q.map eBase.toRingHom)) ∧
      IsWeierstrassPolynomialAt P ∧ IsUnit u ∧ g = u * ι P :=
  spec_first_coordinate_no_transported_preparation_aux

-- An invocation of the re-centred statement at `p = 0`. It instantiates `spec_preparation_at`
-- at the origin; it does not by itself restate the stage-six `spec_preparation_transfer` package.
example {n : ℕ} (g : AnalyticGermAt (n + 1) 0)
    (hreg : ∃ e : AnalyticGermAt (n + 1) 0 ≃+* AnalyticGerm (n + 1),
      (∀ a, analyticGermValue (n + 1) (e a) = analyticGermAtValue (n + 1) 0 a) ∧
      (∀ (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0)
          (ht : AnalyticAt ℂ (fun z ↦ f (0 + z)) 0),
        e ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) f, ⟨f, hf, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) (fun z ↦ f (0 + z)),
            ⟨fun z ↦ f (0 + z), ht, rfl⟩⟩) ∧ IsRegularInLast (e g))
    (hnu : ¬ IsUnit g) :
    ∃ (eFull : AnalyticGermAt (n + 1) 0 ≃+* AnalyticGerm (n + 1))
        (eBase : AnalyticGermAt n (gaga13_basePoint 0) ≃+* AnalyticGerm n)
        (ι₀ : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
        (ι : Polynomial (AnalyticGermAt n (gaga13_basePoint 0)) →+* AnalyticGermAt (n + 1) 0)
        (P : Polynomial (AnalyticGermAt n (gaga13_basePoint 0)))
        (u : AnalyticGermAt (n + 1) 0),
      (∀ a, analyticGermValue (n + 1) (eFull a) = analyticGermAtValue (n + 1) 0 a) ∧
      (∀ (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0)
          (ht : AnalyticAt ℂ (fun z ↦ f (0 + z)) 0),
        eFull ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) f, ⟨f, hf, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) (fun z ↦ f (0 + z)),
            ⟨fun z ↦ f (0 + z), ht, rfl⟩⟩) ∧
      (∀ a, analyticGermValue n (eBase a) =
        analyticGermAtValue n (gaga13_basePoint 0) a) ∧
      (∀ (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f (gaga13_basePoint 0))
          (ht : AnalyticAt ℂ (fun z ↦ f (gaga13_basePoint 0 + z)) 0),
        eBase ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds (gaga13_basePoint 0)) f,
            ⟨f, hf, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0)
              (fun z ↦ f (gaga13_basePoint 0 + z)),
            ⟨fun z ↦ f (gaga13_basePoint 0 + z), ht, rfl⟩⟩) ∧
      IsWeierstrassEmbedding ι₀ ∧
      (∀ Q, eFull (ι Q) = ι₀ (Q.map eBase.toRingHom)) ∧
      IsWeierstrassPolynomialAt P ∧ IsUnit u ∧ g = u * ι P :=
  spec_preparation_at 0 g hreg hnu

/-- Translation to the origin preserves irreducibility of every polynomial factor and their
pairwise coprimality. Source: Bourbaki, *Algebra*, Ch. IV, §1. -/
theorem spec_factors_translate_to_zero {n k : ℕ} (p : Fin n → ℂ)
    (P : Fin k → Polynomial (AnalyticGermAt n p)) :
    ∃ e : AnalyticGermAt n p ≃+* AnalyticGerm n,
      (∀ i, Irreducible ((P i).map e.toRingHom) ↔ Irreducible (P i)) ∧
      (Pairwise (fun i j ↦ IsCoprime ((P i).map e.toRingHom) ((P j).map e.toRingHom)) ↔
        Pairwise (fun i j ↦ IsCoprime (P i) (P j))) :=
  spec_factors_translate_to_zero_aux p P

example {n k : ℕ} (p : Fin n → ℂ)
    (P : Fin k → Polynomial (AnalyticGermAt n p)) :
    ∃ e : AnalyticGermAt n p ≃+* AnalyticGerm n,
      (∀ i, Irreducible ((P i).map e.toRingHom) ↔ Irreducible (P i)) ∧
      (Pairwise (fun i j ↦ IsCoprime ((P i).map e.toRingHom) ((P j).map e.toRingHom)) ↔
        Pairwise (fun i j ↦ IsCoprime (P i) (P j))) :=
  spec_factors_translate_to_zero p P

/-- The clean regular locus is invariant under translation of its ambient affine space.
Source: Gunning--Rossi, II.B, Definition 1; translation is a homeomorphism. -/
theorem spec_clean_regular_locus_translation {n k : ℕ}
    (p : (Fin n → ℂ) × ℂ) (P : Fin k → (Fin n → ℂ) × ℂ → ℂ)
    (i : Fin k) :
    p ∈ closure {y | P i y = 0 ∧ (∀ j, j ≠ i → P j y ≠ 0) ∧ fderiv ℂ (P i) y ≠ 0} ↔
      (0 : (Fin n → ℂ) × ℂ) ∈ closure
        {z | P i (p + z) = 0 ∧ (∀ j, j ≠ i → P j (p + z) ≠ 0) ∧
          fderiv ℂ (fun y ↦ P i (p + y)) z ≠ 0} :=
  spec_clean_regular_locus_translation_aux p P i

example {n k : ℕ} (p : (Fin n → ℂ) × ℂ)
    (P : Fin k → (Fin n → ℂ) × ℂ → ℂ) (i : Fin k) :
    p ∈ closure {y | P i y = 0 ∧ (∀ j, j ≠ i → P j y ≠ 0) ∧ fderiv ℂ (P i) y ≠ 0} ↔
      (0 : (Fin n → ℂ) × ℂ) ∈ closure
        {z | P i (p + z) = 0 ∧ (∀ j, j ≠ i → P j (p + z) ≠ 0) ∧
          fderiv ℂ (fun y ↦ P i (p + y)) z ≠ 0} :=
  spec_clean_regular_locus_translation p P i

/-- Every irreducible factor has clean regular points, avoiding the other pairwise-coprime
factors, arbitrarily close to an arbitrary base point.
Source: Gunning--Rossi, Ch. III; Chirka, §§2--5. -/
theorem spec_point_mem_closure_clean_regular_factor {n k : ℕ}
    (p : (Fin n → ℂ) × ℂ) {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    (hP : ∀ i, AnalyticAt ℂ (P i) p ∧ IsIrreducibleAt (P i) p)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) p)) (i : Fin k) :
    p ∈ closure
      {y | P i y = 0 ∧ (∀ j, j ≠ i → P j y ≠ 0) ∧ fderiv ℂ (P i) y ≠ 0} :=
  spec_point_mem_closure_clean_regular_factor_aux p hP hcP i

-- At the origin the closure statement has exactly the stage-nine conclusion.
example {n k : ℕ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    (hP : ∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0)) (i : Fin k) :
    (0 : (Fin n → ℂ) × ℂ) ∈ closure
      {y | P i y = 0 ∧ (∀ j, j ≠ i → P j y ≠ 0) ∧ fderiv ℂ (P i) y ≠ 0} :=
  spec_point_mem_closure_clean_regular_factor 0 hP hcP i

-- A unit factor cannot satisfy the irreducibility premise.
example {n : ℕ} (p : (Fin n → ℂ) × ℂ) :
    ¬ IsIrreducibleAt (fun _ ↦ (1 : ℂ)) p := by
  simp [IsIrreducibleAt]

-- With no factors there is no index to which the closure assertion could be applied.
example : IsEmpty (Fin 0) := inferInstance

-- Pairwise coprimality is vacuous for one factor.
example {R : Type*} [CommRing R] (P : Fin 1 → Polynomial R) :
    Pairwise (fun i j ↦ IsCoprime (P i) (P j)) := by
  intro i j hij
  fin_cases i
  fin_cases j
  exact (hij rfl).elim

-- Mathlib's empty polynomial product is one, while zero is not a positive-degree
-- Weierstrass polynomial.
example : (∏ i : Fin 0, (i : ℂ)) = 1 := by simp

example {n : ℕ} {p : Fin n → ℂ} :
    ¬ IsWeierstrassPolynomialAt (0 : Polynomial (AnalyticGermAt n p)) := by
  simp [IsWeierstrassPolynomialAt]

-- Regularity is an essential premise: a germ independent of the last coordinate need not be
-- regular there, so generic coordinates are supplied separately by stage six.
example : ¬ IsRegularInLast
    (⟨@Filter.Germ.ofFun (Fin 2 → ℂ) ℂ (nhds 0) (fun z ↦ z 0),
      ⟨fun z ↦ z 0,
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt 0, rfl⟩⟩ :
      AnalyticGerm 2) := by
  rintro ⟨f, hf, hfg, hord⟩
  have heq : Filter.Eventually
      (fun w : ℂ ↦ f (Pi.single (M := fun _ : Fin 2 => ℂ) (Fin.last 1) w) = 0)
      (nhds 0) := by
    have h := hfg.symm
    rw [Filter.Germ.coe_eq] at h
    have ht : Tendsto
        (fun w : ℂ ↦ Pi.single (M := fun _ : Fin 2 => ℂ) (Fin.last 1) w)
        (nhds 0) (nhds 0) := by
      have hc : Continuous
          (fun w : ℂ ↦ Pi.single (M := fun _ : Fin 2 => ℂ) (Fin.last 1) w) := by
        apply continuous_pi
        intro i
        fin_cases i <;> simp [Pi.single_apply] <;> fun_prop
      have hz : Pi.single (M := fun _ : Fin 2 => ℂ) (Fin.last 1) 0 = 0 := by
        ext i
        simp [Pi.single_apply]
      rw [← hz]
      exact hc.continuousAt
    filter_upwards [ht.eventually h] with w hw
    simpa [Pi.single_apply] using hw.symm
  exact hord (analyticOrderAt_eq_top.mpr heq)

end HodgeLean.Foundations.AnalyticDivisorAlgebraic13
