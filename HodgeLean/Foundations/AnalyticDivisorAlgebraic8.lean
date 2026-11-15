import HodgeLean.Foundations.AnalyticDivisorAlgebraic8Proofs

/-! # Local divisors of hypersurface germs: frozen specification

This stage constructs the local divisor as genuine finitely supported data on associate classes
and freezes its invariance and algebra laws. Stage 7's function-level zero-set and transverse-order
theorems explain the geometric meaning of these coefficients, but a change-of-base-point map for
analytic germs is not yet available, so no false locality theorem is claimed.

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic8

open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7

/-- The local divisor of the unit germ is zero.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem spec_localDivisor_one (n : ℕ) : localDivisor n 1 = 0 :=
  spec_localDivisor_one_aux n

/-- The convention for the excluded zero germ is the zero finitely supported function. Geometric
support statements must retain a nonzero hypothesis.
Source: the defining convention for `localDivisor`. -/
theorem spec_localDivisor_zero (n : ℕ) : localDivisor n 0 = 0 :=
  spec_localDivisor_zero_aux n

/-- Associated analytic germs, hence in particular germs differing by a unit, have equal local
divisors.
Source: Gunning--Rossi, II.B, Definition 1 and Theorems 3--6. -/
theorem spec_localDivisor_associated (n : ℕ) (f g : ProductAnalyticGerm n)
    (h : Associated f g) : localDivisor n f = localDivisor n g :=
  spec_localDivisor_associated_aux n f g h

/-- Every unit analytic germ has zero local divisor.
Source: Griffiths--Harris, Ch. 1 §1. -/
theorem spec_localDivisor_unit (n : ℕ) (f : ProductAnalyticGerm n) (hf : IsUnit f) :
    localDivisor n f = 0 :=
  spec_localDivisor_unit_aux n f hf

/-- The local divisor is additive under multiplication of nonzero germs.
Source: Griffiths--Harris, Ch. 1 §1. -/
theorem spec_localDivisor_mul (n : ℕ) (f g : ProductAnalyticGerm n)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    localDivisor n (f * g) = localDivisor n f + localDivisor n g :=
  spec_localDivisor_mul_aux n f g hf hg

/-- Raising a germ to a power multiplies every component multiplicity by that power.
Source: Griffiths--Harris, Ch. 1 §1. -/
theorem spec_localDivisor_pow (n : ℕ) (f : ProductAnalyticGerm n) (m : ℕ) :
    localDivisor n (f ^ m) = m • localDivisor n f :=
  spec_localDivisor_pow_aux n f m

/-- A stage-7 irreducible decomposition computes the canonical local divisor, with exactly its
displayed multiplicities and associate classes.
Source: Gunning--Rossi II.B, Theorems 3--6; Griffiths--Harris, Ch. 1 §1. -/
theorem spec_localDivisor_decomposition {n k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    {m : Fin k → ℕ} (hf : AnalyticAt ℂ f 0) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hP : ∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0 ∧ 0 < m i)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0))
    (hfac : f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i)) :
    localDivisor n (productAnalyticGermOf f hf) =
      ∑ i, m i • Finsupp.single
        (Associates.mk (productAnalyticGermOf (P i) (hP i).1)) 1 :=
  spec_localDivisor_decomposition_aux hf hu hu0 hP hcP hfac

/-- For a nonzero displayed decomposition, divisor support is precisely the displayed associate
classes, and their representatives cut out exactly the nearby zero set.
Source: Gunning--Rossi II.B, Theorems 3--6; Chirka, §§2--3. -/
theorem spec_localDivisor_support_and_zeroSet {n k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    {m : Fin k → ℕ} (hf : AnalyticAt ℂ f 0) (hnz : ¬ ∀ᶠ y in nhds 0, f y = 0)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hP : ∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0 ∧ 0 < m i)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0))
    (hfac : f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i)) :
    ↑(localDivisor n (productAnalyticGermOf f hf)).support =
        {c | ∃ i, c = Associates.mk (productAnalyticGermOf (P i) (hP i).1)} ∧
      ∀ᶠ y in nhds 0, f y = 0 ↔ ∃ i, P i y = 0 :=
  spec_localDivisor_support_and_zeroSet_aux hf hnz hu hu0 hP hcP hfac

/-- At every clean regular point of a displayed component near the origin, its local-divisor
coefficient is the transverse analytic order of the original function.
Source: Gunning--Rossi II.B, Theorems 3--6; Chirka §2.3. -/
theorem spec_localDivisor_multiplicity_eq_transverseOrder {n k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    {m : Fin k → ℕ} (hf : AnalyticAt ℂ f 0) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hP : ∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0 ∧ 0 < m i)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0))
    (hfac : f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i)) :
    ∀ᶠ y in nhds 0, ∀ i, P i y = 0 → (∀ j, j ≠ i → P j y ≠ 0) →
        ∀ a : (Fin n → ℂ) × ℂ, fderiv ℂ (P i) y a ≠ 0 →
          analyticOrderAt (fun t : ℂ ↦ f (y + t • a)) 0 =
            (localDivisor n (productAnalyticGermOf f hf))
              (Associates.mk (productAnalyticGermOf (P i) (hP i).1)) :=
  spec_localDivisor_multiplicity_eq_transverseOrder_aux hf hu hu0 hP hcP hfac

/-- The divisor of `w²(w-z)` is `2[w] + [w-z]`, and the two components are distinct.
Source: the stage-7 decomposition example and `spec_localDivisor_decomposition`. -/
theorem spec_localDivisor_w_sq_mul_w_sub_z :
    let w : (Fin 1 → ℂ) × ℂ → ℂ := fun y ↦ y.2
    let q : (Fin 1 → ℂ) × ℂ → ℂ := fun y ↦ y.2 - y.1 0
    localDivisor 1 (productAnalyticGermOf (fun y ↦ w y ^ 2 * q y)
      ((analyticAt_snd.pow 2).mul (analyticAt_snd.sub
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
          analyticAt_fst rfl)))) =
      2 • Finsupp.single (Associates.mk (productAnalyticGermOf w analyticAt_snd)) 1 +
        Finsupp.single (Associates.mk (productAnalyticGermOf q
          (analyticAt_snd.sub
            (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
              analyticAt_fst rfl)))) 1 ∧
    Associates.mk (productAnalyticGermOf w analyticAt_snd) ≠
      Associates.mk (productAnalyticGermOf q
        (analyticAt_snd.sub
          (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
            analyticAt_fst rfl))) := spec_localDivisor_w_sq_mul_w_sub_z_aux

/-- The concrete germ `1+z` is a unit and has zero local divisor.
Source: `spec_localDivisor_unit`. -/
theorem spec_localDivisor_one_add_z :
    localDivisor 1 (productAnalyticGermOf (fun y : (Fin 1 → ℂ) × ℂ ↦ 1 + y.1 0)
      (analyticAt_const.add
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
          analyticAt_fst rfl))) = 0 := spec_localDivisor_one_add_z_aux

/-- With no base variables, the divisor of `w³` is three times the `w` component.
Source: `spec_localDivisor_pow`. -/
theorem spec_localDivisor_zero_base_w_pow :
    localDivisor 0 (productAnalyticGermOf (fun y : (Fin 0 → ℂ) × ℂ ↦ y.2 ^ 3)
      (analyticAt_snd.pow 3)) =
      3 • Finsupp.single (Associates.mk (productAnalyticGermOf
        (fun y : (Fin 0 → ℂ) × ℂ ↦ y.2) analyticAt_snd)) 1 :=
  spec_localDivisor_zero_base_w_pow_aux

/-- Two distinct coprime factors contribute distinct classes, while associated factors contribute
twice to the same class.
Source: `spec_localDivisor_mul` and `spec_localDivisor_associated`. -/
theorem spec_localDivisor_distinct_and_associated_factors :
    let w : (Fin 1 → ℂ) × ℂ → ℂ := fun y ↦ y.2
    let q : (Fin 1 → ℂ) × ℂ → ℂ := fun y ↦ y.2 - y.1 0
    let hw : AnalyticAt ℂ w 0 := analyticAt_snd
    let hq : AnalyticAt ℂ q 0 := analyticAt_snd.sub
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
        analyticAt_fst rfl)
    localDivisor 1 (productAnalyticGermOf (fun y ↦ w y * q y) (hw.mul hq)) =
        Finsupp.single (Associates.mk (productAnalyticGermOf w hw)) 1 +
          Finsupp.single (Associates.mk (productAnalyticGermOf q hq)) 1 ∧
      localDivisor 1 (productAnalyticGermOf (fun y ↦ w y * (2 * w y))
        (hw.mul (analyticAt_const.mul hw))) =
        2 • Finsupp.single (Associates.mk (productAnalyticGermOf w hw)) 1 :=
  spec_localDivisor_distinct_and_associated_factors_aux

-- Each frozen declaration is exercised below on concrete input.
example : localDivisor 1 (1 : ProductAnalyticGerm 1) = 0 := spec_localDivisor_one 1

example : localDivisor 1 (0 : ProductAnalyticGerm 1) = 0 := spec_localDivisor_zero 1

example : localDivisor 1 (1 : ProductAnalyticGerm 1) = localDivisor 1 1 :=
  spec_localDivisor_associated 1 1 1 Associated.rfl

example : localDivisor 1 (1 : ProductAnalyticGerm 1) = 0 :=
  spec_localDivisor_unit 1 1 isUnit_one

example : localDivisor 1 ((1 : ProductAnalyticGerm 1) * 1) =
    localDivisor 1 1 + localDivisor 1 1 :=
  spec_localDivisor_mul 1 1 1 one_ne_zero one_ne_zero

example : localDivisor 1 ((1 : ProductAnalyticGerm 1) ^ 4) =
    4 • localDivisor 1 1 := spec_localDivisor_pow 1 1 4

example (hw : IsIrreducibleAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2) 0) :
    localDivisor 1 (productAnalyticGermOf (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 ^ 2)
      (analyticAt_snd.pow 2)) =
      2 • Finsupp.single (Associates.mk (productAnalyticGermOf
        (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2) analyticAt_snd)) 1 := by
  simpa using spec_localDivisor_decomposition (n := 1) (k := 1)
    (f := fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 ^ 2) (u := fun _ ↦ 1)
    (P := fun (_ : Fin 1) (y : (Fin 1 → ℂ) × ℂ) ↦ y.2)
    (m := fun _ : Fin 1 ↦ 2) (analyticAt_snd.pow 2) analyticAt_const
    (by norm_num) (fun _ ↦ ⟨analyticAt_snd, hw, by norm_num⟩)
    (fun i j hij ↦ (hij (Subsingleton.elim i j)).elim) (by simp)

example (hw : IsIrreducibleAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2) 0) :
    ↑(localDivisor 1 (productAnalyticGermOf (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 ^ 2)
      (analyticAt_snd.pow 2))).support =
        {Associates.mk (productAnalyticGermOf
          (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2) analyticAt_snd)} ∧
      ∀ᶠ y in nhds (0 : (Fin 1 → ℂ) × ℂ), (y.2 ^ 2 = 0 ↔ y.2 = 0) := by
  have hnz : ¬ ∀ᶠ y in nhds (0 : (Fin 1 → ℂ) × ℂ), y.2 ^ 2 = 0 := by
    intro hz
    have hwz : ∀ᶠ y in nhds (0 : (Fin 1 → ℂ) × ℂ), y.2 = 0 :=
      hz.mono fun _ hy ↦ mul_self_eq_zero.mp (by simpa [pow_two] using hy)
    have hbad := hw.2 (fun _ ↦ 0) (fun _ ↦ 0) analyticAt_const analyticAt_const
      (by filter_upwards [hwz] with y hy; simp [hy])
    rcases hbad with hbad | hbad <;> exact hbad rfl
  simpa using spec_localDivisor_support_and_zeroSet (n := 1) (k := 1)
    (f := fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 ^ 2) (u := fun _ ↦ 1)
    (P := fun (_ : Fin 1) (y : (Fin 1 → ℂ) × ℂ) ↦ y.2)
    (m := fun _ : Fin 1 ↦ 2) (analyticAt_snd.pow 2) hnz
    analyticAt_const (by norm_num) (fun _ ↦ ⟨analyticAt_snd, hw, by norm_num⟩)
    (fun i j hij ↦ (hij (Subsingleton.elim i j)).elim) (by simp)

example (hw : IsIrreducibleAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2) 0) :
    (∀ᶠ y in nhds (0 : (Fin 1 → ℂ) × ℂ), y.2 = 0 →
        ∀ a : (Fin 1 → ℂ) × ℂ, fderiv ℂ (fun q ↦ q.2) y a ≠ 0 →
          analyticOrderAt (fun t : ℂ ↦ (y + t • a).2 ^ 2) 0 =
            (localDivisor 1 (productAnalyticGermOf
              (fun q : (Fin 1 → ℂ) × ℂ ↦ q.2 ^ 2) (analyticAt_snd.pow 2)))
              (Associates.mk (productAnalyticGermOf
                (fun q : (Fin 1 → ℂ) × ℂ ↦ q.2) analyticAt_snd))) ∧
      (0 : (Fin 1 → ℂ) × ℂ) ∈ closure
        {y | y.2 = 0 ∧ fderiv ℂ (fun q : (Fin 1 → ℂ) × ℂ ↦ q.2) y ≠ 0} := by
  constructor
  · simpa using spec_localDivisor_multiplicity_eq_transverseOrder (n := 1) (k := 1)
      (f := fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 ^ 2) (u := fun _ ↦ 1)
      (P := fun (_ : Fin 1) (y : (Fin 1 → ℂ) × ℂ) ↦ y.2)
      (m := fun _ : Fin 1 ↦ 2) (analyticAt_snd.pow 2) analyticAt_const
      (by norm_num) (fun _ ↦ ⟨analyticAt_snd, hw, by norm_num⟩)
      (fun i j hij ↦ (hij (Subsingleton.elim i j)).elim) (by simp)
  · apply subset_closure
    constructor
    · rfl
    · have hd : HasFDerivAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2)
          (ContinuousLinearMap.snd ℂ (Fin 1 → ℂ) ℂ) 0 := by fun_prop
      intro h
      have he := congrArg (fun L ↦ L (0, 1)) h
      rw [hd.fderiv] at he
      norm_num at he

example := spec_localDivisor_w_sq_mul_w_sub_z

example := spec_localDivisor_one_add_z

example := spec_localDivisor_zero_base_w_pow

example := spec_localDivisor_distinct_and_associated_factors

end HodgeLean.Foundations.AnalyticDivisorAlgebraic8
