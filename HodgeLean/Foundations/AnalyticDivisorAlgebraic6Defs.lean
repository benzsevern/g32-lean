import HodgeLean.Foundations.AnalyticDivisorAlgebraic5Defs
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Topology.Germ

/-! # Definitions for the analytic divisor spec, sixth stage

The genuine local ring of analytic germs at the origin and standard predicates used by the
factoriality statements. HC no distance; AV milestone no distance.
-/

noncomputable section
open Filter Topology Polynomial
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic6

/-- Germs at `0 ∈ ℂⁿ` which have a representative analytic at `0`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
def analyticGermSubring (n : ℕ) : Subring (Filter.Germ (nhds (0 : Fin n → ℂ)) ℂ) where
  carrier := {g | ∃ f : (Fin n → ℂ) → ℂ, AnalyticAt ℂ f 0 ∧
    (@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds (0 : Fin n → ℂ)) f) = g}
  zero_mem' := ⟨fun _ ↦ 0, analyticAt_const, rfl⟩
  one_mem' := ⟨fun _ ↦ 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun x ↦ f x + g x, hf.add hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨fun x ↦ -f x, hf.neg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun x ↦ f x * g x, hf.mul hg, rfl⟩

/-- The local ring of analytic function germs at the origin of `ℂⁿ`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
abbrev AnalyticGerm (n : ℕ) := analyticGermSubring n

example (n : ℕ) : CommRing (AnalyticGerm n) := inferInstance

/-- Germs at `(0, 0) ∈ ℂⁿ × ℂ` which have a representative analytic there.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
def productAnalyticGermSubring (n : ℕ) :
    Subring (Filter.Germ (nhds ((0, 0) : (Fin n → ℂ) × ℂ)) ℂ) where
  carrier := {g | ∃ f : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ f 0 ∧
    (@Filter.Germ.ofFun ((Fin n → ℂ) × ℂ) ℂ (nhds 0) f) = g}
  zero_mem' := ⟨fun _ ↦ 0, analyticAt_const, rfl⟩
  one_mem' := ⟨fun _ ↦ 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun x ↦ f x + g x, hf.add hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨fun x ↦ -f x, hf.neg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun x ↦ f x * g x, hf.mul hg, rfl⟩

/-- The local ring of analytic function germs at `(0, 0) ∈ ℂⁿ × ℂ`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
abbrev ProductAnalyticGerm (n : ℕ) := productAnalyticGermSubring n

example (n : ℕ) : CommRing (ProductAnalyticGerm n) := inferInstance

/-- Evaluation at the origin on analytic germs.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
def analyticGermValue (n : ℕ) : AnalyticGerm n →+* ℂ :=
  (Filter.Germ.valueRingHom (X := Fin n → ℂ) (E := ℂ)).comp (analyticGermSubring n).subtype

/-- The ideal of analytic germs vanishing at the origin.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
def analyticGermMaximalIdeal (n : ℕ) : Ideal (AnalyticGerm n) := RingHom.ker (analyticGermValue n)

example : analyticGermValue 1
    ⟨@Filter.Germ.ofFun (Fin 1 → ℂ) ℂ (nhds 0) (fun z ↦ 1 + z 0),
      ⟨fun z ↦ 1 + z 0, analyticAt_const.add
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0), rfl⟩⟩ = 1 := by
  change (@Filter.Germ.ofFun (Fin 1 → ℂ) ℂ (nhds 0) (fun z ↦ 1 + z 0)).value = 1
  simpa using (Filter.Germ.value_ofFun (fun z : Fin 1 → ℂ ↦ 1 + z 0) (0 : Fin 1 → ℂ))

example :
    ⟨@Filter.Germ.ofFun (Fin 1 → ℂ) ℂ (nhds 0) (fun z ↦ z 0),
      ⟨fun z ↦ z 0,
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0, rfl⟩⟩ ∈
      analyticGermMaximalIdeal 1 := by
  rfl

/-- A monic positive-degree polynomial whose nonleading coefficients vanish at the origin.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 2. -/
def IsWeierstrassPolynomial {n : ℕ} (P : Polynomial (AnalyticGerm n)) : Prop :=
  P.Monic ∧ 0 < P.natDegree ∧
    ∀ j < P.natDegree, P.coeff j ∈ analyticGermMaximalIdeal n

example {n : ℕ} : IsWeierstrassPolynomial (X : Polynomial (AnalyticGerm n)) := by
  constructor
  · exact monic_X
  · simp [analyticGermMaximalIdeal]

/-- A germ is regular in the last variable when an analytic representative has finite order on
the last coordinate axis. Source: Gunning--Rossi II.B, Definition 2 and Lemma 1. -/
def IsRegularInLast {n : ℕ} (g : AnalyticGerm (n + 1)) : Prop :=
  ∃ f : (Fin (n + 1) → ℂ) → ℂ, AnalyticAt ℂ f 0 ∧
    (@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) f) = g.1 ∧
    analyticOrderAt (fun w : ℂ ↦ f (Pi.single (Fin.last n) w)) 0 ≠ ⊤

example : IsRegularInLast
    (⟨@Filter.Germ.ofFun (Fin 1 → ℂ) ℂ (nhds 0) (fun z ↦ z (Fin.last 0)),
      ⟨fun z ↦ z (Fin.last 0),
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) (Fin.last 0)).analyticAt 0,
        rfl⟩⟩ : AnalyticGerm 1) := by
  refine ⟨fun z ↦ z (Fin.last 0), ?_, rfl, ?_⟩
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ)
      (Fin.last 0)).analyticAt 0
  · simp only [Pi.single_eq_same]
    change analyticOrderAt (id : ℂ → ℂ) 0 ≠ ⊤
    rw [analyticOrderAt_id]
    exact ENat.one_ne_top

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

/-- `b` is obtained from `a` by adjoining an unused last coordinate.
Source: de Jong--Pfister, *Local Analytic Geometry*, §3. -/
def IsCoordinateExtension {n : ℕ} (a : AnalyticGerm n) (b : AnalyticGerm (n + 1)) : Prop :=
  ∃ f : (Fin n → ℂ) → ℂ, AnalyticAt ℂ f 0 ∧
    (@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) f) = a.1 ∧
    (@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0)
      (fun z ↦ f (fun i ↦ z i.castSucc))) = b.1

example : IsCoordinateExtension (1 : AnalyticGerm 0) (1 : AnalyticGerm 1) := by
  refine ⟨fun _ ↦ 1, analyticAt_const, ?_, ?_⟩ <;> rfl

/-- The canonical substitution map from polynomials over `n`-variable germs to
`n+1`-variable germs, characterized without choosing representatives.
Source: de Jong--Pfister, *Local Analytic Geometry*, §3. -/
def IsWeierstrassEmbedding {n : ℕ}
    (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1)) : Prop :=
  Function.Injective ι ∧ (∀ a, IsCoordinateExtension a (ι (C a))) ∧
    ∃ h : AnalyticGerm (n + 1),
      h.1 = (@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0)
        (fun z ↦ z (Fin.last n))) ∧ ι X = h

example {n : ℕ} (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
    (hι : IsWeierstrassEmbedding ι) : ι X ≠ 0 := by
  intro hX
  have : (X : Polynomial (AnalyticGerm n)) = 0 := hι.1 (by simpa using hX)
  exact X_ne_zero this

/-- A function germ is irreducible at `y` when it vanishes there and every local analytic
factorization has a unit factor. Source: Gunning--Rossi II.B, Definitions 1--2. -/
def IsIrreducibleAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (y : E) : Prop :=
  f y = 0 ∧ ∀ g h : E → ℂ, AnalyticAt ℂ g y → AnalyticAt ℂ h y →
    (f =ᶠ[nhds y] fun x ↦ g x * h x) → g y ≠ 0 ∨ h y ≠ 0

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (y : E) :
    ¬ IsIrreducibleAt (fun _ : E ↦ (1 : ℂ)) y := by
  intro h
  exact one_ne_zero h.1

/-- Two functions are coprime at `y` when they have no common analytic factor vanishing at `y`.
Source: Gunning--Rossi II.B, Theorems 3--6. -/
def IsCoprimeAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) (y : E) : Prop :=
  ¬ ∃ q r s : E → ℂ, AnalyticAt ℂ q y ∧ AnalyticAt ℂ r y ∧ AnalyticAt ℂ s y ∧
      q y = 0 ∧ (f =ᶠ[nhds y] fun x ↦ q x * r x) ∧ (g =ᶠ[nhds y] fun x ↦ q x * s x)

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → ℂ) (y : E) :
    IsCoprimeAt f (fun _ ↦ 1) y := by
  rintro ⟨q, r, s, -, -, -, hq, -, h⟩
  have hy := h.self_of_nhds
  simp [hq] at hy

end HodgeLean.Foundations.AnalyticDivisorAlgebraic6
