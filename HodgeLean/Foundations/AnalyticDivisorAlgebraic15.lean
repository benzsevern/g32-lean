import HodgeLean.Foundations.AnalyticDivisorAlgebraic15Proofs

/-! # Equivalent local divisor data and integer multiplicities

This stage freezes comparison statements for local equation families, translates the transverse
order description to an arbitrary point, and introduces numerator-denominator presentations.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic15

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic8
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14

/-- Equivalent local divisor data is reflexive.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem spec_equivalentLocalDivisorData_refl {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) : EquivalentLocalDivisorData V f V f :=
  spec_equivalentLocalDivisorData_refl_aux hD

/-- Equivalent local divisor data is symmetric.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem spec_equivalentLocalDivisorData_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι κ : Type*} {V : ι → Set E} {f : ι → E → ℂ}
    {W : κ → Set E} {g : κ → E → ℂ} (h : EquivalentLocalDivisorData V f W g) :
    EquivalentLocalDivisorData W g V f := spec_equivalentLocalDivisorData_symm_aux h

/-- Equivalent local divisor data is transitive for three valid families on the common set.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem spec_equivalentLocalDivisorData_trans {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι κ μ : Type*} {U : Set E}
    {V : ι → Set E} {f : ι → E → ℂ} {W : κ → Set E} {g : κ → E → ℂ}
    {R : μ → Set E} {q : μ → E → ℂ} (hF : IsLocalDivisorData U V f)
    (hG : IsLocalDivisorData U W g) (hQ : IsLocalDivisorData U R q)
    (hfg : EquivalentLocalDivisorData V f W g)
    (hgq : EquivalentLocalDivisorData W g R q) : EquivalentLocalDivisorData V f R q :=
  spec_equivalentLocalDivisorData_trans_aux hF hG hQ hfg hgq

/-- Equivalent local equation families have the same support.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem spec_equivalentLocalDivisorData_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι κ : Type*} {U : Set E}
    {V : ι → Set E} {f : ι → E → ℂ} {W : κ → Set E} {g : κ → E → ℂ}
    (hD : IsLocalDivisorData U V f) (hG : IsLocalDivisorData U W g)
    (h : EquivalentLocalDivisorData V f W g) :
    localDivisorSupport V f = localDivisorSupport W g :=
  spec_equivalentLocalDivisorData_support_aux hD hG h

/-- Equivalent local equations have the same local divisor at a cross-overlap point.
Source: Gunning--Rossi, II.B, Definition 1. -/
theorem spec_equivalentLocalDivisorData_localDivisorAt {n : ℕ} {ι κ : Type*}
    {V : ι → Set ((Fin n → ℂ) × ℂ)} {f : ι → (Fin n → ℂ) × ℂ → ℂ}
    {W : κ → Set ((Fin n → ℂ) × ℂ)} {g : κ → (Fin n → ℂ) × ℂ → ℂ}
    (h : EquivalentLocalDivisorData V f W g) (i : ι) (j : κ)
    (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) (hj : p ∈ W j)
    (hf : AnalyticAt ℂ (f i) p) (hg : AnalyticAt ℂ (g j) p) :
    localDivisorAt n (f i) p = localDivisorAt n (g j) p :=
  spec_equivalentLocalDivisorData_localDivisorAt_aux h i j p hi hj hf hg

/-- Cross-intersections give a common refinement of equivalent local equation families.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem spec_equivalentLocalDivisorData_commonRefinement {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {ι κ : Type*} {U : Set E}
    {V : ι → Set E} {f : ι → E → ℂ} {W : κ → Set E} {g : κ → E → ℂ}
    (hD : IsLocalDivisorData U V f) (hG : IsLocalDivisorData U W g)
    (h : EquivalentLocalDivisorData V f W g) :
    IsLocalDivisorData U (fun ij : ι × κ ↦ V ij.1 ∩ W ij.2) (fun ij ↦ f ij.1) ∧
      (∀ ij : ι × κ, V ij.1 ∩ W ij.2 ⊆ V ij.1) ∧
      (∀ ij : ι × κ, V ij.1 ∩ W ij.2 ⊆ W ij.2) :=
  spec_equivalentLocalDivisorData_commonRefinement_aux hD hG h

/-- When `p` is on the support, transverse order at every clean regular point near `p` equals the
corresponding coefficient of the local divisor at `p`.
Source: Gunning--Rossi, II.B, Theorems 3--6; Chirka §2.3. -/
theorem spec_localDivisorAt_multiplicity_eq_transverseOrder {n k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    {m : Fin k → ℕ} {p : (Fin n → ℂ) × ℂ} (hf : AnalyticAt ℂ f p) (hf0 : f p = 0)
    (hu : AnalyticAt ℂ u p) (hu0 : u p ≠ 0)
    (hP : ∀ i, AnalyticAt ℂ (P i) p ∧ IsIrreducibleAt (P i) p ∧ 0 < m i)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) p))
    (hfac : f =ᶠ[nhds p] fun y ↦ u y * ∏ i, (P i y) ^ (m i))
    (hPt : ∀ i, AnalyticAt ℂ (fun z ↦ P i (p + z)) 0) :
    ∀ᶠ y in nhds p, ∀ i, P i y = 0 → (∀ j, j ≠ i → P j y ≠ 0) →
      ∀ a : (Fin n → ℂ) × ℂ, fderiv ℂ (P i) y a ≠ 0 →
        analyticOrderAt (fun t : ℂ ↦ f (y + t • a)) 0 =
          localDivisorAt n f p
            (Associates.mk (productAnalyticGermOf (fun z ↦ P i (p + z)) (hPt i))) :=
  spec_localDivisorAt_multiplicity_eq_transverseOrder_aux hf hf0 hu hu0 hP hcP hfac hPt

/-- Equivalent valid meromorphic presentations have equal integer multiplicities.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem spec_localMeromorphicDivisorAt_eq {n : ℕ} {ι κ : Type*}
    {V : ι → Set ((Fin n → ℂ) × ℂ)} {g h : ι → (Fin n → ℂ) × ℂ → ℂ}
    {W : κ → Set ((Fin n → ℂ) × ℂ)} {a b : κ → (Fin n → ℂ) × ℂ → ℂ}
    {U : Set ((Fin n → ℂ) × ℂ)}
    (hD : IsLocalMeromorphicDivisorData U V g h)
    (hA : IsLocalMeromorphicDivisorData U W a b)
    (heq : EquivalentLocalMeromorphicDivisorData V g h W a b) (i : ι) (j : κ)
    (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) (hj : p ∈ W j)
    (hg : AnalyticAt ℂ (g i) p) (hh : AnalyticAt ℂ (h i) p)
    (ha : AnalyticAt ℂ (a j) p) (hb : AnalyticAt ℂ (b j) p) :
    localMeromorphicDivisorAt n (g i) (h i) p =
      localMeromorphicDivisorAt n (a j) (b j) p :=
  spec_localMeromorphicDivisorAt_eq_aux hD hA heq i j p hi hj hg hh ha hb

/-- A unit denominator recovers the integer cast of the effective local divisor.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem spec_localMeromorphicDivisorAt_unit_denominator {n : ℕ}
    {g h : (Fin n → ℂ) × ℂ → ℂ} {p : (Fin n → ℂ) × ℂ}
    (hh : AnalyticAt ℂ h p) (hh0 : h p ≠ 0) :
    localMeromorphicDivisorAt n g h p =
      (localDivisorAt n g p).mapRange Nat.cast (by simp) :=
  spec_localMeromorphicDivisorAt_unit_denominator_aux hh hh0

/-- Equal numerator and denominator give the zero integer divisor.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem spec_localMeromorphicDivisorAt_self {n : ℕ}
    (g : (Fin n → ℂ) × ℂ → ℂ) (p : (Fin n → ℂ) × ℂ) :
    localMeromorphicDivisorAt n g g p = 0 :=
  spec_localMeromorphicDivisorAt_self_aux g p

/-- Zero cross-products can make invalid meromorphic presentations equivalent while their
integer multiplicities differ. -/
theorem spec_zeroCrossProduct_counterexample :
    EquivalentLocalMeromorphicDivisorData
        (fun _ : Unit ↦ (univ : Set ((Fin 0 → ℂ) × ℂ)))
        (fun _ _ ↦ 0) (fun _ _ ↦ 0)
        (fun _ : Unit ↦ univ) (fun _ z ↦ z.2) (fun _ _ ↦ 1) ∧
      localMeromorphicDivisorAt 0 (fun _ ↦ 0) (fun _ ↦ 0) 0 ≠
        localMeromorphicDivisorAt 0 (fun z ↦ z.2) (fun _ ↦ 1) 0 :=
  spec_zeroCrossProduct_counterexample_aux

-- Empty covers on the empty set satisfy both data conditions and equivalence vacuously.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsLocalMeromorphicDivisorData (∅ : Set E) (fun i : Empty ↦ i.elim)
      (fun i _ ↦ i.elim) (fun i _ ↦ i.elim) := by
  simp [IsLocalMeromorphicDivisorData]

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsLocalMeromorphicDivisorData (∅ : Set E) (fun _ : Unit ↦ ∅)
      (fun _ _ ↦ 0) (fun _ _ ↦ 0) := by
  simp [IsLocalMeromorphicDivisorData]

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    EquivalentLocalDivisorData (fun i : Empty ↦ (i.elim : Set E))
      (fun i _ ↦ i.elim) (fun i : Empty ↦ i.elim) (fun i _ ↦ i.elim) := by
  simp [EquivalentLocalDivisorData]

-- A single chart and an identical family exercise reflexivity.
example (hD : IsLocalDivisorData (univ : Set ℂ) (fun _ : Unit ↦ univ)
    (fun _ z ↦ z)) :
    EquivalentLocalDivisorData (fun _ : Unit ↦ univ) (fun _ z ↦ z)
      (fun _ : Unit ↦ univ) (fun _ z ↦ z) :=
  spec_equivalentLocalDivisorData_refl hD

-- The equations `z` and `1` on the same whole-space chart are not equivalent.
example : ¬ EquivalentLocalDivisorData (fun _ : Unit ↦ (univ : Set ℂ)) (fun _ z ↦ z)
    (fun _ : Unit ↦ univ) (fun _ _ ↦ 1) := by
  intro h
  obtain ⟨u, _, hu0, heq⟩ := h () () 0 ⟨mem_univ _, mem_univ _⟩
  have hz := heq.self_of_nhds
  simp only [mul_one] at hz
  exact hu0 hz.symm

-- Unit denominators, equal pairs, zero base variables, and integer subtraction conventions.
example {n : ℕ} (g : (Fin n → ℂ) × ℂ → ℂ) (p : (Fin n → ℂ) × ℂ) :
    localMeromorphicDivisorAt n g (fun _ ↦ 1) p =
      (localDivisorAt n g p).mapRange Nat.cast (by simp) :=
  spec_localMeromorphicDivisorAt_unit_denominator analyticAt_const one_ne_zero

example (g : (Fin 0 → ℂ) × ℂ → ℂ) (p : (Fin 0 → ℂ) × ℂ) :
    localMeromorphicDivisorAt 0 g g p = 0 := spec_localMeromorphicDivisorAt_self g p

example {α : Type*} (D : α →₀ ℤ) : D - D = 0 := sub_self D

-- An empty middle cover relates arbitrary endpoint families, so endpoint validity is essential.
example :
    IsLocalDivisorData (∅ : Set ℂ) (fun _ : Unit ↦ (∅ : Set ℂ))
        (fun _ (_ : ℂ) ↦ 0) ∧
      EquivalentLocalDivisorData (fun _ : Unit ↦ (univ : Set ℂ)) (fun _ z ↦ z)
        (fun _ : Unit ↦ (∅ : Set ℂ)) (fun _ (_ : ℂ) ↦ 0) ∧
      EquivalentLocalDivisorData (fun _ : Unit ↦ (∅ : Set ℂ)) (fun _ (_ : ℂ) ↦ 0)
        (fun _ : Unit ↦ (univ : Set ℂ)) (fun _ (_ : ℂ) ↦ 1) ∧
      ¬ EquivalentLocalDivisorData (fun _ : Unit ↦ (univ : Set ℂ)) (fun _ z ↦ z)
        (fun _ : Unit ↦ (univ : Set ℂ)) (fun _ (_ : ℂ) ↦ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [IsLocalDivisorData]
  · simp [EquivalentLocalDivisorData]
  · simp [EquivalentLocalDivisorData]
  · intro h
    obtain ⟨u, _, hu0, heq⟩ := h () () 0 ⟨mem_univ _, mem_univ _⟩
    have hz := heq.self_of_nhds
    simp only [mul_one] at hz
    exact hu0 hz.symm

-- Direct uses of the remaining public comparison declarations.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι κ : Type*} {V : ι → Set E} {f : ι → E → ℂ} {W : κ → Set E} {g : κ → E → ℂ}
    (h : EquivalentLocalDivisorData V f W g) : EquivalentLocalDivisorData W g V f :=
  spec_equivalentLocalDivisorData_symm h

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι κ μ : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    {W : κ → Set E} {g : κ → E → ℂ} {R : μ → Set E} {q : μ → E → ℂ}
    (hF : IsLocalDivisorData U V f) (hG : IsLocalDivisorData U W g)
    (hQ : IsLocalDivisorData U R q) (hfg : EquivalentLocalDivisorData V f W g)
    (hgq : EquivalentLocalDivisorData W g R q) : EquivalentLocalDivisorData V f R q :=
  spec_equivalentLocalDivisorData_trans hF hG hQ hfg hgq

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι κ : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    {W : κ → Set E} {g : κ → E → ℂ} (hD : IsLocalDivisorData U V f)
    (hG : IsLocalDivisorData U W g) (h : EquivalentLocalDivisorData V f W g) :
    localDivisorSupport V f = localDivisorSupport W g :=
  spec_equivalentLocalDivisorData_support hD hG h

example {n : ℕ} {ι κ : Type*} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} {W : κ → Set ((Fin n → ℂ) × ℂ)}
    {g : κ → (Fin n → ℂ) × ℂ → ℂ} (h : EquivalentLocalDivisorData V f W g)
    (i : ι) (j : κ) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) (hj : p ∈ W j)
    (hf : AnalyticAt ℂ (f i) p) (hg : AnalyticAt ℂ (g j) p) :
    localDivisorAt n (f i) p = localDivisorAt n (g j) p :=
  spec_equivalentLocalDivisorData_localDivisorAt h i j p hi hj hf hg

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι κ : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    {W : κ → Set E} {g : κ → E → ℂ} (hD : IsLocalDivisorData U V f)
    (hG : IsLocalDivisorData U W g) (h : EquivalentLocalDivisorData V f W g) :
    IsLocalDivisorData U (fun ij : ι × κ ↦ V ij.1 ∩ W ij.2) (fun ij ↦ f ij.1) ∧
      (∀ ij : ι × κ, V ij.1 ∩ W ij.2 ⊆ V ij.1) ∧
      (∀ ij : ι × κ, V ij.1 ∩ W ij.2 ⊆ W ij.2) :=
  spec_equivalentLocalDivisorData_commonRefinement hD hG h

example : EquivalentLocalMeromorphicDivisorData
    (fun _ : Unit ↦ (univ : Set ℂ)) (fun _ z ↦ z) (fun _ _ ↦ 1)
    (fun _ : Unit ↦ univ) (fun _ z ↦ z) (fun _ _ ↦ 1) := by
  intro _ _ x _
  refine ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, ?_⟩
  exact Eventually.of_forall fun y ↦ by simp

example {n k : ℕ} {f u : (Fin n → ℂ) × ℂ → ℂ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {m : Fin k → ℕ}
    {p : (Fin n → ℂ) × ℂ} (hf : AnalyticAt ℂ f p) (hf0 : f p = 0)
    (hu : AnalyticAt ℂ u p) (hu0 : u p ≠ 0)
    (hP : ∀ i, AnalyticAt ℂ (P i) p ∧ IsIrreducibleAt (P i) p ∧ 0 < m i)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) p))
    (hfac : f =ᶠ[nhds p] fun y ↦ u y * ∏ i, (P i y) ^ (m i))
    (hPt : ∀ i, AnalyticAt ℂ (fun z ↦ P i (p + z)) 0) :
    ∀ᶠ y in nhds p, ∀ i, P i y = 0 → (∀ j, j ≠ i → P j y ≠ 0) →
      ∀ a : (Fin n → ℂ) × ℂ, fderiv ℂ (P i) y a ≠ 0 →
        analyticOrderAt (fun t : ℂ ↦ f (y + t • a)) 0 =
          localDivisorAt n f p
            (Associates.mk (productAnalyticGermOf (fun z ↦ P i (p + z)) (hPt i))) :=
  spec_localDivisorAt_multiplicity_eq_transverseOrder hf hf0 hu hu0 hP hcP hfac hPt

example {n : ℕ} {ι κ : Type*} {U : Set ((Fin n → ℂ) × ℂ)}
    {V : ι → Set ((Fin n → ℂ) × ℂ)} {g h : ι → (Fin n → ℂ) × ℂ → ℂ}
    {W : κ → Set ((Fin n → ℂ) × ℂ)} {a b : κ → (Fin n → ℂ) × ℂ → ℂ}
    (hD : IsLocalMeromorphicDivisorData U V g h)
    (hA : IsLocalMeromorphicDivisorData U W a b)
    (heq : EquivalentLocalMeromorphicDivisorData V g h W a b) (i : ι) (j : κ)
    (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) (hj : p ∈ W j)
    (hg : AnalyticAt ℂ (g i) p) (hh : AnalyticAt ℂ (h i) p)
    (ha : AnalyticAt ℂ (a j) p) (hb : AnalyticAt ℂ (b j) p) :
    localMeromorphicDivisorAt n (g i) (h i) p =
      localMeromorphicDivisorAt n (a j) (b j) p :=
  spec_localMeromorphicDivisorAt_eq hD hA heq i j p hi hj hg hh ha hb

example : localMeromorphicDivisorAt 0 (fun _ ↦ 0) (fun _ ↦ 0) 0 ≠
    localMeromorphicDivisorAt 0 (fun z ↦ z.2) (fun _ ↦ 1) 0 :=
  spec_zeroCrossProduct_counterexample.2

end HodgeLean.Foundations.AnalyticDivisorAlgebraic15
