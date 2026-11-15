import HodgeLean.Foundations.AnalyticDivisorAlgebraic20

/-! # Certified factors and continuation

The quotient uses continuation inside the smooth locus of the reduced support, independently
of the multiplicity of an equation. Carriers are sets of anchors, not zero sets of a globally
chosen representative function. HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic21

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic17

/-- A selected member of a complete local irreducible factorization at a point of its chart.
The certificate is precisely the factorization data of stage fourteen, with a selected index.
Source: `spec_exists_irreducible_decomposition_at`, Gunning--Rossi II.B, Theorems 3--6. -/
structure gaga21_LocalFactorOccurrence {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (V : ι → Set E) (f : ι → E → ℂ) where
  chart : ι
  point : E
  mem_chart : point ∈ V chart
  count : ℕ
  unit : E → ℂ
  factors : Fin count → E → ℂ
  exponents : Fin count → ℕ
  selected : Fin count
  unit_analytic : AnalyticAt ℂ unit point
  unit_ne : unit point ≠ 0
  factor_data : ∀ j, AnalyticAt ℂ (factors j) point ∧
    IsIrreducibleAt (factors j) point ∧ 0 < exponents j
  coprime : Pairwise (fun j l ↦ IsCoprimeAt (factors j) (factors l) point)
  factorization : f chart =ᶠ[𝓝 point] fun y ↦ unit y * ∏ j, factors j y ^ exponents j
  selected_zero : factors selected point = 0

/-- The selected representative is used only as a germ at the occurrence's anchor.
Source: Gunning--Rossi II.B, Definition 1. -/
def gaga21_LocalFactorOccurrence.factor {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {V : ι → Set E} {f : ι → E → ℂ}
    (a : gaga21_LocalFactorOccurrence V f) : E → ℂ := a.factors a.selected

/-- Smooth points of the reduced support, using local defining equations with nonzero derivative.
This definition works for nonreduced input equations as well.
Source: Gunning--Rossi III.A, Theorem 4 (hypersurface Jacobian criterion). -/
def gaga21_regularSupport {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : ι → Set E) (f : ι → E → ℂ) : Set E :=
  {p | p ∈ localDivisorSupport V f ∧ ∃ h : E → ℂ,
    AnalyticAt ℂ h p ∧ h p = 0 ∧ fderiv ℂ h p ≠ 0 ∧
    ∀ᶠ y in 𝓝 p, y ∈ localDivisorSupport V f ↔ h y = 0}

/-- Two local branches continue if their smooth germs lie in one connected subset of the
reduced regular support. The anchors need not coincide and may be singular. A branch's
smooth germ is nonempty by local analytic geometry, not by an input to this relation.
Source: Chirka, *Complex Analytic Sets*, §5.1 (continuation along the regular part). -/
def gaga21_continuation {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {V : ι → Set E} {f : ι → E → ℂ}
    (a b : gaga21_LocalFactorOccurrence V f) : Prop :=
  ∃ R : Set E, IsConnected R ∧ R ⊆ gaga21_regularSupport V f ∧
    (∀ᶠ y in 𝓝 a.point, a.factor y = 0 → y ∈ gaga21_regularSupport V f → y ∈ R) ∧
    (∀ᶠ y in 𝓝 b.point, b.factor y = 0 → y ∈ gaga21_regularSupport V f → y ∈ R)

/-- Equivalence closure of continuation, including transitions between different anchors.
Source: Chirka §5.1; `Relation.EqvGen.setoid`. -/
def gaga21_componentSetoid {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : ι → Set E) (f : ι → E → ℂ) : Setoid (gaga21_LocalFactorOccurrence V f) :=
  Relation.EqvGen.setoid gaga21_continuation

/-- Global components indexed by certified branch occurrences modulo continuation.
Source: Chirka §5.1 (local branches and global irreducible components). -/
abbrev gaga21_GlobalComponent {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : ι → Set E) (f : ι → E → ℂ) := Quotient (gaga21_componentSetoid V f)

/-- The carrier consists of anchors of all local branches in a quotient class. A singular
point can belong to several carriers, and several branches there can belong to one carrier.
Source: Chirka §5.1. -/
def gaga21_componentCarrier {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {V : ι → Set E} {f : ι → E → ℂ} (C : gaga21_GlobalComponent V f) : Set E :=
  {q | ∃ a : gaga21_LocalFactorOccurrence V f,
    Quotient.mk (gaga21_componentSetoid V f) a = C ∧ a.point = q}

/-- Near each point and in each chart, a set is the union of finitely many zero germs of
certified irreducible factors of the chart equation.
Source: Chirka, *Complex Analytic Sets*, §5.1 (local branches of analytic components). -/
def gaga21_FiniteLocalBranches {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : ι → Set E) (f : ι → E → ℂ) (C : Set E) : Prop :=
  ∀ q ∈ C, ∀ i, q ∈ V i →
    ∃ k : ℕ, ∃ a : Fin k → gaga21_LocalFactorOccurrence V f,
      0 < k ∧ (∀ j, (a j).point = q ∧ (a j).chart = i) ∧
      (∀ᶠ y in 𝓝 q, y ∈ C ↔ ∃ j, (a j).factor y = 0)

/-- A weighted family of subsets, with no stored chart equations or geometric proof fields.
Analyticity and local finiteness of the constructed family are separate statements.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1 (divisors). -/
structure gaga21_WeightedCarrierFamily (E : Type*) where
  Component : Type
  carrier : Component → Set E
  multiplicity : Component → ℕ

/-- The coefficient of a local branch after restriction: sum the weights of carriers containing
its zero germ. For a genuine irreducible branch, the identification theorem ensures uniqueness.
Source: Griffiths--Harris, Ch. 1 §1 (restriction of divisors by local branches). -/
def gaga21_restrictMultiplicity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : gaga21_WeightedCarrierFamily E) (q : E) (h : E → ℂ) : ℕ := by
  classical
  exact ∑ᶠ C, if (∀ᶠ y in 𝓝 q, h y = 0 → y ∈ D.carrier C) then D.multiplicity C else 0

/-- A coordinate factor with a full one-factor certificate in every positive ambient dimension.
Source: `gaga17_axis_power_data` with exponent one. -/
def gaga21_axisOccurrence (n : ℕ) (q : (Fin n → ℂ) × ℂ) (hq : q.2 = 0) :
    gaga21_LocalFactorOccurrence (fun _ : Unit ↦ (univ : Set ((Fin n → ℂ) × ℂ))) (fun _ y ↦ y.2) where
  chart := ()
  point := q
  mem_chart := mem_univ _
  count := 1
  unit := fun _ ↦ 1
  factors := fun _ y ↦ y.2
  exponents := fun _ ↦ 1
  selected := 0
  unit_analytic := analyticAt_const
  unit_ne := one_ne_zero
  factor_data := fun _ ↦ ⟨analyticAt_snd, (gaga17_axis_power_data n 1 (by decide)).2 q hq,
    Nat.zero_lt_one⟩
  coprime := fun a b hab ↦ (hab (Subsingleton.elim a b)).elim
  factorization := Eventually.of_forall fun y ↦ by simp
  selected_zero := hq

/-- Two identical crossing charts with certified coordinate factors at the node.
Source: `gaga17_crossing_data` and its displayed factorization. -/
def gaga21_crossingOccurrence (i a : Fin 2) :
    gaga21_LocalFactorOccurrence (fun _ : Fin 2 ↦ univ)
      (fun (_ : Fin 2) (y : (Fin 1 → ℂ) × ℂ) ↦ y.1 0 * y.2) where
  chart := i
  point := 0
  mem_chart := mem_univ _
  count := 2
  unit := fun _ ↦ 1
  factors := gaga17_crossingFactors
  exponents := fun _ ↦ 1
  selected := a
  unit_analytic := analyticAt_const
  unit_ne := one_ne_zero
  factor_data := fun j ↦ ⟨gaga17_crossing_data.2.1 j 0 (mem_univ _),
    gaga17_crossing_data.2.2.1 j, Nat.zero_lt_one⟩
  coprime := gaga17_crossing_data.2.2.2.1
  factorization := Eventually.of_forall fun y ↦ by
    simp [gaga17_crossingFactors, Fin.prod_univ_two]
  selected_zero := by fin_cases a <;> rfl

/-- The weighted quotient family, constructed without retaining its input chart data.
Weights use a representative; representative independence is a separate theorem.
Source: Chirka §2.3 and §5.1 (multiplicity on global components). -/
def gaga21_gluedDivisor {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : ι → Set E) (f : ι → E → ℂ) : gaga21_WeightedCarrierFamily E where
  Component := gaga21_GlobalComponent V f
  carrier := gaga21_componentCarrier
  multiplicity C := (Quotient.out C).exponents (Quotient.out C).selected

/-- The nodal polynomial in product coordinates.
Source: Chirka §5.1; the normalization is `(t²-1, t(t²-1))`. -/
def gaga21_node (z : (Fin 1 → ℂ) × ℂ) : ℂ :=
  z.2 ^ 2 - (z.1 0) ^ 2 * (z.1 0 + 1)

example : gaga21_WeightedCarrierFamily ((Fin 0 → ℂ) × ℂ) :=
  gaga21_gluedDivisor (fun _ : Unit ↦ univ) (fun _ y ↦ y.2)
example : gaga21_node 0 = 0 := by norm_num [gaga21_node]

-- Concrete checks for each definition; geometric assertions are in the public stage file.
example : gaga21_LocalFactorOccurrence (fun _ : Unit ↦ (univ : Set ((Fin 0 → ℂ) × ℂ)))
    (fun _ y ↦ y.2) := gaga21_axisOccurrence 0 0 rfl
example : (gaga21_axisOccurrence 0 0 rfl).factor 0 = 0 := rfl
example : gaga21_regularSupport (fun _ : Empty ↦ (∅ : Set ℂ)) (fun _ _ ↦ 1) = ∅ := by
  ext p
  simp [gaga21_regularSupport, localDivisorSupport]
example : gaga21_continuation (gaga21_axisOccurrence 0 0 rfl)
    (gaga21_axisOccurrence 0 0 rfl) := by
  refine ⟨{0}, isConnected_singleton, ?_, ?_, ?_⟩
  · intro y hy
    have hy0 : y = 0 := hy
    subst y
    refine ⟨⟨(), mem_univ _, rfl⟩, (fun z ↦ z.2), analyticAt_snd, rfl, ?_, ?_⟩
    · have hd : HasFDerivAt (fun z : (Fin 0 → ℂ) × ℂ ↦ z.2)
          (ContinuousLinearMap.snd ℂ (Fin 0 → ℂ) ℂ) 0 := by fun_prop
      rw [hd.fderiv]
      intro h
      have hh := congrArg (fun L : ((Fin 0 → ℂ) × ℂ) →L[ℂ] ℂ ↦ L (0, 1)) h
      simp at hh
    · exact Eventually.of_forall fun y ↦ by simp [localDivisorSupport]
  all_goals
    exact Eventually.of_forall fun y hy _ ↦
      (show y = 0 from Prod.ext (Subsingleton.elim _ _) hy)
example : (gaga21_componentSetoid _ _).r (gaga21_axisOccurrence 0 0 rfl)
    (gaga21_axisOccurrence 0 0 rfl) := Relation.EqvGen.refl _
example : gaga21_GlobalComponent (fun _ : Unit ↦ (univ : Set ((Fin 0 → ℂ) × ℂ)))
    (fun _ y ↦ y.2) := Quotient.mk _ (gaga21_axisOccurrence 0 0 rfl)
example : (0 : (Fin 0 → ℂ) × ℂ) ∈
    gaga21_componentCarrier (Quotient.mk _ (gaga21_axisOccurrence 0 0 rfl)) :=
  ⟨gaga21_axisOccurrence 0 0 rfl, rfl, rfl⟩
example : gaga21_WeightedCarrierFamily ℂ := ⟨Empty, fun a ↦ a.elim, fun a ↦ a.elim⟩
example : gaga21_restrictMultiplicity
    (⟨Empty, fun a ↦ a.elim, fun a ↦ a.elim⟩ : gaga21_WeightedCarrierFamily ℂ) 0 id = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro a
  exact a.elim
example : (gaga21_axisOccurrence 1 0 rfl).point = 0 := rfl
example : (gaga21_crossingOccurrence 1 0).chart = 1 := rfl

end HodgeLean.Foundations.AnalyticDivisorAlgebraic21
