import HodgeLean.Blocks.HodgeStructure.HodgeClass
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
import HodgeLean.Meta.Tags

open scoped TensorProduct
noncomputable section
namespace HodgeBlocks

variable (V : Type*) [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- Data for stating the Hodge conjecture for the rational cohomology of an abelian variety
`A` of dimension `g`, over an abstract weight-one rational Hodge structure `V` standing for
`H^1(A, ℚ)`: `H^*(A,ℚ) = Λ^*V` with its Hodge decomposition, bundled degree by degree since this
project has not built a Hodge structure on exterior powers from `weight1` alone
(`HodgeBlocks/HodgeStructure/ExteriorPower.lean` explicitly defers that construction).
Source: Birkenhake-Lange, Complex Abelian Varieties, Lemma 1.3.1 (`birkenhake-lange.txt:851-869`: "The canonical map ∧ⁿ H¹(X,ℤ) → Hⁿ(X,ℤ) induced by the cup product is an isomorphism for every n ≥ 1", for X a complex torus, hence integrally and a fortiori rationally) together with Theorem 1.4.1(a)(b) (`birkenhake-lange.txt:975-1003`: the de Rham/Dolbeault isomorphism Hⁿ(X,ℂ) ≃ ⊕_{p+q=n} H^q(Ω_X^p), compatible with the cup-product exterior-algebra structure via §1.3, giving the induced Hodge decomposition on each ∧ⁿH¹).

**Honest disclosure (referee finding, hodge-LEAN17):** this structure does NOT enforce, by any
field, that `cohomology m` is literally the Hodge structure induced from `weight1`'s `m`-th
wedge power in the sense of Theorem 1.4.1 above -- doing so would need the base-change/exterior-
power construction that `HodgeBlocks/HodgeStructure/ExteriorPower.lean` explicitly defers, and
is not attempted here. `weight1` and `cohomology` are independent data; an instantiation is
faithful to an actual abelian variety only when the caller supplies fields that really do satisfy
this compatibility, which nothing in this file checks or proves. `rank_eq` and `weight1` are, in
particular, not used by any theorem below. -/
@[hodge_hypothesis]
structure AbelianVarietyCohomology where
  g : ℕ
  rank_eq : Module.finrank ℚ V = 2 * g
  weight1 : QHodgeStructure 1 V
  cohomology : (m : ℕ) → QHodgeStructure (m : ℤ) (⋀[ℚ]^m V)

variable {V}

/-- **The milestone statement.** Every Hodge class in `Λ^{2p} V` (standing for `H^{2p}(A,ℚ)`) is
algebraic, for a chosen algebraicity predicate `IsAlgebraic`. -/
def HodgeConjectureFor (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop) : Prop :=
  ∀ (p : ℕ) (v : ⋀[ℚ]^(2 * p) V),
    IsHodgeClass (p := (p : ℤ)) (S.cohomology (2 * p)) v → IsAlgebraic v

/-- A **necessary interface** a cycle-class map (or any candidate algebraicity predicate) must
satisfy for `HodgeConjectureFor` to be a sensible question to ask of it: algebraic classes form
a `ℚ`-subalgebra of `Λ^* V` (containing `1` and closed under `0`, `+`, `ℚ`-scalars, and the
wedge product), consist of Hodge classes, and the given `polarization` class (in degree 2) is
algebraic.
Source: the codimension-1 case is Voisin HTCAG I, Theorem 11.30 (`voisin-htcag1.txt:8229-8236`, integral (1,1) classes = image of c₁ : Pic X → H²(X,ℤ)) and Corollary 11.34 (`voisin-htcag1.txt:8261-8263`, for X projective, these are divisor classes); landing in Hodge classes is a standard PROPERTY of the cycle class map (not a matter of definition), and is not separately quoted here for the general (all-codimension) case beyond the codimension-1 citation above -- state this honestly as the standard shape of a cycle class map, not as a specific higher-codimension theorem quoted verbatim. The polarization class is algebraic by definition (the class of an ample line bundle on the abelian variety).

**Honest disclosure (referee finding, hodge-LEAN17): this is necessary, not sufficient.** These
fields do not CHARACTERIZE the image of an actual cycle class map, only give properties every
such image has. A non-geometric `IsAlgebraic` (for example the constantly-`True` predicate) can
satisfy every field of this structure whenever `S.cohomology`'s Hodge grading happens to make
every class of type `(p,p)` -- as the file's own degenerate `PUnit` witness below does, entirely
deliberately, to check non-vacuity. `HodgeConjectureFor S IsAlgebraic` is therefore faithful to
"the Hodge conjecture for an abelian variety" only when the caller's `S` and `IsAlgebraic`
additionally really are the cohomology and the cycle-class image of an actual abelian variety --
a correspondence this abstract interface cannot force and does not claim to force. -/
@[hodge_hypothesis]
structure IsCycleClassPredicate (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop) (polarization : ⋀[ℚ]^2 V) : Prop where
  /-- A `ℚ`-subalgebra contains the degree-zero unit. -/
  one_mem : IsAlgebraic (exteriorPower.ιMulti ℚ 0 Fin.elim0 : ⋀[ℚ]^0 V)
  zero_mem : ∀ {m}, IsAlgebraic (0 : ⋀[ℚ]^m V)
  add_mem : ∀ {m} {v w : ⋀[ℚ]^m V}, IsAlgebraic v → IsAlgebraic w → IsAlgebraic (v + w)
  smul_mem : ∀ {m} (c : ℚ) {v : ⋀[ℚ]^m V}, IsAlgebraic v → IsAlgebraic (c • v)
  wedge_mem : ∀ {m n} {v : ⋀[ℚ]^m V} {w : ⋀[ℚ]^n V},
      IsAlgebraic v → IsAlgebraic w → IsAlgebraic (exteriorPower.wedge ℚ V m n v w)
  isHodge : ∀ {p : ℕ} {v : ⋀[ℚ]^(2 * p) V}, IsAlgebraic v →
    IsHodgeClass (p := (p : ℤ)) (S.cohomology (2 * p)) v
  polarization_mem : IsAlgebraic polarization

/-- The smallest class of exterior-power elements containing `0` and every degree-2 Hodge
class, closed under `+`, `ℚ`-scalars, and wedge product: the elements the "Hodge ring generated
in degree 2" hypothesis says every Hodge class belongs to. Pure definition, no citation needed
(this is the standard "ring generated by X" closure, spelled out because this project has no
general subalgebra-closure gadget for graded exterior powers). -/
inductive IsGenByDeg2Hodge (S : AbelianVarietyCohomology V) : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop
  | one : IsGenByDeg2Hodge S (exteriorPower.ιMulti ℚ 0 Fin.elim0 : ⋀[ℚ]^0 V)
  | zero {m} : IsGenByDeg2Hodge S (0 : ⋀[ℚ]^m V)
  | deg2 (v : ⋀[ℚ]^2 V) (hv : IsHodgeClass (p := 1) (S.cohomology 2) v) :
      IsGenByDeg2Hodge S v
  | add {m} {v w : ⋀[ℚ]^m V} : IsGenByDeg2Hodge S v → IsGenByDeg2Hodge S w →
      IsGenByDeg2Hodge S (v + w)
  | smul {m} (c : ℚ) {v : ⋀[ℚ]^m V} : IsGenByDeg2Hodge S v → IsGenByDeg2Hodge S (c • v)
  | wedge {m n} {v : ⋀[ℚ]^m V} {w : ⋀[ℚ]^n V} : IsGenByDeg2Hodge S v → IsGenByDeg2Hodge S w →
      IsGenByDeg2Hodge S (exteriorPower.wedge ℚ V m n v w)

/-- The standard "Hodge ring generated in degree 2" hypothesis: every Hodge class of every even
degree lies in `IsGenByDeg2Hodge`, i.e. is a `ℚ`-polynomial combination of divisor classes.
Source: this is the classical reduction strategy; see Markman, "Secant Sheaves and Weil Classes on Abelian Varieties", ICM 2026 Proceedings Vol. 3, §1.1 (`siam-25m1803796.txt:95-103`): "Mumford and Tate tried to prove the Hodge conjecture for abelian varieties by showing that the ℚ-algebra of rational (p,p) classes is generated by those of type (1,1), for which the conjecture was known, but Mumford found a counterexample to this" -- i.e. this hypothesis is cited here as the historically attempted (and, per Mumford's counterexample, not always true) route, not as an established fact about every abelian variety. -/
@[hodge_hypothesis]
structure HodgeRingGeneratedInDegreeTwo (S : AbelianVarietyCohomology V) : Prop where
  generated : ∀ (p : ℕ) {v : ⋀[ℚ]^(2 * p) V},
      IsHodgeClass (p := (p : ℤ)) (S.cohomology (2 * p)) v →
      IsGenByDeg2Hodge S v

/-- **The standard consequence**: if algebraic classes form a subalgebra containing every Hodge
class of degree 2, and every Hodge class of every degree is generated in degree 2, then the
Hodge conjecture holds. Proved directly by induction on `IsGenByDeg2Hodge`. -/
@[hodge_milestone]
theorem hodgeConjecture_of_generatedInDegreeTwo (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop) {polarization : ⋀[ℚ]^2 V}
    (hAlg : IsCycleClassPredicate S IsAlgebraic polarization)
    (hdeg2 : ∀ v : ⋀[ℚ]^2 V, IsHodgeClass (p := 1) (S.cohomology 2) v → IsAlgebraic v)
    (hgen : HodgeRingGeneratedInDegreeTwo S) :
    HodgeConjectureFor S (fun {m} => IsAlgebraic (m := m)) := by
  intro p v hv
  have h := hgen.generated p hv
  have generated_isAlgebraic : ∀ {m : ℕ} {x : ⋀[ℚ]^m V},
      IsGenByDeg2Hodge S x → IsAlgebraic x := by
    intro m x hx
    induction hx with
    | one => exact hAlg.one_mem
    | zero => exact hAlg.zero_mem
    | deg2 v hv => exact hdeg2 v hv
    | add hv hw ihv ihw => exact hAlg.add_mem ihv ihw
    | smul c hv ih => exact hAlg.smul_mem c ih
    | wedge hv hw ihv ihw => exact hAlg.wedge_mem ihv ihw
  exact generated_isAlgebraic h

/-- **Lefschetz (1,1)**, cited directly as a hypothesis structure (this project represents cited
geometric/analytic theorems as `structure`s over free parameters, never as `axiom`s -- see
`HodgeBlocks/Axioms/README.md`): every Hodge class in `H^2` (`Λ^2 V`) is algebraic (the class of
a divisor).
Source: Voisin, Hodge Theory and Complex Algebraic Geometry I, Theorem 11.30 (`voisin-htcag1.txt:8229-8236`): "Let X be a Kahler manifold. Then Hdg²(X,ℤ) is equal to the image of the map c₁ : Pic X → H²(X,ℤ)" -- exact hypothesis: X compact Kähler, conclusion is for INTEGRAL (1,1) classes; the rational statement used here follows by scaling a rational class to an integral multiple (not itself in the quoted theorem -- disclose this honestly in the docstring as the step from integral to rational). Corollary 11.34 (`voisin-htcag1.txt:8261-8263`) gives the divisor-cycle wording for X projective. **An abelian variety is automatically projective** (it embeds in projective space via an ample line bundle associated to a polarization), so Corollary 11.34's hypothesis is immaterial for the intended geometric instantiation of `S`; a fully abstract `S : AbelianVarietyCohomology V`, on the other hand, carries no field asserting or requiring this, so the structure does not itself encode projectivity (referee finding, hodge-LEAN17). -/
@[hodge_hypothesis]
structure LefschetzOneOne (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop) : Prop where
  implication : ∀ v : ⋀[ℚ]^2 V,
    IsHodgeClass (p := 1) (S.cohomology 2) v → IsAlgebraic v

/-- Lefschetz (1,1), named for exactly what it proves: extracting the cited implication. -/
@[hodge_milestone]
theorem lefschetz_one_one (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop)
    (L : LefschetzOneOne S IsAlgebraic) :
    ∀ v : ⋀[ℚ]^2 V, IsHodgeClass (p := 1) (S.cohomology 2) v → IsAlgebraic v :=
  L.implication

/-- Every degree-zero exterior-power class is algebraic once the algebraicity predicate contains the
unit.  This is unconditional on being a Hodge class: `⋀[ℚ]^0 V` is one-dimensional. -/
@[hodge_milestone]
theorem isAlgebraic_of_degree_zero (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop)
    {polarization : ⋀[ℚ]^2 V}
    (hAlg : IsCycleClassPredicate S IsAlgebraic polarization) :
    ∀ v : ⋀[ℚ]^0 V, IsAlgebraic v := by
  intro v
  let c := exteriorPower.zeroEquiv ℚ V v
  have hv : v = c • (exteriorPower.ιMulti ℚ 0 Fin.elim0 : ⋀[ℚ]^0 V) := by
    apply (exteriorPower.zeroEquiv ℚ V).injective
    simp [c]
  rw [hv]
  exact hAlg.smul_mem c hAlg.one_mem

/-- The `g`-fold wedge power of a degree-two polarization, with the canonical degree-zero unit as
its zeroth power. -/
def polarizationPow (polarization : ⋀[ℚ]^2 V) : ∀ g : ℕ, ⋀[ℚ]^(2 * g) V
  | 0 => exteriorPower.ιMulti ℚ 0 Fin.elim0
  | g + 1 =>
      have h : 2 * g + 2 = 2 * (g + 1) := by ring
      h ▸ exteriorPower.wedge ℚ V (2 * g) 2 (polarizationPow polarization g) polarization

/-- Every wedge power of an algebraic polarization is algebraic. -/
@[hodge_milestone]
theorem polarizationPow_isAlgebraic (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop) {polarization : ⋀[ℚ]^2 V}
    (hAlg : IsCycleClassPredicate S IsAlgebraic polarization) (g : ℕ) :
    IsAlgebraic (polarizationPow polarization g) := by
  induction g with
  | zero => exact hAlg.one_mem
  | succ g ih =>
      unfold polarizationPow
      apply hAlg.wedge_mem ih hAlg.polarization_mem

/-- The top exterior power of the rational cohomology space is one-dimensional. -/
theorem finrank_top_exteriorPower (S : AbelianVarietyCohomology V) :
    Module.finrank ℚ (⋀[ℚ]^(2 * S.g) V) = 1 := by
  letI : Unique (Set.powersetCard (Fin (Module.finrank ℚ V)) (Module.finrank ℚ V)) :=
    { default := ⟨Finset.univ, by simp⟩
      uniq s := Subtype.ext (Finset.eq_univ_of_card _ (by simpa using s.2)) }
  rw [← S.rank_eq]
  exact Module.finrank_eq_card_basis
    ((Module.finBasis ℚ V).exteriorPower (Module.finrank ℚ V)) |>.trans Fintype.card_unique

/-- Cited nonvanishing of the top polarization power.  Birkenhake--Lange, *Complex Abelian
Varieties*, gives the positivity input immediately before Geometric Riemann--Roch Theorem 3.6.3:
for a positive definite (ample/polarization) line bundle, `χ(L) = d₁⋯d_g` with every `dᵢ > 0`,
so `χ(L) > 0`.  The theorem at `birkenhake-lange.txt:3638-3644` says
`χ(L) = (1/g!)(L^g)`, where `(L^g) = ∫_X c₁(L)^g`; hence `(L^g) = g! χ(L) ≠ 0`.
The abstract `polarizationPow` here is the Lean encoding of `c₁(L)` raised to the `g`-th
wedge/cup power.  This structure records the rational-coefficient nonvanishing consequence of
that classical positivity fact; it is not separately proved from more basic axioms in this project.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, Geometric Riemann--Roch Theorem 3.6.3 (`birkenhake-lange.txt:3638-3644`) and the positivity input immediately before it. -/
@[hodge_hypothesis]
structure PolarizationTopPowerNonzero (S : AbelianVarietyCohomology V)
    (polarization : ⋀[ℚ]^2 V) : Prop where
  ne_zero : polarizationPow polarization S.g ≠ 0

/-- In top degree every class is algebraic: the top exterior power is a line and its nonzero
polarization-power generator is algebraic. -/
@[hodge_milestone]
theorem isAlgebraic_of_degree_top (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop) {polarization : ⋀[ℚ]^2 V}
    (hAlg : IsCycleClassPredicate S IsAlgebraic polarization)
    (hTop : PolarizationTopPowerNonzero S polarization) :
    ∀ v : ⋀[ℚ]^(2 * S.g) V, IsAlgebraic v := by
  intro v
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (finrank_top_exteriorPower S)
    hTop.ne_zero v
  rw [← hc]
  exact hAlg.smul_mem c (polarizationPow_isAlgebraic S IsAlgebraic hAlg S.g)

private theorem exteriorPower_subsingleton_of_finrank_lt (m : ℕ)
    (hm : Module.finrank ℚ V < m) : Subsingleton (⋀[ℚ]^m V) := by
  apply exteriorPower.subsingleton_of_span_eq_top_of_card_lt (ι := Fin (Module.finrank ℚ V))
    (Module.finBasis ℚ V)
  · exact (Module.finBasis ℚ V).span_eq
  · simpa using hm

/-- Above the top degree every exterior-power class is zero, hence algebraic. -/
@[hodge_milestone]
theorem isAlgebraic_of_degree_above_top (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop) {polarization : ⋀[ℚ]^2 V}
    (hAlg : IsCycleClassPredicate S IsAlgebraic polarization) (m : ℕ)
    (hm : 2 * S.g < m) : ∀ v : ⋀[ℚ]^m V, IsAlgebraic v := by
  intro v
  letI : Subsingleton (⋀[ℚ]^m V) :=
    exteriorPower_subsingleton_of_finrank_lt (V := V) m (by simpa [S.rank_eq] using hm)
  rw [Subsingleton.elim v 0]
  exact hAlg.zero_mem

section DegenerateWitness

/- This degenerate example exists only to check that the interfaces are jointly non-vacuous. -/

private def concentratedWeightZero (W : Type*) [AddCommGroup W] [Module ℚ W]
    [Module.Finite ℚ W] : QHodgeStructure 0 W where
  H := fun pq => if pq = (0, 0) then ⊤ else ⊥
  supported := by
    intro pq h
    simp only [ite_eq_right_iff]
    intro hpq
    subst hpq
    simp at h
  isInternal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · intro i
      by_cases hi : i = (0, 0)
      · subst i
        have hothers : (⨆ (j : ℤ × ℤ) (_ : j ≠ (0, 0)),
            if j = (0, 0) then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] W)) else ⊥) = ⊥ := by
          apply le_antisymm
          · refine iSup_le fun j => iSup_le fun hj => ?_
            simp [hj]
          · exact bot_le
        change Disjoint ⊤ (⨆ (j) (_ : j ≠ (0, 0)),
          if j = (0, 0) then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] W)) else ⊥)
        apply disjoint_bot_right.mono_right
        exact le_of_eq hothers
      · simp [hi]
    · apply top_unique
      exact le_iSup_of_le (0, 0) (by simp)
  conj_symm := by
    intro p q
    by_cases h : (p, q) = (0, 0)
    · have hp : p = 0 := congrArg Prod.fst h
      have hq : q = 0 := congrArg Prod.snd h
      subst p; subst q
      simp only [↓reduceIte, Submodule.map_top]
      rw [LinearMap.range_eq_top]
      intro x
      exact ⟨sigmaQ W x, sigmaQ_involutive W x⟩
    · have h' : (q, p) ≠ (0, 0) := fun h' => by
        have hq : q = 0 := congrArg Prod.fst h'
        have hp : p = 0 := congrArg Prod.snd h'
        exact h (Prod.ext hp hq)
      simp [h, h']

private theorem exteriorPower_punit_subsingleton (m : ℕ) (hm : 0 < m) :
    Subsingleton (⋀[ℚ]^m PUnit) := by
  apply exteriorPower.subsingleton_of_span_eq_top_of_card_lt (ι := Fin 0) Fin.elim0
  · apply top_unique
    intro x _
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  · simpa using hm

private def degenerateCohomology (m : ℕ) : QHodgeStructure (m : ℤ) (⋀[ℚ]^m PUnit) := by
  cases m with
  | zero => exact concentratedWeightZero (⋀[ℚ]^0 PUnit)
  | succ m =>
      letI : Subsingleton (⋀[ℚ]^(m + 1) PUnit) := exteriorPower_punit_subsingleton (m + 1) (by omega)
      exact {
        H := fun _ => ⊥
        supported := by simp
        isInternal := by
          rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
          constructor
          · simp [iSupIndep]
          · ext x
            simp only [iSup_bot, Submodule.mem_bot, Submodule.mem_top]
            simpa using Subsingleton.elim x 0
        conj_symm := by simp }

/-- The zero rational Hodge structure, bundled degree by degree. -/
@[hodge_witness] def degenerateAbelianVarietyCohomology : AbelianVarietyCohomology PUnit where
  g := 0
  rank_eq := by simp only [Module.finrank_zero_of_subsingleton, mul_zero]
  weight1 := by
    letI : Subsingleton PUnit := inferInstance
    exact {
      H := fun _ => ⊥
      supported := by simp
      isInternal := by
        rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
        constructor
        · simp [iSupIndep]
        · ext x
          simp only [iSup_bot, Submodule.mem_bot, Submodule.mem_top]
          simpa using Subsingleton.elim x 0
      conj_symm := by simp }
  cohomology := degenerateCohomology

def degenerateIsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m PUnit → Prop := fun _ => True

private theorem degenerate_isHodge (p : ℕ) (v : ⋀[ℚ]^(2 * p) PUnit) :
    IsHodgeClass (p := (p : ℤ)) (degenerateAbelianVarietyCohomology.cohomology (2 * p)) v := by
  cases p with
  | zero => simp [IsHodgeClass, degenerateAbelianVarietyCohomology, degenerateCohomology,
      concentratedWeightZero]
  | succ p =>
      have hm : 0 < 2 * (p + 1) := by omega
      letI : Subsingleton (⋀[ℚ]^(2 * (p + 1)) PUnit) :=
        exteriorPower_punit_subsingleton _ hm
      rw [Subsingleton.elim v 0]
      simp [IsHodgeClass, degenerateAbelianVarietyCohomology, degenerateCohomology]

@[hodge_witness] def degenerateCycleClassPredicate : IsCycleClassPredicate degenerateAbelianVarietyCohomology
    degenerateIsAlgebraic (0 : ⋀[ℚ]^2 PUnit) := by
  constructor
  · trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro p v _
    exact degenerate_isHodge p v
  · trivial

@[hodge_witness] def degenerateLefschetzOneOne : LefschetzOneOne degenerateAbelianVarietyCohomology
    degenerateIsAlgebraic := ⟨by intros; trivial⟩

@[hodge_witness] def degenerateHodgeRingGeneratedInDegreeTwo :
    HodgeRingGeneratedInDegreeTwo degenerateAbelianVarietyCohomology where
  generated p {v} _ := by
    cases p with
    | zero =>
        let c := exteriorPower.zeroEquiv ℚ PUnit v
        have hv : v = c • (exteriorPower.ιMulti ℚ 0 Fin.elim0 : ⋀[ℚ]^0 PUnit) := by
          apply (exteriorPower.zeroEquiv ℚ PUnit).injective
          simp [c]
        rw [hv]
        exact .smul c .one
    | succ p =>
        have hm : 0 < 2 * (p + 1) := by omega
        letI : Subsingleton (⋀[ℚ]^(2 * (p + 1)) PUnit) :=
          exteriorPower_punit_subsingleton _ hm
        rw [Subsingleton.elim v 0]
        exact .zero

end DegenerateWitness

end HodgeBlocks
