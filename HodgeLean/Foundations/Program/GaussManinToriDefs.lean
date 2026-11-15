import HodgeLean.Foundations.Program.GaussManinToriLatticeDefs
import HodgeLean.Foundations.Program.VariationHodgeDefs
import HodgeLean.Foundations.AppellHumbertDefs

/-!
# The weight-one VHS associated to a marked period presentation: definitions

**Marked holomorphic period data** of dimension `g` over a complex manifold `B` is a holomorphic
map `P : B → M_{g × 2g}(ℂ)` whose value at each point is a period matrix: its `2g` columns are
`ℝ`-linearly independent in `ℂ^g`. No total space and no family of complex manifolds is
constructed here; the data only presents, at each `b`, the torus `ℂ^g / Λ_b`, where `Λ_b` is the
`ℤ`-span of the columns of `P b`, a full lattice in the sense of the repository's lattice
quotients (`IsZLattice ℝ`). The marking labels the `k`-th generator of `Λ_b` by the `k`-th
column, for every `b`, so the lattices form a trivial local system and
`H¹(X_b, ℚ) = Hom(Λ_b, ℚ) = ℚ^{2g}` by evaluation on the generators. The variation built from
this data is the weight-one VHS associated to the marked period presentation. The elementary
period-matrix definitions (`d2_IsPeriodMatrix`, `d2_lattice`, `d2_IsRiemannForm`, `d2_hodgeOne`,
…) are in `GaussManinToriLatticeDefs.lean`, which needs only Mathlib.

In these coordinates:
* `H¹(X_b, ℂ) = ℂ^{2g}`, and `F¹ = H^{1,0}(X_b)` is the space of restrictions to `Λ_b` of the
  `ℂ`-linear forms on `ℂ^g` (the differentials `dz_i`): the image of `d2_evalBilin (P b)`, i.e.
  the row space of `P b`;
* a Riemann form is an integral alternating matrix `A` on `Λ_b` whose real extension `E` is
  invariant under the complex structure and has `E(v, i v) > 0` for `v ≠ 0` (the repository's
  convention for `HermitianForm`: `Re H(v, v) = Im H(v, i v)`);
* the polarization of `H¹` is the dual form `Q = (A^{-1})ᵀ`, so that `Q(E(x, ·), E(y, ·)) = E(x, y)`;
* the Kodaira--Spencer map at `b` sends a tangent vector `v` to the linear map
  `H^{1,0} → H¹ / F¹`, `φ ↦ [φ ∘ dP_b(v)]`: the derivative of the frame `φ ↦ φ(columns of P)`
  of `F¹`, read modulo `F¹`. This is the cup product with the Kodaira--Spencer class in the
  linear-algebra form of Griffiths' computation of the differential of the period map.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory Manifold
open scoped TensorProduct ContDiff Matrix

namespace HodgeLean.Foundations.Program

open HodgeBlocks HodgeLean.Foundations.AppellHumbert

section Hodge

variable {g : ℕ}

open scoped Classical in
/-- The weight-one Hodge filtration `F⁰ = H¹`, `F¹ = H^{1,0}`, `F² = 0` of the torus with period
matrix `P`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.4; Griffiths, *Periods of
integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968), §2. -/
def d2_filtration (P : Fin g → Fin (2 * g) → ℂ) :
    ℤ → Submodule ℂ (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ)) :=
  fun p ↦ if p ≤ 0 then ⊤ else if p = 1 then d2_hodgeOne P else ⊥

example (P : Fin g → Fin (2 * g) → ℂ) : d2_filtration P 1 = d2_hodgeOne P := by
  simp [d2_filtration]

end Hodge

section ChartTarget

/-- The chart coordinates of `d1_chartCoord` at the single step `F¹` for the variation of
`g`-dimensional marked period data: one matrix of size `dim H¹`.
Source: Carlson--Müller-Stach--Peters, *Period Mappings and Period Domains* (2017), ch. 4. -/
abbrev d2_ChartTarget (g : ℕ) : Type :=
  Fin 1 → Fin (Module.finrank ℂ (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ))) →
    Fin (Module.finrank ℂ (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ))) → ℂ

example : d2_ChartTarget 1 := 0

end ChartTarget

section Family

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (B : Type*) [TopologicalSpace B] [ChartedSpace E B]

/-- Marked holomorphic period data of dimension `g` over `B`: a holomorphic map to `g × 2g`
matrices whose values are period matrices. It presents at `b` the torus `ℂ^g / Λ_b` with
`Λ_b = d2_lattice (period b)`, and the `k`-th column labels the same generator of every `Λ_b`.
No total space is part of the data.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §8.1 (families of
period matrices); Kodaira, *Complex Manifolds and Deformation of Complex Structures* (1986),
§2.3, Example 2.13 (the family of complex tori). -/
structure d2_MarkedPeriodFamily (g : ℕ) where
  period : B → Fin g → Fin (2 * g) → ℂ
  holomorphic : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin g → Fin (2 * g) → ℂ) ω period
  isPeriod : ∀ b, d2_IsPeriodMatrix (period b)

/-- The constant period data of a fixed period matrix.
Source: Kodaira, *Complex Manifolds and Deformation of Complex Structures*, §2.3 (trivial
families). -/
def d2_constFamily {g : ℕ} (P : Fin g → Fin (2 * g) → ℂ) (hP : d2_IsPeriodMatrix P) :
    d2_MarkedPeriodFamily E B g where
  period _ := P
  holomorphic := contMDiff_const
  isPeriod _ := hP

example (P : Fin 0 → Fin (2 * 0) → ℂ) : d2_MarkedPeriodFamily E B 0 :=
  haveI : IsEmpty (Fin (2 * 0)) := ⟨fun k ↦ Fin.elim0 k⟩
  d2_constFamily E B P linearIndependent_empty_type

variable {E B} {g : ℕ}

/-- The lattice of the fibre torus at `b`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
def d2_fiberLattice (X : d2_MarkedPeriodFamily E B g) (b : B) : Submodule ℤ (Fin g → ℂ) :=
  d2_lattice (X.period b)

example (X : d2_MarkedPeriodFamily E B g) (b : B) :
    d2_fiberLattice X b = d2_lattice (X.period b) := rfl

variable (B) in
/-- The local system `b ↦ H¹(X_b, ℚ) = Hom(Λ_b, ℚ)`, written in the marked coordinates `ℚ^{2g}`:
the marking identifies every `Λ_b` with `ℤ^{2g}` compatibly along paths, so parallel transport is
the identity in these coordinates.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, ch. 9 (the local system
`R¹f_*ℚ`); Birkenhake--Lange, §1.1. -/
abbrev d2_localSystem (g : ℕ) : d1_LocalSystem B :=
  d1_constLocalSystem B (Fin (2 * g) → ℚ)

example (b : B) : Module.finrank ℚ ((d2_localSystem B g).fiber b) = 2 * g :=
  Module.finrank_fin_fun ℚ

/-- The Kodaira--Spencer map at `b` in linear-algebra form: a tangent vector `v` goes to the map
`H^{1,0} → H¹ / F¹`, `φ ↦ [(φ(dP_b(v) e_k))_k]`, the derivative along `v` of the holomorphic
frame `φ ↦ (φ(P e_k))_k` of `F¹`, read modulo `F¹_b`.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968),
§1 (the differential of the period map is the cup product with the Kodaira--Spencer class);
Voisin, *Hodge Theory I*, Theorem 10.21; Kodaira, *Complex Manifolds and Deformation of Complex
Structures*, §4.1. -/
def d2_kodairaSpencer (X : d2_MarkedPeriodFamily E B g) (b : B) :
    E →ₗ[ℂ] Module.Dual ℂ (Fin g → ℂ) →ₗ[ℂ]
      (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ)) ⧸ d2_hodgeOne (X.period b) :=
  (d2_evalBilin.compr₂ (d2_hodgeOne (X.period b)).mkQ) ∘ₗ
    (show E →L[ℂ] (Fin g → Fin (2 * g) → ℂ) from
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin g → Fin (2 * g) → ℂ) X.period b).toLinearMap

example (X : d2_MarkedPeriodFamily E B g) (b : B) (v : E) (φ : Module.Dual ℂ (Fin g → ℂ)) :
    d2_kodairaSpencer X b v φ = (d2_hodgeOne (X.period b)).mkQ
      (d2_evalBilin (show Fin g → Fin (2 * g) → ℂ from
        mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin g → Fin (2 * g) → ℂ) X.period b v) φ) :=
  rfl


/-- The polarized variation of marked period data, assembled from the three properties of its
filtration. The frozen `d2_toriVHS` supplies them; this constructor only fixes the data: the
local system `d2_localSystem`, weight one, the filtration `d2_filtration`, and the constant form
`d2_dualForm A`.
Source: Griffiths, Publ. Math. IHES 38 (1970), §§1--3; Carlson--Müller-Stach--Peters, ch. 4. -/
def d2_mkVHS [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (hhol : ∀ p, (d2_localSystem B g).IsHolomorphicSubbundle E
      (fun b ↦ d2_filtration (X.period b) p))
    (htr : (d2_localSystem B g).IsTransversal E (fun p b ↦ d2_filtration (X.period b) p))
    (hpol : ∀ b, d1_IsPolarizedFiltration 1 (d2_dualForm A) (d2_filtration (X.period b))) :
    d1_PolarizedVHS E B where
  L := d2_localSystem B g
  weight := 1
  F p b := d2_filtration (X.period b) p
  Q _ := d2_dualForm A
  holomorphic := hhol
  transversal := htr
  flat _ _ _ _ _ := rfl
  polarized := hpol

example [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (hhol : ∀ p, (d2_localSystem B g).IsHolomorphicSubbundle E
      (fun b ↦ d2_filtration (X.period b) p))
    (htr : (d2_localSystem B g).IsTransversal E (fun p b ↦ d2_filtration (X.period b) p))
    (hpol : ∀ b, d1_IsPolarizedFiltration 1 (d2_dualForm A) (d2_filtration (X.period b)))
    (b : B) : (d2_mkVHS X A hhol htr hpol).F 1 b = d2_hodgeOne (X.period b) := by
  show d2_filtration (X.period b) 1 = _
  simp [d2_filtration]

/-- The period map of the period data in the chart of `d1_chartCoord` centred at the filtration of
`b₀`, at the step `F¹`: the matrix of the projection onto `F¹_b` along `\bar F¹_{b₀}`. The local
system is constant in the marked coordinates, so no transport and no simply connected set enter.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
def d2_chartPeriod (X : d2_MarkedPeriodFamily E B g) (b₀ : B) : B → d2_ChartTarget g :=
  fun b ↦ d1_chartCoord 1 (d2_filtration (X.period b₀)) 1 1 (d2_filtration (X.period b))

example (X : d2_MarkedPeriodFamily E B g) (b₀ : B) : d2_ChartTarget g := d2_chartPeriod X b₀ b₀

/-- The open set of points whose `F¹` is a complement of `\bar F¹_{b₀}`, the domain of the chart.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
def d2_chartDomain (X : d2_MarkedPeriodFamily E B g) (b₀ : B) : Set B :=
  interior {b | d2_filtration (X.period b) ∈
    d1_chartDomainSet 1 (d2_filtration (X.period b₀)) 1 1}

example (X : d2_MarkedPeriodFamily E B g) (b₀ : B) : IsOpen (d2_chartDomain X b₀) := isOpen_interior

end Family

section Witnesses

/-- The upper half plane `{τ | Im τ > 0}`, an open subset of `ℂ` and so a complex manifold.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §8.1 (`𝔥₁`). -/
def d2_upperHalf : TopologicalSpace.Opens ℂ :=
  ⟨{τ | 0 < τ.im}, isOpen_lt continuous_const Complex.continuous_im⟩

example : Complex.I ∈ d2_upperHalf := by
  show 0 < Complex.I.im
  simp

end Witnesses


section G32

open scoped Classical in
/-- For period data over an open set `W` of the G32 parameter space `ℂ¹⁰`: the chart domain, as a
subset of `ℂ¹⁰`.
Source: G32 v0.16, §5 (the parameter chart `V` of the Hurwitz family); Griffiths, Publ. Math.
IHES 38 (1970), §1. -/
def d2_g32Chart {g : ℕ} {W : TopologicalSpace.Opens (Fin 10 → ℂ)}
    (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ : W) : Set (Fin 10 → ℂ) :=
  Subtype.val '' d2_chartDomain X b₀

example {g : ℕ} {W : TopologicalSpace.Opens (Fin 10 → ℂ)}
    (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g)
    (b₀ : W) : d2_g32Chart X b₀ ⊆ W := by
  rintro _ ⟨b, _, rfl⟩
  exact b.2

open scoped Classical in
/-- The period map in the coordinates `κ` of `𝓗₃ ⊆ ℂ⁹`: `t ↦ κ(d2_chartPeriod t)` on `W`,
extended by `0`. The coordinate change `κ` from the chart of `d1_chartCoord` to the bounded
realization of `𝓗₃` is an input.
Source: G32 v0.16, §5 and the proof of Theorem 7.2 (the period map `Φ : Δ → 𝓗₃`). -/
def d2_g32Period {g : ℕ} {W : TopologicalSpace.Opens (Fin 10 → ℂ)}
    (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ : W) (κ : d2_ChartTarget g → Fin 9 → ℂ) :
    (Fin 10 → ℂ) → Fin 9 → ℂ :=
  fun t ↦ if h : t ∈ W then κ (d2_chartPeriod X b₀ ⟨t, h⟩) else 0

example {g : ℕ} {W : TopologicalSpace.Opens (Fin 10 → ℂ)}
    (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g)
    (b₀ : W) (κ : d2_ChartTarget g → Fin 9 → ℂ) (b : W) :
    d2_g32Period X b₀ κ b = κ (d2_chartPeriod X b₀ b) := by
  simp [d2_g32Period]

end G32

end HodgeLean.Foundations.Program
