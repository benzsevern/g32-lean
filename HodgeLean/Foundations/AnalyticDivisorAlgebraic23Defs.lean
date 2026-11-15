import HodgeLean.Foundations.AnalyticDivisorAlgebraic22Chow

/-! # Local factor certificates and generic-point indexing

Only data constructions are defined here. No proposition abbreviates a target.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic23
open Filter Set Topology
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21
open HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open scoped Manifold CategoryTheory.MonObj

/-- A complete local factorization, including the empty factorization at a unit.
Source: Gunning--Rossi II.B, Theorems 3--6; `gaga21_br_decomposition`. -/
structure gaga23_Factorization {d : ℕ} (f : (Fin d → ℂ) → ℂ) (p : Fin d → ℂ) where
  count : ℕ
  unit : (Fin d → ℂ) → ℂ
  factors : Fin count → (Fin d → ℂ) → ℂ
  exponents : Fin count → ℕ
  unit_analytic : AnalyticAt ℂ unit p
  unit_ne : unit p ≠ 0
  factor_data : ∀ a, AnalyticAt ℂ (factors a) p ∧ IsIrreducibleAt (factors a) p ∧
    0 < exponents a
  coprime : Pairwise (fun a b ↦ IsCoprimeAt (factors a) (factors b) p)
  factorization : f =ᶠ[𝓝 p] fun z ↦ unit z * ∏ a, factors a z ^ exponents a

/-- Select a complete local factorization from the existing factorization theorem.
Source: `gaga21_br_decomposition`; units have an empty factor list. -/
def gaga23_factorization {d : ℕ} (f : (Fin d → ℂ) → ℂ) (p : Fin d → ℂ)
    (hf : AnalyticAt ℂ f p) (hnz : ¬ ∀ᶠ z in 𝓝 p, f z = 0) :
    gaga23_Factorization f p := Classical.choice (by
  classical
  by_cases hz : f p = 0
  · obtain ⟨k, u, P, m, hu, hu0, hP, hc, he⟩ := gaga21_br_decomposition hf hz hnz
    exact ⟨⟨k, u, P, m, hu, hu0, hP, hc, he⟩⟩
  · exact ⟨⟨0, f, Fin.elim0, Fin.elim0, hf, hz, fun a ↦ a.elim0,
      fun a ↦ a.elim0, Eventually.of_forall fun z ↦ by simp⟩⟩)

/-- Turn each member of a complete factorization into its certified occurrence.
Source: `gaga21_LocalFactorOccurrence`. -/
def gaga23_occurrence {d : ℕ} {J : Type}
    {V : J → Set (Fin d → ℂ)} {f : J → (Fin d → ℂ) → ℂ}
    (j : J) (p : Fin d → ℂ) (hp : p ∈ V j)
    (A : gaga23_Factorization (f j) p) (a : Fin A.count) :
    gaga21_LocalFactorOccurrence V f where
  chart := j
  point := p
  mem_chart := hp
  count := A.count
  unit := A.unit
  factors := A.factors
  exponents := A.exponents
  selected := a
  unit_analytic := A.unit_analytic
  unit_ne := A.unit_ne
  factor_data := A.factor_data
  coprime := A.coprime
  factorization := A.factorization
  selected_zero := (A.factor_data a).2.1.1

/-- The orbit label of each local factor is obtained by the two existing quotients.
Source: Chirka §5.1; `gaga22_ComponentOrbit`. -/
def gaga23_label {d : ℕ} {J : Type}
    {V : J → Set (Fin d → ℂ)} {f : J → (Fin d → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin d → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (j : J) (p : Fin d → ℂ) (hp : p ∈ V j)
    (A : gaga23_Factorization (f j) p) (a : Fin A.count) :
    gaga22_ComponentOrbit Λ hD hper :=
  Quotient.mk _ (Quotient.mk _ (gaga23_occurrence j p hp A a))

/-- The reduced product of precisely those factors carrying a given orbit label.
Source: Griffiths--Harris, Chapter 1 §1 (local equations of an effective divisor). -/
def gaga23_group {d k : ℕ} {I : Type} (P : Fin k → (Fin d → ℂ) → ℂ)
    (label : Fin k → I) (i : I) (z : Fin d → ℂ) : ℂ := by
  classical
  exact ∏ a ∈ Finset.univ.filter (fun a ↦ label a = i), P a z

/-- Complex points of the closure of one scheme point, restated for the bh4 consumer.
Source: `bh4_componentSupport`, LefschetzOneOneAlgebraicAbelianDefs on cloud/bh4;
Hartshorne, Algebraic Geometry, II.1. -/
def gaga23_componentSupport (X : Over (Spec ↧ℂ)) (x : X.left) : Set (ComplexPoint X) :=
  (Point.underlying : ComplexPoint X → X.left) ⁻¹' closure ({x} : Set X.left)

/-- Choose the closed irreducible carrier supplied by stage twenty-two.
Source: `gaga22_chow_support`. -/
def gaga23_carrier (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    (gaga22_descendedOnX X hD hper).Component → Set X.left :=
  (gaga22_chow_support X hD hper hChow).2.choose

/-- The generic scheme point of each chosen algebraic carrier.
Source: Mathlib `IsIrreducible.genericPoint`; `gaga22_chow_support`. -/
def gaga23_point (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (O : (gaga22_descendedOnX X hD hper).Component) : X.left :=
  ((gaga22_chow_support X hD hper hChow).2.choose_spec.2.1 O).2.1.genericPoint

/-- Enumerate the existing finite orbit family without changing its members.
Source: Mathlib `Fintype.equivFin`; `gaga22_finite_orbits`. -/
def gaga23_enumeration {d : ℕ} {J : Type}
    {V : J → Set (Fin d → ℂ)} {f : J → (Fin d → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin d → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    [CompactSpace ((Fin d → ℂ) ⧸ Λ)] :
    Σ n : ℕ, Fin n ≃ gaga22_ComponentOrbit Λ hD hper := by
  letI := gaga22_finite_orbits Λ hD hper
  letI := Fintype.ofFinite (gaga22_ComponentOrbit Λ hD hper)
  exact ⟨Fintype.card _, (Fintype.equivFin _).symm⟩

example : gaga23_Factorization (fun _ : Fin 1 → ℂ ↦ (1 : ℂ)) 0 :=
  ⟨0, fun _ ↦ 1, Fin.elim0, Fin.elim0, analyticAt_const, one_ne_zero,
    fun a ↦ a.elim0, fun a ↦ a.elim0, Eventually.of_forall fun z ↦ by simp⟩
example : gaga23_Factorization (fun _ : Fin 0 → ℂ ↦ (1 : ℂ)) 0 :=
  gaga23_factorization _ _ analyticAt_const (fun h ↦ one_ne_zero h.self_of_nhds)
example : gaga23_group (fun (_ : Fin 0) (_ : Fin 1 → ℂ) ↦ (0 : ℂ))
    (fun _ ↦ ()) () 0 = 1 := by simp [gaga23_group]

/-- Enumerate the scheme-side family using the finiteness supplied by Chow descent.
Source: `gaga22_chow_support`; Mathlib `Fintype.equivFin`. -/
def gaga23_schemeEnumeration (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    Σ n : ℕ, Fin n ≃ (gaga22_descendedOnX X hD hper).Component := by
  letI := (gaga22_chow_support X hD hper hChow).1
  letI := Fintype.ofFinite (gaga22_descendedOnX X hD hper).Component
  exact ⟨Fintype.card _, (Fintype.equivFin _).symm⟩

end HodgeLean.Foundations.AnalyticDivisorAlgebraic23
