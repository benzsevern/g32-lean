import HodgeLean.Papers.G34QuasiInverseDefs

/-! # Premise bundles after deriving quasi-inverses -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters

namespace HodgeLean.Papers

/-- The six G32 literature inputs that remain after the classical isogeny quasi-inverse is
constructed from the abelian-variety structure.
Source: G32 v0.16, Sections 2–7 and Theorem A; Mumford, *Abelian Varieties*, §4. -/
structure qderiv_g32_premises where
  F : g32m_UniversalFamily
  P : g32h_PrymFamily
  h46 : g32s_Prop46 P
  R : g32r_PeriodMap F P
  hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s)
  spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
    (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C

example (B : qderiv_g32_premises) : g32r_PeriodMap B.F B.P :=
  B.R

/-- The six G34 literature inputs that remain after the classical isogeny quasi-inverse is
constructed from the abelian-variety structure.
Source: G34 v1.5, Sections 2–10 and Theorems A and B; Mumford, *Abelian Varieties*, §4. -/
structure qderiv_g34_premises where
  F : wtr_UniversalFamily 4 1
  P : g34h_PrymFamily
  h46 : g34s_Prop46 P
  Φ : g34b_BoundaryPeriodMap F P.fiber
  hpar : ∀ s, g34b_ParabolicPolarization (g34h_fiber_polarized P s)
  spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
    (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧
    {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C

example (B : qderiv_g34_premises) : g34b_BoundaryPeriodMap B.F B.P.fiber :=
  B.Φ

end HodgeLean.Papers
