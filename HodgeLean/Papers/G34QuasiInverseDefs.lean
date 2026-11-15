import HodgeLean.Papers.G34NarrowDefs
import HodgeLean.Papers.QuasiInverseDefs

/-! # G34 quasi-inverse premises: definitions -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers

/-- The classical quasi-inverse input for isogenies of the underlying abelian varieties in
dimension `2 * n`. It contains no Weil-action, polarization, or cycle clause.
Source: Mumford, *Abelian Varieties*, §4 (quasi-inverse of an isogeny). -/
def g34q_premise (n : ℕ) : Prop :=
  ∀ (P Q : wtr_Variety n) (f : P.X ⟶ Q.X),
    IsMonHom f → ccm2_IsogenyOnPoints f → Nonempty (qinv_Witness P Q f)

example {n : ℕ} (h : g34q_premise n) (P Q : wtr_Variety n) (f : P.X ⟶ Q.X)
    (hf : IsMonHom f) (hi : ccm2_IsogenyOnPoints f) :
    Nonempty (qinv_Witness P Q f) :=
  h P Q f hf hi

/-- The G34 literature inputs with reverse isogenies replaced by the classical quasi-inverse
input for eightfolds.
Source: G34 v1.5, Sections 2–10 and Theorems A and B; Mumford, *Abelian Varieties*, §4. -/
structure g34q_premises where
  F : wtr_UniversalFamily 4 1
  P : g34h_PrymFamily
  h46 : g34s_Prop46 P
  Φ : g34b_BoundaryPeriodMap F P.fiber
  hpar : ∀ s, g34b_ParabolicPolarization (g34h_fiber_polarized P s)
  spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
    (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧
    {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C
  qinv : g34q_premise 4

example (B : g34q_premises) : g34q_premise 4 :=
  B.qinv

end HodgeLean.Papers
