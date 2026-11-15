import HodgeLean.Papers.G32NarrowDefs
import HodgeLean.Papers.WeilTransferDefs

/-! # Morphism-level quasi-inverses: definitions -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

/-- A positive multiplication quasi-inverse to a morphism of complex abelian varieties.
Source: Mumford, *Abelian Varieties*, §4 (quasi-inverse of an isogeny). -/
structure qinv_Witness (P Q : g32t_Sixfold) (f : P.X ⟶ Q.X) where
  g : Q.X ⟶ P.X
  g_mon : IsMonHom g
  g_isogeny : ccm2_IsogenyOnPoints g
  N : ℕ
  N_pos : 0 < N
  gf : g ≫ f = 𝟙 Q.X ^ (N : ℤ)

example {n : ℕ} (P Q : wtr_Variety n) (f : P.X ⟶ Q.X)
    (w : qinv_Witness P Q f) : 0 < w.N :=
  w.N_pos

/-- The classical quasi-inverse input for isogenies of the underlying abelian varieties.  It
contains no Weil-action or polarization clause.
Source: Mumford, *Abelian Varieties*, §4 (quasi-inverse of an isogeny). -/
def qinv_premise : Prop :=
  ∀ (P Q : g32t_Sixfold) (f : P.X ⟶ Q.X),
    IsMonHom f → ccm2_IsogenyOnPoints f → Nonempty (qinv_Witness P Q f)

example (h : qinv_premise) (P Q : g32t_Sixfold) (f : P.X ⟶ Q.X)
    (hf : IsMonHom f) (hi : ccm2_IsogenyOnPoints f) :
    Nonempty (qinv_Witness P Q f) :=
  h P Q f hf hi

/-- The G32 literature inputs with reverse isogenies replaced by the classical quasi-inverse
input.
Source: G32 v0.16, Sections 2–7 and Theorem A; Mumford, *Abelian Varieties*, §4. -/
structure qinv_premises where
  F : g32m_UniversalFamily
  P : g32h_PrymFamily
  h46 : g32s_Prop46 P
  R : g32r_PeriodMap F P
  hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s)
  spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
    (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C
  qinv : qinv_premise

example (B : qinv_premises) : qinv_premise :=
  B.qinv

end HodgeLean.Papers
