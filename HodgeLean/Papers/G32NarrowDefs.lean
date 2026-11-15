import HodgeLean.Papers.G32Assembly

/-! # G32 Theorem A with reverse isogenies: definitions -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

/-- The transfer data used by the G32 argument, with algebraicity transport replaced by a
reverse isogeny between members.  Universal fibres are recorded as members because both uses
of transport in the transfer argument have a universal fibre as one endpoint.
Source: G32 v0.16, Lemma 2.2 and Theorem 7.2; Mumford, *Abelian Varieties*, §§4 and 18. -/
structure g32n_TransferDatum where
  S : Type
  fiber : S → g32t_Sixfold
  fiber_polarized : ∀ s, g32t_PolarizedWeil (fiber s)
  fiber_disc : ∀ s, g32t_disc (fiber_polarized s) = classNegTwo
  fiber_alg : ∀ s, g32t_WeilAlg (fiber s)
  M : Type
  [topM : TopologicalSpace M]
  [t2M : T2Space M]
  [connM : ConnectedSpace M]
  [chartM : ChartedSpace (Fin 9 → ℂ) M]
  [manifoldM : IsManifold 𝓘(ℂ, Fin 9 → ℂ) ω M]
  univ : M → g32t_Sixfold
  univ_member : ∀ m, g32t_IsMember (univ m)
  dominant : ∃ U : Set M, IsOpen U ∧ U.Nonempty ∧ ∀ m ∈ U, ∃ s, g32t_KIsog (fiber s) (univ m)
  spread : ∃ C : Set (Set M), C.Countable ∧ (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧
    {m | g32t_WeilAlg (univ m)} = ⋃₀ C
  cover : ∀ P, g32t_IsMember P → ∃ m, g32t_KIsog P (univ m)
  reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q →
    g32t_KIsog P Q → g32t_KIsog Q P

attribute [instance] g32n_TransferDatum.topM g32n_TransferDatum.t2M
  g32n_TransferDatum.connM g32n_TransferDatum.chartM g32n_TransferDatum.manifoldM

example (D : g32n_TransferDatum) (s : D.S) : g32t_IsMember (D.fiber s) :=
  (g32t_isMember_iff _).2 ⟨D.fiber_polarized s, D.fiber_disc s⟩

/-- The G32 literature inputs with the cycle-theoretic transport premise replaced by reverse
isogenies between members.
Source: G32 v0.16, Sections 2–7 and Theorem A; Mumford, *Abelian Varieties*, §§4 and 18. -/
structure g32n_premises where
  F : g32m_UniversalFamily
  P : g32h_PrymFamily
  h46 : g32s_Prop46 P
  R : g32r_PeriodMap F P
  hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s)
  spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
    (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C
  reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q →
    g32t_KIsog P Q → g32t_KIsog Q P

example (B : g32n_premises) (m : g32m_Domain) : g32t_IsMember (B.F.univ m) :=
  B.F.member m

end HodgeLean.Papers
