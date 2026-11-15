import HodgeLean.Papers.G34Assembly

/-! # Generic Weil transfer with reverse isogenies: definitions -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers

/-- Generic transfer data with two-way algebraicity transport replaced by a reverse isogeny
between members. Universal fibres are recorded as members because both uses in the transfer
argument have such a fibre as one endpoint.
Source: G34 v1.5, Lemma 2.2 and Theorem A; Mumford, *Abelian Varieties*, §§4 and 18. -/
structure g34n_TransferDatum (n : ℕ)
    (δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) where
  S : Type
  fiber : S → wtr_Variety n
  fiber_polarized : ∀ s, wtr_PolarizedWeil n (fiber s)
  fiber_disc : ∀ s, wtr_disc (fiber_polarized s) = δ
  fiber_alg : ∀ s, wtr_WeilAlg (fiber s)
  M : Type
  [topM : TopologicalSpace M]
  [t2M : T2Space M]
  [connM : ConnectedSpace M]
  [chartM : ChartedSpace (Fin (n ^ 2) → ℂ) M]
  [manifoldM : IsManifold 𝓘(ℂ, Fin (n ^ 2) → ℂ) ω M]
  univ : M → wtr_Variety n
  univ_member : ∀ m, wtr_IsMember n δ (univ m)
  dominant : ∃ U : Set M, IsOpen U ∧ U.Nonempty ∧
    ∀ m ∈ U, ∃ s, wtr_KIsog (fiber s) (univ m)
  spread : ∃ C : Set (Set M), C.Countable ∧
    (∀ Z ∈ C, IsClosedAnalytic (Fin (n ^ 2) → ℂ) Z) ∧
    {m | wtr_WeilAlg (univ m)} = ⋃₀ C
  cover : ∀ P, wtr_IsMember n δ P → ∃ m, wtr_KIsog P (univ m)
  reverse : ∀ P Q, wtr_IsMember n δ P → wtr_IsMember n δ Q →
    wtr_KIsog P Q → wtr_KIsog Q P

attribute [instance] g34n_TransferDatum.topM g34n_TransferDatum.t2M
  g34n_TransferDatum.connM g34n_TransferDatum.chartM g34n_TransferDatum.manifoldM

example {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : g34n_TransferDatum n δ) (s : D.S) : wtr_IsMember n δ (D.fiber s) :=
  ⟨D.fiber_polarized s, D.fiber_disc s⟩

/-- The G34 literature inputs with algebraicity transport replaced by reverse isogenies between
members.
Source: G34 v1.5, Sections 2–10 and Theorems A and B; Mumford, *Abelian Varieties*, §§4 and 18. -/
structure g34n_premises where
  F : wtr_UniversalFamily 4 1
  P : g34h_PrymFamily
  h46 : g34s_Prop46 P
  Φ : g34b_BoundaryPeriodMap F P.fiber
  hpar : ∀ s, g34b_ParabolicPolarization (g34h_fiber_polarized P s)
  spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
    (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧
    {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C
  reverse : ∀ P Q, wtr_IsMember 4 1 P → wtr_IsMember 4 1 Q →
    wtr_KIsog P Q → wtr_KIsog Q P

example (B : g34n_premises) (m : wtr_Domain 4) :
    wtr_IsMember 4 1 (B.F.univ m) := B.F.member m

end HodgeLean.Papers
