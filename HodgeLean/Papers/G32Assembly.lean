import HodgeLean.Papers.G32AssemblyProofs

/-! # G32 Theorem A, assembly: Theorem A from the named premises (FROZEN SPEC)

The endpoint of the premise-first route to G32 v0.16 Theorem A. The six G32 pieces (the transfer
layer and stages 1–5) each reduce one part of the paper to a named premise and a Lean argument;
this module composes them.

Claimed:
* `g32a_fiber_disc`: the adapter from stage 5 to the field `fiber_disc` of
  `g32h_RemainingFields`. Stage 5 (`g32d_fiber_disc`) gives the discriminant `[-2]` for the one
  proof `g32h_fiber_polarized P s` of polarized Weil type; the field asks for it for every proof.
  By proof irrelevance the two agree;
* `g32a_remainingFields`: the remaining stage fields `g32h_RemainingFields F P` (a `Prop`) from
  stages 3, 4 and 5 and the spreading and transport premises;
* `g32a_theoremA`: the implication from the seven named premises (universal family, Prym family,
  Proposition 4.6, period map, parabolic polarization, Hilbert spreading, isogeny transport) to
  `G32TheoremAStatement A W pol`, for every `A`, `W` and `pol`, through
  `g32h_stageFields_partial`, `g32m_theoremA_of_stages` and `g32t_theoremA_of_transfer`;
* `g32a_theoremA_of_premises`: the same implication from the bundle `g32a_premises`;
* `g32a_exists_member_fiber`: the premises force a Prym factor that is a member of
  `M = (3, ℚ(√-3), [-2])`, so the bundle cannot be built from an empty family.

Not claimed: any of the seven premises. No universal family, Prym family, period map,
parabolic-polarization comparison, spreading or transport is constructed, and Proposition 4.6
(Schoen, Milne) is taken whole, so Theorem A itself remains unasserted. This is a check of the
paper's argument from the named premises, not a check of the cited literature.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

/-- **The stage-5 adapter.** From the parabolic-polarization comparison on every Prym factor,
the discriminant is `[-2]` for every proof of polarized Weil type: the exact type of the field
`fiber_disc` of `g32h_RemainingFields`. Stage 5 (`g32d_fiber_disc`) states it for the stage-2
proof `g32h_fiber_polarized P s`; `g32t_PolarizedWeil` is a `Prop`, so any other proof is equal
to that one.
Source: G32 v0.16, Lemma 3.6 and Proposition 6.3; `g32d_fiber_disc`, `g32h_fiber_polarized`. -/
theorem g32a_fiber_disc (P : g32h_PrymFamily)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s)) :
    ∀ s (h : g32t_PolarizedWeil (P.fiber s)), g32t_disc h = classNegTwo :=
  g32a_fiber_disc_aux P hpol

/-- The adapter at the stage-2 proof is the stage-5 output. -/
example (P : g32h_PrymFamily)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s)) (s : P.S) :
    g32t_disc (g32h_fiber_polarized P s) = classNegTwo :=
  g32a_fiber_disc P hpol s _

/-- **The remaining stage fields from the premises.** `g32h_RemainingFields F P` is a structure
of propositions, hence a `Prop`, so this is a theorem. Over a universal family `F` and a Prym
family `P`: `fiber_disc` from `g32a_fiber_disc` (stage 5), `fiber_alg` from `g32s_fiber_alg`
(stage 3), `dominant` from `g32r_dominant` (stage 4), and the spreading and transport premises as
given.
Source: G32 v0.16, Lemma 2.2, Proposition 4.6, Corollary 5.11, Proposition 6.3, Lemma 7.1; the
fields of `g32h_RemainingFields`. -/
theorem g32a_remainingFields (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (h46 : g32s_Prop46 P) (R : g32r_PeriodMap F P)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q)) :
    g32h_RemainingFields F P :=
  g32a_remainingFields_aux F P h46 R hpol spread transport

/-- The field-by-field construction: each field is filled by a frozen stage output or by the
premise of the same name, with the adapter for `fiber_disc`. -/
example (F : g32m_UniversalFamily) (P : g32h_PrymFamily) (h46 : g32s_Prop46 P)
    (R : g32r_PeriodMap F P)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q)) :
    g32h_RemainingFields F P :=
  ⟨g32a_fiber_disc P hpol, g32s_fiber_alg P h46, g32r_dominant F P R, spread, transport⟩

/-- The stage fields assembled over `F` and `P` have the Prym factors as fibres. -/
example (F : g32m_UniversalFamily) (P : g32h_PrymFamily) (h46 : g32s_Prop46 P)
    (R : g32r_PeriodMap F P)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q)) :
    (g32h_stageFields_partial F P
      (g32a_remainingFields F P h46 R hpol spread transport)).fiber = P.fiber :=
  rfl

/-- **G32 Theorem A from the seven named premises.** For every complex abelian variety `A` with
the five instances, every rational Weil action `W` of `ℚ(√-3)` on `H¹` and every degree-two class
`pol`: from the universal family `F` (Landherr, van Geemen), the Prym family `P` (Chevalley–Weil,
G32 Lemma 3.3), Proposition 4.6 `h46` (Schoen, Milne), the period map `R` (FGP, the Schlesinger
jet), the parabolic-polarization comparison `hpol` (G32 Proposition 6.3), Hilbert spreading
`spread` (G32 Lemma 7.1, Voisin) and isogeny transport `transport` (G32 Lemma 2.2),
`G32TheoremAStatement A W pol` holds: if `(A, W, pol)` is a member of `M = (3, ℚ(√-3), [-2])`,
its Weil classes are algebraic.

The route: `g32a_remainingFields`, then `g32h_stageFields_partial`, then
`g32m_theoremA_of_stages`, which goes through `g32t_theoremA_of_transfer`. This is the
implication from the premises; none of them is asserted here.
Source: G32 v0.16, Theorem A and its proof (Theorem 7.2), with Lemma 2.2, Lemma 3.6,
Proposition 4.6, Corollary 5.11, Proposition 6.3 and Lemma 7.1. -/
theorem g32a_theoremA (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (h46 : g32s_Prop46 P) (R : g32r_PeriodMap F P)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  g32a_theoremA_aux F P h46 R hpol spread transport A W pol

/-- The composition the proof follows, written out: the same conclusion from
`g32m_theoremA_of_stages` applied to the assembled stage fields. -/
example (F : g32m_UniversalFamily) (P : g32h_PrymFamily) (h46 : g32s_Prop46 P)
    (R : g32r_PeriodMap F P)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  g32m_theoremA_of_stages F
    (g32h_stageFields_partial F P (g32a_remainingFields F P h46 R hpol spread transport)) A W pol

/-- **G32 Theorem A from the premise bundle.** The bundled form of `g32a_theoremA`: one
`g32a_premises` gives `G32TheoremAStatement A W pol` for every `A`, `W` and `pol`.
Source: G32 v0.16, Theorem A and its proof; the fields of `g32a_premises`. -/
theorem g32a_theoremA_of_premises (B : g32a_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  g32a_theoremA_of_premises_aux B A W pol

/-- The bundled form, unfolded at a member: its Weil classes are algebraic. -/
example (B : g32a_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2)
    (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol) :
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hM.isWeilType :=
  g32a_theoremA_of_premises B A W pol hM

/-- **The premises force a member among the Prym factors.** Dominance (from the period map) gives
a nonempty open set of `𝓗₃` whose points are isogeny targets of Prym factors, so some factor
exists; it is a polarized sixfold of Weil type (stage 2) with discriminant `[-2]` (stage 5), so a
member of `M = (3, ℚ(√-3), [-2])`. The bundle therefore cannot be built from an empty family, and
`h46` is not vacuous.
Source: G32 v0.16, Lemma 3.6, Corollary 5.11 and Proposition 6.3; `g32t_isMember_iff`. -/
theorem g32a_exists_member_fiber (B : g32a_premises) :
    ∃ s, g32t_IsMember (B.P.fiber s) :=
  g32a_exists_member_fiber_aux B

example (B : g32a_premises) : ∃ s, dim (B.P.fiber s).X.left = 6 :=
  (g32a_exists_member_fiber B).imp fun _ h => h.dim_eq

end HodgeLean.Papers
