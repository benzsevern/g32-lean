import HodgeLean.Papers.G34AssemblyProofs

/-! # G34 Theorems A and B, assembly: the implication from the named premises (FROZEN SPEC)

The endpoint of the premise-first route to G34 v1.5 Theorems A and B. The G34 pieces (the generic
transfer `WeilTransfer`, the Hurwitz family `G34Family`, the supply `G34Supply`, the boundary
certificate `G34Boundary` and the compensation `G34Compensation`) each reduce one part of the
paper to a named premise and a Lean argument; this module composes them.

Claimed:
* `g34a_remainingFields`: the remaining stage fields `g34h_RemainingFields F P` (a `Prop`) from
  Proposition 4.6, the boundary period map, the parabolic polarization and the spreading and
  transport premises. Every stage output has the field type, so no adapter is needed;
* `g34a_theoremA`: the implication from the seven named premises (universal family, Prym family,
  Proposition 4.6, boundary period map, parabolic polarization, Hilbert spreading, isogeny
  transport) to `G34TheoremAStatement A`, for every `A`, through `g34b_theoremA_of_boundary`,
  `wtr_transferFields` and `wtr_g34A_of_transfer`;
* `g34a_theoremA_of_premises`: the same implication from the bundle `g34a_premises`;
* `g34a_theoremB_of_premises`: the implication from the bundle and the compensation premise of
  `g34c_theoremB_of` for a sixfold `A` to `G34TheoremBStatement A`;
* `g34a_exists_member_fiber`: the premises force a Prym–Tyurin factor that is a member of
  `M(4, ℚ(√-3), [1])`, so the bundle cannot be built from an empty family.

Not claimed: any of the seven premises, or the compensation premise. No universal family, Prym
family, boundary period map, parabolic-polarization comparison, spreading or transport is
constructed. Proposition 4.6 (Brauer, Schoen, Milne) and the compensation step (Schoen, Voisin)
are the paper's own steps, taken whole as premises. So neither Theorem A nor Theorem B is
asserted. This is a check of the paper's argument from the named premises, not a check of the
cited literature.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

/-- **The remaining stage fields from the premises.** `g34h_RemainingFields F P` is a structure
of propositions, hence a `Prop`, so this is a theorem. Over a universal family `F` for
`M(4, ℚ(√-3), [1])` and a Prym family `P`: `fiber_disc` from `g34b_fiber_disc` with `hpar`
(boundary certificate; the field quantifies over every proof of `wtr_PolarizedWeil 4`, which is a
`Prop`, so the stage-2 proof `g34h_fiber_polarized P s` serves), `fiber_alg` from
`g34s_fiber_alg` (stage 3), `dominant` from `g34b_dominant` (boundary certificate), and the
spreading and transport premises as given.
Source: G34 v1.5, Lemma 2.2, Proposition 4.6, Lemma 6.1, Theorem 6.2, Proposition 7.1 and
Proposition 8.5; the fields of `g34h_RemainingFields`. -/
theorem g34a_remainingFields (F : wtr_UniversalFamily 4 1) (P : g34h_PrymFamily)
    (h46 : g34s_Prop46 P) (Φ : g34b_BoundaryPeriodMap F P.fiber)
    (hpar : ∀ s, g34b_ParabolicPolarization (g34h_fiber_polarized P s))
    (spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q : wtr_Variety 4, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q)) :
    g34h_RemainingFields F P :=
  g34a_remainingFields_aux F P h46 Φ hpar spread transport

/-- The field-by-field construction: each field is filled by a frozen stage output or by the
premise of the same name. -/
example (F : wtr_UniversalFamily 4 1) (P : g34h_PrymFamily) (h46 : g34s_Prop46 P)
    (Φ : g34b_BoundaryPeriodMap F P.fiber)
    (hpar : ∀ s, g34b_ParabolicPolarization (g34h_fiber_polarized P s))
    (spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q : wtr_Variety 4, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q)) :
    g34h_RemainingFields F P :=
  ⟨fun s _ => g34b_fiber_disc P.fiber (g34h_fiber_polarized P) hpar s, g34s_fiber_alg P h46,
    g34b_dominant F P.fiber Φ, spread, transport⟩

/-- The stage fields assembled over `F` and `P` have the Prym–Tyurin factors as fibres and the
stage-2 proof as `fiber_polarized`. -/
example (F : wtr_UniversalFamily 4 1) (P : g34h_PrymFamily) (h46 : g34s_Prop46 P)
    (Φ : g34b_BoundaryPeriodMap F P.fiber)
    (hpar : ∀ s, g34b_ParabolicPolarization (g34h_fiber_polarized P s))
    (spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q : wtr_Variety 4, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q)) :
    (g34h_stageFields_partial F P
        (g34a_remainingFields F P h46 Φ hpar spread transport)).fiber = P.fiber ∧
      (g34h_stageFields_partial F P
        (g34a_remainingFields F P h46 Φ hpar spread transport)).fiber_polarized =
        g34h_fiber_polarized P :=
  ⟨rfl, rfl⟩

/-- **G34 Theorem A from the seven named premises.** For every complex abelian variety `A` with
the five instances: from the universal family `F` over `𝓗₄` (Landherr, van Geemen), the Prym
family `P` (Chevalley–Weil, G34 Lemma 3.3), Proposition 4.6 `h46` (Brauer, Schoen, Milne), the
boundary period map `Φ` (G34 Section 8 and Theorem 6.2), the parabolic-polarization comparison
`hpar` (G34 Proposition 7.1), Hilbert spreading `spread` (G34 Lemma 6.1, Voisin) and isogeny
transport `transport` (G34 Lemma 2.2), `G34TheoremAStatement A` holds: if `A` is a polarized
abelian eightfold of Weil type for `ℚ(√-3)` with split discriminant `[1]`, its Weil classes are
algebraic.

The route: `g34b_theoremA_of_boundary` with `fiber := P.fiber`, `fiber_polarized :=
g34h_fiber_polarized P` and `fiber_alg := g34s_fiber_alg P h46`; it supplies `fiber_disc` and
`dominant` and goes through `wtr_transferFields` and `wtr_g34A_of_transfer`. This is the
implication from the premises; none of them is asserted here.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem A and its proof in Section 9, with Lemma 2.2, Lemma 9.1,
Proposition 4.6, Lemma 6.1, Theorem 6.2, Proposition 7.1 and Proposition 8.5. -/
theorem g34a_theoremA (F : wtr_UniversalFamily 4 1) (P : g34h_PrymFamily)
    (h46 : g34s_Prop46 P) (Φ : g34b_BoundaryPeriodMap F P.fiber)
    (hpar : ∀ s, g34b_ParabolicPolarization (g34h_fiber_polarized P s))
    (spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q : wtr_Variety 4, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A :=
  g34a_theoremA_aux F P h46 Φ hpar spread transport A

/-- The same conclusion through the generic stage route: `g34h_stageFields_partial` on the
remaining fields, then `wtr_transferFields` with the connectedness of `𝓗₄`, then
`wtr_g34A_of_transfer`. -/
example (F : wtr_UniversalFamily 4 1) (P : g34h_PrymFamily) (h46 : g34s_Prop46 P)
    (Φ : g34b_BoundaryPeriodMap F P.fiber)
    (hpar : ∀ s, g34b_ParabolicPolarization (g34h_fiber_polarized P s))
    (spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q : wtr_Variety 4, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A :=
  haveI := wtr_domain_connectedSpace 4
  wtr_g34A_of_transfer (wtr_transferFields F (g34h_stageFields_partial F P
    (g34a_remainingFields F P h46 Φ hpar spread transport))) A

/-- **G34 Theorem A from the premise bundle.** The bundled form of `g34a_theoremA`: one
`g34a_premises` gives `G34TheoremAStatement A` for every `A`.
Source: G34 v1.5, Theorem A and its proof; the fields of `g34a_premises`. -/
theorem g34a_theoremA_of_premises (B : g34a_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A :=
  g34a_theoremA_of_premises_aux B A

/-- The bundled form, unfolded at a split eightfold: its Weil classes are algebraic. -/
example (B : g34a_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (hW : letI := (finiteBetti_abelian A).finite 1; W.IsWeilType) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : letI := (finiteBetti_abelian A).finite 1;
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J)
    (hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
    (hDim : TopologicalSpace.dim A.left = 8)
    (hDisc : weilDatumClass (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hη hRos = 1) :
    letI := (finiteBetti_abelian A).finite 1
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW :=
  g34a_theoremA_of_premises B A W hW pol hη hRos hPos hDim hDisc

/-- **G34 Theorem B from the premise bundle and the compensation premise.** For every complex
abelian variety `A` with the five instances: from a bundle `B` and the compensation premise
`hComp` of `g34c_theoremB_of` for `A`, `G34TheoremBStatement A` holds: if `A` is a polarized
abelian sixfold of Weil type for `ℚ(√-3)`, of any discriminant, its Weil classes are algebraic.

`hComp` is G34 Proposition 10.2 at `n = 4` for this `A`, taken whole: given a Weil sixfold
structure on `A` and Theorem A for every eightfold, the Weil classes of `A` are algebraic. Its
hypothesis "Theorem A for every eightfold" is supplied here by `g34a_theoremA_of_premises B`,
and `g34c_theoremB_of` does the rest. This is the implication from the bundle and `hComp`; none
of them is asserted here.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem B and its proof (Proposition 10.2 with Theorem A);
Schoen, Compositio Math. 114 (1998), Proposition 10; Voisin, Bourbaki exposé 1248 (2026),
Lemma 2.9; `g34c_theoremB_of`. -/
theorem g34a_theoremB_of_premises (B : g34a_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (hComp : ∀
      (W : letI := (finiteBetti_abelian A).finite 1
        HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
      (hW : letI := (finiteBetti_abelian A).finite 1; W.IsWeilType)
      (pol : HQ A 2)
      (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
      (_hRos : letI := (finiteBetti_abelian A).finite 1;
        IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J)
      (_hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
      (_hDim : TopologicalSpace.dim A.left = 6),
      (∀ (X : Over (Spec ↧ℂ)),
        [GrpObj X] → [IsCommMonObj X] → [IsIntegral X.left] →
        [Smooth X.hom] → [IsProjective X.hom] → G34TheoremAStatement X) →
      letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW) :
    G34TheoremBStatement A :=
  g34a_theoremB_of_premises_aux B A hComp

/-- The composition the proof follows, written out: `g34c_theoremB_of` with Theorem A for every
eightfold from the bundle. -/
example (B : g34a_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (hComp : ∀
      (W : letI := (finiteBetti_abelian A).finite 1
        HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
      (hW : letI := (finiteBetti_abelian A).finite 1; W.IsWeilType)
      (pol : HQ A 2)
      (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
      (_hRos : letI := (finiteBetti_abelian A).finite 1;
        IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J)
      (_hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
      (_hDim : TopologicalSpace.dim A.left = 6),
      (∀ (X : Over (Spec ↧ℂ)),
        [GrpObj X] → [IsCommMonObj X] → [IsIntegral X.left] →
        [Smooth X.hom] → [IsProjective X.hom] → G34TheoremAStatement X) →
      letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW) :
    G34TheoremBStatement A :=
  g34c_theoremB_of A (fun X _ _ _ _ _ => g34a_theoremA_of_premises B X) hComp

/-- **The premises force a member among the Prym–Tyurin factors.** The Prym family has the base
cover with the printed tuple; its factor is a polarized eightfold of Weil type
(`g34h_fiber_polarized`) with split discriminant (`g34b_fiber_disc` with `B.hpar`), so a member
of `M(4, ℚ(√-3), [1])`. The bundle therefore cannot be built from an empty family, and `h46` is
not vacuous.
Source: G34 v1.5, Lemma 9.1, Proposition 7.1 and Proposition 8.5 (the discriminant); the
definition of `wtr_IsMember`. -/
theorem g34a_exists_member_fiber (B : g34a_premises) :
    ∃ s, wtr_IsMember 4 1 (B.P.fiber s) :=
  g34a_exists_member_fiber_aux B

example (B : g34a_premises) : ∃ s, dim (B.P.fiber s).X.left = 8 :=
  (g34a_exists_member_fiber B).imp fun _ h => h.polarized.dim_eq

end HodgeLean.Papers
