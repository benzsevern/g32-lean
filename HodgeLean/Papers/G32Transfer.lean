import HodgeLean.Papers.G32TransferProofs

/-! # G32 Theorem A, the transfer layer (FROZEN SPEC)

The top of the premise-first route to G32 v0.16 Theorem A: the paper's Section 7 (Lemma 7.1,
Theorem 7.2) and its proof of Theorem A, from a `G32TransferDatum`.

Claimed:
* the Baire step: in a Baire space, a countable union of closed sets that contains a nonempty
  open set has a member with nonempty interior;
* a Hausdorff space charted on `ℂ⁹` is a Baire space;
* the Baire step with the identity principle: on a connected Hausdorff space charted on `ℂ⁹`, a
  countable union of closed analytic subsets that contains a nonempty open set is everything;
* from a transfer datum: each fibre is a member of `M = (3, ℚ(√-3), [-2])`, so a member exists;
  the algebraicity locus in the moduli space contains a nonempty open set, and then is all of
  the moduli space; every member has algebraic Weil classes;
* `g32t_theoremA_of_transfer`: the implication from a transfer datum to
  `G32TheoremAStatement A W pol`, for every `A`, `W` and `pol`.

Not claimed: any field of the datum. Memberwise algebraicity (Schoen, Milne), dominance (the
rank-nine certificate and FGP), the discriminant computation, Hilbert spreading (Voisin),
Landherr coverage (van Geemen) and isogeny transport are fields, supplied by later stages or by
the cited literature; no datum is constructed here, so Theorem A itself remains unasserted. The
family structure of the fibres (abelian schemes over a base) is not recorded by the datum.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

section Topology

/-- **The Baire step.** In a Baire space, if a countable family of closed sets covers a nonempty
open set `U`, one of them has nonempty interior. (Apply the Baire category theorem to the closed
cover `Z ∪ Uᶜ` of the whole space and intersect with `U`.)
Source: G32 v0.16, proof of Theorem 7.2 ("a nonempty open subset of `𝓜` is a Baire space, so by
Lemma 7.1 one of the closed sets has nonempty interior"); Bourbaki, *General Topology*, Ch. IX,
§5.3 (Baire spaces). -/
theorem g32t_baire_step {M : Type*} [TopologicalSpace M] [BaireSpace M]
    {C : Set (Set M)} (hC : C.Countable) (hcl : ∀ Z ∈ C, IsClosed Z) {U : Set M}
    (hU : IsOpen U) (hne : U.Nonempty) (hsub : U ⊆ ⋃₀ C) :
    ∃ Z ∈ C, (interior Z).Nonempty :=
  g32t_baire_step_aux hC hcl hU hne hsub

/-- On `ℝ`, the family `{univ}` covers the open set `univ`. -/
example : ∃ Z ∈ ({univ} : Set (Set ℝ)), (interior Z).Nonempty :=
  g32t_baire_step (countable_singleton _) (by simp) isOpen_univ univ_nonempty (by simp)

/-- **Complex charted spaces are Baire.** A Hausdorff space with charts in `ℂ⁹` is locally
compact, hence a Baire space.
Source: Bourbaki, *General Topology*, Ch. IX, §5.3, Theorem 1 (locally compact Hausdorff spaces
are Baire); charts transport local compactness from `ℂ⁹`. -/
theorem g32t_baireSpace {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin 9 → ℂ) M] : BaireSpace M :=
  g32t_baireSpace_aux

example : BaireSpace (Fin 9 → ℂ) := g32t_baireSpace

/-- **Baire and irreducibility.** On a connected Hausdorff space charted on `ℂ⁹`, a countable
union of closed analytic subsets that contains a nonempty open set is the whole space: by
`g32t_baire_step` one member has nonempty interior, and by the identity principle
(`IsClosedAnalytic.eq_univ_of_nonempty_interior`) that member is everything.
Source: G32 v0.16, proof of Theorem 7.2 ("since `𝓜` is irreducible, it is all of `𝓜`"); Schnell,
*Complex Manifolds* (lecture notes), Theorem 1.8 (identity theorem). -/
theorem g32t_eq_univ_of_open_subset {M : Type*} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (Fin 9 → ℂ) M] {C : Set (Set M)} (hC : C.Countable)
    (hZ : ∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) {U : Set M} (hU : IsOpen U)
    (hne : U.Nonempty) (hsub : U ⊆ ⋃₀ C) : ⋃₀ C = univ :=
  g32t_eq_univ_of_open_subset_aux hC hZ hU hne hsub

/-- On `ℂ⁹` itself, the family `{univ}` of closed analytic sets. -/
example : ⋃₀ ({univ} : Set (Set (Fin 9 → ℂ))) = univ :=
  g32t_eq_univ_of_open_subset (countable_singleton _)
    (by simpa using isClosedAnalytic_univ) isOpen_univ univ_nonempty (by simp)

end Topology

section Datum

/-- **Every fibre is a member of `M = (3, ℚ(√-3), [-2])`**: the stage-2 field (polarized
sixfold of Weil type) and the stage-5 field (discriminant `[-2]`) together.
Source: G32 v0.16, Lemma 3.6 and Proposition 6.3; `g32t_isMember_iff`. -/
theorem g32t_fiber_isMember (D : G32TransferDatum) (s : D.S) :
    g32t_IsMember (D.fiber s) :=
  g32t_fiber_isMember_aux D s

example (D : G32TransferDatum) (s : D.S) :
    IsMemberOfM (finiteBetti_abelian (D.fiber s).X) (spec_bettiDeRhamIso_abelian (D.fiber s).X)
      (hodgeDecomposition_of_abelian (D.fiber s).X) (torusCohomology_cupProductOf (D.fiber s).X)
      (D.fiber s).W (D.fiber s).pol :=
  g32t_fiber_isMember D s

/-- **A transfer datum carries a member of `M`.** The dominant open set is nonempty, so some
fibre exists, and it is a member. A datum therefore cannot be built from degenerate data: it
needs an abelian sixfold with the full membership package.
Source: G32 v0.16, Lemma 3.6, Proposition 6.3 and Corollary 5.11 (the family is nonempty). -/
theorem g32t_exists_member (D : G32TransferDatum) : ∃ P, g32t_IsMember P :=
  g32t_exists_member_aux D

example (D : G32TransferDatum) : ∃ P : g32t_Sixfold, dim P.X.left = 6 :=
  (g32t_exists_member D).imp fun _ h => h.dim_eq

/-- **The algebraicity locus contains a nonempty open set**: each point of the dominant open set
receives an isogeny from a fibre whose Weil classes are algebraic, and transport carries the
algebraicity to the universal fibre.
Source: G32 v0.16, proof of Theorem 7.2, second paragraph ("So `𝓜^alg` contains a nonempty open
set"), with Lemma 2.2. -/
theorem g32t_open_subset_locus (D : G32TransferDatum) :
    ∃ U : Set D.M, IsOpen U ∧ U.Nonempty ∧ U ⊆ {m | g32t_WeilAlg (D.univ m)} :=
  g32t_open_subset_locus_aux D

example (D : G32TransferDatum) : {m | g32t_WeilAlg (D.univ m)}.Nonempty :=
  let ⟨_, _, hne, h⟩ := g32t_open_subset_locus D
  hne.mono h

/-- **The algebraicity locus is the whole moduli space**: Hilbert spreading writes it as a
countable union of closed analytic subsets, and it contains a nonempty open set.
Source: G32 v0.16, Lemma 7.1 and the proof of Theorem 7.2; `g32t_eq_univ_of_open_subset`. -/
theorem g32t_locus_eq_univ (D : G32TransferDatum) (m : D.M) : g32t_WeilAlg (D.univ m) :=
  g32t_locus_eq_univ_aux D m

example (D : G32TransferDatum) : {m | g32t_WeilAlg (D.univ m)} = univ :=
  eq_univ_of_forall (g32t_locus_eq_univ D)

/-- **Every member has algebraic Weil classes**: Landherr coverage gives an isogeny to a
universal fibre, whose Weil classes are algebraic by `g32t_locus_eq_univ`, and transport carries
the algebraicity back.
Source: G32 v0.16, last sentence of the proof of Theorem 7.2, with Lemma 2.2. -/
theorem g32t_weilAlg_of_isMember (D : G32TransferDatum) (P : g32t_Sixfold)
    (hP : g32t_IsMember P) : g32t_WeilAlg P :=
  g32t_weilAlg_of_isMember_aux D P hP

example (D : G32TransferDatum) (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    WeilClassesAlgebraic (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
      (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) P.W
      hP.isWeilType :=
  g32t_weilAlg_of_isMember D P hP _

end Datum

/-- **G32 Theorem A from the transfer datum.** For every complex abelian variety `A` with the
five instances, every rational Weil action `W` of `ℚ(√-3)` on `H¹` and every degree-two class
`pol`, a transfer datum gives `G32TheoremAStatement A W pol`: if `(A, W, pol)` is a member of
`M = (3, ℚ(√-3), [-2])`, its Weil classes are algebraic.

This is the implication from the datum; the datum's fields are the outputs of stages 2–5 and
the cited literature premises, and none of them is asserted here.
Source: G32 v0.16, Theorem 7.2 and the proof of Theorem A. -/
theorem g32t_theoremA_of_transfer (D : G32TransferDatum) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  g32t_theoremA_of_transfer_aux D A W pol

/-- Composed with the existing implication from Theorem A to Theorem B's input: the datum
supplies the `hA` premise of `skelg32_theoremB`, here in its unfolded form for one member. -/
example (D : G32TransferDatum) (A : Over (Spec ↧ℂ))
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
  g32t_theoremA_of_transfer D A W pol hM

end HodgeLean.Papers
