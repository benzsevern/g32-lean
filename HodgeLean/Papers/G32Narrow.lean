import HodgeLean.Papers.G32NarrowProofs

/-! # G32 Theorem A from reverse isogenies (FROZEN SPEC)

This module records an implication from reverse `K`-linear polarized isogenies between members.
It claims that reverse isogenies yield two-way Weil algebraicity transport, that the transfer
argument needs this geometric input only between members, and that the corresponding literature
premise bundle implies `G32TheoremAStatement`.

It does not construct reverse isogenies, a universal family, a Prym family, a period map,
parabolic polarizations, Hilbert spreading, or the input to Proposition 4.6.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

/-- Reverse isogenies turn one-way pullback of algebraicity into invariance for polarized Weil
sixfolds.
Source: G32 v0.16, Lemma 2.2; Mumford, *Abelian Varieties*, §§4 and 18;
`g32tr_weilAlg_pullback`. -/
theorem g32n_transport_of_reverse (P Q : g32t_Sixfold)
    (hP : g32t_PolarizedWeil P) (hQ : g32t_PolarizedWeil Q)
    (reverse : g32t_KIsog P Q → g32t_KIsog Q P) :
    g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q) :=
  g32n_transport_of_reverse_aux P Q hP hQ reverse

example (P Q : g32t_Sixfold) (hP : g32t_PolarizedWeil P)
    (hQ : g32t_PolarizedWeil Q) (reverse : g32t_KIsog P Q → g32t_KIsog Q P)
    (h : g32t_KIsog P Q) (hAlg : g32t_WeilAlg Q) : g32t_WeilAlg P :=
  (g32n_transport_of_reverse P Q hP hQ reverse h).2 hAlg

/-- The transfer argument from a datum whose cycle-theoretic transport field is replaced by
reverse isogenies between members.
Source: G32 v0.16, Theorem 7.2 and Lemma 2.2; `g32t_open_subset_locus`,
`g32t_weilAlg_of_isMember`; Mumford, *Abelian Varieties*, §§4 and 18. -/
theorem g32n_theoremA_of_transfer (D : g32n_TransferDatum) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  g32n_theoremA_of_transfer_aux D A W pol

example (D : g32n_TransferDatum) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  g32n_theoremA_of_transfer D A W pol

/-- G32 Theorem A from the named inputs with isogeny transport replaced by the existence of
reverse isogenies between members.
Source: G32 v0.16, Theorem A and Sections 2–7; Mumford, *Abelian Varieties*, §§4 and 18. -/
theorem g32n_theoremA_of_premises (B : g32n_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  g32n_theoremA_of_premises_aux B A W pol

example (B : g32n_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  g32n_theoremA_of_premises B A W pol

end HodgeLean.Papers
