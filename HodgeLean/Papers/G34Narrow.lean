import HodgeLean.Papers.G34NarrowProofs

/-! # Generic Weil transfer with reverse isogenies (FROZEN)

This module freezes an implication from polarized isogeny pullback and from generic transfer
data whose member endpoints have reverse isogenies. It also freezes the corresponding G34
Theorem A implication and the Theorem B implication with its compensation input. It does not
construct a universal family, a Prym family, a boundary period map, spreading, reverse
isogenies, or compensation. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers

/-- Weil algebraicity pulls back along a polarized `K`-linear isogeny in every even dimension.
Source: G34 v1.5, Lemma 2.2; Mumford, *Abelian Varieties*, §§4 and 18. -/
theorem g34n_weilAlg_pullback {n : ℕ} (P Q : wtr_Variety n)
    (hP : wtr_PolarizedWeil n P) (hQ : wtr_PolarizedWeil n Q)
    (h : wtr_KIsog P Q) (hAlg : wtr_WeilAlg Q) : wtr_WeilAlg P :=
  g34n_weilAlg_pullback_aux P Q hP hQ h hAlg

/-- At `n = 3`, the generic statement has the input and output of the existing G32 pullback
after applying the polarized-Weil bridge. -/
example (P Q : g32t_Sixfold) (hP : g32t_PolarizedWeil P) (hQ : g32t_PolarizedWeil Q)
    (h : g32t_KIsog P Q) (hAlg : g32t_WeilAlg Q) : g32t_WeilAlg P :=
  g34n_weilAlg_pullback P Q ((wtr_polarizedWeil_three_iff P).2 hP)
    ((wtr_polarizedWeil_three_iff Q).2 hQ) h hAlg

/-- Reverse isogenies between polarized Weil varieties give algebraicity transport in both
directions.
Source: G34 v1.5, Lemma 2.2; Mumford, *Abelian Varieties*, §§4 and 18. -/
theorem g34n_transport_of_reverse {n : ℕ} (P Q : wtr_Variety n)
    (hP : wtr_PolarizedWeil n P) (hQ : wtr_PolarizedWeil n Q)
    (reverse : wtr_KIsog P Q → wtr_KIsog Q P) :
    wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q) :=
  g34n_transport_of_reverse_aux P Q hP hQ reverse

example {n : ℕ} (P Q : wtr_Variety n) (hP : wtr_PolarizedWeil n P)
    (hQ : wtr_PolarizedWeil n Q) (reverse : wtr_KIsog P Q → wtr_KIsog Q P)
    (h : wtr_KIsog P Q) : wtr_WeilAlg P ↔ wtr_WeilAlg Q :=
  g34n_transport_of_reverse P Q hP hQ reverse h

/-- The generic transfer argument from reverse isogenies between member endpoints.
Source: G34 v1.5, Lemmas 2.2 and 6.1 and Theorem A; van Geemen, LNM 1594, §§5.2–5.11. -/
theorem g34n_theoremA_of_transfer {n : ℕ}
    {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : g34n_TransferDatum n δ) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) (hM : wtr_IsMember n δ (⟨A, W, pol⟩ : wtr_Variety n)) :
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W
      hM.polarized.isWeilType :=
  g34n_theoremA_of_transfer_aux D A W pol hM

example {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : g34n_TransferDatum n δ) (P : wtr_Variety n) (hP : wtr_IsMember n δ P) :
    WeilClassesAlgebraic (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
      (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) P.W
      hP.polarized.isWeilType :=
  g34n_theoremA_of_transfer D P.X P.W P.pol hP

/-- G34 Theorem A from the named inputs with transport narrowed to reverse isogenies between
members.
Source: G34 v1.5, Theorem A and its proof; Mumford, *Abelian Varieties*, §§4 and 18. -/
theorem g34n_theoremA_of_premises (B : g34n_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A :=
  g34n_theoremA_of_premises_aux B A

example (B : g34n_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A := g34n_theoremA_of_premises B A

/-- G34 Theorem B from the narrowed premise bundle and the compensation input.
Source: G34 v1.5, Theorem B and Proposition 10.2; Schoen, Compositio Math. 114 (1998),
Proposition 10; Voisin, Bourbaki exposé 1248 (2026), Lemma 2.9. -/
theorem g34n_theoremB_of_premises (B : g34n_premises) (A : Over (Spec ↧ℂ))
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
  g34n_theoremB_of_premises_aux B A hComp

example (B : g34n_premises) (A : Over (Spec ↧ℂ))
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
  g34n_theoremB_of_premises B A hComp

end HodgeLean.Papers
