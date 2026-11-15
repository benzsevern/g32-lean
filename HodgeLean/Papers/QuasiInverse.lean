import HodgeLean.Papers.QuasiInverseProofs

/-! # Reverse polarized isogenies from morphism-level quasi-inverses (FROZEN SPEC)

This module records an implication from the classical morphism-level quasi-inverse of an
isogeny.  The input supplies only a reverse morphism, its group-homomorphism and isogeny
properties, and a positive multiplication relation.  It supplies no compatibility with the
Weil action, no polarization equation, and no Weil content.  Those two cohomological clauses
are conclusions of the frozen implication.

It does not construct universal families, Prym families, period maps, parabolic polarizations,
Hilbert spreading, or the input to Proposition 4.6.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

/-- A morphism-level quasi-inverse supplies the reverse generic `K`-linear polarized isogeny;
the forward `K`-linearity and polarization equations are explicit inputs.
Source: Mumford, *Abelian Varieties*, §4; `spec_homPullback_comp`,
`spec_homPullback_id`, `spec_homPullback_zpow_degree`. -/
theorem qinv_wtr_KIsog_reverse_of_witness {n : ℕ} (P Q : wtr_Variety n)
    (f : P.X ⟶ Q.X) (f_mon : IsMonHom f) (f_isogeny : ccm2_IsogenyOnPoints f)
    (f_K : letI := (torusCohomology_cupProductOf P.X).finite
      letI := (torusCohomology_cupProductOf Q.X).finite
      ∀ x, homPullback f 1 (Q.W.J x) = P.W.J (homPullback f 1 x))
    (c : ℚ) (c_pos : 0 < c)
    (f_pol : letI := (torusCohomology_cupProductOf P.X).finite
      letI := (torusCohomology_cupProductOf Q.X).finite
      homPullback f 2 Q.pol = c • P.pol)
    (w : qinv_Witness P Q f) : wtr_KIsog Q P :=
  qinv_wtr_KIsog_reverse_of_witness_aux P Q f f_mon f_isogeny f_K c c_pos f_pol w

example {n : ℕ} (P Q : wtr_Variety n) (f : P.X ⟶ Q.X)
    (hf : IsMonHom f) (hi : ccm2_IsogenyOnPoints f)
    (hK : letI := (torusCohomology_cupProductOf P.X).finite
      letI := (torusCohomology_cupProductOf Q.X).finite
      ∀ x, homPullback f 1 (Q.W.J x) = P.W.J (homPullback f 1 x))
    (c : ℚ) (hc : 0 < c)
    (hp : letI := (torusCohomology_cupProductOf P.X).finite
      letI := (torusCohomology_cupProductOf Q.X).finite
      homPullback f 2 Q.pol = c • P.pol)
    (w : qinv_Witness P Q f) : wtr_KIsog Q P :=
  qinv_wtr_KIsog_reverse_of_witness P Q f hf hi hK c hc hp w

/-- A morphism-level quasi-inverse supplies the reverse G32 `K`-linear polarized isogeny.
Source: Mumford, *Abelian Varieties*, §4; `spec_homPullback_comp`,
`spec_homPullback_id`, `spec_homPullback_zpow_degree`. -/
theorem qinv_KIsog_reverse_of_witness (P Q : g32t_Sixfold)
    (f : P.X ⟶ Q.X) (f_mon : IsMonHom f) (f_isogeny : ccm2_IsogenyOnPoints f)
    (f_K : letI := (torusCohomology_cupProductOf P.X).finite
      letI := (torusCohomology_cupProductOf Q.X).finite
      ∀ x, homPullback f 1 (Q.W.J x) = P.W.J (homPullback f 1 x))
    (c : ℚ) (c_pos : 0 < c)
    (f_pol : letI := (torusCohomology_cupProductOf P.X).finite
      letI := (torusCohomology_cupProductOf Q.X).finite
      homPullback f 2 Q.pol = c • P.pol)
    (w : qinv_Witness P Q f) : g32t_KIsog Q P :=
  qinv_KIsog_reverse_of_witness_aux P Q f f_mon f_isogeny f_K c c_pos f_pol w

example (P Q : g32t_Sixfold) (f : P.X ⟶ Q.X)
    (hf : IsMonHom f) (hi : ccm2_IsogenyOnPoints f)
    (hK : letI := (torusCohomology_cupProductOf P.X).finite
      letI := (torusCohomology_cupProductOf Q.X).finite
      ∀ x, homPullback f 1 (Q.W.J x) = P.W.J (homPullback f 1 x))
    (c : ℚ) (hc : 0 < c)
    (hp : letI := (torusCohomology_cupProductOf P.X).finite
      letI := (torusCohomology_cupProductOf Q.X).finite
      homPullback f 2 Q.pol = c • P.pol)
    (w : qinv_Witness P Q f) : g32t_KIsog Q P :=
  qinv_KIsog_reverse_of_witness P Q f hf hi hK c hc hp w

/-- The classical quasi-inverse input yields exactly the reverse field used by
`g32n_premises`.
Source: Mumford, *Abelian Varieties*, §4; `qinv_KIsog_reverse_of_witness`. -/
theorem qinv_reverse_of_premise (h : qinv_premise) :
    ∀ P Q, g32t_IsMember P → g32t_IsMember Q →
      g32t_KIsog P Q → g32t_KIsog Q P :=
  qinv_reverse_of_premise_aux h

example (h : qinv_premise) (P Q : g32t_Sixfold) (hP : g32t_IsMember P)
    (hQ : g32t_IsMember Q) (hf : g32t_KIsog P Q) : g32t_KIsog Q P :=
  qinv_reverse_of_premise h P Q hP hQ hf

/-- The G32 literature bundle with only a classical quasi-inverse input implies Theorem A.
Source: G32 v0.16, Theorem A and Sections 2–7; Mumford, *Abelian Varieties*, §4;
`g32n_theoremA_of_premises`. -/
theorem qinv_g32_theoremA_of_premises (B : qinv_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  qinv_g32_theoremA_of_premises_aux B A W pol

example (B : qinv_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  qinv_g32_theoremA_of_premises B A W pol

end HodgeLean.Papers
