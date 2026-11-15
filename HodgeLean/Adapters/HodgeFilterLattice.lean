import HodgeLean.Adapters.HodgeFilterLatticeProofs

/-! # The Hodge filtration against the lattice holomorphic summand: frozen specification

Inputs stage 4b. Stage 4a (`HodgeDegreeOne`) reduces the degree-one Hodge decomposition of an
abelian `X` to `dim F^1 H_dR^1 = g` and `F^1 ∩ conj F^1 = 0`. The lattice side
(`DegreeOneLattice`) already has a split `ℂ ⊗[ℚ] HQ X 1 = complexHolomorphicH1 X ⊕
complexAntiholomorphicH1 X` with both summands of dimension `g`. This stage connects the two through
the Betti–de Rham map `bettiDeRhamHQ X 1 : ℂ ⊗[ℚ] HQ X 1 → H_dR^1(X)`: write
`F^1_B = (F^1 H_dR^1).comap (bettiDeRhamHQ X 1)` for the Hodge filtration pulled back to the Betti
side. The missing identification is `F^1_B = complexHolomorphicH1 X`.

Claimed:
* for every smooth integral `X`, all `p` and `n`: the pullback of `conj F^p` is the rational
  conjugate of the pullback of `F^p`;
* for abelian `X`: the implication from the inclusion `F^1_B ≤ complexHolomorphicH1 X` to
  `F^1 ∩ conj F^1 = 0` and to `dim F^1 H_dR^1 ≤ g`;
* for abelian `X`: the identification `F^1_B = complexHolomorphicH1 X` is equivalent to that
  inclusion together with `g ≤ dim F^1 H_dR^1`;
* for abelian `X`: the implication from the identification to the identification of the pullback
  of `conj F^1` with `complexAntiholomorphicH1 X`, and to the degree-one Hodge decomposition
  `DirectSum.IsInternal (deRhamHodgePiece X 1)`;
* for abelian `X`: the implication from the inclusion and the degree-one decomposition to the
  identification;
* falsification: for `g ≥ 1` the two lattice summands differ, so the identification with the
  antiholomorphic summand is a different, incompatible statement.

Not claimed: the inclusion `F^1_B ≤ complexHolomorphicH1 X`, the identification itself, or
`g ≤ dim F^1 H_dR^1`. They are premises of the statements that use them. They need global
holomorphic `1`-forms, the computation of `ℍ^1(X; F^1 Ω•)`, and integration of forms along the
lattice loops, none of which exist upstream or here (`docs/specs/HodgeFilterLattice.md`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- Pulled back to `ℂ ⊗[ℚ] HQ X n`, the conjugate filtration `conj F^p` is the rational conjugate
of `F^p`: `bettiDeRhamHQ` intertwines `sigmaQ` with `deRhamConj`, and `sigmaQ` is an involution.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
§7.1.1 (`conj F^p` is the complex conjugate of `F^p` for the real structure of `H^n(X, ℂ)`),
through `bettiDeRhamHQ_sigmaQ` (`HodgeLean/RealDefs/HodgeStructure.lean`). -/
theorem spec_comap_conjHodgeFiltration_eq_map_sigmaQ (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (p : ℤ) (n : ℕ) :
    (conjHodgeFiltrationComplexSubmodule X p (n : ℤ)).comap (bettiDeRhamHQ X n) =
      ((F^p H_dR^(n : ℤ)(X)).comap (bettiDeRhamHQ X n)).map (HodgeBlocks.sigmaQ (HQ X n)) :=
  spec_comap_conjHodgeFiltration_eq_map_sigmaQ_aux X p n

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (ω : ℂ ⊗[ℚ] HQ X 1)
    (hω : bettiDeRhamHQ X 1 ω ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X)) :
    bettiDeRhamHQ X 1 (HodgeBlocks.sigmaQ (HQ X 1) ω) ∈
      conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ) := by
  have h := (spec_comap_conjHodgeFiltration_eq_map_sigmaQ X 1 1).ge
    (Submodule.mem_map_of_mem (f := HodgeBlocks.sigmaQ (HQ X 1)) (Submodule.mem_comap.mpr hω))
  exact Submodule.mem_comap.mp h

/-- For abelian `X`: the implication from `F^1_B ≤ complexHolomorphicH1 X` to
`F^1 ∩ conj F^1 = 0`, the second open condition of stage 4a. Conjugation carries the holomorphic
summand to the antiholomorphic one, which meets it only in `0`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Theorem 1.4.1
(`H^{1,0} ∩ H^{0,1} = 0`), through `spec_comap_conjHodgeFiltration_eq_map_sigmaQ`,
`spec_complexH1_conjugation_exchanges`, `spec_complexH1_split` and
`spec_bettiDeRhamIso_abelian`. -/
theorem spec_disjoint_hodgeFiltration_one_of_le (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hle : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X) :
    Disjoint (F^1 H_dR^((1 : ℕ) : ℤ)(X))
      (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)) :=
  spec_disjoint_hodgeFiltration_one_of_le_aux X hle

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom]
    (hle : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X) :
    F^1 H_dR^((1 : ℕ) : ℤ)(X) ⊓ conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ) = ⊥ :=
  (spec_disjoint_hodgeFiltration_one_of_le X hle).eq_bot

/-- For abelian `X`: the implication from `F^1_B ≤ complexHolomorphicH1 X` to
`dim F^1 H_dR^1 ≤ g`, since `bettiDeRhamHQ X 1` is an isomorphism and the holomorphic summand has
dimension `g`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
Theorem 1.4.1, through `spec_complexH1_dimension` and `spec_bettiDeRhamIso_abelian`. -/
theorem spec_finrank_hodgeFiltration_one_le_of_le (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hle : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X) :
    Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) ≤ dim X.left :=
  spec_finrank_hodgeFiltration_one_le_of_le_aux X hle

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom]
    (hle : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X)
    (hg : dim X.left = 0) :
    Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) = 0 := by
  have h := spec_finrank_hodgeFiltration_one_le_of_le X hle
  omega

/-- For abelian `X`: `F^1_B` is the lattice holomorphic summand exactly when it is contained in
it and `F^1 H_dR^1` has dimension at least `g`. The identification thus splits into one inclusion
and one dimension bound.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Theorem 1.4.1,
through `spec_complexH1_dimension`, `spec_bettiDeRhamIso_abelian` and
`Submodule.eq_of_le_of_finrank_le`. -/
theorem spec_comap_hodgeFiltration_one_eq_iff (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X ↔
      (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X ∧
        dim X.left ≤ Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) :=
  spec_comap_hodgeFiltration_one_eq_iff_aux X

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom]
    (heq : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X) :
    Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) = dim X.left :=
  le_antisymm (spec_finrank_hodgeFiltration_one_le_of_le X heq.le)
    ((spec_comap_hodgeFiltration_one_eq_iff X).mp heq).2

/-- For abelian `X`: the implication from `F^1_B = complexHolomorphicH1 X` to the identification
of the pulled-back conjugate filtration with the antiholomorphic summand, by conjugating both sides.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Theorem 1.4.1
(`H^{0,1} = conj H^{1,0}`), through `spec_comap_conjHodgeFiltration_eq_map_sigmaQ` and
`spec_complexH1_conjugation_exchanges`. -/
theorem spec_comap_conjHodgeFiltration_one_eq_of_eq (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (heq : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X) :
    (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)).comap (bettiDeRhamHQ X 1) =
      complexAntiholomorphicH1 X :=
  spec_comap_conjHodgeFiltration_one_eq_of_eq_aux X heq

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom]
    (heq : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X) :
    Module.finrank ℂ ((conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)).comap
      (bettiDeRhamHQ X 1)) = dim X.left := by
  rw [spec_comap_conjHodgeFiltration_one_eq_of_eq X heq]
  exact (spec_complexH1_dimension X).2

/-- For abelian `X`: the implication from `F^1_B = complexHolomorphicH1 X` to the Hodge
decomposition in degree one. The identification gives both open conditions of stage 4a.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
Theorem 1.4.1 (`H^1(X, ℂ) = H^{1,0} ⊕ H^{0,1}`), through
`spec_comap_hodgeFiltration_one_eq_iff`, `spec_disjoint_hodgeFiltration_one_of_le`,
`spec_finrank_hodgeFiltration_one_le_of_le` and
`spec_deRhamHodgePiece_one_isInternal_of_finrank`. -/
theorem spec_deRhamHodgePiece_one_isInternal_of_comap_eq (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (heq : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X) :
    DirectSum.IsInternal (deRhamHodgePiece X 1) :=
  spec_deRhamHodgePiece_one_isInternal_of_comap_eq_aux X heq

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom]
    (heq : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X) :
    IsCompl (F^1 H_dR^((1 : ℕ) : ℤ)(X))
      (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)) :=
  (spec_deRhamHodgePiece_one_isInternal_iff X).mp
    (spec_deRhamHodgePiece_one_isInternal_of_comap_eq X heq)

/-- For abelian `X`: the implication from `F^1_B ≤ complexHolomorphicH1 X` and the degree-one
Hodge decomposition to the identification. Under the decomposition, one inclusion is all that is
missing.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Theorem 1.4.1,
through `spec_finrank_hodgeFiltration_one_of_isInternal` and
`spec_comap_hodgeFiltration_one_eq_iff`. -/
theorem spec_comap_hodgeFiltration_one_eq_of_le_of_isInternal (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hle : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X)
    (h : DirectSum.IsInternal (deRhamHodgePiece X 1)) :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X :=
  spec_comap_hodgeFiltration_one_eq_of_le_of_isInternal_aux X hle h

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hD : HodgeDecomposition X)
    (hle : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X) :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X :=
  spec_comap_hodgeFiltration_one_eq_of_le_of_isInternal X hle (hD.isInternal 1)

/-- Falsification check, for abelian `X` with `g ≥ 1`: the lattice holomorphic and antiholomorphic
summands differ. So `F^1_B` cannot be identified with both, and identifying it with the
antiholomorphic summand instead is a different statement, incompatible with the intended one.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Theorem 1.4.1,
through `spec_complexH1_split` (the summands meet in `0`) and `spec_complexH1_dimension` (each has
dimension `g`). -/
theorem spec_complexHolomorphicH1_ne_antiholomorphic (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hg : 1 ≤ dim X.left) :
    complexHolomorphicH1 X ≠ complexAntiholomorphicH1 X :=
  spec_complexHolomorphicH1_ne_antiholomorphic_aux X hg

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hg : 1 ≤ dim X.left)
    (heq : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X) :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≠ complexAntiholomorphicH1 X := by
  rw [heq]
  exact spec_complexHolomorphicH1_ne_antiholomorphic X hg

end HodgeLean.Adapters
