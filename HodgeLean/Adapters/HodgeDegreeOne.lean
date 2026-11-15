import HodgeLean.Adapters.HodgeDegreeOneProofs

/-! # The degree-one Hodge decomposition: frozen specification

Inputs stage 4a, the first step toward `HodgeDecomposition X` for abelian `X`.

Claimed:
* for every smooth integral `X`, the degree-one pieces `deRhamHodgePiece X 1` are `F^1 H_dR^1` at
  `(1, 0)`, `conj F^1 H_dR^1` at `(0, 1)`, and `⊥` elsewhere;
* for every smooth integral `X`, `F^p H_dR^n` and its conjugate `conj F^p H_dR^n` have the same
  dimension;
* linear algebra: in a complex space of dimension `2g` with a conjugate-linear involution `σ`, a
  subspace of dimension `g` that meets its conjugate trivially is a complement of it;
* for every smooth integral `X`, the Hodge decomposition in degree one is equivalent to
  `F^1 H_dR^1` and `conj F^1 H_dR^1` being complementary;
* for abelian `X` of dimension `g`: the implication from `dim F^1 H_dR^1 = g` and
  `F^1 ∩ conj F^1 = 0` to the Hodge decomposition in degree one, and conversely that the degree-one
  decomposition forces `h^{1,0} = h^{0,1} = g`;
* the implication from `HodgeDecomposition X` to `dim H^{1,0} = dim H^{0,1} = g` on
  `ℂ ⊗[ℚ] H^1(X(ℂ); ℚ)`, for abelian `X`.

Not claimed: `dim F^1 H_dR^1 = g` or `F^1 ∩ conj F^1 = 0` themselves, holomorphic `1`-forms
`H^0(X, Ω^1)` or their dimension, global sections of `𝒪_X`, the cotangent sheaf of a group scheme,
or any degree above one. The two degree-one conditions are premises, not consequences, of the
statements that use them. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- In degree one, the only Hodge pieces are `F^1` at `(1, 0)` and `conj F^1` at `(0, 1)`: every
other piece on the line `p + q = 1` has `p > 1` or `q > 1` and vanishes, and `F^0` is everything.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
§7.1.1 (the Hodge filtration and `H^{p,q} = F^p ∩ conj F^q`), through `hodgePiece_eq_bot_of_lt`
and `hodgeFiltration_eq_top_of_nonpos` (`HodgeLean/RealDefs/Filtration.lean`). -/
theorem spec_deRhamHodgePiece_one (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (pq : ℤ × ℤ) :
    deRhamHodgePiece X 1 pq =
      if pq = (1, 0) then F^1 H_dR^((1 : ℕ) : ℤ)(X)
      else if pq = (0, 1) then conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)
      else ⊥ :=
  spec_deRhamHodgePiece_one_aux X pq

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    deRhamHodgePiece X 1 (2, -1) = ⊥ := by
  rw [spec_deRhamHodgePiece_one X]
  simp

/-- Complex conjugation is a conjugate-linear bijection of `H_dR^n(X)` carrying `conj F^p` onto
`F^p`, so the two have the same complex dimension.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.1 (`H^{q,p}` is the
conjugate of `H^{p,q}`), through `deRhamConj_deRhamConj` and `rank_eq_of_equiv_equiv`. -/
theorem spec_finrank_conjHodgeFiltration (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (p n : ℤ) :
    Module.finrank ℂ (conjHodgeFiltrationComplexSubmodule X p n) =
      Module.finrank ℂ (F^p H_dR^n(X)) :=
  spec_finrank_conjHodgeFiltration_aux X p n

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    Module.finrank ℂ (conjHodgeFiltrationComplexSubmodule X 1 1) =
      Module.finrank ℂ (F^1 H_dR^1(X)) :=
  spec_finrank_conjHodgeFiltration X 1 1

/-- Linear algebra: if `V` has complex dimension `2g`, `σ` is a conjugate-linear involution of `V`,
and `F ≤ V` has dimension `g` and meets `σ⁻¹ F` trivially, then `F` and `σ⁻¹ F` are complements.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.1 (a Hodge structure of
weight one is a subspace `F` with `V_ℂ = F ⊕ conj F`), with `Submodule.isCompl_iff_disjoint`. -/
theorem spec_isCompl_comap_of_finrank_of_disjoint {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (σ : V →ₛₗ[starRingEnd ℂ] V)
    (hσ : Function.Involutive σ) (F : Submodule ℂ V) {g : ℕ}
    (hV : Module.finrank ℂ V = 2 * g) (hF : Module.finrank ℂ F = g)
    (hdisj : Disjoint F (F.comap σ)) :
    IsCompl F (F.comap σ) :=
  spec_isCompl_comap_of_finrank_of_disjoint_aux σ hσ F hV hF hdisj

example {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (σ : V →ₛₗ[starRingEnd ℂ] V) (hσ : Function.Involutive σ) (F : Submodule ℂ V)
    (hV : Module.finrank ℂ V = 2 * 1) (hF : Module.finrank ℂ F = 1)
    (hdisj : Disjoint F (F.comap σ)) :
    F ⊔ F.comap σ = ⊤ :=
  (spec_isCompl_comap_of_finrank_of_disjoint σ hσ F hV hF hdisj).sup_eq_top

/-- The Hodge decomposition in degree one is equivalent to `H_dR^1 = F^1 ⊕ conj F^1`.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.1 (the decomposition
`H^1 = H^{1,0} ⊕ H^{0,1}` with `H^{1,0} = F^1` and `H^{0,1} = conj F^1`), with
`spec_deRhamHodgePiece_one`. -/
theorem spec_deRhamHodgePiece_one_isInternal_iff (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    DirectSum.IsInternal (deRhamHodgePiece X 1) ↔
      IsCompl (F^1 H_dR^((1 : ℕ) : ℤ)(X))
        (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)) :=
  spec_deRhamHodgePiece_one_isInternal_iff_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (h : DirectSum.IsInternal (deRhamHodgePiece X 1)) :
    Disjoint (F^1 H_dR^((1 : ℕ) : ℤ)(X))
      (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)) :=
  ((spec_deRhamHodgePiece_one_isInternal_iff X).mp h).disjoint

/-- For abelian `X` of dimension `g`: the implication from `dim F^1 H_dR^1 = g` and
`F^1 ∩ conj F^1 = 0` to the Hodge decomposition in degree one. Here `dim H_dR^1 = 2g` comes from
`spec_bettiDeRhamIso_abelian`, so this is pure linear algebra on top of it.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
Theorem 1.4.1 (`H^1(X, ℂ) = H^{1,0} ⊕ H^{0,1}`, each of dimension `g`), with
`spec_isCompl_comap_of_finrank_of_disjoint` and `spec_deRhamHodgePiece_one_isInternal_iff`. -/
theorem spec_deRhamHodgePiece_one_isInternal_of_finrank (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hF : Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) = dim X.left)
    (hdisj : Disjoint (F^1 H_dR^((1 : ℕ) : ℤ)(X))
      (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ))) :
    DirectSum.IsInternal (deRhamHodgePiece X 1) :=
  spec_deRhamHodgePiece_one_isInternal_of_finrank_aux X hF hdisj

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom]
    (hF : Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) = dim X.left)
    (hdisj : Disjoint (F^1 H_dR^((1 : ℕ) : ℤ)(X))
      (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ))) :
    IsCompl (F^1 H_dR^((1 : ℕ) : ℤ)(X))
      (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)) :=
  (spec_deRhamHodgePiece_one_isInternal_iff X).mp
    (spec_deRhamHodgePiece_one_isInternal_of_finrank X hF hdisj)

/-- Falsification check, for abelian `X` of dimension `g`: if degree one decomposes, then
`h^{1,0} = h^{0,1} = g`. A decomposition with pieces of dimensions `(2g, 0)` (for instance
`F^1 = H_dR^1`, `conj F^1 = 0`) is excluded, because conjugation forces equal dimensions.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
Theorem 1.4.1, with `spec_finrank_conjHodgeFiltration`,
`spec_deRhamHodgePiece_one_isInternal_iff` and
`spec_bettiDeRhamIso_abelian`. -/
theorem spec_finrank_hodgeFiltration_one_of_isInternal (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (h : DirectSum.IsInternal (deRhamHodgePiece X 1)) :
    Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) = dim X.left ∧
      Module.finrank ℂ (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)) = dim X.left :=
  spec_finrank_hodgeFiltration_one_of_isInternal_aux X h

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (h : DirectSum.IsInternal (deRhamHodgePiece X 1)) :
    Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) =
      Module.finrank ℂ (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)) := by
  rw [(spec_finrank_hodgeFiltration_one_of_isInternal X h).1,
    (spec_finrank_hodgeFiltration_one_of_isInternal X h).2]

/-- For abelian `X` of dimension `g`: the implication from `HodgeDecomposition X` to
`dim H^{1,0} = dim H^{0,1} = g` on `ℂ ⊗[ℚ] H^1(X(ℂ); ℚ)`. Conjugation exchanges the two pieces
with no hypothesis (`cohomologyHodgePiece_map_sigmaQ`), which this statement is consistent with.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
Theorem 1.4.1, with `spec_finrank_hodgeFiltration_one_of_isInternal`,
`cohomologyHodgePiece_eq_map` and
`spec_bettiDeRhamIso_abelian`. -/
theorem spec_finrank_cohomologyHodgePiece_one (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hD : HodgeDecomposition X) :
    Module.finrank ℂ (cohomologyHodgePiece X 1 (1, 0)) = dim X.left ∧
      Module.finrank ℂ (cohomologyHodgePiece X 1 (0, 1)) = dim X.left :=
  spec_finrank_cohomologyHodgePiece_one_aux X hD

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hD : HodgeDecomposition X) :
    Module.finrank ℂ (cohomologyHodgePiece X 1 (1, 0)) +
      Module.finrank ℂ (cohomologyHodgePiece X 1 (0, 1)) = 2 * dim X.left := by
  rw [(spec_finrank_cohomologyHodgePiece_one X hD).1,
    (spec_finrank_cohomologyHodgePiece_one X hD).2, two_mul]

end HodgeLean.Adapters
