import HodgeLean.Adapters.HodgeDegreeOneAbelian
import HodgeLean.Adapters.TorusCohomology

/-! # The weight-one Hodge structure of an abelian `X` and its cup-wedge pieces

Stage 4m (`HodgeHigherDegreeAbelian`). Stage 4l proved the degree-one Hodge decomposition
`DirectSum.IsInternal (deRhamHodgePiece X 1)` for every abelian `X`, with no hypothesis. Two
definitions build on it:

* `abelianWeightOneHodgeStructure X`: the rational Hodge structure of weight one on
  `H¹(X(ℂ); ℚ)`, whose `(p, q)` piece is the pullback `cohomologyHodgePiece X 1 (p, q)` of
  upstream's `hodgePiece X p q 1`. Unlike `cohomologyHodgeStructure hF hB hD 1`, it needs no
  hypothesis.
* `cupWedgePiece X μ n (p, q)`: the span in `H_dR^n(X)` of the de Rham images of the complexified
  cup products `x₁ ∪ ⋯ ∪ x_n` of degree-one classes, the `i`-th of type `d i`, with total type
  `(p, q)`. Under the torus theorem it is the image of the `(p, q)` piece of `⋀^n` of the
  weight-one structure.

HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- **The weight-one Hodge structure of an abelian `X`.** For abelian `X`, the rational Hodge
structure of weight one on `H¹(X(ℂ); ℚ)` whose `(p, q)` piece is `cohomologyHodgePiece X 1 (p, q)`,
the pullback of upstream's `hodgePiece X p q 1` along `bettiDeRhamHQ` on the line `p + q = 1`
and `⊥` off it. Internality is stage 4l's degree-one decomposition carried back by the bijection
`bettiDeRhamHQ X 1`; conjugation symmetry is `cohomologyHodgePiece_map_sigmaQ`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Theorem 1.4.1;
`spec_deRhamHodgePiece_one_isInternal` (stage 4l), `spec_bettiDeRhamIso_abelian`,
`finiteBetti_abelian`, `cohomologyHodgePiece_eq_map` and `cohomologyHodgePiece_map_sigmaQ`. -/
def abelianWeightOneHodgeStructure (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] :
    letI := (finiteBetti_abelian X).finite 1
    HodgeBlocks.QHodgeStructure 1 (HQ X 1) :=
  letI := (finiteBetti_abelian X).finite 1
  { H := cohomologyHodgePiece X 1
    supported := fun pq h => by
      have h' : pq.1 + pq.2 ≠ ((1 : ℕ) : ℤ) := by simpa using h
      simp only [cohomologyHodgePiece, h', ↓reduceIte]
    isInternal := by
      rw [cohomologyHodgePiece_eq_map (HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X) 1]
      exact (spec_deRhamHodgePiece_one_isInternal X).mapEquiv _
    conj_symm := cohomologyHodgePiece_map_sigmaQ X 1 }

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (pq : ℤ × ℤ) :
    letI := (finiteBetti_abelian X).finite 1
    (abelianWeightOneHodgeStructure X).H pq = cohomologyHodgePiece X 1 pq :=
  rfl

/-- Its `n`-th exterior power, a Hodge structure of weight `n * 1` on `⋀^n H¹(X(ℂ); ℚ)`, is
Blocks' `QHodgeStructure.exteriorPower`. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (n : ℕ) :
    letI := (finiteBetti_abelian X).finite 1
    HodgeBlocks.QHodgeStructure ((n : ℤ) * 1) (⋀[ℚ]^n (HQ X 1)) :=
  letI := (finiteBetti_abelian X).finite 1
  (abelianWeightOneHodgeStructure X).exteriorPower (V := HQ X 1) n

/-- **Cup-wedge pieces.** For a cup product `μ`, the span in `H_dR^n(X)` of the classes
`bettiDeRhamHQ X n (x₁ ∪ ⋯ ∪ x_n)`, where `∪` is the complexified cup product `μ.cupMultiC n`, each
`xᵢ ∈ ℂ ⊗[ℚ] H¹` lies in `cohomologyHodgePiece X 1 (d i)`, and the total type
`HodgeBlocks.totalBidegree n d = ∑ d i` is `pq`. It is the de Rham image of the multiplicative
candidate `⋀^p H^{1,0} ∧ ⋀^q H^{0,1}` for the `(p, q)` piece of `H^n`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.3 and
Lemma 1.3.1 (`H^n = ⋀^n H¹`, with the induced Hodge decomposition); `CupProduct.cupMultiC`
(`RealDefs/AbelianExterior.lean`) and `HodgeBlocks.totalBidegree`. -/
def cupWedgePiece (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) (n : ℕ) (pq : ℤ × ℤ) : Submodule ℂ H_dR^(n : ℤ)(X) :=
  Submodule.span ℂ {α | ∃ (d : Fin n → ℤ × ℤ) (v : Fin n → ℂ ⊗[ℚ] HQ X 1),
    HodgeBlocks.totalBidegree n d = pq ∧ (∀ i, v i ∈ cohomologyHodgePiece X 1 (d i)) ∧
      bettiDeRhamHQ X n (μ.cupMultiC n v) = α}

/-- A generator: the de Rham image of a cup product of degree-one classes of types `d i` lies in
the cup-wedge piece of the total type. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) (n : ℕ) (d : Fin n → ℤ × ℤ) (v : Fin n → ℂ ⊗[ℚ] HQ X 1)
    (hv : ∀ i, v i ∈ cohomologyHodgePiece X 1 (d i)) :
    bettiDeRhamHQ X n (μ.cupMultiC n v) ∈
      cupWedgePiece X μ n (HodgeBlocks.totalBidegree n d) :=
  Submodule.subset_span ⟨d, v, rfl, hv, rfl⟩

end HodgeLean.Adapters
