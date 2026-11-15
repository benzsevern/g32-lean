import HodgeLean.Blocks.Milestone.AbelianVariety
import HodgeLean.Meta.Tags

noncomputable section
namespace HodgeBlocks

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- The Hard Lefschetz isomorphism `H^2 ≅ H^{2*p2}` (standing for
`L^{g-2} : H^2(A) → H^{2g-2}(A)`, with `p2` standing for `g - 1`), cited as a
hypothesis structure: data the caller must supply, not a construction here. This project
represents cited geometric or analytic theorems by structures over free parameters, never by
axioms; see `HodgeBlocks/Axioms/README.md`.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Theorem 6.25 (`voisin-htcag1.txt:4530-4538`): "If X is a compact Kahler manifold of dimension n, then for every k < n, L^{n-k} : H^k(X,R) → H^{2n-k}(X,R) is an isomorphism" (notation normalized from the OCR). Taking `n = g` and `k = 2` gives the displayed map. Voisin states the theorem over `ℝ`, not `ℚ`; the rational version used here follows by the standard descent/dimension-count argument for an `ℝ`-linear base change of a `ℚ`-linear map, but that descent step is not quoted from Voisin. Likewise, cup product with a rational `(1,1)` class shifts Hodge type by `(1,1)` in each factor, so it is a morphism of Hodge structures of that bidegree; this standard basic fact of Hodge theory was not separately quoted in this run. Lieberman 1968 concerns preservation of algebraic classes by the different, adjoint degree-lowering operator `Λ`, not this Hard Lefschetz isomorphism.

**Referee finding (hodge-LEAN23), disclosed rather than fixed by narrowing the statement**:
`Lpow_isAlgebraic` is a THIRD fact bundled into this structure beyond the two disclosed above,
and Theorem 6.25 does not state it either: for the intended geometric instantiation (`Lpow` =
cup product with the `(g-2)`-th power of the polarization class), it follows from the standard
fact that the algebraic classes form an ideal under cup product with an algebraic class (cup
product with a fixed algebraic divisor class sends an algebraic cycle class to an algebraic
cycle class) — again a standard fact of intersection theory, not separately quoted here, and not
a consequence of Theorem 6.25 by itself. A caller instantiating this structure must supply
`Lpow_isAlgebraic` from this fact (or an equivalent one), not from the Hard Lefschetz
isomorphism alone. -/
@[hodge_hypothesis]
structure HardLefschetzFromDegreeTwo (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop) {p2 : ℕ} (hg : S.g = p2 + 1) (hp2 : 1 < p2) where
  Lpow : ⋀[ℚ]^2 V ≃ₗ[ℚ] ⋀[ℚ]^(2 * p2) V
  Lpow_isHodge : ∀ {v : ⋀[ℚ]^2 V},
      IsHodgeClass (p := 1) (S.cohomology 2) v ↔
        IsHodgeClass (p := p2) (S.cohomology (2 * p2)) (Lpow v)
  Lpow_isAlgebraic : ∀ {v : ⋀[ℚ]^2 V}, IsAlgebraic v → IsAlgebraic (Lpow v)

/-- **Hard Lefschetz reduces the conjecture in degree `2g-2` to degree 2.** Given the
Hard-Lefschetz hypothesis and algebraicity of every degree-2 Hodge class, every Hodge class of
degree `2*p2` is algebraic. -/
@[hodge_milestone]
theorem hodgeConjecture_degTwoGMinusTwo_of_hardLefschetz (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop) {p2 : ℕ} {hg : S.g = p2 + 1} {hp2 : 1 < p2}
    (H : HardLefschetzFromDegreeTwo S IsAlgebraic hg hp2)
    (hdeg2 : ∀ v : ⋀[ℚ]^2 V, IsHodgeClass (p := 1) (S.cohomology 2) v → IsAlgebraic v) :
    ∀ v : ⋀[ℚ]^(2 * p2) V, IsHodgeClass (p := p2) (S.cohomology (2 * p2)) v → IsAlgebraic v := by
  intro v hv
  have hw : H.Lpow (H.Lpow.symm v) = v := H.Lpow.apply_symm_apply v
  have hvHodge : IsHodgeClass (p := 1) (S.cohomology 2) (H.Lpow.symm v) := by
    rw [H.Lpow_isHodge, hw]
    exact hv
  have hwAlg : IsAlgebraic (H.Lpow.symm v) := hdeg2 _ hvHodge
  have h := H.Lpow_isAlgebraic hwAlg
  rwa [hw] at h

/-- For elliptic curves, all even-degree Hodge classes are algebraic: degree zero is handled by the
unit, degree two by Lefschetz (1,1), and all higher even degrees vanish.  The degree-two step is
named for the theorem classically due to Lefschetz; the modern reference used here is Voisin's
restatement cited in `LefschetzOneOne`. -/
@[hodge_milestone]
theorem hodgeConjecture_g1 (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop) {polarization : ⋀[ℚ]^2 V}
    (hg : S.g = 1) (hAlg : IsCycleClassPredicate S IsAlgebraic polarization)
    (L : LefschetzOneOne S IsAlgebraic) : HodgeConjectureFor S IsAlgebraic := by
  intro p v hv
  rcases p with _ | _ | p
  · exact isAlgebraic_of_degree_zero S IsAlgebraic hAlg v
  · exact lefschetz_one_one S IsAlgebraic L v hv
  · exact isAlgebraic_of_degree_above_top S IsAlgebraic hAlg (2 * (p + 2)) (by omega) v

/-- For abelian surfaces, degree zero and degree two use the unit and Lefschetz (1,1), while top
degree uses the nonzero algebraic polarization square; degrees above the top vanish. -/
@[hodge_milestone]
theorem hodgeConjecture_g2 (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop) {polarization : ⋀[ℚ]^2 V}
    (hg : S.g = 2) (hAlg : IsCycleClassPredicate S IsAlgebraic polarization)
    (L : LefschetzOneOne S IsAlgebraic)
    (hTop : PolarizationTopPowerNonzero S polarization) :
    HodgeConjectureFor S IsAlgebraic := by
  intro p v hv
  have top_of_eq : ∀ (m : ℕ), m = 2 * S.g → ∀ w : ⋀[ℚ]^m V, IsAlgebraic w := by
    intro m hm w
    subst m
    exact isAlgebraic_of_degree_top S IsAlgebraic hAlg hTop w
  rcases p with _ | _ | _ | p
  · exact isAlgebraic_of_degree_zero S IsAlgebraic hAlg v
  · exact lefschetz_one_one S IsAlgebraic L v hv
  · apply top_of_eq (2 * (0 + 1 + 1)) (by omega) v
  · exact isAlgebraic_of_degree_above_top S IsAlgebraic hAlg (2 * (p + 3)) (by omega) v

/-- For abelian threefolds, degree four is reduced to degree two by Hard Lefschetz, degree six uses
the nonzero algebraic polarization cube, and all higher even degrees vanish. -/
@[hodge_milestone]
theorem hodgeConjecture_g3 (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop) {polarization : ⋀[ℚ]^2 V}
    (hg : S.g = 3) (hAlg : IsCycleClassPredicate S IsAlgebraic polarization)
    (L : LefschetzOneOne S IsAlgebraic)
    (H : HardLefschetzFromDegreeTwo S IsAlgebraic (p2 := 2) (by omega) (by omega))
    (hTop : PolarizationTopPowerNonzero S polarization) :
    HodgeConjectureFor S IsAlgebraic := by
  intro p v hv
  have top_of_eq : ∀ (m : ℕ), m = 2 * S.g → ∀ w : ⋀[ℚ]^m V, IsAlgebraic w := by
    intro m hm w
    subst m
    exact isAlgebraic_of_degree_top S IsAlgebraic hAlg hTop w
  rcases p with _ | _ | _ | _ | p
  · exact isAlgebraic_of_degree_zero S IsAlgebraic hAlg v
  · exact lefschetz_one_one S IsAlgebraic L v hv
  · exact hodgeConjecture_degTwoGMinusTwo_of_hardLefschetz S IsAlgebraic H
      (lefschetz_one_one S IsAlgebraic L) v hv
  · apply top_of_eq (2 * (0 + 1 + 1 + 1)) (by omega) v
  · exact isAlgebraic_of_degree_above_top S IsAlgebraic hAlg (2 * (p + 4)) (by omega) v

end HodgeBlocks
