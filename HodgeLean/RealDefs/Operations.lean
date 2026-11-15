import HodgeConjecture.Variants
import HodgeLean.RealDefs.DegreeZero

/-! # Cup products and Lefschetz powers on the real cohomology

Against the pinned definitions of `HodgeConjecture`, this file states the cup-product package
(`CupProduct`, roadmap `docs/roadmap/layer3.md` §3 O1), the Lefschetz powers built from it
(`lefschetzPow`, O2), and the free bridge from the dimension-bounded Hodge conjecture to its
abelian-variety special case.

The signatures are the roadmap's (§3 O1, O2 and the common prelude), with these changes:

* `unitClass` and `bettiDeRham` are stated without `[IsProjective X.hom]`, which their bodies
  never use. This only generalizes them; every use below has the instance.
* `CupProduct` and `lefschetzPow` are stated over `HQ X n`, a constant defined as upstream's
  `H^n(X; ℚ)` (`HQ_def` is `rfl`), whose `AddCommGroup` and `Module ℚ` instances are upstream's,
  transported with `inferInstanceAs`. The reason is kernel time only: the kernel re-infers each
  distinct `H^n(X; ℚ)` term (about 1–2 s each), and a structure's generated declarations repeat
  every field type, so with `H^i(X; ℚ)` written out this file took about 10 minutes to check.
  Statements compared with upstream (`unitClass`, the rejection lemmas about `[X]`, the bridge)
  keep upstream's types. Tensor products over `HQ X n` and over `H^n(X; ℚ)` are not syntactically
  the same, since their instance terms differ; `HQ.linearEquiv` (in `HodgeStructure`) identifies
  the two spaces, and `bettiDeRhamHQ_eq` relates `bettiDeRhamHQ` to `bettiDeRham` through it.
* `lefschetzPow` has the roadmap's signature; its body (recursion on `r`, with
  `L^(r+1) = (η ∪ -) ∘ L^r`) is new.
* Besides the two rejection lemmas the roadmap names, `CupProduct.unitClass_ne_zero` and
  `CupProduct.cup_ne_zero` show that a cup product makes the unit nonzero, using
  `cycleComponentSheafClass_genericPoint_ne_zero` from `DegreeZero`.

`[X] = 1` (roadmap U3) is proved in `FundamentalClassUnit.lean` (`cycleComponentSheafClass_generic`);
`docs/notes/fundamental-class-unit.md` records how. Proved here, before that:
`unitClass_mem_span_fundamentalClass`, that on a preconnected `X(ℂ)` the unit is a rational
multiple of `[X]`. -/

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLean.RealDefs

section Prelude

variable (X : Over (Spec ↧ℂ))

/-- `H^n(X(ℂ); ℚ)`, upstream's rational cohomology, as a constant. It is definitionally equal to
`H^n(X; ℚ)` (`HQ_def`); it exists only so that the kernel infers the sheaf-cohomology term once. -/
def HQ (n : ℕ) : Type := H^n(X; ℚ)

/-- `HQ X n` is upstream's `H^n(X; ℚ)`, by definition. -/
theorem HQ_def (n : ℕ) : HQ X n = H^n(X; ℚ) := rfl

/-- Upstream's additive group structure on `H^n(X; ℚ)`. -/
noncomputable instance (n : ℕ) : AddCommGroup (HQ X n) :=
  inferInstanceAs (AddCommGroup (H^n(X; ℚ)))

/-- Upstream's `ℚ`-vector space structure on `H^n(X; ℚ)` (`fieldCohomologyModule`). -/
noncomputable instance (n : ℕ) : Module ℚ (HQ X n) :=
  inferInstanceAs (Module ℚ (H^n(X; ℚ)))

variable [IsIntegral X.left] [Smooth X.hom]

/-- The unit `1 ∈ H^0(X(ℂ); ℚ)`, the constant class with value `1`. -/
noncomputable abbrev unitClass : H^0(X; ℚ) := fieldCohomologyClass ℚ X 1

/-- The `ℂ`-linear extension `ℂ ⊗[ℚ] H^n(X(ℂ); ℚ) → H_dR^n(X)` of the Betti-to-de Rham map. -/
noncomputable def bettiDeRham (n : ℕ) :
    TensorProduct ℚ ℂ (H^n(X; ℚ)) →ₗ[ℂ] H_dR^(n : ℤ)(X) :=
  (fieldToDeRhamCohomologyLinear ℚ X n).liftBaseChange ℂ

end Prelude

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- A cup product on `H^*(X(ℂ); ℚ)`: `ℚ`-bilinear maps `H^i × H^j → H^(i+j)`, unital for the
constant class `1`, associative and graded commutative, for which the fundamental class of `X`
(the class of its generic point) acts as the identity.

Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, Ch. II §7 (cup products in sheaf cohomology, their unit and graded commutativity), section only.

The theorem numbers inside II §7 are not pinned: the statement relies on the section as a whole
(the cup product on `H^*(X; ℚ)` for the constant sheaf, its unit `1 ∈ H^0`, associativity and
`b ∪ a = (-1)^(ij) a ∪ b` for `a ∈ H^i`, `b ∈ H^j`). `fundamental_cup` is not in Bredon: it states
that upstream's `cycleComponentSheafClass` of the generic point is the unit, which is the
normalization `[X] = 1`, proved as `cycleComponentSheafClass_generic` in
`FundamentalClassUnit.lean` (roadmap U3). So `fundamental_cup` is consistent with upstream's
normalization; this does not construct a `CupProduct` instance. The structure lists the properties of a cup product and does not pin
`cup` to Bredon's construction: any unital, associative, graded-commutative product for which
`[X]` acts as the identity is an instance.

**Consistency.** For `X = Spec ℂ` (as `𝟙 : Spec ℂ ⟶ Spec ℂ`, integral, smooth and projective),
`X(ℂ)` is one point, so `H^0(X; ℚ) = ℚ` with `unitClass` the element `1`, and `H^i = 0` for
`i > 0`, because global sections are exact on a point. Take `cup` to be multiplication of `ℚ` in
bidegree `(0, 0)` and zero otherwise. Then `one_cup`, `cup_one`, `assoc` and `graded_comm` hold
(every product with a factor in positive degree lands in `0`, and `ℚ` is commutative).
`fundamental_cup` holds exactly when `[Spec ℂ] = 1`, which is U3 for this `X`. Upstream's
normalization gives the point class `+[pt]` in degree `0` and the coclass taking it to `1`, and
U3 is proved: `cycleComponentSheafClass_generic` in `FundamentalClassUnit.lean` (F-1683).

**Non-degeneracy.** The unit is pinned to the real constant class `fieldCohomologyClass ℚ X 1`,
and `fundamental_cup` with `cup_one` forces `[X] = unitClass X`
(`CupProduct.fundamentalClass_eq_unit`). `DegreeZero` proves `[X] ≠ 0` unconditionally, so any
`μ : CupProduct X` has `unitClass X ≠ 0` (`CupProduct.unitClass_ne_zero`). A zero cup product
would give `unitClass X = 1 ∪ 1 = 0`, so it is no instance (`CupProduct.cup_ne_zero`). Neither is
any instance on a trivial `H^0` (`CupProduct.not_subsingleton_of_unit_ne_zero`). -/
@[hodge_hypothesis]
structure CupProduct where
  cup : ∀ {i j k : ℕ}, i + j = k → HQ X i →ₗ[ℚ] HQ X j →ₗ[ℚ] HQ X k
  one_cup : ∀ {j : ℕ} (a : HQ X j), cup (zero_add j) (unitClass X) a = a
  cup_one : ∀ {i : ℕ} (a : HQ X i), cup (add_zero i) a (unitClass X) = a
  assoc : ∀ {i j l ij jl k : ℕ} (hij : i + j = ij) (hjl : j + l = jl)
      (h₁ : ij + l = k) (h₂ : i + jl = k) a b c,
      cup h₁ (cup hij a b) c = cup h₂ a (cup hjl b c)
  graded_comm : ∀ {i j k : ℕ} (h : i + j = k) (h' : j + i = k) a b,
      cup h' b a = ((-1 : ℚ) ^ (i * j)) • cup h a b
  /-- Compatibility with the class of `X` itself. -/
  fundamental_cup : ∀ (x : X.left) (hx : Order.coheight x = 0) {j : ℕ} (a : HQ X j),
      cup (zero_add j) (cycleComponentSheafClass X x hx) a = a

namespace CupProduct

variable {X}

/-- A cup product forces the class of `X` to be the unit. -/
theorem fundamentalClass_eq_unit (μ : CupProduct X) (x : X.left)
    (hx : Order.coheight x = 0) :
    cycleComponentSheafClass X x hx = unitClass X := by
  have h₁ := μ.fundamental_cup x hx (unitClass X)
  have h₂ := μ.cup_one (i := 0) (cycleComponentSheafClass X x hx)
  exact h₂.symm.trans h₁

/-- With a nonzero unit, `H^0` is not trivial. -/
theorem not_subsingleton_of_unit_ne_zero (_μ : CupProduct X) (h : unitClass X ≠ 0) :
    ¬ Subsingleton (H^0(X; ℚ)) :=
  fun _ => h (Subsingleton.elim _ _)

/-- A cup product forces the unit to be nonzero, since the class of `X` is nonzero.

Subsumed by the unconditional `unitClass_ne_zero'` (`FundamentalClassUnit.lean`, F-1683), which
needs no cup product; this version predates that proof and is still used below. -/
theorem unitClass_ne_zero (μ : CupProduct X) : unitClass X ≠ 0 := by
  rw [← μ.fundamentalClass_eq_unit _ (coheight_genericPoint X.left)]
  exact cycleComponentSheafClass_genericPoint_ne_zero X _

/-- Cup product with the unit is nonzero in degree zero, so the zero pairing is no cup product. -/
theorem cup_ne_zero (μ : CupProduct X) : μ.cup (zero_add 0) ≠ 0 := by
  intro h
  apply μ.unitClass_ne_zero
  have h₀ := congrArg (fun f => f (unitClass X) (unitClass X)) h
  exact (μ.one_cup (unitClass X)).symm.trans h₀

end CupProduct

/-- The Lefschetz power `L^r = (η ∪ -)^r : H^k → H^m`, where `k + 2r = m`. -/
noncomputable def lefschetzPow (μ : CupProduct X) (η : HQ X 2) :
    ∀ (r : ℕ) {k m : ℕ}, k + 2 * r = m → HQ X k →ₗ[ℚ] HQ X m
  | 0, _, _, rfl => LinearMap.id
  | r + 1, k, _, rfl => μ.cup (by ring) η ∘ₗ lefschetzPow μ η r (k := k) rfl

/-- On a preconnected `X(ℂ)`, the unit is a rational multiple of the class of `X`.

Checks: F-1661 -/
theorem unitClass_mem_span_fundamentalClass [PreconnectedSpace (ComplexPoint X)]
    (hη : Order.coheight (genericPoint X.left) = 0) :
    ∃ q : ℚ, q • cycleComponentSheafClass X (genericPoint X.left) hη = unitClass X := by
  have h := span_singleton_eq_top_of_rank_le_one (rank_H0_le_one X)
    (cycleComponentSheafClass_genericPoint_ne_zero X hη)
  have hu : unitClass X ∈ Submodule.span ℚ {cycleComponentSheafClass X (genericPoint X.left) hη} :=
    h ▸ Submodule.mem_top
  exact Submodule.mem_span_singleton.mp hu

/-- The Hodge conjecture in dimension at most `n` implies its abelian-variety case. -/
theorem hodgeConjectureForAbelianVarietiesInDimensionLE_of_inDimensionLE {n : ℕ}
    (h : HodgeConjectureInDimensionLE n) : HodgeConjectureForAbelianVarietiesInDimensionLE n :=
  fun X _ _ _ _ hX p => h X hX p

end HodgeLean.RealDefs
