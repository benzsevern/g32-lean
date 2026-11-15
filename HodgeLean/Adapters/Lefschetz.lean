import HodgeLean.Foundations.Lefschetz
import HodgeLean.RealDefs.AbelianVariety
import HodgeLean.RealDefs.DimensionThree
import HodgeLean.Blocks.Milestone.HardLefschetz
import HodgeLean.Adapters.Polarization

/-! # Adapters: Hard Lefschetz from nondegeneracy of the polarization

Instantiates Foundations target T2 (`HodgeLean.Foundations.Lefschetz`).

* `hardLefschetz_of_torusCohomology`: for abelian `X`, `RealDefs.HardLefschetz X μ η` (O3) from the
  torus theorem C7 (`TorusCohomology μ`) and nondegeneracy of the preimage of `η` in `⋀² H¹`. The
  Lefschetz power `L^r = η ∪ ⋯ ∪ η ∪ -` on `H^*` is `ω^r ∧ -` on `⋀^* H¹` read through the torus
  isomorphisms (`cupWedgeMap_lefschetz`).
* `lpowOfNondegenerate`: the `Lpow` field of `HodgeBlocks.HardLefschetzFromDegreeTwo` as the
  Hard Lefschetz isomorphism `ω^(p₂ - 1) ∧ - : ⋀² V ≃ ⋀^(2p₂) V`, and
  `hardLefschetzFromDegreeTwoOfNondegenerate`, the structure with that `Lpow` and the two other
  fields supplied by the caller.

Relation to the goal: HC no distance; AV milestone no distance; the abelian milestones of
F-1690 (`g = 2, 3`) can take nondegeneracy of the polarization instead of O3 `HardLefschetz`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Module

namespace HodgeLean.Adapters

open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.Lefschetz HodgeLean.RealDefs

section Abelian

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- `castDeg h` is the transport `h ▸` along an equation of degrees. -/
theorem castDeg_eq_cast {M : Type*} [AddCommGroup M] [Module ℚ M] {m n : ℕ} (h : m = n)
    (x : ⋀[ℚ]^m M) : castDeg h x = h ▸ x := by
  subst h
  rfl

/-- **The wedge map intertwines the two Lefschetz operators.** If `cupWedgeMap 2 ω = η`, then
`cupWedgeMap` sends `ω^r ∧ x` to `L^r (cupWedgeMap x) = η ∪ ⋯ ∪ η ∪ cupWedgeMap x`. -/
theorem cupWedgeMap_lefschetz (μ : CupProduct X) {η : HQ X 2} (ω : ⋀[ℚ]^2 (HQ X 1))
    (hω : μ.cupWedgeMap 2 ω = η) (k : ℕ) :
    ∀ (r : ℕ) {m : ℕ} (h : k + 2 * r = m) (x : ⋀[ℚ]^k (HQ X 1)),
      μ.cupWedgeMap m (castDeg h (lefschetz ω r k x)) =
        lefschetzPow X μ η r h (μ.cupWedgeMap k x)
  | 0, m, h, x => by
    obtain rfl : m = k := by omega
    rw [lefschetzPow_zero]
    congr 1
    exact Subtype.ext (by rw [coe_castDeg, coe_lefschetz, pow_zero, one_mul])
  | r + 1, m, h, x => by
    have e : castDeg h (lefschetz ω (r + 1) k x) =
        castDeg (by omega : 2 + (k + 2 * r) = m)
          (exteriorPower.wedge ℚ _ 2 (k + 2 * r) ω (castDeg rfl (lefschetz ω r k x))) :=
      Subtype.ext (by
        rw [coe_castDeg, coe_castDeg, coe_wedge, coe_castDeg, coe_lefschetz, coe_lefschetz,
          pow_succ', mul_assoc])
    rw [e, castDeg_eq_cast, μ.cupWedgeMap_cast, μ.cupWedgeMap_wedge, CupProduct.castEquiv_cup, hω,
      cupWedgeMap_lefschetz μ ω hω k r rfl x,
      lefschetzPow_succ μ η r h (m' := k + 2 * r) rfl (by omega)]

variable [GrpObj X]

/-- **Hard Lefschetz (O3) for an abelian variety, from the torus theorem and nondegeneracy.**
For abelian `X` with the torus theorem C7 (`hT : TorusCohomology μ`, so `H^m ≅ ⋀^m H¹` by cup
product and `dim H¹ = 2 · dim X`) and a class `η ∈ H²` whose preimage `(cupWedgeEquiv 2).symm η`
in `⋀² H¹` is nondegenerate (`Symplectic.IsNondegenerate`), `η` satisfies Hard Lefschetz:
`L^(n - k) : H^k → H^(2n - k)` is bijective for `k ≤ n = dim X`.

This **replaces** the hypothesis O3 `HardLefschetz` for abelian `X` by C7 plus nondegeneracy of
the polarization's preimage in `⋀² H¹`. Neither is proved: C7 is a hypothesis structure, and
nondegeneracy of the preimage of an ample class is the nondegeneracy of the Riemann form of the
polarization (Birkenhake–Lange, Ch. 4), which is not formalized. The linear algebra is
`Lefschetz.lefschetz_bijective`.

Relation to the goal: HC no distance; AV milestone no distance; the abelian milestones of
F-1690 (`g = 2, 3`) can take nondegeneracy instead of O3.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1
(`⋀^* H¹ ≅ H^*` for a complex torus) and Ch. 4 (the Riemann form of a polarization); Huybrechts,
*Complex Geometry*, §1.2 (Hard Lefschetz on the exterior algebra). -/
theorem hardLefschetz_of_torusCohomology {μ : CupProduct X} (hT : TorusCohomology μ)
    {η : HQ X 2} (hη : IsNondegenerate ((hT.cupWedgeEquiv 2).symm η)) :
    HardLefschetz X μ η := by
  refine ⟨fun {k m} hk h => ?_⟩
  set ω := (hT.cupWedgeEquiv 2).symm η
  have hω : μ.cupWedgeMap 2 ω = η := by
    rw [← hT.cupWedgeEquiv_apply, LinearEquiv.apply_symm_apply]
  have hfun : ⇑(lefschetzPow X μ η (dim X.left - k) h) =
      ⇑(hT.cupWedgeEquiv m) ∘ ⇑(castDeg (V := HQ X 1) (K := ℚ) h) ∘
        ⇑(lefschetz ω (dim X.left - k) k) ∘ ⇑(hT.cupWedgeEquiv k).symm := by
    funext a
    simp only [Function.comp_apply, TorusCohomology.cupWedgeEquiv_apply]
    rw [cupWedgeMap_lefschetz μ ω hω k _ h, ← TorusCohomology.cupWedgeEquiv_apply hT k,
      LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (hT.cupWedgeEquiv m).bijective.comp ((castDeg h).bijective.comp
    ((lefschetz_bijective hη hT.finrank_eq hk).comp (hT.cupWedgeEquiv k).symm.bijective))

end Abelian

section Blocks

open HodgeBlocks

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- **The `Lpow` field of `HodgeBlocks.HardLefschetzFromDegreeTwo` from nondegeneracy.** For a
nondegenerate `ω ∈ ⋀² V` and `S.g = p₂ + 1` (so `2g - 2 = 2p₂`), the Hard Lefschetz isomorphism
`ω^(p₂ - 1) ∧ - : ⋀² V ≃ₗ[ℚ] ⋀^(2p₂) V` (`Lefschetz.lefschetzEquivOfEq` at `k = 2`).

It supplies exactly the field `Lpow` (the linear equivalence) of `HardLefschetzFromDegreeTwo`. It
does **not** supply `Lpow_isHodge` (that `Lpow` reflects and preserves Hodge classes, which needs
`Lpow` to be a morphism of Hodge structures and depends on how `S.cohomology` is tied to
`S.weight1`) or `Lpow_isAlgebraic` (that `Lpow` preserves `IsAlgebraic`, which needs `ω`
algebraic and the predicate closed under wedge). Those stay hypotheses of
`hardLefschetzFromDegreeTwoOfNondegenerate`.

Source: Huybrechts, *Complex Geometry*, §1.2 (Hard Lefschetz on the exterior algebra);
Voisin I, Ch. 6. -/
noncomputable def lpowOfNondegenerate (S : AbelianVarietyCohomology V) {ω : ⋀[ℚ]^2 V}
    (hω : IsNondegenerate ω) {p2 : ℕ} (hg : S.g = p2 + 1) (hp2 : 1 ≤ p2) :
    ⋀[ℚ]^2 V ≃ₗ[ℚ] ⋀[ℚ]^(2 * p2) V :=
  lefschetzEquivOfEq hω S.rank_eq (k := 2) (by omega) (by omega)

/-- `lpowOfNondegenerate` is `v ↦ ω^(p₂ - 1) ∧ v`. -/
theorem coe_lpowOfNondegenerate (S : AbelianVarietyCohomology V) {ω : ⋀[ℚ]^2 V}
    (hω : IsNondegenerate ω) {p2 : ℕ} (hg : S.g = p2 + 1) (hp2 : 1 ≤ p2) (v : ⋀[ℚ]^2 V) :
    (lpowOfNondegenerate S hω hg hp2 v : ExteriorAlgebra ℚ V) =
      (ω : ExteriorAlgebra ℚ V) ^ (p2 - 1) * v := by
  rw [lpowOfNondegenerate, coe_lefschetzEquivOfEq]
  congr 2
  omega

/-- For an abelian threefold (`g = 3`, `p₂ = 2`), `Lpow` is `ω ∧ - : ⋀² V ≃ ⋀⁴ V`. -/
example (S : AbelianVarietyCohomology V) {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω)
    (hg : S.g = 2 + 1) (v : ⋀[ℚ]^2 V) :
    (lpowOfNondegenerate S hω hg (by norm_num) v : ExteriorAlgebra ℚ V) = ω * v := by
  rw [coe_lpowOfNondegenerate, show 2 - 1 = 1 from rfl, pow_one]

/-- The Blocks datum `HardLefschetzFromDegreeTwo` with `Lpow := lpowOfNondegenerate`. Nondegeneracy
of `ω` supplies the field `Lpow`; the caller supplies `Lpow_isHodge` and `Lpow_isAlgebraic` for
that map.

Source: the Blocks structure `HardLefschetzFromDegreeTwo` and its citation (Voisin, *Hodge Theory
and Complex Algebraic Geometry I*, Theorem 6.25); the map is `lefschetzEquiv` (Huybrechts,
*Complex Geometry*, §1.2).

Relation to the goal: HC no distance; AV milestone no distance; the bijectivity content of
`HardLefschetzFromDegreeTwo` is replaced by nondegeneracy of `ω`. -/
noncomputable def hardLefschetzFromDegreeTwoOfNondegenerate (S : AbelianVarietyCohomology V)
    (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop) {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω) {p2 : ℕ}
    (hg : S.g = p2 + 1) (hp2 : 1 < p2)
    (hHodge : ∀ {v : ⋀[ℚ]^2 V}, IsHodgeClass (p := 1) (S.cohomology 2) v ↔
      IsHodgeClass (p := p2) (S.cohomology (2 * p2)) (lpowOfNondegenerate S hω hg hp2.le v))
    (hAlg : ∀ {v : ⋀[ℚ]^2 V}, IsAlgebraic v →
      IsAlgebraic (lpowOfNondegenerate S hω hg hp2.le v)) :
    HardLefschetzFromDegreeTwo S IsAlgebraic hg hp2 where
  Lpow := lpowOfNondegenerate S hω hg hp2.le
  Lpow_isHodge := hHodge
  Lpow_isAlgebraic := hAlg

/-- The `Lpow` field of `hardLefschetzFromDegreeTwoOfNondegenerate` is `lpowOfNondegenerate`. -/
example (S : AbelianVarietyCohomology V) (IsAlgebraic : ∀ {m : ℕ}, ⋀[ℚ]^m V → Prop)
    {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω) (hg : S.g = 2 + 1) (hHodge) (hAlg) :
    (hardLefschetzFromDegreeTwoOfNondegenerate S IsAlgebraic hω hg (by norm_num) hHodge
      hAlg).Lpow = lpowOfNondegenerate S hω hg (by norm_num) :=
  rfl

end Blocks

end HodgeLean.Adapters
