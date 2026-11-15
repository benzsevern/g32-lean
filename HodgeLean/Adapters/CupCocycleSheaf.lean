import HodgeLean.Adapters.CupCocycleSheafProofs

/-! # Left cup with a degree-one cocycle on the sheafified singular cochains: frozen specification

Stage hl2 of the `hL` track, singular side (`docs/specs/CupCocycleSheaf.md`). For a singular
`1`-cocycle `a` on a space `Y`, `HodgeLean.Adapters.CupCocycleSheafDefs` builds the morphism of
integer-indexed complexes of sheaves `C_a : S• ⟶ S•⟦1⟧` (`cupLeftSheafComplexHom`), given on an
open `U` by `c ↦ a|_U ∪ c` with the repository's Alexander–Whitney cup `cupCochain 1 n`. The
morphism, its naturality in `U` and its compatibility with the differentials are proved there.

Claimed:
* on presheaf sections, the sheafified `C_a` sends the germ of a cochain `c` on `U` to the germ of
  `a|_U ∪ c`;
* the sign: `C_a ≫ d = −(d ≫ C_a)` with the unshifted differential in every integer degree, that is
  `δ(a ∪ c) = −a ∪ δc`, which is Mathlib's sign on `S•⟦1⟧`;
* on global sections, `C_a` is the repository's left cup with `a` on singular cochains of `Y`,
  through upstream's map from raw cochains to global sections of the sheaf complex;
* on `X(ℂ)`, for any commutative ring `K` and any `X`: the action of `C_a` on hypercohomology
  `ℍ^k(S•) → ℍ^{1+k}(S•)`, read through `singularToSheafHypercohomology` (the first four legs of
  stage 3c's `singularToFieldCohomology`), is left cup with `[a]` on `H^k_sing(X(ℂ); K)`, with no
  scalar and no sign;
* sanity checks: `C_0 = 0`, `C_{a+b} = C_a + C_b`, and `C_{δb}` acts by `0` on hypercohomology;
* nonzero action (amendment after the statement review): if `singularToSheafHypercohomology` is
  injective in degree `1 + k` (an explicit binder) and `[a] ∪ y ≠ 0`, then `C_a` acts on the class
  of `y` by a nonzero class. This pins `C_a` against the zero morphism without relying on an open
  statement.

Not claimed: the transport of the hypercohomology statement to `HQ X k` or to `ℂ ⊗ HQ X k` along
`bettiDeRhamHQ` (it needs the normalization scalar of `spec_singularToFieldCohomology_cupComparison`,
which is open), the integration of a holomorphic `1`-form `θ` as a cocycle, the de Rham side
`L_θ : Ω• ⟶ Ω•⟦1⟧` (stage hl1), and the zig-zag of quasi-isomorphisms between `(Ω•, L_θ)` and
`(S•, C_a)`. No statement assumes `BettiDeRhamIso` or `HodgeDecomposition`, and none adds a
hypothesis. It is an implication from no geometric input: every statement holds for every space,
every `X` and every commutative ring `K`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Simplicial
open AlgebraicGeometry ComplexPoint
open AlgebraicTopology.Singular (singularCochainPresheaf OpenCochains singularCochainSheafComplex)

namespace HodgeLean.Adapters

/-- On sections over an open `U`, the sheafified left cup with `a` sends the germ of a singular
cochain `c ∈ C^n(U)` to the germ of `a|_U ∪ c`.
Source: Hatcher, *Algebraic Topology*, §3.2 (cup product); Bredon, *Sheaf Theory*, 2nd ed.,
GTM 170, I.5 (naturality of the sheafification unit; Mathlib's `toSheafify_naturality`). -/
theorem spec_cupLeftSheafHom_toSheafify {K : Type} [CommRing K] {Y : TopCat.{0}}
    (a : Cochain K (TopCat.toSSet.obj Y) 1) (n : ℕ) (U : (Opens Y)ᵒᵖ)
    (c : OpenCochains K Y U n) :
    ((TopCat.Sheaf.forget AddCommGrpCat Y).map (cupLeftSheafHom a n)).app U
        ((toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf K Y n)).app U c) =
      (toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf K Y (1 + n))).app U
        (HodgeLean.Foundations.Singular.cupCochain _ 1 n (cupLeftRestrict a U) c) :=
  spec_cupLeftSheafHom_toSheafify_aux a n U c

example {Y : TopCat.{0}} (a : Cochain ℂ (TopCat.toSSet.obj Y) 1) (c : OpenCochains ℂ Y
    (Opposite.op ⊤) 2) :
    ((TopCat.Sheaf.forget AddCommGrpCat Y).map (cupLeftSheafHom a 2)).app (Opposite.op ⊤)
        ((toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf ℂ Y 2)).app
          (Opposite.op ⊤) c) =
      (toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf ℂ Y (1 + 2))).app
        (Opposite.op ⊤)
        (HodgeLean.Foundations.Singular.cupCochain _ 1 2 (cupLeftRestrict a (Opposite.op ⊤)) c) :=
  spec_cupLeftSheafHom_toSheafify a 2 _ c

/-- The sign of `C_a` against the unshifted differential: in every integer degree `i`,
`C_a ≫ d = −(d ≫ C_a)`, the sheafified Leibniz rule `δ(a ∪ c) = −(a ∪ δc)` for `δa = 0`. With
Mathlib's convention `d_{S⟦1⟧} = −d_S` (`CochainComplex.shiftFunctor_obj_d'`) this is the statement
that `c ↦ a ∪ c`, with no sign, is a morphism `S• ⟶ S•⟦1⟧`.
Source: Hatcher, *Algebraic Topology*, §3.2, Lemma 3.6 (`δ(φ ∪ ψ) = δφ ∪ ψ + (−1)^p φ ∪ δψ`, here
with `p = 1`); Mathlib's `CochainComplex.shiftFunctor_obj_d'`. -/
theorem spec_cupLeftSheafComplexHom_comp_d {K : Type} [CommRing K] {Y : TopCat.{0}}
    (a : Cochain K (TopCat.toSSet.obj Y) 1) (ha : coboundary K 1 a = 0) (i : ℤ) :
    (cupLeftSheafComplexHom a ha).f i ≫
        ((singularCochainSheafComplex K Y).extend ComplexShape.embeddingUpNat).d (i + 1)
          (i + 1 + 1) =
      -(((singularCochainSheafComplex K Y).extend ComplexShape.embeddingUpNat).d i (i + 1) ≫
        (cupLeftSheafComplexHom a ha).f (i + 1)) :=
  spec_cupLeftSheafComplexHom_comp_d_aux a ha i

example {Y : TopCat.{0}} (a : Cochain ℂ (TopCat.toSSet.obj Y) 1) (ha : coboundary ℂ 1 a = 0) :
    (cupLeftSheafComplexHom a ha).f 0 ≫
        ((singularCochainSheafComplex ℂ Y).extend ComplexShape.embeddingUpNat).d (0 + 1)
          (0 + 1 + 1) =
      -(((singularCochainSheafComplex ℂ Y).extend ComplexShape.embeddingUpNat).d 0 (0 + 1) ≫
        (cupLeftSheafComplexHom a ha).f (0 + 1)) :=
  spec_cupLeftSheafComplexHom_comp_d a ha 0

/-- On global sections, `C_a` is the repository's left cup with `a`: for a singular `n`-cochain `c`
on `Y`, the global section of `S^n` represented by `c` (through upstream's
`topOpenToGlobalSingularCochainSheafComplex`, after identifying `Y` with its top open set) is sent
to the global section represented by `cupCochain Y 1 n a c`.
Source: Hatcher, *Algebraic Topology*, §3.2 (naturality of the cup product); Bredon, *Sheaf
Theory*, 2nd ed., GTM 170, I.5 (naturality of the sheafification unit); upstream's
`topOpenToGlobalSingularCochainSheafComplex` is the plus-plus unit followed by the natural
isomorphism `plusPlusFunctorIsoSheafification`. -/
theorem spec_cupLeftGlobalHom_topOpen {K : Type} [CommRing K] {Y : TopCat.{0}}
    (a : Cochain K (TopCat.toSSet.obj Y) 1) (n : ℕ) (c : Cochain K (TopCat.toSSet.obj Y) n) :
    cupLeftGlobalHom a n
        ((AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K Y).f n
          (cupLeftRestrict c (Opposite.op ⊤))) =
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K Y).f (1 + n)
        (cupLeftRestrict (HodgeLean.Foundations.Singular.cupCochain Y 1 n a c)
          (Opposite.op ⊤)) :=
  spec_cupLeftGlobalHom_topOpen_aux a n c

example {Y : TopCat.{0}} (a c : Cochain ℂ (TopCat.toSSet.obj Y) 1) :
    cupLeftGlobalHom a 1
        ((AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℂ Y).f 1
          (cupLeftRestrict c (Opposite.op ⊤))) =
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℂ Y).f (1 + 1)
        (cupLeftRestrict (HodgeLean.Foundations.Singular.cupCochain Y 1 1 a c)
          (Opposite.op ⊤)) :=
  spec_cupLeftGlobalHom_topOpen a 1 c

/-- On `X(ℂ)`, for every commutative ring `K`, the action of `C_a` on hypercohomology of the
`K`-singular-cochain resolution, `ℍ^k(S•) → ℍ^{1+k}(S•)`, is left cup with `[a]` on singular
cohomology, read through `singularToSheafHypercohomology` (raw cochains, global sections, the edge
map). There is no scalar and no sign: every identification used is sign-free (Mathlib's
`Cocycle.equivHomShift`, `shiftFunctor_map_f'` and `shiftFunctorAdd'_inv_app_f'`, upstream's
`fromSingleZeroIsoPreadditiveCoyoneda`).
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, II.4 and II.7 (the edge map from cohomology of
global sections to hypercohomology is natural, and the cup product of sheaf cohomology is computed
on a resolution by cochains); Hatcher, *Algebraic Topology*, §3.2; `spec_cupLeftGlobalHom_topOpen`. -/
theorem spec_cupLeftHypercohomology_singularToSheafHypercohomology (K : Type) [CommRing K]
    (X : Over (Spec ↧ℂ)) (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ))
    (y : AlgebraicTopology.Singular.Cohomology K (TopCat.of (ComplexPoint X)) k) :
    cupLeftHypercohomology X a h (singularToSheafHypercohomology X K k y) =
      singularToSheafHypercohomology X K (1 + k)
        (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint X)) rfl
          (HodgeLean.Foundations.Singular.cohomologyClass _ 1 a) y) :=
  spec_cupLeftHypercohomology_singularToSheafHypercohomology_aux K X a k h y

example (X : Over (Spec ↧ℂ)) (a : Cocycle ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (y : AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) 1) :
    cupLeftHypercohomology X a (by norm_num) (singularToSheafHypercohomology X ℂ 1 y) =
      singularToSheafHypercohomology X ℂ (1 + 1)
        (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint X)) rfl
          (HodgeLean.Foundations.Singular.cohomologyClass _ 1 a) y) :=
  spec_cupLeftHypercohomology_singularToSheafHypercohomology ℂ X a 1 _ y

/-- Left cup with the zero cochain is the zero morphism.
Source: Hatcher, *Algebraic Topology*, §3.2 (bilinearity of the cup product). -/
theorem spec_cupLeftSheafComplexHom_zero {K : Type} [CommRing K] {Y : TopCat.{0}}
    (h0 : coboundary K 1 (0 : Cochain K (TopCat.toSSet.obj Y) 1) = 0) :
    cupLeftSheafComplexHom (0 : Cochain K (TopCat.toSSet.obj Y) 1) h0 = 0 :=
  spec_cupLeftSheafComplexHom_zero_aux h0

example {Y : TopCat.{0}} :
    cupLeftSheafComplexHom (0 : Cochain ℚ (TopCat.toSSet.obj Y) 1) (map_zero _) = 0 :=
  spec_cupLeftSheafComplexHom_zero _

/-- Left cup with a cocycle is additive in the cocycle.
Source: Hatcher, *Algebraic Topology*, §3.2 (bilinearity of the cup product); additivity of
sheafification (Mathlib's `presheafToSheaf` is additive). -/
theorem spec_cupLeftSheafComplexHom_add {K : Type} [CommRing K] {Y : TopCat.{0}}
    (a b : Cochain K (TopCat.toSSet.obj Y) 1) (ha : coboundary K 1 a = 0)
    (hb : coboundary K 1 b = 0) (hab : coboundary K 1 (a + b) = 0) :
    cupLeftSheafComplexHom (a + b) hab =
      cupLeftSheafComplexHom a ha + cupLeftSheafComplexHom b hb :=
  spec_cupLeftSheafComplexHom_add_aux a b ha hb hab

example {Y : TopCat.{0}} (a : Cochain ℚ (TopCat.toSSet.obj Y) 1) (ha : coboundary ℚ 1 a = 0)
    (h2 : coboundary ℚ 1 (a + a) = 0) :
    cupLeftSheafComplexHom (a + a) h2 = cupLeftSheafComplexHom a ha + cupLeftSheafComplexHom a ha :=
  spec_cupLeftSheafComplexHom_add a a ha ha h2

/-- If `a = δb` for a singular `0`-cochain `b`, then `C_a` acts by `0` on hypercohomology: `C_{δb}`
is null-homotopic, with homotopy `−(b ∪ ·)`, because `δb ∪ c = δ(b ∪ c) − b ∪ δc`. So the action
depends only on the class `[a]`.
Source: Hatcher, *Algebraic Topology*, §3.2, Lemma 3.6 (with `p = 0`); Kashiwara–Schapira,
*Sheaves on Manifolds*, §1.7 (null-homotopic morphisms vanish in the derived category). -/
theorem spec_cupLeftHypercohomology_eq_zero_of_coboundary (K : Type) [CommRing K]
    (X : Over (Spec ↧ℂ)) (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (b : Cochain K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 0)
    (hab : a.1 = coboundary K 0 b) {n m : ℤ} (h : 1 + n = m)
    (α : Hypercohomology X (singularCochainSheafComplexInt X K) n) :
    cupLeftHypercohomology X a h α = 0 :=
  spec_cupLeftHypercohomology_eq_zero_of_coboundary_aux K X a b hab h α

example (X : Over (Spec ↧ℂ)) (a : Cocycle ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (b : Cochain ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 0)
    (hab : a.1 = coboundary ℂ 0 b)
    (α : Hypercohomology X (singularCochainSheafComplexInt X ℂ) 2) :
    cupLeftHypercohomology X a (n := 2) rfl α = 0 :=
  spec_cupLeftHypercohomology_eq_zero_of_coboundary ℂ X a b hab rfl α

/-- **Nonzero action.** If `singularToSheafHypercohomology X K (1 + k)` is injective and
`[a] ∪ y ≠ 0` in `H^{1+k}_sing(X(ℂ); K)`, then `ℍ(C_a)` sends the class of `y` to a nonzero class.
So `C_a` is not the zero morphism whenever the cup with `[a]` is nonzero, with the injectivity
(open in general: `spec_singularToFieldCohomology_bijective`) carried as an explicit binder.
Added after the statement review: statements 5–6 alone do not exclude `C_a = 0`.
Source: statement 4 (`spec_cupLeftHypercohomology_singularToSheafHypercohomology`). -/
theorem spec_cupLeftHypercohomology_ne_zero (K : Type) [CommRing K]
    (X : Over (Spec ↧ℂ)) (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ))
    (y : AlgebraicTopology.Singular.Cohomology K (TopCat.of (ComplexPoint X)) k)
    (hinj : Function.Injective (singularToSheafHypercohomology X K (1 + k)))
    (hne : HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint X)) rfl
      (HodgeLean.Foundations.Singular.cohomologyClass _ 1 a) y ≠ 0) :
    cupLeftHypercohomology X a h (singularToSheafHypercohomology X K k y) ≠ 0 :=
  spec_cupLeftHypercohomology_ne_zero_aux K X a k h y hinj hne

example (X : Over (Spec ↧ℂ)) (a : Cocycle ℚ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (y : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint X)) 1)
    (hinj : Function.Injective (singularToSheafHypercohomology X ℚ (1 + 1)))
    (hne : HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint X)) rfl
      (HodgeLean.Foundations.Singular.cohomologyClass _ 1 a) y ≠ 0) :
    cupLeftHypercohomology X a (n := 1) (m := ((1 + 1 : ℕ) : ℤ)) (by norm_num)
      (singularToSheafHypercohomology X ℚ 1 y) ≠ 0 :=
  spec_cupLeftHypercohomology_ne_zero ℚ X a 1 _ y hinj hne

end HodgeLean.Adapters
