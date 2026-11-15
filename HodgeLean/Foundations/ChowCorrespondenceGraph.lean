import HodgeLean.Adapters.ChowCorrespondenceDefs
import HodgeLean.Foundations.GeometricIntegralitySchemes

/-! # Scheme-theoretic intersections with graphs, for track A2

Helper results for the graph statements of `HodgeLean.Adapters.ChowCorrespondence`:
* ideal sheaves along a closed immersion `G`: an ideal `K ≥ ker G` is the pushforward of its
  pullback, so the scheme-theoretic intersection of the image of `G` with a closed subscheme is
  the image of the scheme-theoretic preimage;
* the fundamental cycle `a2g_fundCycle i` of a morphism `i : S ⟶ P` (the generic lengths of the
  irreducible components of `S`, placed at their images), which is the common shape of
  `ccm11_intersectionCycle` and `ccm3_flatPullbackPrime`, its value on integral schemes and its
  invariance under isomorphisms over `P`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace HodgeLean.Adapters

universe u

section IdealCorrespondence

open Scheme.IdealSheafData

/-- The pushforward of the reduced ideal of `closure {y}` along any morphism is the reduced ideal
of `closure {G y}`.
Source: Mathlib, `Scheme.IdealSheafData.map_vanishingIdeal`. -/
theorem a2g_map_primeIdeal {X P : Scheme.{u}} (G : X ⟶ P) (y : X) :
    (ccm3_primeIdeal X y).map G = ccm3_primeIdeal P (G y) := by
  unfold ccm3_primeIdeal
  rw [map_vanishingIdeal]
  congr 1
  ext1
  simp only [Closeds.coe_closure, Closeds.coe_mk]
  apply subset_antisymm
  · exact closure_minimal ((image_closure_subset_closure_image G.continuous).trans
      (by rw [Set.image_singleton])) isClosed_closure
  · exact closure_mono (Set.singleton_subset_iff.mpr ⟨y, subset_closure rfl, rfl⟩)

/-- On an integral scheme the reduced ideal of the closure of the generic point is `⊥`.
Source: Mathlib, `vanishingIdeal_top` and `Scheme.nilradical_eq_bot`. -/
theorem a2g_primeIdeal_genericPoint_eq_bot (X : Scheme.{u}) [IsIntegral X] :
    ccm3_primeIdeal X (genericPoint X) = ⊥ := by
  unfold ccm3_primeIdeal
  have : (⟨closure ({genericPoint X} : Set X), isClosed_closure⟩ : Closeds X) = ⊤ := by
    ext1; exact (genericPoint_spec X).def
  rw [this, vanishingIdeal_top, Scheme.nilradical_eq_bot]

/-- The kernel of a morphism out of an integral scheme is the reduced ideal of the closure of the
image of the generic point.
Source: Mathlib, `Scheme.IdealSheafData.map_bot` and `map_vanishingIdeal`. -/
theorem a2g_ker_eq_primeIdeal {X P : Scheme.{u}} [IsIntegral X] (G : X ⟶ P) :
    G.ker = ccm3_primeIdeal P (G (genericPoint X)) := by
  rw [← map_bot, ← a2g_primeIdeal_genericPoint_eq_bot, a2g_map_primeIdeal]

/-- The pullback of the kernel of `G` along `G` is `⊥`.
Source: Mathlib, `Scheme.IdealSheafData.le_map_iff_comap_le`. -/
theorem a2g_comap_ker_self {X P : Scheme.{u}} (G : X ⟶ P) : G.ker.comap G = ⊥ :=
  le_bot_iff.mp (le_map_iff_comap_le.mp (by rw [map_bot]))

/-- For a closed immersion `G` and an ideal `K` containing `ker G`, `K` is the pushforward of its
pullback: the ideals of `P` containing `ker G` correspond to the ideals of `X`.
Source: Mathlib, `IsClosedImmersion.lift` and the Galois connection
`Scheme.IdealSheafData.map_gc`; Hartshorne, *Algebraic Geometry*, II, Exercise 3.11 (b). -/
theorem a2g_map_comap_of_ker_le {X P : Scheme.{u}} (G : X ⟶ P) [IsClosedImmersion G]
    (K : P.IdealSheafData) (hK : G.ker ≤ K) : (K.comap G).map G = K := by
  refine le_antisymm ?_ (le_map_comap _ _)
  let h : K.subscheme ⟶ X := IsClosedImmersion.lift G K.subschemeι (by rwa [ker_subschemeι])
  have hh : h ≫ G = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have h1 : K.comap G ≤ h.ker := by
    rw [← map_bot, le_map_iff_comap_le, ← comap_comp, hh, ← le_map_iff_comap_le, map_bot,
      ker_subschemeι]
  calc (K.comap G).map G ≤ h.ker.map G := map_mono G h1
    _ = K := by rw [← Scheme.Hom.ker_comp, hh, ker_subschemeι]

/-- The intersection of the image of a closed immersion `G` with a closed subscheme `K` is the
image of the preimage of `K`: `ker G ⊔ K = (K.comap G).map G`.
Source: `a2g_map_comap_of_ker_le`; Hartshorne, *Algebraic Geometry*, II, Exercise 3.11 (b). -/
theorem a2g_ker_sup_eq_map_comap {X P : Scheme.{u}} (G : X ⟶ P) [IsClosedImmersion G]
    (K : P.IdealSheafData) : G.ker ⊔ K = (K.comap G).map G := by
  rw [← a2g_map_comap_of_ker_le G (G.ker ⊔ K) le_sup_left, comap_sup, a2g_comap_ker_self, bot_sup_eq]

/-- An ideal whose closed subscheme is reduced is the vanishing ideal of its support.
Source: Mathlib, `Scheme.IdealSheafData.ker_subschemeι`, `map_vanishingIdeal`. -/
theorem a2g_eq_vanishingIdeal_of_isReduced {P : Scheme.{u}} (I : P.IdealSheafData)
    [IsReduced I.subscheme] : I = vanishingIdeal I.support := by
  conv_lhs => rw [← ker_subschemeι I, ← map_bot, ← Scheme.nilradical_eq_bot, ← vanishingIdeal_top,
    map_vanishingIdeal]
  congr 1
  ext1
  simp only [Closeds.coe_closure, Closeds.coe_top, Set.image_univ, range_subschemeι]
  exact I.support.isClosed.closure_eq

end IdealCorrespondence

/-- The fundamental cycle of a morphism `i : S ⟶ P`: each irreducible component of `S`
contributes the length of the local ring of `S` at its generic point, placed at the image of that
generic point. For a closed immersion it is the cycle `[S]` of the closed subscheme.
Source: Fulton, *Intersection Theory*, second edition, §1.5, the cycle `[X]` of a scheme. -/
def a2g_fundCycle {S P : Scheme.{u}} (i : S ⟶ P) : AlgebraicCycle P ℚ := by
  classical
  exact ∑ᶠ y : S,
    if closure ({y} : Set S) ∈ irreducibleComponents S then
      Function.locallyFinsuppWithin.single (i y)
        ((Module.length (S.presheaf.stalk y) (S.presheaf.stalk y)).toNat : ℚ)
    else 0

example (P : Scheme.{0}) [IsNoetherian P] (I J : P.IdealSheafData) :
    ccm11_intersectionCycle P I J = a2g_fundCycle (I ⊔ J).subschemeι := rfl

example {X Z : Scheme.{0}} (f : X ⟶ Z) (x : Z) :
    ccm3_flatPullbackPrime f x = a2g_fundCycle (ccm3_inverseIdeal f x).subschemeι := rfl

/-- The length of a commutative ring over itself is invariant under ring isomorphisms.
Source: Mathlib, `LinearEquiv.length_eq` and `Module.length_eq_of_surjective`. -/
theorem a2g_length_self_eq {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Module.length A A = Module.length B B := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  have e' : A ≃ₗ[A] B :=
    { e.toAddEquiv with
      map_smul' := fun a x => by
        change e (a * x) = e a * e x
        exact map_mul e a x }
  rw [e'.length_eq]
  exact Module.length_eq_of_surjective (R := B) (M := B) e.surjective

theorem a2g_closure_mem_irreducibleComponents_of_homeo {S S' : Type*} [TopologicalSpace S]
    [TopologicalSpace S'] (h : S ≃ₜ S') (y : S)
    (hy : closure ({h y} : Set S') ∈ irreducibleComponents S') :
    closure ({y} : Set S) ∈ irreducibleComponents S := by
  have := preimage_mem_irreducibleComponents hy h.isOpenEmbedding
    ⟨h y, subset_closure rfl, y, rfl⟩
  have hs : h ⁻¹' {h y} = {y} := by ext z; simp [h.injective.eq_iff]
  rwa [h.preimage_closure, hs] at this

/-- Under a homeomorphism, `closure {y}` is an irreducible component exactly when
`closure {h y}` is.
Source: Mathlib, `preimage_mem_irreducibleComponents`. -/
theorem a2g_closure_mem_irreducibleComponents_iff {S S' : Type*} [TopologicalSpace S]
    [TopologicalSpace S'] (h : S ≃ₜ S') (y : S) :
    closure ({h y} : Set S') ∈ irreducibleComponents S' ↔
      closure ({y} : Set S) ∈ irreducibleComponents S := by
  refine ⟨a2g_closure_mem_irreducibleComponents_of_homeo h y, fun hy => ?_⟩
  exact a2g_closure_mem_irreducibleComponents_of_homeo h.symm (h y)
    (by rwa [Homeomorph.symm_apply_apply])

/-- The fundamental cycle is invariant under an isomorphism over the target.
Source: `a2g_closure_mem_irreducibleComponents_iff` and `a2g_length_self_eq`. -/
theorem a2g_fundCycle_iso {S S' P : Scheme.{u}} (e : S ≅ S') (i : S ⟶ P) (i' : S' ⟶ P)
    (h : i = e.hom ≫ i') : a2g_fundCycle i = a2g_fundCycle i' := by
  classical
  unfold a2g_fundCycle
  rw [← finsum_comp_equiv e.hom.homeomorph.toEquiv]
  refine finsum_congr fun y => ?_
  have hc := a2g_closure_mem_irreducibleComponents_iff e.hom.homeomorph y
  split_ifs with h1 h2 h2
  · change Function.locallyFinsuppWithin.single (i y) _ =
      Function.locallyFinsuppWithin.single (i' (e.hom y)) _
    rw [h, Scheme.Hom.comp_apply]
    congr 3
    have : IsIso (e.hom.stalkMap y) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 y
    exact (a2g_length_self_eq (asIso (e.hom.stalkMap y)).commRingCatIsoToRingEquiv).symm
  · exact (h2 (hc.mpr h1)).elim
  · exact (h1 (hc.mp h2)).elim
  · rfl

/-- The fundamental cycle of a morphism out of an integral scheme is the image of its generic point
with multiplicity one.
Source: Mathlib, `isField_stalk_of_closure_mem_irreducibleComponents` and
`Module.length_eq_one`; Fulton, *Intersection Theory*, second edition, §1.5. -/
theorem a2g_fundCycle_of_isIntegral {S P : Scheme.{u}} [IsIntegral S] (i : S ⟶ P) :
    a2g_fundCycle i = by
      classical exact Function.locallyFinsuppWithin.single (i (genericPoint S)) 1 := by
  classical
  unfold a2g_fundCycle
  have hη : closure ({genericPoint S} : Set S) ∈ irreducibleComponents S := by
    rw [(genericPoint_spec S).def, irreducibleComponents_eq_singleton]
    rfl
  rw [finsum_eq_single _ (genericPoint S)]
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hη)]
    have hfield := isField_stalk_of_closure_mem_irreducibleComponents S (genericPoint S) hη
    let _ := hfield.toField
    rw [Module.length_eq_one]
    rfl
  · intro y hy
    refine ite_eq_right_of_eq_false _ _ (eq_false fun hc => ?_)
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hc
    exact hy ((genericPoint_spec S).eq hc).symm

/-- The fundamental cycle of the image of a closed immersion is its fundamental cycle.
Source: Mathlib, `IsClosedImmersion` (the map to the image is an isomorphism) and
`Scheme.Hom.toImage_imageι`. -/
theorem a2g_fundCycle_ker {S P : Scheme.{u}} (i : S ⟶ P) [IsClosedImmersion i] :
    a2g_fundCycle i.ker.subschemeι = a2g_fundCycle i :=
  (a2g_fundCycle_iso (asIso i.toImage) i i.ker.subschemeι i.toImage_imageι.symm).symm

/-- The pushforward of an ideal along a closed immersion `G` has the fundamental cycle of the
composite `J.subschemeι ≫ G`.
Source: `a2g_fundCycle_ker`. -/
theorem a2g_fundCycle_map {X P : Scheme.{u}} (G : X ⟶ P) [IsClosedImmersion G]
    (J : X.IdealSheafData) :
    a2g_fundCycle (J.map G).subschemeι = a2g_fundCycle (J.subschemeι ≫ G) :=
  a2g_fundCycle_ker (J.subschemeι ≫ G)

/-- On a Noetherian space only finitely many points are generic points of irreducible
components.
Source: Mathlib, `NoetherianSpace.finite_irreducibleComponents`; schemes are `T0`. -/
theorem a2g_finite_genericPoints (S : Scheme.{u}) [NoetherianSpace S] :
    {y : S | closure ({y} : Set S) ∈ irreducibleComponents S}.Finite := by
  refine (NoetherianSpace.finite_irreducibleComponents (α := S)).preimage ?_
  intro y _ z _ h
  exact (inseparable_iff_closure_eq.mpr h).eq

/-- Pushforward of a fundamental cycle along `q`, when `q` has degree one at the images of the
generic points of the components.
Source: A1, `a1p_pushforward_single` and `a1p_pushforward_add` (through `a2_pushforwardHom`). -/
theorem a2g_pushforward_fundCycle {S P Q : Scheme.{u}} [NoetherianSpace S] (i : S ⟶ P)
    (q : P ⟶ Q) [QuasiCompact q]
    (hdeg : ∀ y : S, closure ({y} : Set S) ∈ irreducibleComponents S →
      a1p_degree q (i y) = 1) :
    a1p_pushforward q (a2g_fundCycle i) = a2g_fundCycle (i ≫ q) := by
  classical
  unfold a2g_fundCycle
  have hfin : (Function.support fun y : S =>
      if closure ({y} : Set S) ∈ irreducibleComponents S then
        Function.locallyFinsuppWithin.single (i y)
          ((Module.length (S.presheaf.stalk y) (S.presheaf.stalk y)).toNat : ℚ)
      else 0).Finite := by
    refine (a2g_finite_genericPoints S).subset fun y hy => ?_
    by_contra h
    exact hy (ite_eq_right_of_eq_false _ _ (eq_false h))
  change a2_pushforwardHom q ℚ _ = _
  rw [map_finsum _ hfin]
  refine finsum_congr fun y => ?_
  split_ifs with hy
  · change a1p_pushforward q _ = _
    rw [a1p_pushforward_single, hdeg y hy, Nat.cast_one, mul_one, Scheme.Hom.comp_apply]
  · exact map_zero _

/-- The scheme-theoretic preimage of an integral closed subscheme `I` of `B`, along a base change
`p` of an integral `C` of finite type over `ℂ`, is integral: it is `I ×_ℂ C`.
Source: `isIntegral_pullback_of_isAlgClosed` (Stacks Project, Tag 05P3); Mathlib,
`Scheme.IdealSheafData.comapIso` and `IsPullback.paste_horiz`. -/
theorem a2g_isIntegral_comap {P B C : Scheme.{0}} {p : P ⟶ B} {q : P ⟶ C}
    {b : B ⟶ Spec (.of ℂ)} {c : C ⟶ Spec (.of ℂ)} (h : IsPullback p q b c) [IsIntegral C]
    [LocallyOfFiniteType c] (I : B.IdealSheafData) [IsIntegral I.subscheme]
    [LocallyOfFiniteType (I.subschemeι ≫ b)] : IsIntegral (I.comap p).subscheme := by
  have t := ((IsPullback.of_hasPullback p I.subschemeι).paste_horiz h.flip).flip
  have := HodgeLean.Foundations.isIntegral_pullback_of_isAlgClosed ℂ I.subscheme C (I.subschemeι ≫ b) c
  exact IsIntegral.of_isIso ((I.comapIso p) ≪≫ t.isoPullback).inv

/-- Pushforward along equal morphisms, with independent quasi-compactness instances.
Source: A1, `a1p_pushforward`. -/
theorem a2g_pushforward_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) [QuasiCompact f]
    [QuasiCompact g] {R : Type*} [Semiring R] (c : AlgebraicCycle X R) :
    a1p_pushforward f c = a1p_pushforward g c := by
  subst h; rfl

/-- Evaluation of a cycle at a point, as an additive map.
Source: Mathlib, `Function.locallyFinsuppWithin` (pointwise addition). -/
def a2g_evalHom (X : Scheme.{u}) (p : X) : AlgebraicCycle X ℚ →+ ℚ where
  toFun c := c p
  map_zero' := rfl
  map_add' _ _ := rfl

example (X : Scheme.{u}) (p : X) (c : AlgebraicCycle X ℚ) : a2g_evalHom X p c = c p := rfl

/-- A finitely supported sum of cycles is evaluated pointwise.
Source: Mathlib, `map_finsum`. -/
theorem a2g_finsum_apply {X : Scheme.{u}} {ι : Type*} (F : ι → AlgebraicCycle X ℚ)
    (h : (Function.support F).Finite) (p : X) : (∑ᶠ i, F i) p = ∑ᶠ i, F i p :=
  map_finsum (a2g_evalHom X p) h

/-- A cycle with finite support is the sum of its prime cycles.
Source: Mathlib, `finsum_eq_single`. -/
theorem a2g_eq_finsum_single {X : Scheme.{u}} [DecidableEq X] (c : AlgebraicCycle X ℚ)
    (hc : (Function.support c).Finite) :
    c = ∑ᶠ x, Function.locallyFinsuppWithin.single x (c x) := by
  have hfin : (Function.support fun x => Function.locallyFinsuppWithin.single x (c x)).Finite :=
    hc.subset fun x hx h => hx (by simp only [h, Function.locallyFinsuppWithin.single_zero])
  ext p
  rw [a2g_finsum_apply _ hfin, finsum_eq_single _ p]
  · simp
  · intro x hx
    simp [Ne.symm hx]

/-- The pushforward of a finitely supported cycle, prime by prime.
Source: A1, `a1p_pushforward_single`; Mathlib, `map_finsum`. -/
theorem a2g_pushforward_eq_finsum {X Y : Scheme.{u}} [DecidableEq X] [DecidableEq Y]
    (f : X ⟶ Y) [QuasiCompact f] (c : AlgebraicCycle X ℚ) (hc : (Function.support c).Finite) :
    a1p_pushforward f c =
      ∑ᶠ x, Function.locallyFinsuppWithin.single (f x) (c x * (a1p_degree f x : ℚ)) := by
  have hfin : (Function.support fun x => Function.locallyFinsuppWithin.single x (c x)).Finite :=
    hc.subset fun x hx h => hx (by simp only [h, Function.locallyFinsuppWithin.single_zero])
  conv_lhs => rw [a2g_eq_finsum_single c hc]
  change a2_pushforwardHom f ℚ _ = _
  rw [map_finsum _ hfin]
  exact finsum_congr fun x => a1p_pushforward_single f x (c x)

/-- The degree of `G` at `x` is `1` when `G` has a left inverse.
Source: A1, `a1p_degree_comp`; Mathlib, `Scheme.Hom.residueDegree_id`. -/
theorem a2g_degree_eq_one_of_retraction {X P : Scheme.{u}} (G : X ⟶ P) (r : P ⟶ X)
    (h : G ≫ r = 𝟙 X) (x : X) : a1p_degree G x = 1 ∧ a1p_degree r (G x) = 1 := by
  have := a1p_degree_comp G r x
  rw [h] at this
  have h1 : a1p_degree (𝟙 X) x = 1 := Scheme.Hom.residueDegree_id x
  rw [h1] at this
  exact ⟨(mul_eq_one.mp this.symm).2, (mul_eq_one.mp this.symm).1⟩

/-- For a closed subscheme that is integral, the closure of the image of its generic point is its
support.
Source: Mathlib, `IsClosedEmbedding.closure_image_eq` and
`Scheme.IdealSheafData.range_subschemeι`. -/
theorem a2g_closure_genericPoint {P : Scheme.{u}} (I : P.IdealSheafData)
    [IsIntegral I.subscheme] :
    closure ({I.subschemeι (genericPoint I.subscheme)} : Set P) = I.support := by
  rw [← Set.image_singleton, I.subschemeι.isClosedEmbedding.closure_image_eq,
    (genericPoint_spec I.subscheme).def, Set.image_univ, Scheme.IdealSheafData.range_subschemeι]

/-- An integral closed subscheme is the reduced subscheme on the closure of the image of its
generic point.
Source: `a2g_eq_vanishingIdeal_of_isReduced` and `a2g_closure_genericPoint`. -/
theorem a2g_eq_primeIdeal {P : Scheme.{u}} (I : P.IdealSheafData) [IsIntegral I.subscheme] :
    I = ccm3_primeIdeal P (I.subschemeι (genericPoint I.subscheme)) := by
  conv_lhs => rw [a2g_eq_vanishingIdeal_of_isReduced I]
  unfold ccm3_primeIdeal
  congr 1
  ext1
  exact (a2g_closure_genericPoint I).symm

/-- If the support of an integral closed subscheme is `closure {z}`, its generic point maps
to `z`.
Source: `a2g_closure_genericPoint`; schemes are `T0`. -/
theorem a2g_genericPoint_eq {P : Scheme.{u}} (I : P.IdealSheafData) [IsIntegral I.subscheme]
    (z : P) (hz : (I.support : Set P) = closure {z}) :
    I.subschemeι (genericPoint I.subscheme) = z := by
  rw [← a2g_closure_genericPoint] at hz
  exact (inseparable_iff_closure_eq.mpr hz).eq

/-- The generic point of the reduced subscheme on `closure {z}` maps to `z`. -/
theorem a2g_primeIdeal_genericPoint {P : Scheme.{u}} (z : P)
    [IsIntegral (ccm3_primeIdeal P z).subscheme] :
    (ccm3_primeIdeal P z).subschemeι (genericPoint _) = z := by
  refine a2g_genericPoint_eq _ z ?_
  unfold ccm3_primeIdeal
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The support of the scheme-theoretic inverse image of `closure {w}` is `p⁻¹ (closure {w})`.
Source: Mathlib, `Scheme.IdealSheafData.support_comap`. -/
theorem a2g_support_inverseIdeal {P B : Scheme.{u}} (p : P ⟶ B) (w : B) :
    ((ccm3_inverseIdeal p w).support : Set P) = p ⁻¹' closure {w} := by
  unfold ccm3_inverseIdeal ccm3_primeIdeal
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The generic point of an integral scheme-theoretic inverse image `p⁻¹ (closure {w})`.
Source: Mathlib, `genericPoint`; Fulton, *Intersection Theory*, second edition, §1.7. -/
def a2g_genPt {P B : Scheme.{u}} (p : P ⟶ B) (w : B)
    [IsIntegral (ccm3_inverseIdeal p w).subscheme] : P :=
  (ccm3_inverseIdeal p w).subschemeι (genericPoint _)

example {P : Scheme.{u}} (w : P) [IsIntegral (ccm3_inverseIdeal (𝟙 P) w).subscheme] :
    a2g_genPt (𝟙 P) w = (ccm3_inverseIdeal (𝟙 P) w).subschemeι (genericPoint _) := rfl

/-- For a surjective `p`, the generic point of an integral `p⁻¹ (closure {w})` lies over `w`.
Source: Mathlib, `Specializes.map`; schemes are `T0`. -/
theorem a2g_genPt_spec {P B : Scheme.{u}} (p : P ⟶ B) (hp : Function.Surjective p) (w : B)
    [IsIntegral (ccm3_inverseIdeal p w).subscheme] : p (a2g_genPt p w) = w := by
  have hcl := a2g_closure_genericPoint (ccm3_inverseIdeal p w)
  rw [a2g_support_inverseIdeal] at hcl
  change closure {a2g_genPt p w} = _ at hcl
  have h1 : p (a2g_genPt p w) ∈ closure ({w} : Set B) := by
    have : a2g_genPt p w ∈ p ⁻¹' closure {w} := hcl ▸ subset_closure rfl
    exact this
  obtain ⟨v, hv⟩ := hp w
  have h2 : a2g_genPt p w ⤳ v := by
    rw [specializes_iff_mem_closure, hcl]
    change p v ∈ closure {w}
    rw [hv]; exact subset_closure rfl
  have h3 : p (a2g_genPt p w) ⤳ w := hv ▸ h2.map p.continuous
  exact (h3.antisymm (specializes_iff_mem_closure.mpr h1)).eq

/-- The flat pullback along `p` when every scheme-theoretic inverse image of a prime is
integral: each prime goes to the generic point of its inverse image with multiplicity one.
Source: `a2g_fundCycle_of_isIntegral`; Fulton, *Intersection Theory*, second edition, §1.7. -/
theorem a2g_flatPullback_eq {P B : Scheme.{u}} (p : P ⟶ B)
    [∀ w, IsIntegral (ccm3_inverseIdeal p w).subscheme] [DecidableEq P]
    (β : AlgebraicCycle B ℚ) :
    ccm3_flatPullback p β =
      ∑ᶠ w, Function.locallyFinsuppWithin.single (a2g_genPt p w) (β w) := by
  unfold ccm3_flatPullback
  refine finsum_congr fun w => ?_
  change (a2g_fundCycle (ccm3_inverseIdeal p w).subschemeι).mapRange _ _ = _
  rw [a2g_fundCycle_of_isIntegral]
  ext q
  simp only [Function.locallyFinsuppWithin.mapRange_apply,
    Function.locallyFinsuppWithin.single_apply]
  unfold a2g_genPt
  split_ifs <;> simp

/-- The reduced subscheme on `closure {z}` is integral (it is upstream's `cycleComponent`).
Source: upstream, `cycleComponent`. -/
instance a2g_primeIdeal_isIntegral {P : Scheme.{u}} (z : P) :
    IsIntegral (ccm3_primeIdeal P z).subscheme :=
  inferInstanceAs (IsIntegral (cycleComponent P z))

/-- The naive intersection of a prime cycle `[closure {γ}]` with a sum of primes at distinct
points `φ w` is the sum of the intersection cycles, with the coefficients `β w`.
Source: `a2_naiveIntersect`; Mathlib, `finsum_eq_single` and `finsum_mem_range`. -/
theorem a2g_naiveIntersect_single {Z : Scheme.{0}} [IsNoetherian Z] [DecidableEq Z] {B : Type*}
    (γ : Z) (φ : B → Z) (hφ : Function.Injective φ) (β : B → ℚ)
    (hβ : (Function.support β).Finite) :
    a2_naiveIntersect Z (Function.locallyFinsuppWithin.single γ 1)
        (∑ᶠ w, Function.locallyFinsuppWithin.single (φ w) (β w)) =
      ∑ᶠ w, (ccm11_intersectionCycle Z (ccm3_primeIdeal Z γ)
        (ccm3_primeIdeal Z (φ w))).mapRange (β w * ·) (mul_zero _) := by
  set d := ∑ᶠ w, Function.locallyFinsuppWithin.single (φ w) (β w) with hd
  have hfin : (Function.support fun w => Function.locallyFinsuppWithin.single (φ w) (β w)).Finite :=
    hβ.subset fun w hw h => hw (by simp only [h, Function.locallyFinsuppWithin.single_zero])
  have hdφ : ∀ w, d (φ w) = β w := by
    intro w
    rw [hd, a2g_finsum_apply _ hfin, finsum_eq_single _ w]
    · simp
    · intro w' hw'
      simp [hφ.ne (Ne.symm hw')]
  have hd0 : ∀ v, v ∉ Set.range φ → d v = 0 := by
    intro v hv
    rw [hd, a2g_finsum_apply _ hfin]
    refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
    have : v ≠ φ w := fun h => hv ⟨w, h.symm⟩
    simp [this]
  unfold a2_naiveIntersect
  rw [finsum_eq_single _ γ]
  · have hsupp : (Function.support fun v => (ccm11_intersectionCycle Z (ccm3_primeIdeal Z γ)
        (ccm3_primeIdeal Z v)).mapRange
          ((Function.locallyFinsuppWithin.single γ (1 : ℚ)) γ * d v * ·) (mul_zero _)) ⊆
        Set.range φ := by
      intro v hv
      by_contra h
      apply hv
      ext q
      simp [Function.locallyFinsuppWithin.mapRange_apply, hd0 v h]
    have key : ∀ F : Z → AlgebraicCycle Z ℚ, Function.support F ⊆ Set.range φ →
        ∑ᶠ v, F v = ∑ᶠ w, F (φ w) := fun F hF => by
      rw [← finsum_mem_range hφ, finsum_mem_def, Set.indicator_eq_self.mpr hF]
    rw [key _ hsupp]
    refine finsum_congr fun w => ?_
    ext q
    simp [Function.locallyFinsuppWithin.mapRange_apply, hdφ]
  · intro u hu
    refine finsum_eq_zero_of_forall_eq_zero fun v => ?_
    ext q
    simp [Function.locallyFinsuppWithin.mapRange_apply, hu]

/-- The naive intersection of two prime cycles is their intersection cycle.
Source: `a2_naiveIntersect`; Mathlib, `finsum_eq_single`. -/
theorem a2g_naiveIntersect_single_single {Z : Scheme.{0}} [IsNoetherian Z] [DecidableEq Z]
    (γ v : Z) :
    a2_naiveIntersect Z (Function.locallyFinsuppWithin.single γ 1)
        (Function.locallyFinsuppWithin.single v 1) =
      ccm11_intersectionCycle Z (ccm3_primeIdeal Z γ) (ccm3_primeIdeal Z v) := by
  unfold a2_naiveIntersect
  rw [finsum_eq_single _ γ, finsum_eq_single _ v]
  · ext q
    simp [Function.locallyFinsuppWithin.mapRange_apply]
  · intro v' hv'
    ext q
    simp [Function.locallyFinsuppWithin.mapRange_apply, hv']
  · intro u hu
    refine finsum_eq_zero_of_forall_eq_zero fun v' => ?_
    ext q
    simp [Function.locallyFinsuppWithin.mapRange_apply, hu]

/-- The flat pullback of a prime cycle whose inverse image is integral.
Source: `a2g_fundCycle_of_isIntegral`; Fulton, *Intersection Theory*, second edition, §1.7. -/
theorem a2g_flatPullback_single {P B : Scheme.{u}} [DecidableEq B] [DecidableEq P] (p : P ⟶ B)
    (w : B) [IsIntegral (ccm3_inverseIdeal p w).subscheme] :
    ccm3_flatPullback p (Function.locallyFinsuppWithin.single w 1) =
      Function.locallyFinsuppWithin.single (a2g_genPt p w) 1 := by
  unfold ccm3_flatPullback
  rw [finsum_eq_single _ w]
  · change (a2g_fundCycle (ccm3_inverseIdeal p w).subschemeι).mapRange _ _ = _
    rw [a2g_fundCycle_of_isIntegral]
    ext q
    simp only [Function.locallyFinsuppWithin.mapRange_apply,
      Function.locallyFinsuppWithin.single_apply]
    unfold a2g_genPt
    split_ifs <;> simp
  · intro w' hw'
    ext q
    simp [Function.locallyFinsuppWithin.mapRange_apply, hw']

/-- The intersection of the image of a closed immersion `G` with the scheme-theoretic inverse
image `p⁻¹ (closure {w})` has the fundamental cycle of `(G ≫ p)⁻¹ (closure {w})`, placed in `P`
through `G`.
Source: `a2g_ker_sup_eq_map_comap` and `a2g_fundCycle_map`; Hartshorne, *Algebraic Geometry*, II,
Exercise 3.11. -/
theorem a2g_intersectionCycle_ker {X P B : Scheme.{0}} [IsNoetherian P] (G : X ⟶ P)
    [IsClosedImmersion G] (p : P ⟶ B) (w : B) :
    ccm11_intersectionCycle P G.ker (ccm3_inverseIdeal p w) =
      a2g_fundCycle ((ccm3_inverseIdeal (G ≫ p) w).subschemeι ≫ G) := by
  change a2g_fundCycle (G.ker ⊔ _).subschemeι = _
  rw [a2g_ker_sup_eq_map_comap, a2g_fundCycle_map]
  unfold ccm3_inverseIdeal
  rw [Scheme.IdealSheafData.comap_comp]

/-! ## Graphs over `ℂ` -/

section Graph

open CartesianMonoidalCategory

variable {X Y : Over (Spec ↧ℂ)}

/-- The first projection `X ×_ℂ Y → X`, typed on `gagam_product`.
Source: Mathlib, `CartesianMonoidalCategory.fst`. -/
def a2g_fst (X Y : Over (Spec ↧ℂ)) : (gagam_product X Y).left ⟶ X.left := (fst X Y).left

/-- The second projection `X ×_ℂ Y → Y`, typed on `gagam_product`.
Source: Mathlib, `CartesianMonoidalCategory.snd`. -/
def a2g_snd (X Y : Over (Spec ↧ℂ)) : (gagam_product X Y).left ⟶ Y.left := (snd X Y).left

example (X Y : Over (Spec ↧ℂ)) : a2g_fst X Y = pullback.fst X.hom Y.hom := rfl
example (X Y : Over (Spec ↧ℂ)) : a2g_snd X Y = pullback.snd X.hom Y.hom := rfl

/-- The product square of `X ×_ℂ Y`.
Source: Mathlib, `IsPullback.of_hasPullback`. -/
theorem a2g_isPullback (X Y : Over (Spec ↧ℂ)) :
    IsPullback (a2g_fst X Y) (a2g_snd X Y) X.hom Y.hom :=
  IsPullback.of_hasPullback X.hom Y.hom

/-- The first projection is separated when `Y` is.
Source: Mathlib, `IsSeparated` is stable under base change. -/
instance a2g_fst_isSeparated [IsSeparated Y.hom] : IsSeparated (a2g_fst X Y) :=
  inferInstanceAs (IsSeparated (pullback.fst X.hom Y.hom))

/-- The second projection is quasi-compact when `X` is quasi-compact over `ℂ`.
Source: Mathlib, `QuasiCompact` is stable under base change. -/
instance a2g_snd_quasiCompact [QuasiCompact X.hom] : QuasiCompact (a2g_snd X Y) :=
  inferInstanceAs (QuasiCompact (pullback.snd X.hom Y.hom))

/-- The graph is a section of the first projection.
Source: Mathlib, `CartesianMonoidalCategory.lift_fst`. -/
theorem a2g_graph_fst (f : X ⟶ Y) : (a2_graph f).left ≫ a2g_fst X Y = 𝟙 X.left := by
  have h : a2_graph f ≫ (fst X Y : gagam_product X Y ⟶ X) = 𝟙 X := lift_fst _ _
  exact congrArg (fun g => Over.Hom.left g) h

/-- The graph followed by the second projection is the morphism.
Source: Mathlib, `CartesianMonoidalCategory.lift_snd`. -/
theorem a2g_graph_snd (f : X ⟶ Y) : (a2_graph f).left ≫ a2g_snd X Y = f.left := by
  have h : a2_graph f ≫ (snd X Y : gagam_product X Y ⟶ Y) = f := lift_snd _ _
  exact congrArg (fun g => Over.Hom.left g) h

/-- The graph of a morphism to a separated scheme is a closed immersion.
Source: Mathlib, `IsClosedImmersion.of_comp` (a section of a separated morphism); Hartshorne,
*Algebraic Geometry*, II, Exercise 4.8. -/
instance a2g_graph_isClosedImmersion [IsSeparated Y.hom] (f : X ⟶ Y) :
    IsClosedImmersion (a2_graph f).left := by
  have : IsClosedImmersion ((a2_graph f).left ≫ a2g_fst X Y) := by
    rw [a2g_graph_fst]; infer_instance
  exact IsClosedImmersion.of_comp _ (a2g_fst X Y)

/-- The first projection `X ×_ℂ Y → X` is surjective when `Y` is nonempty.
Source: Mathlib, `Scheme.Pullback.exists_preimage_pullback`. -/
theorem a2g_fst_surjective [Nonempty Y.left] : Function.Surjective (a2g_fst X Y) := by
  intro x
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := X.hom) (g := Y.hom)
    x (Classical.choice (inferInstance : Nonempty Y.left)) (Subsingleton.elim _ _)
  exact ⟨z, hz⟩

/-- The scheme-theoretic inverse image of a prime of `X` in `X ×_ℂ Y` is integral: it is
`closure {x} ×_ℂ Y`.
Source: `a2g_isIntegral_comap` (Stacks Project, Tag 05P3). -/
instance a2g_fst_inverseIdeal_isIntegral [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (x : X.left) :
    IsIntegral (ccm3_inverseIdeal (a2g_fst X Y) x).subscheme :=
  a2g_isIntegral_comap (a2g_isPullback X Y) (ccm3_primeIdeal X.left x)

/-- A cycle on a scheme quasi-compact over `ℂ` has finite support.
Source: Mathlib, `Function.locallyFinsupp.finite_support`. -/
theorem a2g_finite_support [QuasiCompact X.hom] (c : AlgebraicCycle X.left ℚ) :
    (Function.support c).Finite :=
  have := QuasiCompact.compactSpace_of_compactSpace X.hom
  Function.locallyFinsupp.finite_support c

/-- The naive intersection of the graph with the flat pullback of `α` along the first projection
is the image of `α` on the graph: `[Γ_f] ·ₙ p₁^* α = (id, f)_* α`.
Source: `a2g_flatPullback_eq`, `a2g_naiveIntersect_single` and `a2g_intersectionCycle_ker`;
Fulton, *Intersection Theory*, second edition, §16.1. -/
theorem a2g_naiveIntersect_graph [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsIntegral X.left] [IsIntegral Y.left]
    [IsSeparated Y.hom] (f : X ⟶ Y) (α : AlgebraicCycle X.left ℚ) :
    a2_naiveIntersect (gagam_product X Y).left (a2_graphCorr f)
        (ccm3_flatPullback (a2g_fst X Y) α) =
      a1p_pushforward (a2_graph f).left α := by
  classical
  have hs : Function.Surjective (a2g_fst X Y) := a2g_fst_surjective
  have hinj : Function.Injective fun x => a2g_genPt (a2g_fst X Y) x := fun a b h => by
    rw [← a2g_genPt_spec _ hs a, ← a2g_genPt_spec _ hs b]
    exact congrArg _ h
  rw [a2g_flatPullback_eq, a2g_pushforward_eq_finsum _ α (a2g_finite_support α)]
  unfold a2_graphCorr
  rw [a2g_naiveIntersect_single _ _ hinj _ (a2g_finite_support α),
    ← a2g_ker_eq_primeIdeal]
  refine finsum_congr fun x => ?_
  rw [a2g_genPt, ← a2g_eq_primeIdeal, a2g_intersectionCycle_ker, a2g_graph_fst]
  unfold ccm3_inverseIdeal
  rw [Scheme.IdealSheafData.comap_id, a2g_fundCycle_of_isIntegral, Scheme.Hom.comp_apply,
    a2g_primeIdeal_genericPoint,
    (a2g_degree_eq_one_of_retraction _ _ (a2g_graph_fst f) x).1]
  ext q
  simp [Function.locallyFinsuppWithin.mapRange_apply, Function.locallyFinsuppWithin.single_apply]

/-- A closed subscheme of a Noetherian scheme has a Noetherian underlying space.
Source: Mathlib, `LocallyOfFiniteType.isLocallyNoetherian` and
`QuasiCompact.compactSpace_of_compactSpace`. -/
theorem a2g_subscheme_noetherianSpace {P : Scheme.{u}} [IsNoetherian P]
    (I : P.IdealSheafData) : NoetherianSpace I.subscheme := by
  have := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  have := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  have : IsNoetherian I.subscheme := {}
  infer_instance

/-- The transposed graph `(f, id) : X → Y ×_ℂ X`.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 4.8 (the graph morphism), composed with the
swap. -/
def a2g_tgraph (f : X ⟶ Y) : X.left ⟶ (gagam_product Y X).left :=
  (a2_graph f).left ≫ (a2_swap X Y).left

example (f : X ⟶ Y) : a2g_tgraph f = (a2_graph f ≫ a2_swap X Y).left := rfl

/-- The transposed graph followed by the first projection is the morphism.
Source: Mathlib, `CartesianMonoidalCategory.lift_fst` and `lift_snd`. -/
theorem a2g_tgraph_fst (f : X ⟶ Y) : a2g_tgraph f ≫ a2g_fst Y X = f.left := by
  have h1 : a2_swap X Y ≫ (fst Y X : gagam_product Y X ⟶ Y) = snd X Y := lift_fst _ _
  have h : (a2_graph f ≫ a2_swap X Y) ≫ (fst Y X : gagam_product Y X ⟶ Y) = f :=
    (Category.assoc _ _ _).trans ((congrArg (a2_graph f ≫ ·) h1).trans (lift_snd _ _))
  exact congrArg (fun g => Over.Hom.left g) h

/-- The transposed graph is a section of the second projection.
Source: Mathlib, `CartesianMonoidalCategory.lift_fst` and `lift_snd`. -/
theorem a2g_tgraph_snd (f : X ⟶ Y) : a2g_tgraph f ≫ a2g_snd Y X = 𝟙 X.left := by
  have h1 : a2_swap X Y ≫ (snd Y X : gagam_product Y X ⟶ X) = fst X Y := lift_snd _ _
  have h : (a2_graph f ≫ a2_swap X Y) ≫ (snd Y X : gagam_product Y X ⟶ X) = 𝟙 X :=
    (Category.assoc _ _ _).trans ((congrArg (a2_graph f ≫ ·) h1).trans (lift_fst _ _))
  exact congrArg (fun g => Over.Hom.left g) h

/-- The transposed graph of a morphism to a separated scheme is a closed immersion.
Source: `a2g_graph_isClosedImmersion`; the swap is an isomorphism. -/
instance a2g_tgraph_isClosedImmersion [IsSeparated Y.hom] (f : X ⟶ Y) :
    IsClosedImmersion (a2g_tgraph f) := by
  unfold a2g_tgraph; infer_instance

/-- The transpose of a graph correspondence is the prime cycle of the transposed graph.
Source: A1, `a1p_pushforward_single`; the swap has degree one, being an isomorphism. -/
theorem a2g_transpose_graphCorr [IrreducibleSpace X.left] [DecidableEq (gagam_product Y X).left]
    (f : X ⟶ Y) :
    a2_transpose (a2_graphCorr f) =
      Function.locallyFinsuppWithin.single (a2g_tgraph f (genericPoint X.left)) 1 := by
  classical
  unfold a2_transpose a2_graphCorr
  rw [a1p_pushforward_single]
  have hs : (a2_swap X Y).left ≫ (a2_swap Y X).left = 𝟙 _ := by
    rw [← Over.comp_left, a2_swap_swap]; rfl
  rw [(a2g_degree_eq_one_of_retraction _ _ hs _).1]
  ext q
  simp [a2g_tgraph, Function.locallyFinsuppWithin.single_apply]

/-- The transposed graph acts as the inverse-image cycle:
`p₂_*([Γ_f]ᵗ ·ₙ p₁^* β) = ccm3_flatPullback f β`. The intersection of the transposed graph with
`p₁⁻¹ (closure {w})` is the image of `f⁻¹ (closure {w})`, and `p₂` maps it back isomorphically.
Source: `a2g_flatPullback_eq`, `a2g_naiveIntersect_single`, `a2g_intersectionCycle_ker` and
`a2g_pushforward_fundCycle`; Fulton, *Intersection Theory*, second edition, §16.1 and §1.7. -/
theorem a2g_naiveCorrAction_transpose_graph [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsIntegral X.left] [IsIntegral Y.left]
    [IsSeparated Y.hom] (f : X ⟶ Y) (β : AlgebraicCycle Y.left ℚ) :
    a1p_pushforward (a2g_snd Y X) (a2_naiveIntersect (gagam_product Y X).left
        (a2_transpose (a2_graphCorr f)) (ccm3_flatPullback (a2g_fst Y X) β)) =
      ccm3_flatPullback f.left β := by
  classical
  have hs : Function.Surjective (a2g_fst Y X) := a2g_fst_surjective
  have hinj : Function.Injective fun w => a2g_genPt (a2g_fst Y X) w := fun a b h => by
    rw [← a2g_genPt_spec _ hs a, ← a2g_genPt_spec _ hs b]
    exact congrArg _ h
  rw [a2g_transpose_graphCorr, a2g_flatPullback_eq,
    a2g_naiveIntersect_single _ _ hinj _ (a2g_finite_support β), ← a2g_ker_eq_primeIdeal]
  have hfin : (Function.support fun w => (ccm11_intersectionCycle (gagam_product Y X).left
      (a2g_tgraph f).ker (ccm3_primeIdeal _ (a2g_genPt (a2g_fst Y X) w))).mapRange
        (β w * ·) (mul_zero _)).Finite := by
    refine (a2g_finite_support β).subset fun w hw h => hw ?_
    ext q
    simp [Function.locallyFinsuppWithin.mapRange_apply, h]
  change a2_pushforwardHom (a2g_snd Y X) ℚ _ = _
  rw [map_finsum _ hfin]
  unfold ccm3_flatPullback
  refine finsum_congr fun w => ?_
  change a1p_pushforward _ _ = _
  rw [a1p_pushforward_mul]
  congr 1
  rw [a2g_genPt, ← a2g_eq_primeIdeal, a2g_intersectionCycle_ker, a2g_tgraph_fst]
  have := a2g_subscheme_noetherianSpace (ccm3_inverseIdeal f.left w)
  rw [a2g_pushforward_fundCycle, Category.assoc, a2g_tgraph_snd, Category.comp_id]
  · rfl
  · intro y _
    exact (a2g_degree_eq_one_of_retraction _ _ (a2g_tgraph_snd f) _).2

end Graph

/-- The kernel of a base change of a closed immersion is the pullback of its kernel.
Source: Mathlib, `Scheme.IdealSheafData.ker_fst_of_isClosedImmersion` and
`IsPullback.isoPullback_hom_fst`. -/
theorem a2g_ker_of_isPullback {W P X Y : Scheme.{u}} {a : W ⟶ P} {b : W ⟶ X} {p : P ⟶ Y}
    {i : X ⟶ Y} [IsClosedImmersion i] (h : IsPullback a b p i) : a.ker = i.ker.comap p := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

section Comp

open CartesianMonoidalCategory

variable {X Y Z : Over (Spec ↧ℂ)}

/-- `Γ_f × Z : X ×_ℂ Z → (X ×_ℂ Y) ×_ℂ Z`.
Source: Mathlib, `CartesianMonoidalCategory.lift`. -/
def a2g_graphProd (f : X ⟶ Y) (Z : Over (Spec ↧ℂ)) :
    gagam_product X Z ⟶ gagam_product (gagam_product X Y) Z :=
  lift (fst X Z ≫ a2_graph f) (snd X Z)

/-- `f × Z : X ×_ℂ Z → Y ×_ℂ Z`.
Source: Mathlib, `CartesianMonoidalCategory.lift`. -/
def a2g_prodMap (f : X ⟶ Y) (Z : Over (Spec ↧ℂ)) : gagam_product X Z ⟶ gagam_product Y Z :=
  lift (fst X Z ≫ f) (snd X Z)

example (f : X ⟶ Y) : a2g_graphProd f Z ≫ snd (gagam_product X Y) Z = snd X Z := lift_snd _ _
example (f : X ⟶ Y) : a2g_prodMap f Z ≫ snd Y Z = snd X Z := lift_snd _ _

theorem a2g_graphProd_fst (f : X ⟶ Y) :
    (a2g_graphProd f Z).left ≫ a2g_fst (gagam_product X Y) Z = a2g_fst X Z ≫ (a2_graph f).left :=
  congrArg (fun g => Over.Hom.left g) (lift_fst _ _ : a2g_graphProd f Z ≫
    (fst (gagam_product X Y) Z : gagam_product (gagam_product X Y) Z ⟶ _) = _)

theorem a2g_graphProd_snd (f : X ⟶ Y) :
    (a2g_graphProd f Z).left ≫ a2g_snd (gagam_product X Y) Z = a2g_snd X Z :=
  congrArg (fun g => Over.Hom.left g) (lift_snd _ _ : a2g_graphProd f Z ≫
    (snd (gagam_product X Y) Z : gagam_product (gagam_product X Y) Z ⟶ _) = _)

theorem a2g_graphProd_p13 (f : X ⟶ Y) :
    (a2g_graphProd f Z).left ≫ (a2_p13 X Y Z).left = 𝟙 _ := by
  have h : a2g_graphProd f Z ≫ a2_p13 X Y Z = 𝟙 _ := by
    unfold a2g_graphProd a2_p13 a2_graph gagam_product
    apply CartesianMonoidalCategory.hom_ext <;> simp
  exact congrArg (fun g => Over.Hom.left g) h

theorem a2g_graphProd_p23 (f : X ⟶ Y) :
    (a2g_graphProd f Z).left ≫ (a2_p23 X Y Z).left = (a2g_prodMap f Z).left := by
  have h : a2g_graphProd f Z ≫ a2_p23 X Y Z = a2g_prodMap f Z := by
    unfold a2g_graphProd a2_p23 a2_graph a2g_prodMap gagam_product
    apply CartesianMonoidalCategory.hom_ext <;> simp
  exact congrArg (fun g => Over.Hom.left g) h

theorem a2g_graph_prodMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    (a2_graph (f ≫ g)).left ≫ (a2g_prodMap f Z).left = f.left ≫ (a2_graph g).left := by
  have h : a2_graph (f ≫ g) ≫ a2g_prodMap f Z = f ≫ a2_graph g := by
    unfold a2_graph a2g_prodMap gagam_product
    apply CartesianMonoidalCategory.hom_ext <;> simp
  exact congrArg (fun g => Over.Hom.left g) h

theorem a2g_prodMap_fst (f : X ⟶ Y) :
    (a2g_prodMap f Z).left ≫ a2g_fst Y Z = a2g_fst X Z ≫ f.left :=
  congrArg (fun g => Over.Hom.left g) (lift_fst _ _ : a2g_prodMap f Z ≫
    (fst Y Z : gagam_product Y Z ⟶ _) = _)

theorem a2g_prodMap_snd (f : X ⟶ Y) :
    (a2g_prodMap f Z).left ≫ a2g_snd Y Z = a2g_snd X Z :=
  congrArg (fun g => Over.Hom.left g) (lift_snd _ _ : a2g_prodMap f Z ≫
    (snd Y Z : gagam_product Y Z ⟶ _) = _)

theorem a2g_p23_fst :
    (a2_p23 X Y Z).left ≫ a2g_fst Y Z = a2g_fst (gagam_product X Y) Z ≫ a2g_snd X Y :=
  congrArg (fun g => Over.Hom.left g) (lift_fst _ _ : a2_p23 X Y Z ≫
    (fst Y Z : gagam_product Y Z ⟶ _) = _)

theorem a2g_p23_snd :
    (a2_p23 X Y Z).left ≫ a2g_snd Y Z = a2g_snd (gagam_product X Y) Z :=
  congrArg (fun g => Over.Hom.left g) (lift_snd _ _ : a2_p23 X Y Z ≫
    (snd Y Z : gagam_product Y Z ⟶ _) = _)

/-- `X ×_ℂ Z` is the base change of `Γ_f` along `(X ×_ℂ Y) ×_ℂ Z → X ×_ℂ Y`.
Source: Mathlib, `IsPullback.of_right`. -/
theorem a2g_isPullback_graphProd (f : X ⟶ Y) :
    IsPullback (a2g_graphProd f Z).left (a2g_fst X Z) (a2g_fst (gagam_product X Y) Z)
      (a2_graph f).left := by
  refine IsPullback.of_right (h₁₂ := a2g_snd (gagam_product X Y) Z)
    (h₂₂ := (gagam_product X Y).hom) (v₁₃ := Z.hom) ?_ (a2g_graphProd_fst f)
    (a2g_isPullback (gagam_product X Y) Z).flip
  rw [a2g_graphProd_snd, Over.w]
  exact (a2g_isPullback X Z).flip

/-- `X ×_ℂ Z` is the base change of `f × Z` along `fst : Y ×_ℂ Z → Y`.
Source: Mathlib, `IsPullback.of_bot`. -/
theorem a2g_isPullback_prodMap (f : X ⟶ Y) :
    IsPullback (a2g_fst X Z) (a2g_prodMap f Z).left f.left (a2g_fst Y Z) := by
  refine IsPullback.of_bot (v₂₁ := a2g_snd Y Z) (v₂₂ := Y.hom) (h₃₁ := Z.hom) ?_
    (a2g_prodMap_fst f).symm (a2g_isPullback Y Z)
  rw [a2g_prodMap_snd, Over.w]
  exact a2g_isPullback X Z

/-- The graph of `f ≫ g` is the base change of the graph of `g` along `f × Z`.
Source: Mathlib, `IsPullback.of_right` and `IsPullback.id_horiz`. -/
theorem a2g_isPullback_graph_prodMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsPullback (a2_graph (f ≫ g)).left f.left (a2g_prodMap f Z).left (a2_graph g).left := by
  refine IsPullback.of_right (h₁₂ := a2g_fst X Z) (h₂₂ := a2g_fst Y Z) (v₁₃ := f.left) ?_
    (a2g_graph_prodMap f g) (a2g_isPullback_prodMap f)
  rw [a2g_graph_fst, a2g_graph_fst]
  exact IsPullback.id_horiz f.left

/-- `p₂₃ : (X ×_ℂ Y) ×_ℂ Z → Y ×_ℂ Z` is the base change of `X → Spec ℂ`.
Source: Mathlib, `IsPullback.of_right` and `IsPullback.paste_vert`. -/
theorem a2g_isPullback_p23 :
    IsPullback (a2_p23 X Y Z).left (a2g_fst (gagam_product X Y) Z ≫ a2g_fst X Y)
      (gagam_product Y Z).hom X.hom := by
  have T : IsPullback (a2_p23 X Y Z).left (a2g_fst (gagam_product X Y) Z) (a2g_fst Y Z)
      (a2g_snd X Y) := by
    refine IsPullback.of_right (h₁₂ := a2g_snd Y Z) (h₂₂ := Y.hom) (v₁₃ := Z.hom) ?_
      a2g_p23_fst (a2g_isPullback Y Z).flip
    rw [a2g_p23_snd, ← (a2g_isPullback X Y).w]
    exact (a2g_isPullback (gagam_product X Y) Z).flip
  exact T.paste_vert (a2g_isPullback X Y).flip

/-- Graph correspondences compose as their morphisms:
`p₁₃_*(p₁₂^*[Γ_f] ·ₙ p₂₃^*[Γ_g]) = [Γ_{f ≫ g}]`. The first pullback is the image of
`Γ_f × Z : X ×_ℂ Z → (X ×_ℂ Y) ×_ℂ Z`; its intersection with `p₂₃⁻¹ Γ_g` is the image of the
graph of `f ≫ g`, and `p₁₃` is a retraction of `Γ_f × Z`.
Source: `a2g_isPullback_graphProd`, `a2g_isPullback_graph_prodMap`, `a2g_isPullback_p23` and
`a2g_intersectionCycle_ker`; Fulton, *Intersection Theory*, second edition, §16.1. -/
theorem a2g_naiveCorrComp_graph [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsIntegral X.left] [IsIntegral Y.left] [IsIntegral Z.left]
    [IsSeparated Y.hom] [IsSeparated Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) :
    a1p_pushforward (a2_p13 X Y Z).left
        (a2_naiveIntersect (gagam_product (gagam_product X Y) Z).left
          (ccm3_flatPullback (a2g_fst (gagam_product X Y) Z) (a2_graphCorr f))
          (ccm3_flatPullback (a2_p23 X Y Z).left (a2_graphCorr g))) =
      a2_graphCorr (f ≫ g) := by
  classical
  have : IsIntegral (ccm3_inverseIdeal (a2_p23 X Y Z).left
      ((a2_graph g).left (genericPoint Y.left))).subscheme :=
    a2g_isIntegral_comap a2g_isPullback_p23 (ccm3_primeIdeal _ _)
  have : IsClosedImmersion (a2g_graphProd f Z).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (a2g_isPullback_graphProd f).flip inferInstance
  have hA : ccm3_inverseIdeal (a2g_fst (gagam_product X Y) Z)
      ((a2_graph f).left (genericPoint X.left)) = (a2g_graphProd f Z).left.ker := by
    unfold ccm3_inverseIdeal
    rw [← a2g_ker_eq_primeIdeal, a2g_ker_of_isPullback (a2g_isPullback_graphProd f)]
  have hB : ccm3_inverseIdeal (a2g_prodMap f Z).left
      ((a2_graph g).left (genericPoint Y.left)) = (a2_graph (f ≫ g)).left.ker := by
    unfold ccm3_inverseIdeal
    rw [← a2g_ker_eq_primeIdeal, a2g_ker_of_isPullback (a2g_isPullback_graph_prodMap f g)]
  unfold a2_graphCorr
  rw [a2g_flatPullback_single, a2g_flatPullback_single, a2g_naiveIntersect_single_single,
    a2g_genPt, a2g_genPt, ← a2g_eq_primeIdeal, ← a2g_eq_primeIdeal, hA,
    a2g_intersectionCycle_ker, a2g_graphProd_p23, hB, ← a2g_fundCycle_map,
    Scheme.IdealSheafData.map_ker, a2g_fundCycle_ker, a2g_fundCycle_of_isIntegral,
    a1p_pushforward_single, Scheme.Hom.comp_apply,
    (a2g_degree_eq_one_of_retraction _ _ (a2g_graphProd_p13 f) _).2,
    ← Scheme.Hom.comp_apply (a2g_graphProd f Z).left, a2g_graphProd_p13]
  simp

end Comp

end HodgeLean.Adapters