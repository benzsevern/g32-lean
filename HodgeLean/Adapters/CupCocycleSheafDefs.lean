import HodgeLean.Foundations.Singular.Cup
import HodgeLean.Foundations.ComplexSheafSingularDefs

/-! # Left cup with a degree-one cocycle on the sheafified singular cochains

For a singular `1`-cochain `a` on a space `Y` with `δa = 0`, this file builds the morphism of
complexes `C_a : S• ⟶ S•[1]` on the sheafified singular cochains, given on an open `U` by
`c ↦ a|_U ∪ c` (the repository's Alexander–Whitney cup `cupCochain 1 n`, with `a` on the left):

1. `cupLeftPresheafHom a n : C^n(-) ⟶ C^{1+n}(-)` on the presheaves of singular cochains, natural in
   the open set by naturality of the cup product;
2. `cupLeftPresheafHom_comm`: the Leibniz rule `δ(a ∪ c) = −a ∪ δc`, from `δa = 0`;
3. `cupLeftSheafHom a n`, its sheafification;
4. `cupLeftSheafComplexHom a ha : S• ⟶ S•⟦1⟧` on the integer-indexed complex. Mathlib's shift
   negates the differential (`CochainComplex.shiftFunctor_obj_d'`), so the Leibniz sign makes
   `c ↦ a ∪ c` itself, with no sign, a morphism into the shift;
5. on `X(ℂ)`: `cupLeftComplexHom X a` for a cocycle `a`, its action
   `cupLeftHypercohomology X a h : ℍ^n(S•) → ℍ^m(S•)` for `1 + n = m`, and
   `singularToSheafHypercohomology X K n : H^n_sing(X(ℂ); K) → ℍ^n(S•)`, the first four legs of
   stage 3c's `singularToFieldCohomology`.

Everything here is a definition or a lemma with a complete proof. HC no distance; AV milestone no
distance.
-/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Simplicial
open AlgebraicTopology.Singular (singularCochainPresheaf OpenCochains singularCochainCoboundary
  singularCochainSheaf singularCochainSheafCoboundary singularCochainSheafComplex)
open scoped Simplicial

namespace HodgeLean.Adapters

variable {K : Type} [CommRing K] {Y : TopCat.{0}}

/-- Two simplicial cochains with the same values on simplices are equal. -/
theorem cupLeft_cochain_ext {Z : SSet.{0}} {n : ℕ} (φ ψ : Cochain K Z n)
    (h : ∀ σ : Z _⦋n⦌, φ (chainOfSimplex K σ) = ψ (chainOfSimplex K σ)) : φ = ψ := by
  have hc : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
    have hi : (Z.ιChainComplex (R := ModuleCat.of K K) σ).hom c =
        c • chainOfSimplex K σ := by
      rw [chainOfSimplex, ← map_smul]
      simp
    change φ ((Z.ιChainComplex (R := ModuleCat.of K K) σ).hom c) =
      ψ ((Z.ιChainComplex (R := ModuleCat.of K K) σ).hom c)
    rw [hi, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom hc

/-- Pulling back cochains along two composable maps is pulling back along the composite. -/
theorem cupLeft_cochainMap_comp {Z₁ Z₂ Z₃ : SSet.{0}} (f : Z₁ ⟶ Z₂) (g : Z₂ ⟶ Z₃) (n : ℕ)
    (φ : Cochain K Z₃ n) :
    cochainMap K f n (cochainMap K g n φ) = cochainMap K (f ≫ g) n φ :=
  cupLeft_cochain_ext _ _ fun σ => by
    simp only [cochainMap_apply, chainOfSimplex_map]
    rfl

/-- The restriction `a|_U` of a singular `n`-cochain `a` on `Y` to an open subset `U`: the pullback
along the inclusion `U ↪ Y`.
Source: Hatcher, *Algebraic Topology*, §3.1 (induced maps on cochains). -/
def cupLeftRestrict {n : ℕ} (a : Cochain K (TopCat.toSSet.obj Y) n) (U : (Opens Y)ᵒᵖ) :
    OpenCochains K Y U n :=
  cochainMap K (TopCat.toSSet.map (Opens.inclusion' U.unop)) n a

example (U : (Opens Y)ᵒᵖ) : cupLeftRestrict (0 : Cochain K (TopCat.toSSet.obj Y) 1) U = 0 :=
  map_zero _

/-- Restricting `a|_U` further to `V ⊆ U` gives `a|_V`. -/
theorem cupLeftRestrict_map {n : ℕ} (a : Cochain K (TopCat.toSSet.obj Y) n)
    {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V) :
    (singularCochainPresheaf K Y n).map i (cupLeftRestrict a U) = cupLeftRestrict a V := by
  change cochainMap K (TopCat.toSSet.map ((Opens.toTopCat Y).map i.unop)) n
    (cochainMap K (TopCat.toSSet.map (Opens.inclusion' U.unop)) n a) = _
  rw [cupLeft_cochainMap_comp, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Left cup with a singular `1`-cochain `a` on `Y`, on the presheaves of singular cochains: on an
open `U` it sends `c ∈ C^n(U)` to `a|_U ∪ c ∈ C^{1+n}(U)`, the repository's Alexander–Whitney cup
`cupCochain 1 n`. Naturality in `U` is naturality of the cup product.
Source: Hatcher, *Algebraic Topology*, §3.2 (cup product and its naturality); Bredon, *Sheaf
Theory*, 2nd ed., GTM 170, III.1 (the presheaf of singular cochains). -/
def cupLeftPresheafHom (a : Cochain K (TopCat.toSSet.obj Y) 1) (n : ℕ) :
    singularCochainPresheaf K Y n ⟶ singularCochainPresheaf K Y (1 + n) where
  app U := AddCommGrpCat.ofHom
    (HodgeLean.Foundations.Singular.cupCochain ((Opens.toTopCat Y).obj U.unop) 1 n
      (cupLeftRestrict a U)).toAddMonoidHom
  naturality {U V} i := by
    ext c
    change HodgeLean.Foundations.Singular.cupCochain _ 1 n (cupLeftRestrict a V)
        (cochainMap K (TopCat.toSSet.map ((Opens.toTopCat Y).map i.unop)) n c) =
      cochainMap K (TopCat.toSSet.map ((Opens.toTopCat Y).map i.unop)) (1 + n)
        (HodgeLean.Foundations.Singular.cupCochain _ 1 n (cupLeftRestrict a U) c)
    rw [HodgeLean.Foundations.Singular.cupCochain_naturality, ← cupLeftRestrict_map a i]
    rfl

example (a : Cochain K (TopCat.toSSet.obj Y) 1) (n : ℕ) (U : (Opens Y)ᵒᵖ)
    (c : OpenCochains K Y U n) :
    (cupLeftPresheafHom a n).app U c =
      HodgeLean.Foundations.Singular.cupCochain _ 1 n (cupLeftRestrict a U) c := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The Leibniz rule for left cup with a cocycle: `δ(a ∪ c) = −(a ∪ δc)` when `δa = 0`. -/
theorem cupLeftPresheafHom_comm (a : Cochain K (TopCat.toSSet.obj Y) 1)
    (ha : coboundary K 1 a = 0) (n : ℕ) :
    cupLeftPresheafHom a n ≫ singularCochainCoboundary K Y (1 + n) =
      -(singularCochainCoboundary K Y n ≫ cupLeftPresheafHom a (n + 1)) := by
  apply NatTrans.ext
  funext U
  ext c
  change coboundary K (1 + n)
      (HodgeLean.Foundations.Singular.cupCochain _ 1 n (cupLeftRestrict a U) c) =
    -(HodgeLean.Foundations.Singular.cupCochain _ 1 (n + 1) (cupLeftRestrict a U)
      (coboundary K n c))
  have h0 : coboundary K 1 (cupLeftRestrict a U) = 0 := by
    rw [cupLeftRestrict, HodgeLean.Foundations.Simplicial.coboundary_cochainMap, ha, map_zero]
  rw [HodgeLean.Foundations.Singular.coboundary_cupCochain, h0, map_zero, LinearMap.zero_apply,
    LinearMap.zero_comp, zero_add, pow_one, neg_one_smul]

/-- The sheafification of `cupLeftPresheafHom a n`: left cup with `a` on the sheaves of singular
cochains.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, I.5 and III.1 (sheafification is a functor; the
sheaf of singular cochains). -/
def cupLeftSheafHom (a : Cochain K (TopCat.toSSet.obj Y) 1) (n : ℕ) :
    singularCochainSheaf K Y n ⟶ singularCochainSheaf K Y (1 + n) :=
  (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map (cupLeftPresheafHom a n)

example (n : ℕ) : cupLeftSheafHom (0 : Cochain K (TopCat.toSSet.obj Y) 1) n =
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
      (cupLeftPresheafHom 0 n) := rfl

/-- The Leibniz rule after sheafification. -/
theorem cupLeftSheafHom_comm (a : Cochain K (TopCat.toSSet.obj Y) 1)
    (ha : coboundary K 1 a = 0) (n : ℕ) :
    cupLeftSheafHom a n ≫ singularCochainSheafCoboundary K Y (1 + n) =
      -(singularCochainSheafCoboundary K Y n ≫ cupLeftSheafHom a (n + 1)) := by
  have h := congrArg (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
    (cupLeftPresheafHom_comm a ha n)
  rw [Functor.map_comp, Functor.map_neg, Functor.map_comp] at h
  exact h

/-- `cupLeftSheafHom` between the terms of the natural-number-indexed sheaf complex.
Source: upstream's `singularCochainSheafComplex` (its term in degree `n` is the sheafification of
the degree-`n` singular cochain presheaf); Hatcher, *Algebraic Topology*, §3.2 (cup product). -/
def cupLeftSheafHomX (a : Cochain K (TopCat.toSSet.obj Y) 1) (n : ℕ) :
    (singularCochainSheafComplex K Y).X n ⟶ (singularCochainSheafComplex K Y).X (1 + n) :=
  cupLeftSheafHom a n

example (a : Cochain K (TopCat.toSSet.obj Y) 1) (n : ℕ) :
    cupLeftSheafHomX a n = cupLeftSheafHom a n := rfl

/-- The Leibniz rule with the differentials of the sheaf complex. -/
theorem cupLeftSheafHomX_comm (a : Cochain K (TopCat.toSSet.obj Y) 1)
    (ha : coboundary K 1 a = 0) (n : ℕ) :
    cupLeftSheafHomX a n ≫ (singularCochainSheafComplex K Y).d (1 + n) (1 + n + 1) =
      -((singularCochainSheafComplex K Y).d n (n + 1) ≫ cupLeftSheafHomX a (n + 1)) := by
  rw [AlgebraicTopology.Singular.singularCochainSheafComplex_d,
    AlgebraicTopology.Singular.singularCochainSheafComplex_d]
  exact cupLeftSheafHom_comm a ha n

/-- The degree-`i` component of `cupLeftSheafComplexHom`: `cupLeftSheafHomX a n` in degree
`i = n ≥ 0`, and `0` in negative degrees, where the source is zero.
Source: Mathlib's `HomologicalComplex.extendXIso` (the terms of the extension by zero along
`ComplexShape.embeddingUpNat`); Hatcher, *Algebraic Topology*, §3.2 (cup product). -/
def cupLeftSheafComplexHomF (a : Cochain K (TopCat.toSSet.obj Y) 1) : (i : ℤ) →
    ((singularCochainSheafComplex K Y).extend ComplexShape.embeddingUpNat).X i ⟶
      ((singularCochainSheafComplex K Y).extend ComplexShape.embeddingUpNat).X (i + 1) :=
  fun i => match i with
  | Int.ofNat n =>
      ((singularCochainSheafComplex K Y).extendXIso ComplexShape.embeddingUpNat
          (i := n) rfl).hom ≫ cupLeftSheafHomX a n ≫
        ((singularCochainSheafComplex K Y).extendXIso ComplexShape.embeddingUpNat
          (i := 1 + n) (by simp; omega)).inv
  | Int.negSucc _ => 0

example (a : Cochain K (TopCat.toSSet.obj Y) 1) :
    cupLeftSheafComplexHomF a (Int.negSucc 0) = 0 := rfl

theorem cupLeftSheafComplexHomF_natCast (a : Cochain K (TopCat.toSSet.obj Y) 1) (n : ℕ) :
    cupLeftSheafComplexHomF a (n : ℤ) =
      ((singularCochainSheafComplex K Y).extendXIso ComplexShape.embeddingUpNat
          (i' := (n : ℤ)) (i := n) rfl).hom ≫ cupLeftSheafHomX a n ≫
        ((singularCochainSheafComplex K Y).extendXIso ComplexShape.embeddingUpNat
          (i' := (n : ℤ) + 1) (i := 1 + n) (by simp; omega)).inv := rfl

/-- Left cup with a singular `1`-cocycle `a` on `Y`, as a morphism `S• ⟶ S•⟦1⟧` of
integer-indexed complexes of sheaves, where `S•` is the sheafified singular-cochain complex
extended by zero (upstream's `singularCochainSheafComplexInt` for `Y = X(ℂ)`). In degree `n ≥ 0`
it is the sheafification of `c ↦ a|_U ∪ c`, with no sign: Mathlib's shift negates the
differential, and the Leibniz rule `δ(a ∪ c) = −(a ∪ δc)` supplies the matching sign.
Source: Hatcher, *Algebraic Topology*, §3.2, Lemma 3.6 (the Leibniz rule); Mathlib's
`CochainComplex.shiftFunctor_obj_d'` (the sign convention on the shift). -/
def cupLeftSheafComplexHom (a : Cochain K (TopCat.toSSet.obj Y) 1) (ha : coboundary K 1 a = 0) :
    (singularCochainSheafComplex K Y).extend ComplexShape.embeddingUpNat ⟶
      ((singularCochainSheafComplex K Y).extend ComplexShape.embeddingUpNat)⟦(1 : ℤ)⟧ where
  f i := cupLeftSheafComplexHomF a i
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    rw [CochainComplex.shiftFunctor_obj_d']
    rcases lt_or_ge i 0 with hi | hi
    · refine Limits.IsZero.eq_of_src
        (HomologicalComplex.isZero_extend_X _ _ _ fun k hk => ?_) _ _
      simp at hk
      omega
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    simp only [Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.comp_neg]
    change -(cupLeftSheafComplexHomF a (n : ℤ) ≫ _) = _ ≫
      cupLeftSheafComplexHomF a ((n + 1 : ℕ) : ℤ)
    rw [cupLeftSheafComplexHomF_natCast, cupLeftSheafComplexHomF_natCast]
    rw [HomologicalComplex.extend_d_eq _ _ (i := 1 + n) (j := 1 + n + 1) (by simp; omega)
      (by simp; omega)]
    rw [HomologicalComplex.extend_d_eq _ _ (i' := (n : ℤ)) (j' := (n : ℤ) + 1) (i := n)
      (j := n + 1) rfl (by simp)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% (cupLeftSheafHomX_comm a ha n)]
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
    simp only [Category.assoc]

example (a : Cochain K (TopCat.toSSet.obj Y) 1) (ha : coboundary K 1 a = 0) (n : ℕ) :
    (cupLeftSheafComplexHom a ha).f (n : ℤ) =
      ((singularCochainSheafComplex K Y).extendXIso ComplexShape.embeddingUpNat
          (i' := (n : ℤ)) (i := n) rfl).hom ≫ cupLeftSheafHomX a n ≫
        ((singularCochainSheafComplex K Y).extendXIso ComplexShape.embeddingUpNat
          (i' := (n : ℤ) + 1) (i := 1 + n) (by simp; omega)).inv := rfl

/-- Left cup with `a` on global sections of the natural-number-indexed sheaf complex: the
component on the top open set of `cupLeftSheafHomX a n`, as a map between the terms of upstream's
`globalSingularCochainSheafComplex`.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, I.1 (sections of a sheaf morphism). -/
def cupLeftGlobalHom (a : Cochain K (TopCat.toSSet.obj Y) 1) (n : ℕ) :
    (AlgebraicTopology.Singular.globalSingularCochainSheafComplex K Y).X n ⟶
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex K Y).X (1 + n) :=
  ((TopCat.Sheaf.forget AddCommGrpCat Y).map (cupLeftSheafHomX a n)).app (Opposite.op ⊤)

example (n : ℕ) :
    cupLeftGlobalHom (0 : Cochain K (TopCat.toSSet.obj Y) 1) n =
      ((TopCat.Sheaf.forget AddCommGrpCat Y).map (cupLeftSheafHomX 0 n)).app (Opposite.op ⊤) :=
  rfl

section OnX
open AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance cupLeftHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- On `X(ℂ)`, left cup with a singular `1`-cocycle `a`, as a morphism
`S• ⟶ S•⟦1⟧` of upstream's integer-indexed singular-cochain resolution
`singularCochainSheafComplexInt X K`.
Source: `cupLeftSheafComplexHom`; Hatcher, *Algebraic Topology*, §3.2, Lemma 3.6. -/
def cupLeftComplexHom (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1) :
    singularCochainSheafComplexInt X K ⟶ (singularCochainSheafComplexInt X K)⟦(1 : ℤ)⟧ :=
  cupLeftSheafComplexHom a.1 (LinearMap.mem_ker.mp a.2)

example (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1) :
    cupLeftComplexHom X a = cupLeftSheafComplexHom a.1 (LinearMap.mem_ker.mp a.2) := rfl

/-- The action of `cupLeftComplexHom X a` on hypercohomology, `ℍ^n(S•) → ℍ^m(S•)` for
`1 + n = m`: a class `α : ℤ[0] → S•[n]` in the derived category is sent to
`C_a[n] ∘ α : ℤ[0] → S•[1][n] = S•[m]` (Mathlib's `SmallShiftedHom.comp` with `SmallShiftedHom.mk`).
Source: Mathlib's `CategoryTheory.Localization.SmallShiftedHom.comp`; Kashiwara–Schapira,
*Sheaves on Manifolds*, §1.7 (morphisms in the derived category act on hypercohomology). -/
def cupLeftHypercohomology (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    {n m : ℤ} (h : 1 + n = m) :
    Hypercohomology X (singularCochainSheafComplexInt X K) n →+
      Hypercohomology X (singularCochainSheafComplexInt X K) m where
  toFun α := α.comp
    (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (cupLeftComplexHom X a)) h
  map_zero' := by
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_zero, ShiftedHom.zero_comp]
  map_add' α β := by
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_add, ShiftedHom.add_comp]

example (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1) (n : ℤ) :
    cupLeftHypercohomology X a (n := n) rfl 0 = 0 :=
  map_zero _

/-- The comparison `H^n_sing(X(ℂ); K) → ℍ^n(X(ℂ); S•)` from singular cohomology to
hypercohomology of the `K`-singular-cochain resolution, for any commutative ring `K`: singular
cohomology as homology of raw global cochains, then global sections of the sheaf complex, then the
edge map. These are the first four legs of stage 3c's `singularToFieldCohomology`, which is this
map followed by upstream's identification of `ℍ^n(S•)` with `H^n(X(ℂ); K)` (see the `example`).
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1 and II.4; stage 3c
`singularToFieldCohomology` (`HodgeLean/Foundations/ComplexSheafSingularDefs.lean`). -/
def singularToSheafHypercohomology (K : Type) [CommRing K] (n : ℕ) :
    AlgebraicTopology.Singular.Cohomology K (TopCat.of (ComplexPoint X)) n →+
      Hypercohomology X (singularCochainSheafComplexInt X K) n :=
  let Y := TopCat.of (ComplexPoint X)
  let G := AlgebraicTopology.Singular.globalSingularCochainSheafComplex K Y
  (HodgeLean.Foundations.globalSectionsToHypercohomology X
      (singularCochainSheafComplexInt X K) n).comp <|
  ((HomologicalComplex.homologyMapIso
      (HodgeLean.Foundations.globalSectionsSingularCochainComplexIntIsoExtendField K X)
        (n : ℤ)).symm |>.addCommGroupIsoToAddEquiv.toAddMonoidHom).comp <|
  ((G.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).symm
      |>.addCommGroupIsoToAddEquiv.toAddMonoidHom).comp <|
  (HomologicalComplex.homologyMap
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K Y) n).hom.comp
    (AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw K Y n).toAddMonoidHom

example (K : Type) [Field K] [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    HodgeLean.Foundations.singularToFieldCohomology K X n =
      ((hypercohomologyAddEquivConstantCohomology K X n).toAddMonoidHom.comp
        (HodgeLean.Foundations.fieldHypercohomologySingularCochainAddEquiv K X n).symm.toAddMonoidHom).comp
        (singularToSheafHypercohomology X K n) := rfl

end OnX

end HodgeLean.Adapters
