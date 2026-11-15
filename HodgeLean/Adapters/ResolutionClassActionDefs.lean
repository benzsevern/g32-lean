import HodgeLean.Adapters.CupCocycleSheaf
import HodgeLean.Adapters.WedgeThetaComplex

/-! # The class of a degree-one endomorphism of a resolution

Stage hl3 of the `hL` track (`docs/specs/ResolutionClassAction.md`). For a quasi-isomorphism
`q : A ⟶ K` of integer-indexed complexes of sheaves on `X(ℂ)` and a morphism of complexes
`L : K ⟶ K⟦1⟧`, this file defines the degree-one morphism of the derived category

`e_L = Q(q)⁻¹[1] ∘ Q(L) ∘ Q(q) : A ⟶ A[1]`

as a `SmallShiftedHom` (`resolutionClass`), in the composition form of hl1's statement 11 and of
hl2's `cupLeftHypercohomology`. For `A = ℂ[0]` and the resolutions `q_Ω : ℂ[0] ⟶ Ω•` (upstream's
`constantsToHolomorphicDeRhamComplexInt`) and `q_S : ℂ[0] ⟶ S•` (upstream's
`constantsToSingularCochainComplexInt`), the frozen file compares `e_{L_θ}` and `e_{C_a}` with the
classes of `θ` and `a`. It also defines the unit map `ℤ[0] ⟶ K[0]` (hypercohomology classes have
source `ℤ[0]`), the identification of the degree-`0` term of `K[0]` with the constant sheaf, and
the global constant sections.

Everything here is a definition or a lemma with a complete proof. HC no distance; AV milestone no
distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ))

/-- The class `e_L : A ⟶ A[1]` in the derived category of a morphism of complexes
`L : K ⟶ K⟦1⟧` on a complex `K` with a quasi-isomorphism `q : A ⟶ K`: the composite
`q`, then `L` read as a degree-one shifted morphism `K ⟶ K`, then the formal inverse of `q`
(`SmallShiftedHom.mk₀Inv`). In the derived category it is `Q(q)⁻¹[1] ∘ Q(L) ∘ Q(q)`.
Source: Iversen, *Cohomology of Sheaves*, Springer Universitext 1986, Ch. I (Yoneda products and
morphisms of resolutions); Kashiwara–Schapira, *Sheaves on Manifolds*, Grundlehren 292, §1.7;
Mathlib's `Localization.SmallShiftedHom.comp`, `mk` and `mk₀Inv`. -/
def resolutionClass {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L : K ⟶ K⟦(1 : ℤ)⟧) :
    Localization.SmallShiftedHom.{1} (analyticQuasiIsomorphisms X) A A (1 : ℤ) :=
  ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q).comp
      (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom K K (1 : ℤ) from L)) (add_zero 1)).comp
    (Localization.SmallShiftedHom.mk₀Inv (W := analyticQuasiIsomorphisms X) (0 : ℤ) rfl q hq)
    (zero_add 1)

example {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L : K ⟶ K⟦(1 : ℤ)⟧) :
    resolutionClass X q hq L =
      ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q).comp
          (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
            (show ShiftedHom K K (1 : ℤ) from L)) (add_zero 1)).comp
        (Localization.SmallShiftedHom.mk₀Inv (W := analyticQuasiIsomorphisms X) (0 : ℤ) rfl q
          hq) (zero_add 1) := rfl

/-- The unit map `ℤ[0] ⟶ K[0]` of integer-indexed constant sheaf complexes on `X(ℂ)`, for a
commutative ring `K`: the constant sheaf functor applied to `ℤ → K`, `1 ↦ 1`, in degree `0`.
Hypercohomology classes are morphisms from `ℤ[0]`, so this map sends the class
`Q(f) ∘ Q(u)` of a morphism `f : K[0] ⟶ T` to `ℍ^0(T)`.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, I.1 (constant sheaves) and II.2 (sheaf
cohomology with coefficients); upstream `constantIntegerSheafComplexInt` and
`constantCoefficientSheafComplexInt`. -/
def constantsIntToCoefficient (K : Type) [CommRing K] :
    constantIntegerSheafComplexInt X ⟶ constantCoefficientSheafComplexInt X K :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
        (AddCommGrpCat.ofHom (Int.castAddHom K)))) ComplexShape.embeddingUpNat

/-- For `K = ℂ` the target is upstream's `ℂ[0]`, the source of the de Rham resolution. -/
example [IsIntegral X.left] [Smooth X.hom] :
    constantIntegerSheafComplexInt X ⟶ Ω•(X) :=
  constantsIntToCoefficient X ℂ ≫ constantsToHolomorphicDeRhamComplexInt X

/-- The degree-`0` term of `K[0]` is the constant sheaf `K_X`.
Source: Mathlib's `HomologicalComplex.extendXIso` and `HomologicalComplex.singleObjXSelf`. -/
def constantCoefficientXZeroIso (K : Type) [CommRing K] :
    (constantCoefficientSheafComplexInt X K).X ((0 : ℕ) : ℤ) ≅
      𝓒(↧(ComplexPoint X); K) :=
  ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj 𝓒(↧(ComplexPoint X); K)).extendXIso
      ComplexShape.embeddingUpNat (i := 0) rfl ≪≫
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 _

example (K : Type) [CommRing K] :
    (constantCoefficientXZeroIso X K).hom ≫ (constantCoefficientXZeroIso X K).inv = 𝟙 _ :=
  Iso.hom_inv_id _

/-- The global section of the constant sheaf `K_X` with constant value `c`: the image of `c`
under the sheafification unit of the constant presheaf, on the top open set.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, I.1 (constant sections); Mathlib's
`CategoryTheory.toSheafify` and `CategoryTheory.constantSheaf`. -/
def constantGlobalSection (K : Type) [CommRing K] :
    K →+ (𝓒(↧(ComplexPoint X); K)).presheaf.obj (op ⊤) :=
  ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    𝓒ᵖ(TopCat.of (ComplexPoint X); K)).app (op ⊤)).hom

example (K : Type) [CommRing K] : constantGlobalSection X K 0 = 0 := map_zero _

/-- Upstream's `ℂ[0] ⟶ Ω•` is a quasi-isomorphism (the holomorphic Poincaré lemma), as a member of
the class of quasi-isomorphisms that defines the derived category. -/
theorem constantsToHolomorphicDeRham_mem [IsIntegral X.left] [Smooth X.hom] :
    analyticQuasiIsomorphisms X (constantsToHolomorphicDeRhamComplexInt X) :=
  (HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance

/-- Upstream's `K[0] ⟶ S•` is a quasi-isomorphism on smooth `X`, as a member of the class of
quasi-isomorphisms that defines the derived category. -/
theorem constantsToSingularCochain_mem [IsIntegral X.left] [Smooth X.hom] (K : Type)
    [CommRing K] :
    analyticQuasiIsomorphisms X (constantsToSingularCochainComplexInt X K) :=
  (HomologicalComplex.mem_quasiIso_iff _).mpr (constantsToSingularCochainComplexInt_quasiIso X K)

end HodgeLean.Adapters
