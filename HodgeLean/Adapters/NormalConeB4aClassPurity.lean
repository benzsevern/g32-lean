import HodgeLean.Adapters.NormalConeB4aClassOpenFiltration
import HodgeLean.Adapters.NormalConeB4aClassLayer
import HodgeLean.Adapters.NormalConeB4aClassLocalGlobal
import HodgeLean.Adapters.NormalConeB4aClassTopology
import HodgeLean.Adapters.NormalConeB4aClassSheaf

/-! # Lower support vanishing in fixed ambient dimension

Route: use the finite reduced smooth filtration of the algebraic support.
Each layer has cofinal lower vanishing by normal neighborhoods, hence its
relative group vanishes by the supported singular section comparison.
Finite support localization then gives vanishing for the initial support.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Analytic

set_option backward.isDefEq.respectTransparency false in
/-- Cohomology with an algebraic support of codimension at least `c` vanishes
below degree `2*c` in a smooth ambient scheme of fixed relative dimension. -/
theorem a3b4a_classRelative_purity_vanishing_fixedDimension
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (d c : ℕ)
    [SmoothOfRelativeDimension d q] [LocallyOfFiniteType q]
    [QuasiCompact q] [IsSeparated q]
    (S : Closeds Z) (hc : ∀ z ∈ S, (c : ℕ∞) ≤ Order.coheight z)
    (n : ℕ) (hn : n < 2 * c) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set (ComplexPoint (Over.mk q)))
        (Point.underlying ⁻¹' (S : Set Z))) n) := by
  let X := TopCat.of (ComplexPoint (Over.mk q))
  letI : LocallyOfFiniteType (Over.mk q).hom := ‹LocallyOfFiniteType q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  letI : T2Space X := f4_t2Space (Over.mk q)
  letI (V : Opens X) : ParacompactSpace V := a3b4a_class_openParacompact q V
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian q
  letI : CompactSpace Z := a3b4_compactSpace q
  letI : IsNoetherian Z := {}
  let F := reducedSmoothClosedFiltration q S
  let T : ℕ → Closeds X := fun k => (F k).preimage
    (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))
  let N := (reducedSmoothStratification q S).length
  have hT : Antitone T := fun i j hij x hx =>
    reducedSmoothClosedFiltration_antitone q S hij hx
  have hN : T N = ⊥ := by
    dsimp only [T, F, N]
    rw [reducedSmoothClosedFiltration_length]
    rfl
  refine a3b4a_classRelative_vanishing_of_finiteFiltration X T hT N hN n ?_
  intro k hk
  apply a3b4a_classRelative_vanishing_of_cofinal_local_vanishing
  intro j hj x hx V hxV
  by_cases hxS : x ∈ T k
  · exact a3b4a_classLayer_exists_relative_vanishing q d c (F k)
      (fun z hz => hc z (reducedSmoothClosedFiltration_le q S k hz)) x hxS hx V hxV
      |>.imp (fun W hW => ⟨hW.1, hW.2.1, hW.2.2 j (hj.trans_lt hn)⟩)
  · let W := V ⊓ (T k).compl
    refine ⟨W, inf_le_left, ⟨hxV, hxS⟩, ?_⟩
    letI := neighborhoodSupportRelativeCohomology_subsingleton X (T k) j W
      (fun _ hy => hy.2)
    exact ModuleCat.isZero_of_subsingleton _

/-- Cohomology with an algebraic support of codimension at least `c` vanishes
below degree `2*c` in a smooth ambient scheme of fixed relative dimension. -/
theorem a3b4a_classRelative_purity_vanishing_fixedDimension_onOpen
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (d c : ℕ)
    [SmoothOfRelativeDimension d q] [LocallyOfFiniteType q]
    [QuasiCompact q] [IsSeparated q]
    (S : Closeds Z) (hc : ∀ z ∈ S, (c : ℕ∞) ≤ Order.coheight z)
    (U : Opens (ComplexPoint (Over.mk q))) (n : ℕ) (hn : n < 2 * c) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set (ComplexPoint (Over.mk q)))
        (Point.underlying ⁻¹' (S : Set Z))) n) := by
  let X := TopCat.of (ComplexPoint (Over.mk q))
  letI : LocallyOfFiniteType (Over.mk q).hom := ‹LocallyOfFiniteType q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : T2Space X := f4_t2Space (Over.mk q)
  letI : SecondCountableTopology X := f4_secondCountable (Over.mk q)
  letI : LocallyCompactSpace X := an_locallyCompactSpace (f4_analytification (Over.mk q))
  letI : LocallyCompactSpace U := U.isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  letI (V : Opens U) : LocallyCompactSpace V := V.isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  letI (V : Opens U) : ParacompactSpace V := inferInstance
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian q
  letI : CompactSpace Z := a3b4_compactSpace q
  letI : IsNoetherian Z := {}
  let F := reducedSmoothClosedFiltration q S
  let T : ℕ → Closeds X := fun k => (F k).preimage
    (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))
  let N := (reducedSmoothStratification q S).length
  have hT : Antitone T := fun i j hij x hx =>
    reducedSmoothClosedFiltration_antitone q S hij hx
  have hN : T N = ⊥ := by
    dsimp only [T, F, N]
    rw [reducedSmoothClosedFiltration_length]
    rfl
  refine a3b4a_classRelative_vanishing_onOpen_of_finite_localFiltration X U T hT N hN n ?_
  intro k hk j hj x hx V hxV
  by_cases hxS : x ∈ T k
  · exact a3b4a_classLayer_exists_relative_vanishing q d c (F k)
      (fun z hz => hc z (reducedSmoothClosedFiltration_le q S k hz)) x hxS hx V hxV
      |>.imp (fun W hW => ⟨hW.1, hW.2.1, hW.2.2 j (hj.trans_lt hn)⟩)
  · let W := V ⊓ (T k).compl
    refine ⟨W, inf_le_left, ⟨hxV, hxS⟩, ?_⟩
    letI := neighborhoodSupportRelativeCohomology_subsingleton X (T k) j W
      (fun _ hy => hy.2)
    exact ModuleCat.isZero_of_subsingleton _

end HodgeLean.Adapters
