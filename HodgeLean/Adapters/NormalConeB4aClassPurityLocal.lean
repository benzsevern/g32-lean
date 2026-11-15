import HodgeLean.Adapters.NormalConeB4aClassPurity

/-! # Cofinal lower support vanishing with varying ambient dimension

Route: take a standard-smooth affine neighborhood of the underlying point.
Open immersions preserve algebraic coheight. Fixed-dimensional purity on
analytic opens then transports to neighborhoods in the original ambient.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
/-- Every analytic neighborhood contains a neighborhood with zero supported
cohomology below twice the algebraic codimension bound. -/
theorem a3b4a_classRelative_purity_vanishing_basis
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (S : Closeds Z) (c : ℕ)
    (hc : ∀ z ∈ S, (c : ℕ∞) ≤ Order.coheight z)
    (x : ComplexPoint (Over.mk q)) (V : Opens (ComplexPoint (Over.mk q))) (hxV : x ∈ V) :
    ∃ W : Opens (ComplexPoint (Over.mk q)), W ≤ V ∧ x ∈ W ∧
      ∀ n : ℕ, n < 2 * c → IsZero (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W : Set (ComplexPoint (Over.mk q)))
          (Point.underlying ⁻¹' (S : Set Z))) n) := by
  obtain ⟨A, hA, hxA, hs⟩ := Smooth.exists_affine_isStandardSmooth q x.underlying
  obtain ⟨d, hd⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension hs
  let qA := A.ι ≫ q
  letI : IsAffine A.toScheme := hA
  letI : SmoothOfRelativeDimension d qA :=
    smoothOfRelativeDimension_affineOpen_of_isStandardSmooth q hA hd
  letI : LocallyOfFiniteType qA := inferInstanceAs (LocallyOfFiniteType (A.ι ≫ q))
  letI : QuasiCompact qA := (quasiCompact_iff_compactSpace qA).2 inferInstance
  letI : IsSeparated qA := inferInstanceAs (IsSeparated (A.ι ≫ q))
  let SA : Closeds A.toScheme := S.preimage A.ι.continuous
  have hcA : ∀ z ∈ SA, (c : ℕ∞) ≤ Order.coheight z := by
    intro z hz
    have h := hc (A.ι z) hz
    rwa [coheight_eq_of_isOpenImmersion A.ι] at h
  let f := Point.map (ComplexPoint.openInclusion (Over.mk q) A)
  have hf : Topology.IsOpenEmbedding f := ComplexPoint.isOpenEmbedding_map_open (Over.mk q) A
  let VA : Opens (ComplexPoint (Over.mk qA)) :=
    ⟨f ⁻¹' (V : Set (ComplexPoint (Over.mk q))), V.isOpen.preimage hf.continuous⟩
  let W : Opens (ComplexPoint (Over.mk q)) := ⟨f '' (VA : Set (ComplexPoint (Over.mk qA))),
    hf.isOpenMap _ VA.isOpen⟩
  have hx : f (ComplexPoint.asOpenPoint (Over.mk q) A x hxA) = x :=
    Over.OverMorphism.ext (ComplexPoint.liftToOpen_fac (Over.mk q) A x hxA)
  refine ⟨W, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hz
  · refine ⟨ComplexPoint.asOpenPoint (Over.mk q) A x hxA, ?_, hx⟩
    change f _ ∈ V
    rw [hx]
    exact hxV
  · intro n hn
    have hzero := a3b4a_classRelative_purity_vanishing_fixedDimension_onOpen
      qA d c SA hcA VA n hn
    exact hzero.of_iso (neighborhoodSupportPairImageCohomologyIso f hf.isEmbedding
      (VA : Set (ComplexPoint (Over.mk qA)))
      (Point.underlying ⁻¹' (SA : Set A.toScheme))
      (Point.underlying ⁻¹' (S : Set Z)) (fun _ _ => Iff.rfl) n)

end HodgeLean.Adapters
