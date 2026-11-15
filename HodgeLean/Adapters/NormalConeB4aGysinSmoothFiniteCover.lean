import HodgeLean.Adapters.NormalConeB4aGysinLowerStrata

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- A smooth finite type complex scheme of dimension below `n` has a finite
affine cover by fixed-dimensional smooth regions of dimension below `n`. -/
theorem a3b4a_gysin_smooth_finite_affine_dimension_cover
    (X : Over (Spec (CommRingCat.of ℂ))) [Smooth X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (n : ℕ) (hdim : topologicalKrullDim X.left < (n : ℕ)) :
    ∃ (U : X.left → X.left.Opens) (d : X.left → ℕ),
      (∀ x, IsAffineOpen (U x) ∧ x ∈ U x ∧ d x < n ∧
        SmoothOfRelativeDimension (d x) ((U x).ι ≫ X.hom)) ∧
      ∃ J : Finset X.left, ∀ y : X.left, ∃ x ∈ J, y ∈ U x := by
  classical
  choose U hU hx d hd hstd using fun x =>
    Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt X.hom hdim x
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x : Set X.left)) (fun x => (U x).isOpen)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hx y⟩)
  refine ⟨U, d, ?_, J, ?_⟩
  · intro x
    refine ⟨hU x, hx x, hd x, ?_⟩
    exact smoothOfRelativeDimension_affineOpen_of_isStandardSmooth X.hom (hU x) (hstd x)
  · intro y
    obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp (hJ (Set.mem_univ y))
    exact ⟨i, hi, hy⟩

end HodgeLean.Adapters
