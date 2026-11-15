import HodgeLean.Adapters.CycleClassFlatComparisonDefs

/-! # Support inclusion for flat prime pullback

Proved prerequisites independent of the supported-prime comparison.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.RealDefs
namespace HodgeLean.Adapters

attribute [local instance] specializationOrder in
private lemma ccm4_flatPullbackPrime_coheight_eq_zero_of_component_generic
    {T : Type*} [TopologicalSpace T] [T0Space T]
    {y : T} (hy : closure ({y} : Set T) ∈ irreducibleComponents T) :
    Order.coheight y = 0 := by
  rw [Order.coheight_eq_zero]
  intro y' hyy'
  have hsub : closure ({y} : Set T) ⊆ closure ({y'} : Set T) := by
    change Specializes y' y at hyy'
    exact closure_minimal (Set.singleton_subset_iff.mpr
      (specializes_iff_mem_closure.mp hyy')) isClosed_closure
  have hrev : closure ({y'} : Set T) ⊆ closure ({y} : Set T) :=
    hy.2 isIrreducible_singleton.closure hsub
  change Specializes y y'
  exact specializes_iff_mem_closure.mpr
    (hrev (subset_closure (Set.mem_singleton y')))

attribute [local instance] specializationOrder in
private lemma ccm4_flatPullbackPrime_component_maps_to_point {X Z : Scheme}
    (f : X ⟶ Z) [Flat f] (x : Z)
    (y : (ccm3_inverseIdeal f x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f x).subscheme) :
    f ((ccm3_inverseIdeal f x).subschemeι y) = x := by
  let I := ccm3_inverseIdeal f x
  have hymax : IsMax y := Order.coheight_eq_zero.mp
    (ccm4_flatPullbackPrime_coheight_eq_zero_of_component_generic hy)
  have hymem : I.subschemeι y ∈ I.support := by
    change I.subschemeι y ∈ (I.support : Set X)
    rw [← I.range_subschemeι]
    exact ⟨y, rfl⟩
  have hfx : f (I.subschemeι y) ∈ closure ({x} : Set Z) := by
    change I.subschemeι y ∈ ((ccm3_primeIdeal Z x).comap f).support at hymem
    rw [Scheme.IdealSheafData.support_comap] at hymem
    change f (I.subschemeι y) ∈
      ((Scheme.IdealSheafData.vanishingIdeal
        ⟨closure ({x} : Set Z), isClosed_closure⟩).support : Set Z) at hymem
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hymem
    exact hymem
  obtain ⟨z', hz', hfz'⟩ := (Flat.generalizingMap f)
    (specializes_iff_mem_closure.mpr hfx)
  have hz'mem : z' ∈ I.support := by
    change z' ∈ ((ccm3_primeIdeal Z x).comap f).support
    rw [Scheme.IdealSheafData.support_comap]
    change f z' ∈
      ((Scheme.IdealSheafData.vanishingIdeal
        ⟨closure ({x} : Set Z), isClosed_closure⟩).support : Set Z)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, hfz']
    exact subset_closure (Set.mem_singleton x)
  obtain ⟨y', hy'⟩ := Set.mem_range.mp (I.range_subschemeι.symm.subset hz'mem)
  have hyy' : y ≤ y' := by
    change Specializes y' y
    apply I.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp
    simpa only [hy'] using hz'
  have heq : y' = y := le_antisymm (hymax hyy') hyy'
  simpa only [I, ← hy', heq] using hfz'

/-- Source: Fulton, *Intersection Theory*, second edition, §1.7, inverse images
of supports under flat pullback. -/
theorem ccm4_flatPullbackPrime_support_le_aux {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Flat f.left] (x : Z.left) (z : X.left)
    (hz : ccm3_flatPullbackPrime f.left x z ≠ 0) :
    cycleComponentAnalyticClosedSupport X z ≤
      ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x) := by
  obtain ⟨y, hyz, hy⟩ := (ccm3_flatPullbackPrime_support f x z).mp hz
  have hcoeff := ccm3_flatPullbackPrime_coeff f x y hy
  have hfz : f.left z = x := by
    simpa only [hyz] using
      ccm4_flatPullbackPrime_component_maps_to_point f.left x y hy
  intro a ha
  change Point.underlying a ∈ closure ({z} : Set X.left) at ha
  change Point.underlying (Point.map f a) ∈ closure ({x} : Set Z.left)
  rw [Point.underlying_map]
  have himage := image_closure_subset_closure_image f.left.continuous
    ⟨Point.underlying a, ha, rfl⟩
  simpa only [Set.image_singleton, hfz] using himage

end HodgeLean.Adapters
