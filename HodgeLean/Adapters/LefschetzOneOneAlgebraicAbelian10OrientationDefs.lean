import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian9Orientation
import HodgeLean.Adapters.ThetaDivisorOnXProofs

/-! # The period torus as a map of support pairs

The boundary-avoidance input constructs the relative map. HC no distance;
AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.Singular Set Topology
open scoped CategoryTheory.MonObj
namespace HodgeLean.Adapters

/-- Real representatives give the exponential of the ordered affine period square.
Source: Birkenhake--Lange, Complex Abelian Varieties, second edition, section 1.3. -/
theorem bh10_periodTorus_real
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X)
    (z : Fin (dim X.left) → ℂ) (s t : ℝ) :
    bh8_periodTorus X l m z ![(s : UnitAddCircle), (t : UnitAddCircle)] =
      abelianExp X (z + s • (l : Fin (dim X.left) → ℂ) +
        t • (m : Fin (dim X.left) → ℂ)) := by
  rw [abelianExp_add_eq_mul, abelianExp_add_eq_mul]
  change abelianExp X z *
    Additive.toMul (oneParameterSubgroup X (dim X.left) l s) *
    Additive.toMul (oneParameterSubgroup X (dim X.left) m t) = _
  simp only [abelianExp, complexExponential_smul]

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : bh8_periodTorus X 0 0 0 0 = abelianExp X 0 := by
  have he : ![(0 : UnitAddCircle), 0] = (0 : UnitAddTorus (Fin 2)) := by
    ext i
    fin_cases i <;> rfl
  simpa only [AddCircle.coe_zero, he, zero_smul, add_zero] using
    bh10_periodTorus_real X 0 0 0 0 0

/-- Boundary avoidance implies avoidance on both coordinate circles.
Source: Hatcher, Algebraic Topology, section 2.2, the quotient square. -/
theorem bh10_periodTorus_skeleton
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (l m : abelianPeriodLattice X)
    (z : Fin (dim X.left) → ℂ)
    (ha : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      abelianExp X (bh4_squareEdge X l m z i t) ∉ cycleComponentSupport X x)
    (t : UnitAddTorus (Fin 2)) (ht : t ∈ bh9_torusSkeleton) :
    bh8_periodTorus X l m z t ∉ cycleComponentSupport X x := by
  rcases ht with ht | ht
  · obtain ⟨r, hr, he⟩ := AddCircle.eq_coe_Ico (t 1)
    have ht' : t = ![(0 : UnitAddCircle), (r : UnitAddCircle)] := by
      ext i
      fin_cases i <;> simp [ht, he]
    rw [ht']
    have hreal := bh10_periodTorus_real X l m z 0 r
    simp only [AddCircle.coe_zero, zero_smul, add_zero] at hreal
    rw [hreal]
    simpa [bh4_squareEdge] using ha 3 (1 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
  · obtain ⟨r, hr, he⟩ := AddCircle.eq_coe_Ico (t 0)
    have ht' : t = ![(r : UnitAddCircle), (0 : UnitAddCircle)] := by
      ext i
      fin_cases i <;> simp [ht, he]
    rw [ht']
    have hreal := bh10_periodTorus_real X l m z r 0
    simp only [AddCircle.coe_zero, zero_smul, add_zero] at hreal
    rw [hreal]
    simpa [bh4_squareEdge] using ha 0 r ⟨hr.1, hr.2.le⟩

/-- The actual translated period torus, relative to its coordinate circles and the component.
Source: Hatcher, section 3.3, functoriality of relative cohomology. -/
def bh10_periodTorusPairMap
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (l m : abelianPeriodLattice X)
    (z : Fin (dim X.left) → ℂ)
    (ha : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      abelianExp X (bh4_squareEdge X l m z i t) ∉ cycleComponentSupport X x) :
    bh9_torusPair ⟶ neighborhoodSupportComplementPair
      ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X)) (cycleComponentSupport X x) :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun t ↦ ⟨bh8_periodTorus X l m z t, mem_univ _⟩,
      (bh8_periodTorus X l m z).continuous.subtype_mk _⟩)
    (fun t ht ↦ bh10_periodTorus_skeleton X x l m z ha t ht)

/-- The relative square factors through the constructed relative torus.
Source: the defining exponential formula and the ordered real clamped coordinates. -/
theorem bh10_square_factorization
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (l m : abelianPeriodLattice X)
    (z : Fin (dim X.left) → ℂ)
    (ha : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      abelianExp X (bh4_squareEdge X l m z i t) ∉ cycleComponentSupport X x) :
    bh9_squareTorusMap ≫ bh10_periodTorusPairMap X x l m z ha =
      bh5_componentPairMap X x l m z ha := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext q
    apply Subtype.ext
    apply Subtype.ext
    exact bh10_periodTorus_real X l m z _ _
  · ext q
    apply Subtype.ext
    exact bh10_periodTorus_real X l m z _ _

end HodgeLean.Adapters
