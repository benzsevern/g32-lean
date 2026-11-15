import HodgeLean.Foundations.Singular.TorusExteriorIso
import HodgeLean.Foundations.Uniformization

/-! # Transport of the singular torus theorem
Stage S13. HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicTopology.Singular AlgebraicGeometry
namespace HodgeLean.Foundations.Singular

/-- The S5 and S7 wedge maps agree, including their specified iterated cup product.
Source: the exterior-power universal property and the shared `cupMulti` construction. -/
theorem cupWedgeMap_eq_wedgeToCohomology (n m : ℕ) :
    cupWedgeMap (TopCat.of (UnitAddTorus (Fin n))) m = wedgeToCohomology n m := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, cupWedgeMap_ιMulti,
    wedgeToCohomology_ιMulti]

/-- Pullback intertwines exterior powers with the specified singular wedge map.
Source: Hatcher, Algebraic Topology, §3.2; `cohomologyMap_cupMulti`. -/
theorem cohomologyMap_cupWedgeMap {Y Z : TopCat.{0}} (f : Z ⟶ Y) (m : ℕ) :
    (cohomologyMap ℚ m f).comp (cupWedgeMap Y m) =
      (cupWedgeMap Z m).comp (exteriorPower.map m (cohomologyMap ℚ 1 f)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, cupWedgeMap_ιMulti, cohomologyMap_cupMulti]
  rfl

/-- The exterior power of a rational linear equivalence, with the specified map.
Source: Mathlib `exteriorPower.map_injective_field` and `exteriorPower.map_surjective`. -/
def exteriorPowerEquiv {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (e : V ≃ₗ[ℚ] W) (m : ℕ) :
    (⋀[ℚ]^m V) ≃ₗ[ℚ] (⋀[ℚ]^m W) :=
  LinearEquiv.ofBijective (exteriorPower.map m e.toLinearMap)
    ⟨exteriorPower.map_injective_field e.injective,
      exteriorPower.map_surjective e.surjective⟩

example {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (e : V ≃ₗ[ℚ] W) (m : ℕ) (v : ⋀[ℚ]^m V) :
    exteriorPowerEquiv e m v = exteriorPower.map m e.toLinearMap v := rfl

/-- A space homeomorphic to a torus has bijective singular cup-wedge maps.
Source: Hatcher, Algebraic Topology, Example 3.11 and Theorem 3.15;
`torusWedgeEquiv` and naturality of cup products. -/
theorem cupWedgeMap_bijective_of_homeomorph {Y : Type} [TopologicalSpace Y]
    {n : ℕ} (e : Y ≃ₜ UnitAddTorus (Fin n)) (m : ℕ) :
    Function.Bijective (cupWedgeMap (TopCat.of Y) m) := by
  let E k := cohomologyHomeomorphEquiv e k
  have h := cohomologyMap_cupWedgeMap (TopCat.ofHom ⟨e, e.continuous⟩) m
  rw [cupWedgeMap_eq_wedgeToCohomology] at h
  have hb : Function.Bijective ((cupWedgeMap (TopCat.of Y) m).comp
      (exteriorPower.map m (E 1).symm.toLinearMap)) := by
    change Function.Bijective ((cupWedgeMap (TopCat.of Y) m).comp
      (exteriorPower.map m (cohomologyMap ℚ 1 (TopCat.ofHom ⟨e, e.continuous⟩))))
    rw [← h]
    exact (E m).symm.bijective.comp (wedgeToCohomology_bijective n m)
  exact (Function.Bijective.of_comp_iff _ (exteriorPowerEquiv (E 1).symm m).bijective).mp hb

/-- The singular wedge map preserves multiplication in every bidegree.
Source: Hatcher, Algebraic Topology, §3.2; associativity and the exterior universal property. -/
theorem cupWedgeMap_wedge (Y : TopCat.{0}) (m n : ℕ)
    (v : ⋀[ℚ]^m (Cohomology ℚ Y 1)) (w : ⋀[ℚ]^n (Cohomology ℚ Y 1)) :
    cupWedgeMap Y (m + n) (exteriorPower.wedge ℚ _ m n v w) =
      cup Y rfl (cupWedgeMap Y m v) (cupWedgeMap Y n w) := by
  have key : (exteriorPower.wedge ℚ (Cohomology ℚ Y 1) m n).compr₂
      (cupWedgeMap Y (m + n)) =
      (cup Y rfl).compl₁₂ (cupWedgeMap Y m) (cupWedgeMap Y n) := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun a => ?_)
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun b => ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.compr₂_apply,
      LinearMap.compl₁₂_apply]
    have hw : exteriorPower.wedge ℚ _ m n (exteriorPower.ιMulti ℚ m a)
        (exteriorPower.ιMulti ℚ n b) = exteriorPower.ιMulti ℚ (m + n) (Fin.append a b) := by
      apply Subtype.ext
      exact ExteriorAlgebra.ιMulti_mul_ιMulti a b
    rw [hw, cupWedgeMap_ιMulti, cupWedgeMap_ιMulti, cupWedgeMap_ιMulti]
    exact cupMulti_append Y n b m a (m + n) rfl _
      (fun i => Fin.append_left a b i) (fun j => Fin.append_right a b j)
  exact LinearMap.congr_fun₂ key v w

/-- The specified cup-wedge isomorphism on complex points of an abelian variety.
Source: Birkenhake–Lange, Complex Abelian Varieties, Lemma 1.3.1;
`complexPointTorusHomeomorph` and the singular model-torus theorem. -/
def complexPointWedgeEquiv (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (m : ℕ) :
    (⋀[ℚ]^m (Cohomology ℚ (TopCat.of (ComplexPoint X)) 1)) ≃ₗ[ℚ]
      Cohomology ℚ (TopCat.of (ComplexPoint X)) m :=
  LinearEquiv.ofBijective (cupWedgeMap _ m)
    (cupWedgeMap_bijective_of_homeomorph
      (complexPointTorusHomeomorph X (TopologicalSpace.dim X.left)) m)

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (m : ℕ) (v : ⋀[ℚ]^m (Cohomology ℚ (TopCat.of (ComplexPoint X)) 1)) :
    complexPointWedgeEquiv X m v = cupWedgeMap _ m v := rfl

/-- The transported equivalences preserve the graded ring multiplication.
Source: `cupWedgeMap_wedge`; Birkenhake–Lange, Complex Abelian Varieties, Lemma 1.3.1. -/
theorem complexPointWedgeEquiv_wedge (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (m n : ℕ)
    (v : ⋀[ℚ]^m (Cohomology ℚ (TopCat.of (ComplexPoint X)) 1))
    (w : ⋀[ℚ]^n (Cohomology ℚ (TopCat.of (ComplexPoint X)) 1)) :
    complexPointWedgeEquiv X (m + n) (exteriorPower.wedge ℚ _ m n v w) =
      cup _ rfl (complexPointWedgeEquiv X m v) (complexPointWedgeEquiv X n w) :=
  cupWedgeMap_wedge _ m n v w

/-- The transported equivalence preserves the unit in degree zero.
Source: the empty iterated cup product. -/
theorem complexPointWedgeEquiv_unit (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    complexPointWedgeEquiv X 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0) =
      unit (TopCat.of (ComplexPoint X)) := cupWedgeMap_ιMulti _ 0 _

#print axioms complexPointWedgeEquiv
#print axioms complexPointWedgeEquiv_wedge
#print axioms complexPointWedgeEquiv_unit
end HodgeLean.Foundations.Singular
