import HodgeLean.Foundations.BundleResolution.DegreeZeroCocycleDetectionHelpers

/-! # Detection of actual degree-zero singular classes at points

Each original zero-simplex factors through its unique point, and closed
zero-cochains have no boundary ambiguity.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Simplicial AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
open scoped Simplicial
namespace HodgeLean.Foundations.BundleResolution

variable {R : Type} [CommRing R] (Y : TopCat.{0})

theorem i1_degreeZero_eq_of_point_pullbacks
    (α β : Cohomology R Y 0)
    (h : ∀ x : Y, cohomologyMap R 0 (TopCat.ofHom (ContinuousMap.const PUnit x)) α =
      cohomologyMap R 0 (TopCat.ofHom (ContinuousMap.const PUnit x)) β) : α = β := by
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective Y 0 α
  obtain ⟨ψ, rfl⟩ := cohomologyClass_surjective Y 0 β
  let pull (x : Y) (χ : Cocycle R (TopCat.toSSet.obj Y) 0) :
      Cocycle R (TopCat.toSSet.obj (TopCat.of PUnit)) 0 :=
    ⟨cochainMap R (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const PUnit x))) 0 χ.1, by
      change coboundary R 0 _ = 0
      rw [HodgeLean.Foundations.Simplicial.coboundary_cochainMap, χ.2, map_zero]⟩
  have hp (x : Y) : (pull x φ).1 = (pull x ψ).1 := by
    have he := h x
    rw [cohomologyMap_class Y _ 0 φ (pull x φ) rfl,
      cohomologyMap_class Y _ 0 ψ (pull x ψ) rfl] at he
    exact congrArg Subtype.val (i1_degreeZero_cohomologyClass_injective _ he)
  have hs (σ : (TopCat.toSSet.obj Y) _⦋0⦌) :
      φ.1 (chainOfSimplex R σ) = ψ.1 (chainOfSimplex R σ) := by
    let x : Y := Y.toSSetObjEquiv _ σ default
    let τ : (TopCat.toSSet.obj (TopCat.of PUnit)) _⦋0⦌ :=
      ((TopCat.of PUnit).toSSetObjEquiv _).symm (ContinuousMap.const _ PUnit.unit)
    have hi : (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const PUnit x))).app _ τ = σ := by
      apply (Y.toSSetObjEquiv _).injective
      ext t
      change Y.toSSetObjEquiv _ σ default = Y.toSSetObjEquiv _ σ t
      exact congrArg (Y.toSSetObjEquiv _ σ) (Subsingleton.elim (default : Convexity.StdSimplex ℝ (Fin 1)) t)
    have he := LinearMap.congr_fun (hp x) (chainOfSimplex R τ)
    change cochainMap R _ 0 φ.1 _ = cochainMap R _ 0 ψ.1 _ at he
    simpa only [cochainMap_apply, chainOfSimplex_map, hi] using he
  have hc : ModuleCat.ofHom φ.1 = ModuleCat.ofHom ψ.1 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have hi : ((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of R R) σ).hom a =
        a • chainOfSimplex R σ := by
      rw [chainOfSimplex, ← map_smul]
      simp
    change φ.1 (((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of R R) σ).hom a) =
      ψ.1 (((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of R R) σ).hom a)
    rw [hi, map_smul, map_smul, hs]
  exact congrArg (cohomologyClass Y 0) (Subtype.ext (congrArg ModuleCat.Hom.hom hc))

end HodgeLean.Foundations.BundleResolution
