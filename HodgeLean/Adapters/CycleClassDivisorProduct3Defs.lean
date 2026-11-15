import HodgeLean.Adapters.CycleClassDivisorProduct2
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-! # Relative cup cochains and their cohomology models
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Adapters

/-- The dual small relative short complex, with cycles and boundaries explicit.
Source: Spanier, Algebraic Topology, chapter 5, cohomology of relative cochains. -/
abbrev ccm15_smallDual (Y : TopCat.{0}) (S T : Set Y) (n : ℕ) :=
  ((ccm14_smallRelativeComplex Y S T).sc n).linearDual

/-- The dual genuine relative short complex.
Source: Spanier, Algebraic Topology, chapter 5, relative cohomology. -/
abbrev ccm15_relativeDual (Y : TopCat.{0}) (S : Set Y) (n : ℕ) :=
  (((relativeChainFunctor ℚ).obj (TopPair.ofSubset Sᶜ)).sc n).linearDual

/-- The factorization defining the descended cochain.
Source: Hatcher, Algebraic Topology, §3.2, relative cup construction. -/
theorem ccm15_smallCup_projection (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ)
    (u : RelativeCochain ℚ (TopPair.ofSubset Sᶜ) p)
    (v : RelativeCochain ℚ (TopPair.ofSubset Tᶜ) q) :
    (ccm14_smallRelativeCup Y S T p q u v).comp
      ((ccm14_smallProjection Y S T).f (p + q)).hom =
        ccm13_relativeCupLift Y S T p q u v := by
  exact congrArg ModuleCat.Hom.hom
    ((Cofork.IsColimit.π_desc (ccm14_projectionIsCokernel Y S T (p + q))).trans
      (CokernelCofork.π_ofπ _ _ _))

private theorem ccm15_small_ext (Y : TopCat.{0}) (S T : Set Y) (n : ℕ)
    (f g : ccm14_smallRelativeCochain Y S T n)
    (h : f.comp ((ccm14_smallProjection Y S T).f n).hom =
      g.comp ((ccm14_smallProjection Y S T).f n).hom) : f = g := by
  have he := Cofork.IsColimit.hom_ext (ccm14_projectionIsCokernel Y S T n)
    (show (ccm14_smallProjection Y S T).f n ≫ ModuleCat.ofHom f =
      (ccm14_smallProjection Y S T).f n ≫ ModuleCat.ofHom g from ModuleCat.hom_ext h)
  exact congrArg ModuleCat.Hom.hom he

/-- Bilinear packaging of the actual descended Alexander–Whitney functional.
Source: Hatcher, Algebraic Topology, §3.2, bilinearity of cup products. -/
def ccm15_smallCupLinear (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ) :
    RelativeCochain ℚ (TopPair.ofSubset Sᶜ) p →ₗ[ℚ]
      RelativeCochain ℚ (TopPair.ofSubset Tᶜ) q →ₗ[ℚ]
        ccm14_smallRelativeCochain Y S T (p + q) where
  toFun u :=
    { toFun := ccm14_smallRelativeCup Y S T p q u
      map_add' := by
        intro v w
        apply ccm15_small_ext
        simp only [LinearMap.add_comp, ccm15_smallCup_projection]
        simp [ccm13_relativeCupLift]
      map_smul' := by
        intro a v
        apply ccm15_small_ext
        simp only [LinearMap.smul_comp, ccm15_smallCup_projection]
        simp [ccm13_relativeCupLift] }
  map_add' := by
    intro u v
    ext w : 1
    change ccm14_smallRelativeCup Y S T p q (u + v) w =
      ccm14_smallRelativeCup Y S T p q u w + ccm14_smallRelativeCup Y S T p q v w
    apply ccm15_small_ext
    simp only [LinearMap.add_apply, LinearMap.add_comp, ccm15_smallCup_projection]
    simp [ccm13_relativeCupLift]
  map_smul' := by
    intro a u
    ext v : 1
    change ccm14_smallRelativeCup Y S T p q (a • u) v =
      a • ccm14_smallRelativeCup Y S T p q u v
    apply ccm15_small_ext
    simp only [LinearMap.smul_apply, LinearMap.smul_comp, ccm15_smallCup_projection,
      RingHom.id_apply]
    simp [ccm13_relativeCupLift]

/-- Source: the two-point characteristic cochains retain the descended product. -/
example : ccm15_smallCupLinear ccm14_twoPoints {true} {true} 0 0
    ccm14_nonzeroInput ccm14_nonzeroInput =
      ccm14_smallRelativeCup ccm14_twoPoints {true} {true} 0 0
        ccm14_nonzeroInput ccm14_nonzeroInput := rfl

end HodgeLean.Adapters
