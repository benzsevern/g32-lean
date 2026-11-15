import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CoefficientBaseChange
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.RingTheory.Flat.TorsionFree

/-! Integral singular homology and its actual torsion quotient.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.IntegralHomology

/-- Integral singular chains, with the same model as the C1a6 integral bridge.
Source: Hatcher, Algebraic Topology, §2.1. -/
abbrev ZChains (X : TopCat.{0}) :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)

example : (ZChains (TopCat.of PUnit)).X 0 →ₗ[ℤ]
    (ZChains (TopCat.of PUnit)).X 0 := LinearMap.id

/-- Rational singular chains viewed as integral modules.
Source: Hatcher, Algebraic Topology, §3.A, change of coefficients. -/
abbrev RestrictedQChains (X : TopCat.{0}) :=
  ((ModuleCat.restrictScalars (algebraMap ℤ ℚ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (QChains X)

example : (RestrictedQChains (TopCat.of PUnit)).X 0 →ₗ[ℤ]
    (RestrictedQChains (TopCat.of PUnit)).X 0 := LinearMap.id

/-- Extend coefficients on each actual singular simplex.
Source: Hatcher, Algebraic Topology, §3.A; C1a6IntegralBaseChange, zToCChainGroup. -/
def coefficient (X : TopCat.{0}) (n : ℕ) :
    (ZChains X).X n →ₗ[ℤ] (QChains X).X n :=
  ((chainGroupFinsuppIso ℚ X n).symm.toLinearEquiv.restrictScalars ℤ).toLinearMap.comp
    ((Finsupp.mapRange.linearMap (Algebra.linearMap ℤ ℚ)).comp
      (chainGroupFinsuppIso ℤ X n).toLinearEquiv.toLinearMap)

example : coefficient (TopCat.of PUnit) 0 0 = 0 := map_zero _

/-- Actual integral singular H₁, without a choice of generators.
Source: Hatcher, Algebraic Topology, §2.1; C1a6IntegralDefs, integralH1. -/
abbrev H1 (X : TopCat.{0}) := (ZChains X).homology 1

example : H1 (TopCat.of PUnit) →ₗ[ℤ] H1 (TopCat.of PUnit) := LinearMap.id

/-- The torsion quotient; finite generation is a separate assumption.
Source: Hatcher, Algebraic Topology, §3.1; C1a6IntegralDefs, integralLattice. -/
abbrev Lattice (X : TopCat.{0}) := H1 X ⧸ Submodule.torsion ℤ (H1 X)

example : Lattice (TopCat.of PUnit) := 0

/-- The covariant map on actual integral singular H₁.
Source: Hatcher, Algebraic Topology, §2.1, induced homomorphisms. -/
def mapH1 {X Y : TopCat.{0}} (f : X ⟶ Y) : H1 X →ₗ[ℤ] H1 Y :=
  ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map f)).hom

example : mapH1 (𝟙 (TopCat.of PUnit)) 0 = 0 := map_zero _

private theorem torsion_map {R M N : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    Submodule.torsion R M ≤ (Submodule.torsion R N).comap f := by
  intro x hx
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
  refine (Submodule.mem_torsion_iff (f x)).mpr ⟨a, ?_⟩
  have ha' : (a : R) • x = 0 := ha
  change (a : R) • f x = 0
  rw [← map_smul, ha', map_zero]

/-- Functorial quotient map for the actual torsion submodule.
Source: Hatcher, Algebraic Topology, §3.1, torsion in abelian groups. -/
def torsionQuotientMap {R M N : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (M ⧸ Submodule.torsion R M) →ₗ[R] (N ⧸ Submodule.torsion R N) :=
  (Submodule.torsion R M).mapQ (Submodule.torsion R N) f (torsion_map f)

example (x : ℤ) : torsionQuotientMap (2 • LinearMap.id : ℤ →ₗ[ℤ] ℤ)
    (Submodule.Quotient.mk x) = Submodule.Quotient.mk (2 * x) := by
  rfl

/-- The covariant integral lattice map.
Source: Hatcher, Algebraic Topology, §2.1 and §3.1. -/
def mapLattice {X Y : TopCat.{0}} (f : X ⟶ Y) : Lattice X →ₗ[ℤ] Lattice Y :=
  torsionQuotientMap (mapH1 f)

example : mapLattice (𝟙 (TopCat.of PUnit)) 0 = 0 := map_zero _

private def intLinear {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := map_add f
  map_smul' n x := by
    convert! AddMonoidHom.map_zsmul f n x <;> ext <;> apply int_smul_eq_zsmul

/-- Coefficient extension on homology for a specified chain map.
Source: Hatcher, Algebraic Topology, §3.A; C1a6IntegralBaseChange, zToCHomology. -/
def coefficientH1 (X : TopCat.{0}) (c : ZChains X ⟶ RestrictedQChains X) :
    H1 X →ₗ[ℤ] (QChains X).homology 1 :=
  intLinear (HomologicalComplex.homologyMap c 1 ≫
    (((QChains X).sc 1).homologyData.left.map
      (ModuleCat.restrictScalars (algebraMap ℤ ℚ))).homologyIso.hom).hom.toAddMonoidHom

example (c : ZChains (TopCat.of PUnit) ⟶ RestrictedQChains (TopCat.of PUnit)) :
    coefficientH1 _ c 0 = 0 := map_zero _
end HodgeLean.Foundations.IntegralHomology
