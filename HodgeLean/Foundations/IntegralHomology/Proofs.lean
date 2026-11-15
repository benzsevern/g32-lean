import HodgeLean.Foundations.IntegralHomology.CoefficientConstruction
import HodgeLean.Foundations.IntegralHomology.TorsionKernel
import Mathlib.LinearAlgebra.FreeModule.PID
import HodgeLean.Foundations.IntegralHomology.Naturality
import HodgeLean.Foundations.IntegralHomology.QuotientBaseChange

/-! First-stage integral lattice and rational comparison specifications.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
open scoped TensorProduct
namespace HodgeLean.Foundations.IntegralHomology

private theorem finiteFree_torsionQuotient (R M : Type) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Finite R (M ⧸ Submodule.torsion R M) ∧
      Module.Free R (M ⧸ Submodule.torsion R M) := by
  exact ⟨inferInstance, inferInstance⟩

/-- Coefficient extension respects the singular differential.
Source: Hatcher, Algebraic Topology, §3.A; C1a6IntegralBaseChange, zToCChainMap. -/
theorem coefficient_chainMap_aux (X : TopCat.{0}) :
    ∃ c : ZChains X ⟶ RestrictedQChains X,
      ∀ n z, (c.f n).hom z = coefficient X n z :=
  by
    exact ⟨rational_zToQChainMap X, fun _ _ => rfl⟩

example : ((Finsupp.single (0 : Fin 2) (2 : ℤ)).mapRange (Int.castRingHom ℚ) (map_zero _)) 0 = 2 := by simp

/-- Rational singular H₁ is scalar extension of integral singular H₁.
Source: Hatcher, Algebraic Topology, §3.A; C1a6IntegralBaseChange, zToCHomology_isBaseChange. -/
theorem coefficient_baseChange_aux (X : TopCat.{0}) (c : ZChains X ⟶ RestrictedQChains X)
    (hc : ∀ n z, (c.f n).hom z = coefficient X n z) :
    IsBaseChange ℚ (coefficientH1 X c) :=
  by
    have h : c = rational_zToQChainMap X := by
      ext n z
      exact hc n z
    subst c
    exact rational_zToQHomology_isBaseChange X 1

example : IsBaseChange ℚ (Algebra.linearMap ℤ ℚ) := IsBaseChange.linearMap ℤ ℚ

/-- Exactly the torsion classes vanish under rational coefficient extension.
Source: Hatcher, Algebraic Topology, §3.A; C1a6IntegralTorsionKernel, baseChange_zero_mem_torsion. -/
theorem coefficient_kernel_aux (X : TopCat.{0}) (c : ZChains X ⟶ RestrictedQChains X)
    (hc : ∀ n z, (c.f n).hom z = coefficient X n z) :
    LinearMap.ker (coefficientH1 X c) = Submodule.torsion ℤ (H1 X) :=
  by
    ext a
    constructor
    · intro ha
      exact baseChange_zero_mem_torsion _ (coefficient_baseChange_aux X c hc) a ha
    · exact fun ha => torsion_le_ker_field (S := ℚ) (coefficientH1 X c) ha


example : LinearMap.ker (Algebra.linearMap ℤ ℚ) = ⊥ := by
  ext x
  simp

/-- Finite generation of actual integral H₁ gives a finite free torsion quotient.
Source: Hatcher, Algebraic Topology, §3.1, finitely generated abelian groups. -/
theorem lattice_finiteFree_aux (X : TopCat.{0}) [Module.Finite ℤ (H1 X)] :
    Module.Finite ℤ (Lattice X) ∧ Module.Free ℤ (Lattice X) :=
  by
    have hmod : (Submodule.Quotient.module (Submodule.torsion ℤ (H1 X)) :
        Module ℤ (Lattice X)) = AddCommGroup.toIntModule (Lattice X) :=
      Subsingleton.elim _ _
    rw [← hmod]
    exact finiteFree_torsionQuotient ℤ (H1 X)


example : Module.finrank ℤ (Fin 2 → ℤ) = 2 := by simp

/-- The actual torsion quotient is covariant and respects identities and composition.
Source: Hatcher, Algebraic Topology, §2.1 and §3.1. -/
theorem mapLattice_id_comp_aux (X : TopCat.{0}) :
    mapLattice (𝟙 X) = LinearMap.id ∧
    ∀ (Y Z : TopCat.{0}) (f : X ⟶ Y) (g : Y ⟶ Z),
      mapLattice (f ≫ g) = (mapLattice g).comp (mapLattice f) :=
  by
    constructor
    · ext a
      refine Quotient.inductionOn' a ?_
      intro a
      change Submodule.Quotient.mk (mapH1 (𝟙 X) a) = Submodule.Quotient.mk a
      have h := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ) |>.map_id X
      exact congrArg Submodule.Quotient.mk
        (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) a)
    · intro Y Z f g
      ext a
      refine Quotient.inductionOn' a ?_
      intro a
      change Submodule.Quotient.mk (mapH1 (f ≫ g) a) =
        Submodule.Quotient.mk (mapH1 g (mapH1 f a))
      have h := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ) |>.map_comp f g
      exact congrArg Submodule.Quotient.mk
        (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) a)

example : torsionQuotientMap (2 • LinearMap.id : ℤ →ₗ[ℤ] ℤ)
    (Submodule.Quotient.mk (3 : ℤ)) = Submodule.Quotient.mk (6 : ℤ) := rfl

/-- The actual coefficient map commutes with each continuous map.
Source: Hatcher, Algebraic Topology, §3.A, naturality of coefficient extension. -/
theorem coefficient_natural_aux {X Y : TopCat.{0}} (f : X ⟶ Y)
    (cX : ZChains X ⟶ RestrictedQChains X)
    (cY : ZChains Y ⟶ RestrictedQChains Y)
    (hcX : ∀ n z, (cX.f n).hom z = coefficient X n z)
    (hcY : ∀ n z, (cY.f n).hom z = coefficient Y n z) (a : H1 X) :
    coefficientH1 Y cY (mapH1 f a) =
      (HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)) 1).hom (coefficientH1 X cX a) :=
  by
    let z := SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)
    let q := SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)
    have h := congrArg (fun k => HomologicalComplex.homologyMap k 1)
      (coefficient_chain_naturality f cX cY hcX hcY)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
    have h' := congrArg (fun k => k ≫ (rational_restrictedQChainsModelHomologyIso Y 1).hom) h
    simp only [Category.assoc] at h'
    rw [restricted_homology_naturality q 1] at h'
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h') a

example : LinearEquiv.prodComm ℚ ℚ ℚ (1, 0) = (0, 1) := rfl

/-- Rationalization of the actual torsion quotient has the specified integral normalization.
Source: Hatcher, Algebraic Topology, §3.A; Birkenhake–Lange, Complex Abelian Varieties, second edition, §2.4. -/
theorem rationalComparison_aux (X : TopCat.{0}) (c : ZChains X ⟶ RestrictedQChains X)
    (hc : ∀ n z, (c.f n).hom z = coefficient X n z) :
    ∃ e : (ℚ ⊗[ℤ] Lattice X) ≃ₗ[ℚ] (QChains X).homology 1,
      ∀ a : H1 X, e (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice X)) =
        coefficientH1 X c a :=
  by
    have hmod : (Submodule.Quotient.module (Submodule.torsion ℤ (H1 X)) :
        Module ℤ (Lattice X)) = AddCommGroup.toIntModule (Lattice X) :=
      Subsingleton.elim _ _
    rw [← hmod]
    exact quotient_baseChange_equiv (coefficientH1 X c)
      (coefficient_baseChange_aux X c hc) (Submodule.torsion ℤ (H1 X))
      (coefficient_kernel_aux X c hc).ge

example : (IsBaseChange.linearMap ℤ ℚ).equiv ((1 : ℚ) ⊗ₜ[ℤ] (2 : ℤ)) = 2 := by
  rw [IsBaseChange.equiv_tmul]
  norm_num

/-- The normalized rational comparisons commute with the integral lattice maps.
Source: Hatcher, Algebraic Topology, §3.A; Birkenhake–Lange, Complex Abelian Varieties, second edition, §2.4. -/
theorem rationalComparison_natural_aux {X Y : TopCat.{0}} (f : X ⟶ Y)
    (cX : ZChains X ⟶ RestrictedQChains X)
    (cY : ZChains Y ⟶ RestrictedQChains Y)
    (hcX : ∀ n z, (cX.f n).hom z = coefficient X n z)
    (hcY : ∀ n z, (cY.f n).hom z = coefficient Y n z)
    (eX : (ℚ ⊗[ℤ] Lattice X) ≃ₗ[ℚ] (QChains X).homology 1)
    (eY : (ℚ ⊗[ℤ] Lattice Y) ≃ₗ[ℚ] (QChains Y).homology 1)
    (heX : ∀ a : H1 X, eX (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice X)) = coefficientH1 X cX a)
    (heY : ∀ a : H1 Y, eY (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice Y)) = coefficientH1 Y cY a)
    (t : ℚ ⊗[ℤ] Lattice X) :
    eY ((mapLattice f).baseChange ℚ t) =
      (HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)) 1).hom (eX t) :=
  by
    have h : eY.toLinearMap.comp ((mapLattice f).baseChange ℚ) =
        (HomologicalComplex.homologyMap (SSet.chainComplexMap
          (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)) 1).hom.comp eX.toLinearMap := by
      ext a
      refine Quotient.inductionOn' a ?_
      intro a
      change eY ((1 : ℚ) ⊗ₜ[ℤ] (Submodule.Quotient.mk (mapH1 f a) : Lattice Y)) =
        (HomologicalComplex.homologyMap (SSet.chainComplexMap
          (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)) 1).hom
            (eX ((1 : ℚ) ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice X)))
      rw [heY, heX]
      exact coefficient_natural_aux f cX cY hcX hcY a
    exact DFunLike.congr_fun h t

example : (2 • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)).baseChange ℚ
    ((1 : ℚ) ⊗ₜ[ℤ] (3 : ℤ)) = (1 : ℚ) ⊗ₜ[ℤ] (6 : ℤ) := by
  rw [LinearMap.baseChange_tmul]
  rfl
end HodgeLean.Foundations.IntegralHomology
