import HodgeLean.Foundations.IntegralHomology.Proofs

/-! First-stage integral lattice and rational comparison specifications.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
open scoped TensorProduct
namespace HodgeLean.Foundations.IntegralHomology

/-- Coefficient extension respects the singular differential.
Source: Hatcher, Algebraic Topology, §3.A; C1a6IntegralBaseChange, zToCChainMap. -/
theorem coefficient_chainMap (X : TopCat.{0}) :
    ∃ c : ZChains X ⟶ RestrictedQChains X,
      ∀ n z, (c.f n).hom z = coefficient X n z :=
  coefficient_chainMap_aux X

example : ((Finsupp.single (0 : Fin 2) (2 : ℤ)).mapRange (Int.castRingHom ℚ) (map_zero _)) 0 = 2 := by simp

/-- Rational singular H₁ is scalar extension of integral singular H₁.
Source: Hatcher, Algebraic Topology, §3.A; C1a6IntegralBaseChange, zToCHomology_isBaseChange. -/
theorem coefficient_baseChange (X : TopCat.{0}) (c : ZChains X ⟶ RestrictedQChains X)
    (hc : ∀ n z, (c.f n).hom z = coefficient X n z) :
    IsBaseChange ℚ (coefficientH1 X c) :=
  coefficient_baseChange_aux X c hc

example : IsBaseChange ℚ (Algebra.linearMap ℤ ℚ) := IsBaseChange.linearMap ℤ ℚ

/-- Exactly the torsion classes vanish under rational coefficient extension.
Source: Hatcher, Algebraic Topology, §3.A; C1a6IntegralTorsionKernel, baseChange_zero_mem_torsion. -/
theorem coefficient_kernel (X : TopCat.{0}) (c : ZChains X ⟶ RestrictedQChains X)
    (hc : ∀ n z, (c.f n).hom z = coefficient X n z) :
    LinearMap.ker (coefficientH1 X c) = Submodule.torsion ℤ (H1 X) :=
  coefficient_kernel_aux X c hc

example : LinearMap.ker (Algebra.linearMap ℤ ℚ) = ⊥ := by
  ext x
  simp

/-- Finite generation of actual integral H₁ gives a finite free torsion quotient.
Source: Hatcher, Algebraic Topology, §3.1, finitely generated abelian groups. -/
theorem lattice_finiteFree (X : TopCat.{0}) [Module.Finite ℤ (H1 X)] :
    Module.Finite ℤ (Lattice X) ∧ Module.Free ℤ (Lattice X) :=
  lattice_finiteFree_aux X

example : Module.finrank ℤ (Fin 2 → ℤ) = 2 := by simp

/-- The actual torsion quotient is covariant and respects identities and composition.
Source: Hatcher, Algebraic Topology, §2.1 and §3.1. -/
theorem mapLattice_id_comp (X : TopCat.{0}) :
    mapLattice (𝟙 X) = LinearMap.id ∧
    ∀ (Y Z : TopCat.{0}) (f : X ⟶ Y) (g : Y ⟶ Z),
      mapLattice (f ≫ g) = (mapLattice g).comp (mapLattice f) :=
  mapLattice_id_comp_aux X

example : torsionQuotientMap (2 • LinearMap.id : ℤ →ₗ[ℤ] ℤ)
    (Submodule.Quotient.mk (3 : ℤ)) = Submodule.Quotient.mk (6 : ℤ) := rfl

/-- The actual coefficient map commutes with each continuous map.
Source: Hatcher, Algebraic Topology, §3.A, naturality of coefficient extension. -/
theorem coefficient_natural {X Y : TopCat.{0}} (f : X ⟶ Y)
    (cX : ZChains X ⟶ RestrictedQChains X)
    (cY : ZChains Y ⟶ RestrictedQChains Y)
    (hcX : ∀ n z, (cX.f n).hom z = coefficient X n z)
    (hcY : ∀ n z, (cY.f n).hom z = coefficient Y n z) (a : H1 X) :
    coefficientH1 Y cY (mapH1 f a) =
      (HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)) 1).hom (coefficientH1 X cX a) :=
  coefficient_natural_aux f cX cY hcX hcY a

example : LinearEquiv.prodComm ℚ ℚ ℚ (1, 0) = (0, 1) := rfl

/-- Rationalization of the actual torsion quotient has the specified integral normalization.
Source: Hatcher, Algebraic Topology, §3.A; Birkenhake–Lange, Complex Abelian Varieties, second edition, §2.4. -/
theorem rationalComparison (X : TopCat.{0}) (c : ZChains X ⟶ RestrictedQChains X)
    (hc : ∀ n z, (c.f n).hom z = coefficient X n z) :
    ∃ e : (ℚ ⊗[ℤ] Lattice X) ≃ₗ[ℚ] (QChains X).homology 1,
      ∀ a : H1 X, e (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice X)) =
        coefficientH1 X c a :=
  rationalComparison_aux X c hc

example : (IsBaseChange.linearMap ℤ ℚ).equiv ((1 : ℚ) ⊗ₜ[ℤ] (2 : ℤ)) = 2 := by
  rw [IsBaseChange.equiv_tmul]
  norm_num

/-- The normalized rational comparisons commute with the integral lattice maps.
Source: Hatcher, Algebraic Topology, §3.A; Birkenhake–Lange, Complex Abelian Varieties, second edition, §2.4. -/
theorem rationalComparison_natural {X Y : TopCat.{0}} (f : X ⟶ Y)
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
  rationalComparison_natural_aux f cX cY hcX hcY eX eY heX heY t

example : (2 • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)).baseChange ℚ
    ((1 : ℚ) ⊗ₜ[ℤ] (3 : ℤ)) = (1 : ℚ) ⊗ₜ[ℤ] (6 : ℤ) := by
  rw [LinearMap.baseChange_tmul]
  rfl
end HodgeLean.Foundations.IntegralHomology
