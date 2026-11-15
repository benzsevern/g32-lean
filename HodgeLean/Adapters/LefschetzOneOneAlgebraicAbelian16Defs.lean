import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian14

/-! # Carriers and linear extension for compatible singular cones

These definitions contain data only. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory Limits AlgebraicTopology.Singular
open scoped Simplicial
namespace HodgeLean.Adapters

/-- Singular simplices with their existing simplicial-set carrier.
Source: Hatcher, Algebraic Topology, §2.1; `TopCat.toSSet`. -/
abbrev bh16_simplex (X : TopCat.{0}) (k : ℕ) := (TopCat.toSSet.obj X) _⦋k⦌

/-- The indexed face of a singular simplex.
Source: Hatcher, Algebraic Topology, §2.1; `SimplicialObject.δ`. -/
def bh16_face (X : TopCat.{0}) (k : ℕ) (i : Fin (k + 2))
    (σ : bh16_simplex X (k + 1)) : bh16_simplex X k :=
  (TopCat.toSSet.obj X).δ i σ

/-- A constant singular simplex at a specified point.
Source: Hatcher, Algebraic Topology, §2.1; `TopCat.toSSetObjEquiv`. -/
def bh16_const (X : TopCat.{0}) (k : ℕ) (p : X) : bh16_simplex X k :=
  (TopCat.toSSetObjEquiv X _).symm (ContinuousMap.const _ p)

/-- Include one rational coefficient on a specified singular simplex.
Source: Hatcher, Algebraic Topology, §2.1; `SSet.ιChainComplex`. -/
def bh16_generator (X : TopCat.{0}) (k : ℕ) (σ : bh16_simplex X k) :
    ℚ →ₗ[ℚ] (SingularChainComplex ℚ X).X k :=
  ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom

example : bh16_generator (TopCat.of (Fin 0 → ℂ)) 0 (bh16_const _ 0 0) 0 = 0 :=
  map_zero _

/-- Rational linear extension of a chosen simplex cone, using the actual coproduct.
Source: Hatcher, Algebraic Topology, §2.1 (free singular chains); `Sigma.desc`. -/
def bh16_linearCone (X : TopCat.{0}) (k : ℕ)
    (s : bh16_simplex X k → bh16_simplex X (k + 1)) :
    (SingularChainComplex ℚ X).X k →ₗ[ℚ] (SingularChainComplex ℚ X).X (k + 1) :=
  (Sigma.desc (fun σ ↦ (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ)
    (s σ))).hom

/-- Sum of the rational coefficients of a singular zero-chain.
Source: Hatcher, Algebraic Topology, §2.1 (augmentation and reduced homology). -/
def bh16_augmentation (X : TopCat.{0}) :
    (SingularChainComplex ℚ X).X 0 →ₗ[ℚ] ℚ :=
  (Sigma.desc (fun _ : bh16_simplex X 0 ↦ 𝟙 (ModuleCat.of ℚ ℚ))).hom

example : bh16_augmentation (TopCat.of (Fin 0 → ℂ)) 0 = 0 := map_zero _

example : Nonempty (bh16_simplex (TopCat.of (Fin 0 → ℂ)) 2) :=
  ⟨bh16_const _ 2 0⟩

example : bh16_face (TopCat.of (Fin 0 → ℂ)) 0 0 (bh16_const _ 1 0) =
    bh16_const _ 0 0 := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext x i
  exact Fin.elim0 i

example : bh16_const (TopCat.of (Fin 0 → ℂ)) 0 0 = bh16_const _ 0 0 := rfl

example : bh16_linearCone (TopCat.of (Fin 0 → ℂ)) 0
    (fun _ ↦ bh16_const _ 1 0) 0 = 0 := map_zero _

end HodgeLean.Adapters
