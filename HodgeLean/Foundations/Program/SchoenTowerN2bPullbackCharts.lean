import HodgeLean.Foundations.SegreProjective

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The source chart pulled back from a specified standard projective chart.
Source: Hartshorne, Algebraic Geometry, II.2.5. -/
def n2b_pullbackChart {X : Scheme.{0}} {n : ℕ} (ψ : X ⟶ g3c_P n)
    (i : Fin (n + 1)) : Scheme.{0} := pullback ψ (g3c_chartι n i)

/-- The actual inclusion of a pulled-back projective chart.
Source: Hartshorne, Algebraic Geometry, II.2.5. -/
def n2b_pullbackChartι {X : Scheme.{0}} {n : ℕ} (ψ : X ⟶ g3c_P n)
    (i : Fin (n + 1)) : n2b_pullbackChart ψ i ⟶ X := pullback.fst _ _

/-- The normalized coordinate on a pulled-back standard chart.
Source: Hartshorne, Algebraic Geometry, II.2.5. -/
def n2b_pullbackChartCoord {X : Scheme.{0}} {n : ℕ} (ψ : X ⟶ g3c_P n)
    (i j : Fin (n + 1)) : Γ(n2b_pullbackChart ψ i, ⊤) :=
  (pullback.snd ψ (g3c_chartι n i)).appTop.hom
    ((Scheme.ΓSpecIso _).inv.hom (chartCoordinate i j))

theorem n2b_pullbackChartCoord_self {X : Scheme.{0}} {n : ℕ}
    (ψ : X ⟶ g3c_P n) (i : Fin (n + 1)) :
    n2b_pullbackChartCoord ψ i i = 1 := by
  unfold n2b_pullbackChartCoord
  rw [chartCoordinate_self]
  exact _root_.map_one ((pullback.snd ψ (g3c_chartι n i)).appTop.hom.comp
    (Scheme.ΓSpecIso _).inv.hom)

instance {X : Scheme.{0}} {n : ℕ} (ψ : X ⟶ g3c_P n) (i : Fin (n + 1)) :
    IsOpenImmersion (n2b_pullbackChartι ψ i) := by
  dsimp only [n2b_pullbackChartι]
  infer_instance

/-- The overlap with another pulled-back chart is the principal open of its normalized coordinate. -/
theorem n2b_pullbackChart_preimage_chart {X : Scheme.{0}} {n : ℕ}
    (ψ : X ⟶ g3c_P n) (i j : Fin (n + 1)) :
    n2b_pullbackChartι ψ i ⁻¹ᵁ (n2b_pullbackChartι ψ j).opensRange =
      (n2b_pullbackChart ψ i).basicOpen (n2b_pullbackChartCoord ψ i j) := by
  change pullback.fst ψ (g3c_chartι n i) ⁻¹ᵁ
    (pullback.fst ψ (g3c_chartι n j)).opensRange = _
  rw [Scheme.Hom.opensRange_pullbackFst, ← Scheme.Hom.comp_preimage,
    pullback.condition, Scheme.Hom.comp_preimage,
    g3c_chartι_preimage_opensRange, Scheme.preimage_basicOpen_top]
  rfl

/-- A nonempty actual chart in an integral source is integral.
Source: Hartshorne, Algebraic Geometry, II.3. -/
instance {X : Scheme.{0}} [IsIntegral X] {n : ℕ}
    (ψ : X ⟶ g3c_P n) (i : Fin (n + 1)) [Nonempty (n2b_pullbackChart ψ i)] :
    IsIntegral (n2b_pullbackChart ψ i) :=
  isIntegral_of_isOpenImmersion (n2b_pullbackChartι ψ i)

/-- An affine source morphism has affine actual projective charts.
Source: Hartshorne, Algebraic Geometry, II.3, affine morphisms and affine base change. -/
instance {X : Scheme.{0}} {n : ℕ} (ψ : X ⟶ g3c_P n) [IsAffineHom ψ]
    (i : Fin (n + 1)) : IsAffine (n2b_pullbackChart ψ i) := by
  dsimp only [n2b_pullbackChart]
  exact isAffine_of_isAffineHom (pullback.snd ψ (g3c_chartι n i))

end HodgeLean.Foundations.Program
