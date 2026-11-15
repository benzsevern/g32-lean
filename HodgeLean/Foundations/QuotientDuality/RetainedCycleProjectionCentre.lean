import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionCentreParameters
import HodgeLean.Adapters.IntersectionProductMovingProjCharts
import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionValues
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension

/-! # The actual algebraic centre of a projective linear projection -/

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial TopologicalSpace
open HodgeLean.Adapters
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The common vanishing set of the actual homogeneous projection forms is Zariski closed. -/
lemma retained_projection_forms_zero_isClosed {N n : ℕ}
    (ℓ : Matrix (Fin (n+1)) (Fin (N+1)) ℂ) :
    IsClosed {x : a3m_Pn N | ∀ i, a3r_lin ℓ (MvPolynomial.X i) ∈ (a3m_projCharts N).prime x} := by
  classical
  let C := a3m_projCharts N
  have he : {x : a3m_Pn N | ∀ i, a3r_lin ℓ (MvPolynomial.X i) ∈ C.prime x}ᶜ =
      ⋃ j, ⋃ i, C.κ j '' (PrimeSpectrum.basicOpen (C.θ j (a3r_lin ℓ (MvPolynomial.X i)))).carrier := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hx
      push_neg at hx
      obtain ⟨i, hi⟩ := hx
      obtain ⟨j, p, hp⟩ := C.cover x
      refine ⟨j, i, p, ?_, hp⟩
      exact fun h => hi ((C.mem_prime_iff_of_isHomogeneous x j p hp _ 1
        (a3r_lin_X_isHomogeneous ℓ i)).mpr h)
    · rintro ⟨j, i, p, hp, hpx⟩ hall
      exact hp ((C.mem_prime_iff_of_isHomogeneous x j p hpx _ 1
        (a3r_lin_X_isHomogeneous ℓ i)).mp (hall i))
  rw [← isOpen_compl_iff, he]
  exact isOpen_iUnion fun j => isOpen_iUnion fun i =>
    (C.κ j).isOpenEmbedding.isOpenMap _ PrimeSpectrum.isOpen_basicOpen

end HodgeLean.Foundations.QuotientDuality


/-! The algebraic centre of an actual linear projection. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

/-- Homogeneous nonvanishing is open in an actual projective chart atlas.
Source: Hartshorne, Algebraic Geometry, II.2. -/
lemma retained_chart_homogeneous_nonvanishing_open
    {Y : Scheme.{0}} {σ : Type} [Fintype σ] (C : a3m_SpecCharts Y σ ℂ)
    (p : MvPolynomial σ ℂ) (d : ℕ) (hp : p.IsHomogeneous d) :
    IsOpen {y : Y | p ∉ C.prime y} := by
  have he : {y : Y | p ∉ C.prime y} =
      ⋃ j, (C.κ j) '' {x : Spec (C.T j) | C.θ j p ∉ x.asIdeal} := by
    ext y
    constructor
    · intro hy
      obtain ⟨j, x, hx⟩ := C.cover y
      exact Set.mem_iUnion.mpr ⟨j, x,
        (not_congr (C.mem_prime_iff_of_isHomogeneous y j x hx p d hp)).mp hy, hx⟩
    · intro hy
      obtain ⟨j, x, hx, rfl⟩ := Set.mem_iUnion.mp hy
      exact (not_congr (C.mem_prime_iff_of_isHomogeneous _ j x rfl p d hp)).mpr hx
  rw [he]
  apply isOpen_iUnion
  intro j
  exact (C.κ j).isOpenEmbedding.isOpenMap _ PrimeSpectrum.isOpen_basicOpen

/-- The actual algebraic centre is the common zero locus of the retained linear forms. -/
def retained_projection_centre {N d : ℕ}
    (ℓ : Matrix (Fin (d+1)) (Fin (N+1)) ℂ) : Closeds (a3m_Pn N) :=
  ⟨{y | ∀ i, a3r_lin ℓ (MvPolynomial.X i) ∈ (a3m_projCharts N).prime y}, by
    apply isOpen_compl_iff.mp
    have he : {y : a3m_Pn N | ∀ i, a3r_lin ℓ (MvPolynomial.X i) ∈
        (a3m_projCharts N).prime y}ᶜ =
        ⋃ i, {y | a3r_lin ℓ (MvPolynomial.X i) ∉ (a3m_projCharts N).prime y} := by
      ext y
      simp
    rw [he]
    exact isOpen_iUnion fun i => retained_chart_homogeneous_nonvanishing_open
      (a3m_projCharts N) _ 1 (a3r_lin_X_isHomogeneous ℓ i)⟩

end HodgeLean.Foundations.QuotientDuality
