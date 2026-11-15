import HodgeLean.Foundations.Program.SchoenCycleClassDefs
import HodgeLean.Foundations.Program.SchoenCycleStageDefs
import HodgeLean.Adapters.NormalConeB4Defs
import HodgeLean.Foundations.Singular.Cup
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff

/-! # Hyperplane and normal self-intersection classes
These are scheme ideals and operations on actual singular cohomology.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The reduced coordinate hyperplane X₀ = 0 in projective space.
Source: Hartshorne, II.2; Schoen (1988), Lemma 2.6. -/
def s2e_hyperplaneIdeal (k : ℕ) :
    (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨(AlgebraicGeometry.ComplexProjectiveSpace.projectiveSpaceBasicOpen k
      (MvPolynomial.X 0)).carrierᶜ,
      (AlgebraicGeometry.ComplexProjectiveSpace.projectiveSpaceBasicOpen k
        (MvPolynomial.X 0)).isOpen.isClosed_compl⟩

example (k : ℕ) : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).IdealSheafData :=
  s2e_hyperplaneIdeal k

/-- Pullback on singular cohomology of complex points, including singular schemes.
Source: Hatcher, Algebraic Topology, §3.1; Schoen (1988), p. 18. -/
def s2e_pullback (R : Type) [CommRing R] {X Y : Over (Spec ↧ℂ)}
    (f : X ⟶ Y) (n : ℕ) :=
  AlgebraicTopology.Singular.cohomologyMap R n (TopCat.ofHom (Point.continuousMap f))

example {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y) (n : ℕ) :
    s2e_pullback ℚ f n 0 = 0 := map_zero _

/-- Powers of a degree-two class using the Alexander–Whitney cup product.
Source: Hatcher, §3.2; Schoen (1988), Lemma 2.6, H^(h/2). -/
def s2e_hyperplanePower (X : TopCat) (H : AlgebraicTopology.Singular.Cohomology ℚ X 2) :
    (k : ℕ) → AlgebraicTopology.Singular.Cohomology ℚ X (2 * k)
  | 0 => HodgeLean.Foundations.Singular.unit X
  | k + 1 => HodgeLean.Foundations.Singular.cup X (by omega) H (s2e_hyperplanePower X H k)

example (X : TopCat) (H : AlgebraicTopology.Singular.Cohomology ℚ X 2) :
    s2e_hyperplanePower X H 0 = HodgeLean.Foundations.Singular.unit X := rfl

/-- Self-intersection of the immersion, represented by its supported class.
For a normalized Thom class this is the Euler class of the complex normal
bundle, hence its top Chern class.
Source: Fulton, Intersection Theory, §6.3; Schoen (1988), pp. 15–16. -/
def s2e_normalEuler {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (k : ℕ)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k) :=
  s2e_pullback ℚ ι (2 * k) (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c)

example {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left] (ι : Q ⟶ W) (k : ℕ) :
    s2e_normalEuler ι k 0 = 0 := by
  simp only [s2e_normalEuler, map_zero]

end HodgeLean.Foundations.Program
