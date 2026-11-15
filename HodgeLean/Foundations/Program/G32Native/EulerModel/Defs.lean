import HodgeLean.Foundations.Program.SchoenCyclePushDefs

/-! # Canonical orbit constructions
Actual scheme maps, hyperplane ideals and finite coefficient combinations are retained.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified translate of a component immersion.
Source: Schoen (1988), printed p. 13, translated canonical components.
HC no distance; AV milestone no distance. -/
def orbitImmersion {Q W : Over (Spec ↧ℂ)} (ι : Q ⟶ W) (d : W ⟶ W) (t : ℕ) : Q ⟶ W :=
  ι ≫ (End.of d ^ t).asHom

example (Q : Over (Spec ↧ℂ)) : orbitImmersion (𝟙 Q) (𝟙 Q) 1 = 𝟙 Q := by
  simp [orbitImmersion]

/-- The coordinate hyperplane on the specified projective component, with its actual ideal.
Source: Hartshorne, Algebraic Geometry, II.7; Schoen (1988), Lemma 2.6.
HC no distance; AV milestone no distance. -/
def coordinateHyperplane {Q : Over (Spec ↧ℂ)} {k : ℕ}
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :
    Q.left.IdealSheafData := (s2e_hyperplaneIdeal k).comap eQ.hom.left

example (k : ℕ) : coordinateHyperplane (Iso.refl
    (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))) = s2e_hyperplaneIdeal k := by
  simp [coordinateHyperplane]

/-- Finite rational combinations of a specified linear orbit.
Source: Schoen (1988), Theorem 2.0, rational orbit coefficients.
HC no distance; AV milestone no distance. -/
def rationalOrbit {V : Type*} [AddCommGroup V] [Module ℚ V]
    (T : Module.End ℚ V) (m : ℕ) (a : Fin m → ℚ) (v : V) : V :=
  ∑ t : Fin m, a t • (T ^ t.val) v

example : rationalOrbit (LinearMap.id : Module.End ℚ ℚ) 1 (fun _ => (3 : ℚ)) 2 = 6 := by
  norm_num [rationalOrbit, Fin.sum_univ_one]

/-- Inverse-power character combination, matching the cohomological variance in U2.
Source: Schoen (1988), Lemma 2.6, primitive character projection.
HC no distance; AV milestone no distance. -/
def primitiveOrbit {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (T : Module.End R V) (m : ℕ) (χ : ZMod m → R) (v : V) : V :=
  s2e_weightedSum m χ (fun t : Fin m => (T ^ (m - t.val)) v)

example : primitiveOrbit (LinearMap.id : Module.End ℚ ℚ) 1 (fun _ => (2 : ℚ)) 3 = 6 := by
  norm_num [primitiveOrbit, s2e_weightedSum, Fin.sum_univ_one]

end HodgeLean.Foundations.Program.G32Native.EulerModel
