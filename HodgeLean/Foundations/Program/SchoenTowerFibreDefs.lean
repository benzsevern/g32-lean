import HodgeLean.Foundations.Program.SchoenTowerChecks
import HodgeLean.Foundations.Program.SchoenTowerConormalDefs
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.GroupWithZero

/-! # Actual covering-fibre action and the normalized two-point model
The model retains its map to the sphere, as well as its component action.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped OnePoint
namespace HodgeLean.Foundations.Program

/-- The generator on the actual covering fibre over a centre point.
Source: G32 v0.16, Lemma 4.3, restriction of the residual generator. -/
def s2c_coveringFibreDeck {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K)
    (d : W ⟶ W) (hd : d ≫ β = β) (k : ComplexPoint K) :
    s2b_coveringFibre β j p k ⟶ s2b_coveringFibre β j p k :=
  pullback.lift
    (pullback.fst (s2b_toExceptional β j ≫ p) k ≫ s2b_preimageDeck β j d hd)
    (pullback.snd (s2b_toExceptional β j ≫ p) k)
    (by rw [Category.assoc, s2b_check_deck_base]; exact pullback.condition)

example {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K)
    (d : W ⟶ W) (hd : d ≫ β = β) (k : ComplexPoint K) :
    s2c_coveringFibreDeck β j p d hd k ≫ pullback.fst (s2b_toExceptional β j ≫ p) k =
      pullback.fst (s2b_toExceptional β j ≫ p) k ≫ s2b_preimageDeck β j d hd :=
  pullback.lift_fst _ _ _

/-- Projection of the covering fibre to the exceptional projective-line fibre.
Source: Schoen (1988), p. 18, the exceptional-preimage square. -/
def s2c_coveringFibreProjection {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K) (k : ComplexPoint K) :
    s2b_coveringFibre β j p k ⟶ pullback p k :=
  pullback.lift (pullback.fst (s2b_toExceptional β j ≫ p) k ≫ s2b_toExceptional β j)
    (pullback.snd (s2b_toExceptional β j ≫ p) k)
    (by rw [Category.assoc]; exact pullback.condition)

example {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K) (k : ComplexPoint K) :
    s2c_coveringFibreProjection β j p k ≫ pullback.fst p k =
      pullback.fst (s2b_toExceptional β j ≫ p) k ≫ s2b_toExceptional β j :=
  pullback.lift_fst _ _ _

/-- The normalized two-point fibre with gcd(m,a) sphere components.
Source: G32 v0.16, Lemma 4.3, normalization of the two-point cyclic cover. -/
abbrev s2c_twoPointFibre (m a : ℕ) := ZMod (Nat.gcd m a) × OnePoint ℂ

example : s2c_twoPointFibre 6 2 := (0, ∞)

/-- Component translation followed by complex dilation on each sphere.
Source: G32 v0.16, Lemma 4.3, normalized two-point covering action. -/
def s2c_twoPointDeck (m a : ℕ) (c : ℂ) (hc : c ≠ 0) :
    s2c_twoPointFibre m a ≃ₜ s2c_twoPointFibre m a :=
  (Homeomorph.ofDiscrete (Equiv.addRight (1 : ZMod (Nat.gcd m a)))).prodCongr
    (Homeomorph.onePointCongr (Homeomorph.mulLeft₀ c hc))

example (m a : ℕ) (c : ℂ) (hc : c ≠ 0) (i : ZMod (Nat.gcd m a)) (z : ℂ) :
    s2c_twoPointDeck m a c hc (i, (z : OnePoint ℂ)) =
      (i + 1, ((c * z : ℂ) : OnePoint ℂ)) := rfl

/-- Projection to the sphere, in normalized coordinates with degree m/gcd(m,a).
The phase factor makes the displayed generator preserve this projection.
Source: Schoen (1988), Lemma 2.5, normalized binomial equation. -/
def s2c_twoPointProjection (m a : ℕ) (c : ℂ) : s2c_twoPointFibre m a → OnePoint ℂ :=
  fun x => Option.map
    (fun z : ℂ => c ^ (-((m / Nat.gcd m a * x.1.val : ℕ) : ℤ)) *
      z ^ (m / Nat.gcd m a)) x.2

example (m a : ℕ) (c : ℂ) (i : ZMod (Nat.gcd m a)) :
    s2c_twoPointProjection m a c (i, ∞) = ∞ := rfl

/-- Analytic complex points as a functor on schemes over the complex base.
Source: the complex-point topology defined by regular-function evaluations. -/
def s2c_points : Over (Spec ↧ℂ) ⥤ TopCat where
  obj X := TopCat.of (ComplexPoint X)
  map f := TopCat.ofHom (Point.continuousMap f)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

example {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y) (x : ComplexPoint X) :
    s2c_points.map f x = Point.map f x := rfl

end HodgeLean.Foundations.Program
