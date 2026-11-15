import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs
import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers

/-! # Retained tower maps and collected orbit coefficients

The maps are compositions of the retained normalization transitions.
Coefficients are evaluated after geometric pushforward and collection.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The total modification with its retained endpoint identifications.
Source: Schoen, On the Hodge conjecture for products of curves, section 2, pp. 15–18.
HC no distance; AV milestone no distance. -/
def retainedCycleModification {r : ℕ} (N : Fin (r + 1) → Over (Spec ↧ℂ))
    {W W₀ : Over (Spec ↧ℂ)} (e₀ : N 0 ≅ W₀) (e : N (Fin.last r) ≅ W)
    (w : ∀ i : Fin r, N i.succ ⟶ N i.castSucc) : W ⟶ W₀ :=
  e.inv ≫ s2e_towerTotalMap N e₀.hom w (Fin.last r)

example (X : Over (Spec ↧ℂ)) : retainedCycleModification
    (fun _ : Fin 1 => X) (Iso.refl X) (Iso.refl X) (fun i : Fin 0 => Fin.elim0 i) =
      𝟙 X := by simp [retainedCycleModification, s2e_towerTotalMap]

/-- The actual collected coefficient at a target prime, retaining residue degrees.
Source: Fulton, Intersection Theory, second edition, section 1.4.
HC no distance; AV milestone no distance. -/
def retainedOrbitCoefficient {Q W W₀ : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (φ : W ⟶ W₀) [QuasiCompact φ.left] (ι : Q ⟶ W) (δ : W ⟶ W) (m : ℕ)
    (a : Fin m → ℚ) (y : W₀.left) : ℚ :=
  a1p_pushforward φ.left (s2e_rationalOrbitCycle ι δ m a) y

example {Q W W₀ : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (φ : W ⟶ W₀) [QuasiCompact φ.left] (ι : Q ⟶ W) (δ : W ⟶ W) (y : W₀.left) :
    retainedOrbitCoefficient φ ι δ 0 (fun i => Fin.elim0 i) y = 0 := by
  simp [retainedOrbitCoefficient, s2e_rationalOrbitCycle, a1p_pushforward,
    Function.locallyFinsupp.map]

/-- The reduced component as a scheme over the original complex base.
Source: Fulton, Intersection Theory, section 1.3.
HC no distance; AV milestone no distance. -/
abbrev intrinsicComponent (X : Over (Spec ↧ℂ)) (x : X.left) : Over (Spec ↧ℂ) :=
  Over.mk (cycleComponentι X.left x ≫ X.hom)

example (X : Over (Spec ↧ℂ)) (x : X.left) :
    (intrinsicComponent X x).left = cycleComponent X.left x := rfl

/-- Reduced components inherit the specified projective presentation.
Source: Hartshorne, Algebraic Geometry, II.4, composition of projective morphisms.
HC no distance; AV milestone no distance. -/
instance intrinsicComponentProjective (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (x : X.left) : IsProjective (intrinsicComponent X x).hom := by
  rcases ‹IsProjective X.hom›.nonempty_presentation with ⟨P⟩
  exact ⟨⟨{ ambientDimension := P.ambientDimension
            immersion := cycleComponentι X.left x ≫ P.immersion
            isClosedImmersion := by
              letI := P.isClosedImmersion
              infer_instance
            immersion_toBase := by
              rw [Category.assoc, P.immersion_toBase]
              rfl }⟩⟩

example (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (x : X.left) :
    IsProjective (intrinsicComponent X x).hom := inferInstance

/-- The component inclusion retains its actual scheme arrow.
Source: Fulton, Intersection Theory, section 1.3.
HC no distance; AV milestone no distance. -/
def intrinsicComponentInclusion (X : Over (Spec ↧ℂ)) (x : X.left) :
    intrinsicComponent X x ⟶ X := Over.homMk (cycleComponentι X.left x)

example (X : Over (Spec ↧ℂ)) (x : X.left) :
    (intrinsicComponentInclusion X x).left = cycleComponentι X.left x := rfl

/-- The retained comparison map on an actual inverse-image open.
Source: Hatcher, Algebraic Topology, section 3.1, maps of pairs.
HC no distance; AV milestone no distance. -/
def retainedOpenMap {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    (V : TopologicalSpace.Opens (ComplexPoint Y)) :
    (Point.map f ⁻¹' (V : Set (ComplexPoint Y))) → V :=
  fun z => ⟨Point.map f z, z.2⟩

example {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    (V : TopologicalSpace.Opens (ComplexPoint Y)) (z : Point.map f ⁻¹' (V : Set _)) :
    (retainedOpenMap f V z).val = Point.map f z.val := rfl

/-- Specified retained local transport is inverse pullback followed by support enlargement.
It uses the literal retained map on a comparison open where that map is an isomorphism.
Source: Hatcher, Algebraic Topology, section 3.1, maps of pairs.
HC no distance; AV milestone no distance. -/
def retainedLocalTransport {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    (S : Set (ComplexPoint X)) (T : Set (ComplexPoint Y))
    (himage : Point.map f '' S ⊆ T)
    (V : TopologicalSpace.Opens (ComplexPoint Y))
    (hV : IsHomeomorph (retainedOpenMap f V)) (n : ℕ) :
    CohomologyWithSupport ℚ (TopCat.of (Point.map f ⁻¹' (V : Set _)))
        (Subtype.val ⁻¹' S) n →ₗ[ℚ]
      CohomologyWithSupport ℚ (TopCat.of V) (Subtype.val ⁻¹' T) n := by
  let XU : TopCat.{0} := TopCat.of (Point.map f ⁻¹' (V : Set (ComplexPoint Y)))
  let YU : TopCat.{0} := TopCat.of V
  let e : XU ≃ₜ YU := hV.homeomorph (retainedOpenMap f V)
  let h : e.symm ⁻¹' (Subtype.val ⁻¹' S) ⊆ (Subtype.val ⁻¹' T : Set YU) := by
    intro y hy
    have he : Point.map f (e.symm y).val = y.val :=
      congrArg Subtype.val (e.apply_symm_apply y)
    change y.val ∈ T
    rw [← he]
    exact himage ⟨(e.symm y).val, hy, rfl⟩
  exact (enlargeSupport ℚ YU h n).comp
    (supportHomeomorphTransfer (X := XU) (Y := YU) e (Subtype.val ⁻¹' S) n)

example {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    (S : Set (ComplexPoint X)) (T : Set (ComplexPoint Y))
    (h : Point.map f '' S ⊆ T) (V : TopologicalSpace.Opens (ComplexPoint Y))
    (hV : IsHomeomorph (retainedOpenMap f V)) (n : ℕ) :
    retainedLocalTransport f S T h V hV n 0 = 0 := map_zero _

end HodgeLean.Foundations.QuotientDuality
