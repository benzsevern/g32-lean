import HodgeLean.Foundations.QuotientDuality.ProperCycleZeroDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingletonOrientation

/-! # Pushforward of the specified zero-dimensional fundamental class -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual map between zero-dimensional integral complex schemes sends the specified complex-normalized fundamental class to the specified target class.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; complex chart normalization.
HC no distance; AV milestone no distance. -/
lemma properCycle_zero_dimension_orientation_pushforward
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [IsIntegral Y.left]
    [IsProjective X.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) (hdimX : TopologicalSpace.dim X.left = 0)
    (hdimY : TopologicalSpace.dim Y.left = 0)
    (cX : Homology ℚ (a3b4_an X.hom) 0)
    (hcomplexX : ∀ (e : OpenPartialHomeomorph (ComplexPoint X) (Fin 0 → ℂ)),
      (∀ i, (f4_analytification X).IsHolFun (fun z : e.source => e z i)) →
      ∀ (x : ComplexPoint X) (hx : x ∈ e.source),
        localOrientation (a3b4_an X.hom) 0 cX x = localClassOfChart 0 e x hx)
    (cY : Homology ℚ (a3b4_an Y.hom) 0)
    (hcomplexY : ∀ (e : OpenPartialHomeomorph (ComplexPoint Y) (Fin 0 → ℂ)),
      (∀ i, (f4_analytification Y).IsHolFun (fun z : e.source => e z i)) →
      ∀ (x : ComplexPoint Y) (hx : x ∈ e.source),
        localOrientation (a3b4_an Y.hom) 0 cY x = localClassOfChart 0 e x hx) :
    homologyMap ℚ 0 (TopCat.ofHom (Point.continuousMap f)) cX = cY := by
  letI : Subsingleton (ComplexPoint X) := properCycle_zero_dimension_complex_subsingleton X hdimX
  letI : Subsingleton (ComplexPoint Y) := properCycle_zero_dimension_complex_subsingleton Y hdimY
  letI : Subsingleton (a3b4_an Y.hom) := properCycle_zero_dimension_complex_subsingleton Y hdimY
  letI : Unique (ComplexPoint X) :=
    { default := Classical.choice (properCycle_zero_dimension_complex_nonempty X hdimX)
      uniq := fun _ => Subsingleton.elim _ _ }
  letI : Unique (ComplexPoint Y) :=
    { default := Classical.choice (properCycle_zero_dimension_complex_nonempty Y hdimY)
      uniq := fun _ => Subsingleton.elim _ _ }
  letI : Unique (Fin 0 → ℂ) := { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
  let H : ComplexPoint X ≃ₜ ComplexPoint Y := Homeomorph.homeomorphOfUnique _ _
  let e : OpenPartialHomeomorph (ComplexPoint X) (Fin 0 → ℂ) :=
    (Homeomorph.homeomorphOfUnique _ _).toOpenPartialHomeomorph
  let x : ComplexPoint X := default
  have hx : x ∈ e.source := Set.mem_univ x
  have hX := hcomplexX e (fun i => Fin.elim0 i) x hx
  have hY := hcomplexY (H.symm.transOpenPartialHomeomorph e) (fun i => Fin.elim0 i)
    (H x) (mem_homeomorphTransportedChart H x 0 e hx)
  have hmap : TopCat.ofHom (Point.continuousMap f) = TopCat.ofHom ⟨H, H.continuous⟩ := by
    ext z : 1
    exact Subsingleton.elim _ _
  rw [hmap]
  apply properCycle_subsingleton_local_orientation_injective (a3b4_an Y.hom) (H x) 0
  dsimp only
  have hn := properCycle_local_orientation_homeomorph
    (X := a3b4_an X.hom) (Y := a3b4_an Y.hom) H x 0 cX
  have ht := localClassOfChart_homeomorphTransport H x 0 e hx
  have ht' : relativeHomologyMap ℚ 0 (pointComplementHomeomorphPairMap H x)
      (localClassOfChart 0 e x hx) =
      localClassOfChart 0 (H.symm.transOpenPartialHomeomorph e) (H x)
        (mem_homeomorphTransportedChart H x 0 e hx) := by
    simpa only [Nat.mul_zero] using ht
  exact hn.symm.trans ((congrArg
    (relativeHomologyMap ℚ 0 (pointComplementHomeomorphPairMap H x)) hX).trans
      (ht'.trans hY.symm))

end HodgeLean.Foundations.QuotientDuality
