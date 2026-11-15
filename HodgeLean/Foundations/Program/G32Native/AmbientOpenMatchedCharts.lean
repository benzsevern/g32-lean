import HodgeLean.Foundations.Program.G32Native.HolomorphicChartOpenImmersionTransport
import HodgeLean.Foundations.TubularEuler.ImmersionZeroCoordinateHelpers
import HodgeLean.Foundations.Program.G32Native.MatchedHolomorphicChartRegularity
import HodgeLean.Adapters.NormalConeB4aClassChartRegularity
import HodgeLean.Foundations.BundleThom.ImmersionDefs
import HodgeLean.Foundations.Program.SchoenCycleC2SupportHelpers
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Proofs

/-! # Matched holomorphic charts in the original ambient scheme

Smoothness is required on the given ambient open, and the chart is transported
back to the original ambient scheme with the actual immersion image retained.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
open scoped Manifold ContDiff
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

theorem ambient_open_matched_holomorphic_charts
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
    {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
    (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)] (x : ComplexPoint Q) :
    ∃ (b : OpenPartialHomeomorph (ComplexPoint Q) (Fin k → ℂ))
      (a : OpenPartialHomeomorph (ComplexPoint W) ((Fin k → ℂ) × (Fin k → ℂ))),
      a3b4_IsHolChart Q.hom (b.trans
        (Homeomorph.prodUnique (Fin k → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph) ∧
      a3b4_IsHolChart W.hom a ∧ x ∈ b.source ∧ Point.map ι x ∈ a.source ∧
      (∀ y ∈ b.source, Point.map ι y ∈ a.source ∧ a (Point.map ι y) = (b y, 0)) ∧
      (∀ y ∈ a.source,
        y ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ↔ (a y).2 = 0) ∧
      ContMDiffOn 𝓘(ℂ, Fin k → ℂ) 𝓘(ℂ, Fin k → ℂ) ω b.symm b.target ∧
      (let X := Over.mk (v ≫ W.hom)
       letI : SmoothOfRelativeDimension (k + k) X.hom :=
         ‹SmoothOfRelativeDimension (k + k) (v ≫ W.hom)›
       let J := i1_smoothLift ι v j hj
       let I : X ⟶ W := Over.homMk v rfl
       ∃ aX : OpenPartialHomeomorph (ComplexPoint X) ((Fin k → ℂ) × (Fin k → ℂ)),
         ContMDiffOn 𝓘(ℂ, Fin (k + k) → ℂ) 𝓘(ℂ, (Fin k → ℂ) × (Fin k → ℂ))
           ω aX aX.source ∧
         ContMDiffOn 𝓘(ℂ, (Fin k → ℂ) × (Fin k → ℂ)) 𝓘(ℂ, Fin (k + k) → ℂ)
           ω aX.symm aX.target ∧
         a.source = Point.map I '' aX.source ∧
         (∀ z, a (Point.map I z) = aX z) ∧
         ∀ y ∈ b.source, Point.map J y ∈ aX.source ∧ aX (Point.map J y) = (b y, 0)) := by
  let X := Over.mk (v ≫ W.hom)
  let J := i1_smoothLift ι v j hj
  let I : X ⟶ W := Over.homMk v rfl
  letI : IsClosedImmersion J.left := ‹IsClosedImmersion j›
  letI : IsOpenImmersion I.left := ‹IsOpenImmersion v›
  letI : SmoothOfRelativeDimension (k + k) X.hom :=
    ‹SmoothOfRelativeDimension (k + k) (v ≫ W.hom)›
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  letI : QuasiCompact v := inferInstance
  letI : LocallyOfFiniteType X.hom := inferInstanceAs (LocallyOfFiniteType (v ≫ W.hom))
  letI : QuasiCompact X.hom := inferInstanceAs (QuasiCompact (v ≫ W.hom))
  letI : IsSeparated X.hom := inferInstanceAs (IsSeparated (v ≫ W.hom))
  letI : Nonempty (ComplexPoint X) := ⟨Point.map J x⟩
  have hcharts := immersion_matched_holomorphic_charts_regular X Q J k (k + k) x
  rw [Nat.add_sub_cancel_left] at hcharts
  obtain ⟨b, aX, hxb, hxaX, hb, haX, hm, hs, hbInv, haXInv⟩ := hcharts
  obtain ⟨a, ha, hsource, heval⟩ :=
    holomorphic_chart_openImmersion_transport X W I k k aX haX
  have hcomp : J ≫ I = ι := Over.OverMorphism.ext hj
  have hp (y : ComplexPoint Q) : Point.map I (Point.map J y) = Point.map ι y := by
    rw [← Point.map_comp_apply, hcomp]
  have hmatch : ∀ y ∈ b.source,
      Point.map ι y ∈ a.source ∧ a (Point.map ι y) = (b y, 0) := by
    intro y hy
    obtain ⟨hyX, hyval⟩ := hm y hy
    constructor
    · rw [hsource]
      exact ⟨Point.map J y, hyX, hp y⟩
    · rw [← hp y, heval, hyval]
  have haXReg := a3b4a_classHolomorphicChart_contMDiffOn X (k + k) k k aX haX
  refine ⟨b, a, hb, ha, hxb, (hmatch x hxb).1, hmatch, ?_, hbInv,
    aX, haXReg, haXInv, hsource, heval, hm⟩
  intro y hy
  rw [hsource] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [heval]
  have himage : Set.range (Point.map ι) =
      (Point.underlying : ComplexPoint W → W.left) ⁻¹' Set.range ι.left :=
    ComplexPoint.range_map_of_closedImmersion ι
  rw [s2e_componentCycle_analytic_support, ← himage]
  have hinj := (ComplexTopology.openImmersion_points_aux I).injective
  have hpre : Point.map I z ∈ Set.range (Point.map ι) ↔ z ∈ Set.range (Point.map J) := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, hinj ?_⟩
      rw [hp y]
      exact hy
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hp y).symm⟩
  exact hpre.trans (hs z hz)

#print axioms ambient_open_matched_holomorphic_charts
end HodgeLean.Foundations.TubularEuler
