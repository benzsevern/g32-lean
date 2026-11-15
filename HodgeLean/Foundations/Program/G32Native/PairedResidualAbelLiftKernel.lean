import HodgeLean.Foundations.Program.G32Native.PairedResidualCurvePrimitive
import HodgeLean.Foundations.Program.G32Native.PairedResidualResidueRank
import HodgeLean.Foundations.Program.G32Native.AbelCollisionLiftJets

/-! # The actual Abel lift covector kernel retains every divisor multiplicity -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Manifold Filter
open HodgeLean.Adapters
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped ContDiff Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [Module.Finite ℤ (b3_periodLattice E C)]
  [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]

/-- For an actual local Abel lift in monic block coordinates, an annihilating
original holomorphic covector belongs to the full principal residue kernel.
Source: Forster, Lectures on Riemann Surfaces, §21; Schoen, Compositio
Mathematica 65 (1988), Lemma 2.6. -/
theorem residual_abel_lift_covector_kernel
    (h : Module.finrank ℂ E = 1) (p : C) (D : C →₀ ℤ)
    (f : ((Σ i : D.support, Fin (Int.toNat (D i.1))) → ℂ) → b3Rest2_VJ E C)
    (hf : DifferentiableAt ℂ f 0)
    (he : ∀ᶠ z in 𝓝 (0 : (Σ i : D.support, Fin (Int.toNat (D i.1))) → ℂ),
      b3Rest2_covHom (f (collisionBlockCoefficients (fun i : D.support =>
        Int.toNat (D i.1)) z)) =
      ∑ s : Σ i : D.support, Fin (Int.toNat (D i.1)),
        analyticAbel h p (b3A_disc s.1.1 (b4cov_lineEquiv h 1) (z s)))
    (θ : b3_HolForm E C)
    (hz : fderiv ℂ (fun z => periodLinear θ (f z)) 0 = 0) :
    θ ∈ LinearMap.ker (RiemannRochAna_holPrincipalResidueLinear h D) := by
  classical
  choose g hg hcover hderiv using
    (fun i : D.support => residual_curve_local_abel_primitive h p i.1)
  have hroots : ∀ᶠ z in 𝓝 (0 : (Σ i : D.support, Fin (Int.toNat (D i.1))) → ℂ),
      ∀ s : Σ i : D.support, Fin (Int.toNat (D i.1)),
        b3Rest2_covHom (g s.1 (z s)) =
          analyticAbel h p (b3A_disc s.1.1 (b4cov_lineEquiv h 1) (z s)) := by
    apply eventually_all.mpr
    intro s
    exact (show Tendsto (fun z : (Σ i : D.support, Fin (Int.toNat (D i.1))) → ℂ => z s)
          (𝓝 0) (𝓝 0) from (continuous_apply s).continuousAt.tendsto).eventually (hcover s.1)
  have htrace : ∀ᶠ z in 𝓝 (0 : (Σ i : D.support, Fin (Int.toNat (D i.1))) → ℂ),
      b3Rest2_covHom (f (collisionBlockCoefficients (fun i : D.support =>
        Int.toNat (D i.1)) z)) =
        ∑ s : Σ i : D.support, Fin (Int.toNat (D i.1)), b3Rest2_covHom (g s.1 (z s)) := by
    filter_upwards [he, hroots] with z hz hr
    rw [hz]
    exact Finset.sum_congr rfl (fun s _ => (hr s).symm)
  have hord := collision_quotient_lift_jet_orders
    (fun i : D.support => Int.toNat (D i.1)) b3Rest2_covHom
    b3Rest2_covHom_spec.1.isLocalHomeomorph f hf g hg (periodLinear θ) hz htrace
  apply (RiemannRochAna_mem_holPrincipalResidueKernel_iff_analyticOrder h D θ).mpr
  intro i
  have hi := hord i
  change (Int.toNat (D i.1) : ℕ∞) ≤
    analyticOrderAt (deriv (fun z => periodLinear θ (g i z))) 0 at hi
  rw [analyticOrderAt_congr (hderiv i θ)] at hi
  exact hi

#print axioms residual_abel_lift_covector_kernel

/-- Above the canonical degree, every actual Abel lift in monic block coordinates
has a surjective differential, including at repeated roots.
Source: Forster, Lectures on Riemann Surfaces, §21; Schoen, Compositio
Mathematica 65 (1988), Lemma 2.6. -/
theorem residual_abel_lift_differential_surjective
    (h : Module.finrank ℂ E = 1) (p : C) (D : C →₀ ℤ)
    (f : ((Σ i : D.support, Fin (Int.toNat (D i.1))) → ℂ) → b3Rest2_VJ E C)
    (hf : DifferentiableAt ℂ f 0)
    (he : ∀ᶠ z in 𝓝 (0 : (Σ i : D.support, Fin (Int.toNat (D i.1))) → ℂ),
      b3Rest2_covHom (f (collisionBlockCoefficients (fun i : D.support =>
        Int.toNat (D i.1)) z)) =
      ∑ s : Σ i : D.support, Fin (Int.toNat (D i.1)),
        analyticAbel h p (b3A_disc s.1.1 (b4cov_lineEquiv h 1) (z s)))
    (hD : ∀ x, 0 ≤ D x)
    (hd : 2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) - 2 < b4c_deg D) :
    Function.Surjective (fderiv ℂ f 0) := by
  let A := (fderiv ℂ f 0).toLinearMap
  change Function.Surjective A
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro φ hφ
  change φ = 0
  let ℓ := φ.toContinuousLinearMap
  obtain ⟨θ, hθ⟩ := (periodFormEquiv h).surjective ℓ
  have hℓ : periodLinear θ = ℓ := (periodFormEquiv_apply h θ).symm.trans hθ
  have hz : fderiv ℂ (fun z => periodLinear θ (f z)) 0 = 0 := by
    rw [hℓ]
    change fderiv ℂ (ℓ ∘ f) 0 = 0
    rw [fderiv_comp 0 ℓ.differentiableAt hf, ℓ.fderiv]
    ext v
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp hφ) v
  have hk := residual_abel_lift_covector_kernel h p D f hf he θ hz
  rw [residual_high_degree_residue_kernel h D hD hd] at hk
  have hθ0 : θ = 0 := hk
  have heq : ℓ = 0 := by simpa only [hθ0, map_zero] using hθ.symm
  apply LinearMap.ext
  intro v
  exact DFunLike.congr_fun heq v

#print axioms residual_abel_lift_differential_surjective
end HodgeLean.Foundations.Program.G32Native
