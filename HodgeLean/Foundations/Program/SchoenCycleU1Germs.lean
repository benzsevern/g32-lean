import HodgeLean.Foundations.Program.SchoenCycleU1Variation

/-! # Analytic local rings and dual-number divisor ideals -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- The subring of function germs represented by holomorphic functions near zero.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, local rings and divisors. -/
def s2e_u1_analyticGermRing : Subring (Germ (𝓝 (0 : ℂ)) ℂ) where
  carrier := {a | ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ (f : Germ (𝓝 (0 : ℂ)) ℂ) = a}
  zero_mem' := ⟨fun _ => 0, analyticAt_const, rfl⟩
  one_mem' := ⟨fun _ => 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun z => f z + g z, hf.add hg, rfl⟩
  mul_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun z => f z * g z, hf.mul hg, rfl⟩
  neg_mem' := by
    rintro a ⟨f, hf, rfl⟩
    exact ⟨fun z => -f z, hf.neg, rfl⟩

/-- The germ of a specified holomorphic function, with its analytic-ring membership.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, local rings and divisors. -/
def s2e_u1_analyticGerm (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    s2e_u1_analyticGermRing := ⟨f, f, hf, rfl⟩

/-- The actual local coefficient germ of a holomorphic differential.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, divisors of differentials. -/
def s2e_u1_differentialGerm
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) (p : C) :
    s2e_u1_analyticGermRing :=
  s2e_u1_analyticGerm (HurwitzPrymRR_loc hE θ p) (RiemannRochEichler_loc_analytic hE θ p)

/-- An unchanged principal divisor ideal over dual numbers makes its variation
scalar. Equality is in the analytic local ring, with all zero multiplicities.
Source: ACGH, Geometry of Algebraic Curves I, Chapter IV, differential of the Abel map. -/
theorem s2e_u1_fixed_divisor_ideal_variation
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (θ δ : b3_HolForm E C) (hθ : θ ≠ 0)
    (hideal : ∀ p : C,
      Ideal.span (Set.singleton (TrivSqZeroExt.inl (M := s2e_u1_analyticGermRing)
        (s2e_u1_differentialGerm hE θ p) +
        TrivSqZeroExt.inr (R := s2e_u1_analyticGermRing) (s2e_u1_differentialGerm hE δ p)) :
          Set (DualNumber s2e_u1_analyticGermRing)) =
      Ideal.span (Set.singleton (TrivSqZeroExt.inl (M := s2e_u1_analyticGermRing)
        (s2e_u1_differentialGerm hE θ p)))) :
    (∃ c : ℂ, δ = c • θ) ∧
      Submodule.Quotient.mk (p := Submodule.span ℂ {θ}) δ = 0 := by
  apply s2e_u1_locally_divisible_variation hE θ δ hθ
  intro p
  let a := s2e_u1_differentialGerm hE θ p
  let b := s2e_u1_differentialGerm hE δ p
  have hm : TrivSqZeroExt.inl a + TrivSqZeroExt.inr b ∈
      Ideal.span (Set.singleton (TrivSqZeroExt.inl a) : Set (DualNumber s2e_u1_analyticGermRing)) := by
    rw [← hideal p]
    exact Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hm
  have hb : b = u.snd * a := by
    have he := congrArg TrivSqZeroExt.snd hu
    simpa only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
      DualNumber.snd_mul, TrivSqZeroExt.fst_inl, zero_add, zero_mul, add_zero, mul_comm] using he
  obtain ⟨g, hg, hge⟩ := u.snd.property
  refine ⟨g, hg, ?_⟩
  have he := congrArg Subtype.val hb
  change (HurwitzPrymRR_loc hE δ p : Germ (𝓝 (0 : ℂ)) ℂ) =
    u.snd.val * (HurwitzPrymRR_loc hE θ p : Germ (𝓝 (0 : ℂ)) ℂ) at he
  rw [← hge] at he
  exact (Germ.coe_eq.mp he).filter_mono nhdsWithin_le_nhds

end HodgeLean.Foundations.Program
