import HodgeLean.Foundations.Program.SchoenCycleS1i4Pre3Proofs

noncomputable section
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- Linear substitution on analytic function germs.
Source: Mathlib, Filter.Germ.compTendsto and AnalyticAt.comp. -/
def s2e_nativeAnalytic_pullback (m n : ℕ)
    (L : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) :
    s2e_nativeAnalyticGermRing n →+* s2e_nativeAnalyticGermRing m where
  toFun a := ⟨a.val.compTendsto L (by simpa only [map_zero] using L.continuous.continuousAt.tendsto (x := 0)), by
    obtain ⟨f, hf, he⟩ := a.property
    refine ⟨f ∘ L, ?_, ?_⟩
    · exact hf.comp_of_eq (L.analyticAt 0) (map_zero L)
    · rw [← he]
      rfl⟩
  map_one' := by apply Subtype.ext; rfl
  map_zero' := by apply Subtype.ext; rfl
  map_add' a b := by
    apply Subtype.ext
    obtain ⟨f, hf, he⟩ := a.property
    obtain ⟨g, hg, hge⟩ := b.property
    change (a.val + b.val).compTendsto L (by simpa only [map_zero] using L.continuous.continuousAt.tendsto (x := 0)) = a.val.compTendsto L (by simpa only [map_zero] using L.continuous.continuousAt.tendsto (x := 0)) + b.val.compTendsto L (by simpa only [map_zero] using L.continuous.continuousAt.tendsto (x := 0))
    rw [← he, ← hge]
    rfl
  map_mul' a b := by
    apply Subtype.ext
    obtain ⟨f, hf, he⟩ := a.property
    obtain ⟨g, hg, hge⟩ := b.property
    change (a.val * b.val).compTendsto L (by simpa only [map_zero] using L.continuous.continuousAt.tendsto (x := 0)) = a.val.compTendsto L (by simpa only [map_zero] using L.continuous.continuousAt.tendsto (x := 0)) * b.val.compTendsto L (by simpa only [map_zero] using L.continuous.continuousAt.tendsto (x := 0))
    rw [← he, ← hge]
    rfl

theorem s2e_nativeAnalytic_pullback_representative (m n : ℕ)
    (L : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ))
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    (s2e_nativeAnalytic_pullback m n L ⟨Filter.Germ.ofFun f, ⟨f, hf, rfl⟩⟩).val =
      Filter.Germ.ofFun (f ∘ L) := rfl

example (m n : ℕ) (L : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) :
    s2e_nativeAnalytic_pullback m n L 0 = 0 := map_zero _

/-- An invertible linear substitution induces an equivalence of germ rings.
Source: Mathlib, ContinuousLinearEquiv and Filter.Germ.compTendsto. -/
def s2e_nativeAnalytic_linearEquiv (d : ℕ)
    (L : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ)) :
    s2e_nativeAnalyticGermRing d ≃+* s2e_nativeAnalyticGermRing d where
  __ := s2e_nativeAnalytic_pullback d d L.toContinuousLinearMap
  invFun := s2e_nativeAnalytic_pullback d d L.symm.toContinuousLinearMap
  left_inv a := by
    obtain ⟨f, hf, he⟩ := a.property
    apply Subtype.ext
    change (a.val.compTendsto L (by simpa only [map_zero] using L.continuous.continuousAt.tendsto (x := 0))).compTendsto L.symm (by simpa only [map_zero] using L.symm.continuous.continuousAt.tendsto (x := 0)) = a.val
    rw [← he]
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun x => congrArg f (L.apply_symm_apply x)
  right_inv a := by
    obtain ⟨f, hf, he⟩ := a.property
    apply Subtype.ext
    change (a.val.compTendsto L.symm (by simpa only [map_zero] using L.symm.continuous.continuousAt.tendsto (x := 0))).compTendsto L (by simpa only [map_zero] using L.continuous.continuousAt.tendsto (x := 0)) = a.val
    rw [← he]
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun x => congrArg f (L.symm_apply_apply x)

example (d : ℕ) (L : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ))
    (a : s2e_nativeAnalyticGermRing d) :
    (s2e_nativeAnalytic_linearEquiv d L).symm (s2e_nativeAnalytic_linearEquiv d L a) = a :=
  (s2e_nativeAnalytic_linearEquiv d L).symm_apply_apply a

end HodgeLean.Foundations.Program
