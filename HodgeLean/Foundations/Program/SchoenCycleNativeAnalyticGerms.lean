import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.LocalRing.Basic

/-! # Native complex analytic germs at the origin -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- Native complex analytic germs form a subring of function germs at the origin.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6. -/
def s2e_nativeAnalyticGermRing (d : ℕ) :
    Subring (Filter.Germ (nhds (0 : Fin d → ℂ)) ℂ) where
  carrier := {g | ∃ f : (Fin d → ℂ) → ℂ, AnalyticAt ℂ f 0 ∧ Filter.Germ.ofFun f = g}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

#print axioms s2e_nativeAnalyticGermRing
/-- An analytic function nonzero at the origin defines a unit in the native
analytic germ ring.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6;
Mathlib, AnalyticAt.inv. -/
theorem s2e_nativeAnalyticGerm_isUnit_of_nonzero
    (d : ℕ) (f : (Fin d → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 ≠ 0) :
    IsUnit (⟨Filter.Germ.ofFun f, ⟨f, hf, rfl⟩⟩ : s2e_nativeAnalyticGermRing d) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨Filter.Germ.ofFun (fun x => (f x)⁻¹), ⟨_, hf.inv hf0, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change (Filter.Germ.ofFun (fun x => f x * (f x)⁻¹)) = Filter.Germ.ofFun (fun _ => (1 : ℂ))
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.continuousAt.eventually_ne hf0] with x hx
  exact mul_inv_cancel₀ hx

#print axioms s2e_nativeAnalyticGerm_isUnit_of_nonzero
/-- The native analytic germ ring at the origin is a local ring.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6. -/
instance s2e_nativeAnalyticGerm_isLocalRing (d : ℕ) :
    IsLocalRing (s2e_nativeAnalyticGermRing d) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro g
  obtain ⟨f, hf, he⟩ := g.property
  have hg : g = (⟨Filter.Germ.ofFun f, ⟨f, hf, rfl⟩⟩ : s2e_nativeAnalyticGermRing d) :=
    Subtype.ext he.symm
  rw [hg]
  by_cases h : f 0 = 0
  · right
    have hu := s2e_nativeAnalyticGerm_isUnit_of_nonzero d (fun z => 1 - f z)
      (analyticAt_const.sub hf) (by simp [h])
    convert hu using 1
    apply Subtype.ext
    rfl
  · exact Or.inl (s2e_nativeAnalyticGerm_isUnit_of_nonzero d f hf h)

#print axioms s2e_nativeAnalyticGerm_isLocalRing
/-- Evaluation at the origin is well defined on native analytic germs.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6;
Mathlib, Filter.EventuallyEq.eq_of_nhds. -/
def s2e_nativeAnalyticGerm_value (d : ℕ) : s2e_nativeAnalyticGermRing d →+* ℂ where
  toFun g := Filter.Germ.liftOn g.val (fun f => f 0) (fun _ _ h => h.eq_of_nhds)
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by
    obtain ⟨f, _, hf⟩ := a.property
    obtain ⟨g, _, hg⟩ := b.property
    change Filter.Germ.liftOn (a.val + b.val) _ _ = _
    rw [← hf, ← hg]
    rfl
  map_mul' a b := by
    obtain ⟨f, _, hf⟩ := a.property
    obtain ⟨g, _, hg⟩ := b.property
    change Filter.Germ.liftOn (a.val * b.val) _ _ = _
    rw [← hf, ← hg]
    rfl

#print axioms s2e_nativeAnalyticGerm_value
/-- Units in the native analytic local ring are precisely the germs with
nonzero value at the origin.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6. -/
theorem s2e_nativeAnalyticGerm_isUnit_iff_value_ne_zero
    (d : ℕ) (g : s2e_nativeAnalyticGermRing d) :
    IsUnit g ↔ s2e_nativeAnalyticGerm_value d g ≠ 0 := by
  constructor
  · intro hg
    exact isUnit_iff_ne_zero.mp (hg.map (s2e_nativeAnalyticGerm_value d))
  · intro hg
    obtain ⟨f, hf, he⟩ := g.property
    have hval : s2e_nativeAnalyticGerm_value d g = f 0 := by
      change Filter.Germ.liftOn g.val _ _ = _
      rw [← he]
      rfl
    have hge : g = (⟨Filter.Germ.ofFun f, ⟨f, hf, rfl⟩⟩ : s2e_nativeAnalyticGermRing d) :=
      Subtype.ext he.symm
    rw [hge]
    apply s2e_nativeAnalyticGerm_isUnit_of_nonzero d f hf
    rwa [hval] at hg

#print axioms s2e_nativeAnalyticGerm_isUnit_iff_value_ne_zero
end HodgeLean.Foundations.Program
