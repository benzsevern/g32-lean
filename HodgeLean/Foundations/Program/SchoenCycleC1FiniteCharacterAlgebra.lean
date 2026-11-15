import HodgeLean.Foundations.Program.SchoenCycleC1FiniteCharacterSeries
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # The invariant algebra of a faithful finite scalar character -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- The full finite character invariant algebra is a power series algebra,
with its inclusion given by expansion by the exact group cardinality. -/
theorem s2e_c1_finite_character_invariant_algebra
    {G k : Type*} [Group G] [Finite G] [CommRing k] [IsDomain k]
    (χ : G →* kˣ) (hχ : Function.Injective χ) :
    ∃ E : PowerSeries k ≃ₐ[k]
        (⨅ g, AlgHom.equalizer (PowerSeries.rescaleAlgHom (χ g : k))
          (AlgHom.id k (PowerSeries k)) : Subalgebra k (PowerSeries k)),
      ∀ f, (E f : PowerSeries k) = PowerSeries.expand (Nat.card G) Nat.card_pos.ne' f := by
  let S : Subalgebra k (PowerSeries k) := ⨅ g,
    AlgHom.equalizer (PowerSeries.rescaleAlgHom (χ g : k)) (AlgHom.id k (PowerSeries k))
  have hr (g : G) (x : PowerSeries k) :
      PowerSeries.rescaleAlgHom (χ g : k) x = PowerSeries.rescale (χ g : k) x := by
    simpa only [RingHom.coe_coe] using
      DFunLike.congr_fun (PowerSeries.coe_rescaleAlgHom (χ g : k)) x
  have hi : Function.Injective (PowerSeries.expand (Nat.card G) Nat.card_pos.ne' :
      PowerSeries k → PowerSeries k) := by
    intro f g h
    ext n
    simpa only [PowerSeries.coeff_expand_mul] using congrArg (PowerSeries.coeff (Nat.card G * n)) h
  have hm (f : PowerSeries k) : PowerSeries.expand (Nat.card G) Nat.card_pos.ne' f ∈ S := by
    simp only [S, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply, hr]
    apply (s2e_c1_finite_character_invariant_series χ hχ _).mpr
    exact ⟨f, rfl, fun y hy => hi hy⟩
  let F : PowerSeries k →ₐ[k] S :=
    (PowerSeries.expand (Nat.card G) Nat.card_pos.ne').codRestrict S hm
  have hF : Function.Bijective F := by
    constructor
    · intro f g h
      exact hi (congrArg Subtype.val h)
    · intro f
      have hf := f.property
      change (f : PowerSeries k) ∈ S at hf
      simp only [S, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply, hr] at hf
      obtain ⟨g, hg, _⟩ := (s2e_c1_finite_character_invariant_series χ hχ _).mp hf
      exact ⟨g, Subtype.ext hg⟩
  exact ⟨AlgEquiv.ofBijective F hF, fun _ => rfl⟩

end HodgeLean.Foundations.Program
