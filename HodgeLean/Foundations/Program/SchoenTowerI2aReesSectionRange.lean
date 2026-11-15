import HodgeLean.Foundations.Program.SchoenTowerI2aReesLocalInverse
import Mathlib.AlgebraicGeometry.PullbackCarrier

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The image of a local section in an actual integral Rees chart is exactly
the inverse image of the specified open neighborhood in the retained target.
Source: Mathlib, `Scheme.Pullback.range_fst`;
Hartshorne, Algebraic Geometry, II.7, Proposition 7.13. -/
theorem s2v_i2a_rees_section_range
    (R : Type) [CommRing R] [IsDomain R] (x y : R) (hx : x ≠ 0)
    (Y V : Scheme.{0}) [IsIntegral V] (b : Y ⟶ Spec (CommRingCat.of R))
    (g : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {x, y}) x)) ⟶ Y)
    (hg : g ≫ b = Spec.map (CommRingCat.ofHom (algebraMap R _)))
    (u : V ⟶ Y) [IsOpenImmersion u] [QuasiCompact u]
    (f : V ⟶ Spec (CommRingCat.of (s2t_reesChart (Ideal.span {x, y}) x)))
    (hf : f ≫ g = u) : Set.range f = g ⁻¹' Set.range u := by
  haveI : IsIso (pullback.snd g u) :=
    (s2v_i2a_rees_local_inverse R x y hx Y V b g hg u f hf).1
  let l : V ⟶ pullback g u := pullback.lift f (𝟙 V) (by simpa using hf)
  have hl : l = inv (pullback.snd g u) := by
    apply (cancel_mono (pullback.snd g u)).mp
    simp [l]
  haveI : IsIso l := by rw [hl]; infer_instance
  have hlf : l ≫ pullback.fst g u = f := by simp [l]
  rw [← Scheme.Pullback.range_fst g u, ← hlf]
  change Set.range ((pullback.fst g u) ∘ l) = Set.range (pullback.fst g u)
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨l q, rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨v, rfl⟩ := l.surjective q
    exact ⟨v, rfl⟩

end HodgeLean.Foundations.Program
