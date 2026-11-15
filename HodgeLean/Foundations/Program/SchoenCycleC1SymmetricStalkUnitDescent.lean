import HodgeLean.Foundations.Program.SchoenCycleC1FiniteFibreUnitDescent
import HodgeLean.Foundations.Program.SchoenCycleC1InvariantRationalUnitTransport
import HodgeLean.Foundations.Program.SchoenCycleC1GenericStalkActionHelpers
import HodgeLean.Foundations.Program.SchoenCycleStep1
import HodgeLean.Foundations.Program.SchoenCycleC11SchemeHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A base rational pullback unit at one actual symmetric tuple determines
a base chart unit near its quotient point, using the retained orbit relation. -/
theorem s2e_c1_symmetric_stalk_unit_descent
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] (N : ℕ)
    (γ : g3_power Z N ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z N ⟶ T),
      (∀ σ, s2_permute Z N σ ≫ v = v) → ∃! w : B ⟶ T, γ ≫ w = v)
    (x : ComplexPoint (g3_power Z N)) (U : B.left.Opens) (hx : γ.left x.underlying ∈ U)
    (t : B.left.functionField) (ht : t ≠ 0) :
    letI : Surjective γ.left := s2e_c11_surjective_of_point_surjective (g3_power Z N) B γ hsurj
    let hg := s2e_c1_dominant_generic_point γ.left
    let φ := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
      γ.left.stalkMap (genericPoint (g3_power Z N).left)).hom
    (∃ u : ((g3_power Z N).left.presheaf.stalk x.underlying)ˣ,
      algebraMap ((g3_power Z N).left.presheaf.stalk x.underlying)
        (g3_power Z N).left.functionField (u : _) = φ t) →
    ∃ (V : B.left.affineOpens) (hxV : γ.left x.underlying ∈ V.1), V.1 ≤ U ∧
      letI : Nonempty V.1 := ⟨⟨γ.left x.underlying, hxV⟩⟩
      ∃ v : Γ(B.left, V.1)ˣ, B.left.germToFunctionField V.1 (v : Γ(B.left, V.1)) = t := by
  letI : Surjective γ.left := s2e_c11_surjective_of_point_surjective (g3_power Z N) B γ hsurj
  dsimp only
  let hg := s2e_c1_dominant_generic_point γ.left
  let φ := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
    γ.left.stalkMap (genericPoint (g3_power Z N).left)).hom
  intro hlocal
  apply s2e_c1_finite_fibre_unit_descent (g3_power Z N) B γ (Point.map γ x) U hx t ht
  intro z hz
  obtain ⟨σ, hσ⟩ := s2e_step1_retained_symmetric_orbits Z B N γ hsurj hγ hquot z x hz
  letI := s2e_step1_action_isIso (g3_power Z N) (Equiv.Perm (Fin N))
    (s2_permute Z N) (s2e_step1_permute_one Z N) (s2e_step1_permute_mul Z N) σ
  have hpoint : (s2_permute Z N σ).left z.underlying = x.underlying :=
    congrArg Point.underlying hσ
  have hi : (s2_permute Z N σ).left ≫ γ.left = γ.left := congrArg Over.Hom.left (hγ σ)
  have hf := RingHom.congr_fun (s2e_c1_fieldPullback_fixes_base γ.left φ
    (s2e_c1_genericStalkMap_square γ.left hg) (s2_permute Z N σ).left hi) t
  change s2e_step1_fieldPullback (g3_power Z N).left (s2_permute Z N σ).left (φ t) = φ t at hf
  have hl : ∃ u : ((g3_power Z N).left.presheaf.stalk ((s2_permute Z N σ).left z.underlying))ˣ,
      algebraMap ((g3_power Z N).left.presheaf.stalk ((s2_permute Z N σ).left z.underlying))
        (g3_power Z N).left.functionField (u : _) = φ t :=
    (congrArg (fun p : (g3_power Z N).left => ∃ u : ((g3_power Z N).left.presheaf.stalk p)ˣ,
      algebraMap ((g3_power Z N).left.presheaf.stalk p) (g3_power Z N).left.functionField
        (u : _) = φ t) hpoint.symm) ▸ hlocal
  obtain ⟨u, hu⟩ := hl
  exact s2e_c1_invariant_rational_unit_transport (g3_power Z N).left
    (s2_permute Z N σ).left (φ t) hf z.underlying u hu

end HodgeLean.Foundations.Program
