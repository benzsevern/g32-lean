import HodgeLean.Foundations.Program.SchoenCycleC1AdicIdentity
import HodgeLean.Foundations.Program.SchoenCycleC1MeasuredFormalPointValues
import HodgeLean.Foundations.Program.SchoenCycleC1ActualGenericDeckRepresentation
import HodgeLean.Foundations.Program.SchoenCycleC1ActualFieldDegreeHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1FixedStalkCompositionHelpers
import HodgeLean.Foundations.Program.SchoenQuotientNormality
import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms

/-! # Actual formal bijections at measured free deck points -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- A free point of a measured faithful finite deck action has bijective
actual formal stalk pullback over a smooth base, without smoothness of the source. -/
theorem s2e_c1_measured_free_formal_pullback_bijective
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    [IsIntegral Y.left] [Smooth Y.hom]
    (G : Type) [Group G] [Fintype G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a) (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hmeas : ∀ V : Y.left.Opens, (V : Set Y.left).Nonempty →
      ∃ y : ComplexPoint Y, y.underlying ∈ V ∧ Nat.card ((Point.map q) ⁻¹' {y}) = Nat.card G)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint X) (hx : x.underlying ∈ q.left ⁻¹ᵁ U)
    (hfree : ∀ g, Point.map (a g) x = x → g = 1) :
    Function.Bijective (s2e_formal_stalk_pullback X Y q x.underlying) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  letI : Nonempty U := ⟨⟨q.left x.underlying, hx⟩⟩
  letI : Nonempty (q.left ⁻¹ᵁ U) := ⟨⟨x.underlying, hx⟩⟩
  letI : IsIntegrallyClosed Γ(Y.left, U) :=
    s2_affineOpen_sections_integrallyClosed (zmtiso_normal_of_smooth Y.left Y.hom) hU
  letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
  have hg := s2_dominant_genericPoint q.left
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    q.left.stalkMap (genericPoint X.left)).hom
  letI := φ.toAlgebra
  have hd : Module.finrank Y.left.functionField X.left.functionField = Nat.card G :=
    s2e_c1_actual_fieldDegree_of_measured_fibres X Y q hg (Nat.card G) hmeas
  letI : Module.Finite Y.left.functionField X.left.functionField :=
    Module.finite_of_finrank_pos (by rw [hd]; exact Nat.card_pos)
  obtain ⟨ρ, hρ, hρval⟩ := s2e_c1_actual_generic_deck_representation X Y G a ha1 hamul hinj q hinv hg
  have hcx : IsClosed ({x.underlying} : Set X.left) :=
    ((pointEquivClosedPoint X.hom) ⟨x.left, by simp⟩).2
  have hcy : IsClosed ({q.left x.underlying} : Set Y.left) := by
    simpa only [Set.image_singleton] using q.left.isClosedMap {x.underlying} hcx
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  let P := ((hU.preimage q.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal
  let o : MulAction.orbit G P := ⟨P, MulAction.mem_orbit_self P⟩
  let H := MulAction.stabilizer G o
  have hone (g : H) : g.val = 1 := by
    apply hfree
    apply (s2e_quotient_point_prime_stabilizer X Y G a ha1 hamul q hinv U hU x hx g.val).mp
    exact congrArg Subtype.val g.property
  let R := X.left.presheaf.stalk x.underlying
  let S := Y.left.presheaf.stalk (q.left x.underlying)
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  letI : Algebra ℂ S := (HodgeLean.Foundations.Curves.stalkC (q.left x.underlying)).toAlgebra
  obtain ⟨hfix, D, hD⟩ := s2e_c1_measured_formal_point_values
    X Y G a ha1 hamul q hinv hg U hU x hx hcx hcy ρ hρ hd hρval
  let β (g : H) : R →ₐ[ℂ] R :=
    { toRingHom := s2e_fixed_point_stalkPullback X.left (a g.val⁻¹).left x.underlying (hfix g)
      commutes' := s2e_fixed_point_stalkPullback_scalars X (a g.val⁻¹) x.underlying (hfix g) }
  let βhat (g : H) := s2e_adic_algebra_map _ _ (β g)
    (s2e_fixed_point_stalkPullback_power X.left (a g.val⁻¹).left x.underlying (hfix g))
  let Z := AdicCompletion (IsLocalRing.maximalIdeal R) R
  have hb (g : H) : β g = AlgHom.id ℂ R := by
    apply AlgHom.ext
    intro z
    change s2e_fixed_point_stalkPullback X.left (a g.val⁻¹).left x.underlying (hfix g) z = z
    simp only [hone g, inv_one, ha1, Over.id_left, s2e_c1_fixed_stalk_pullback_id, RingHom.id_apply]
  have hbh (g : H) : βhat g = AlgHom.id ℂ Z := by
    dsimp only [βhat]
    simp only [hb, s2e_c1_adic_algebra_map_id]
    rfl
  have hm (z : Z) : z ∈ (⨅ g, AlgHom.equalizer (βhat g) (AlgHom.id ℂ Z) : Subalgebra ℂ Z) := by
    simp only [Algebra.mem_iInf]
    intro g
    change βhat g z = z
    rw [hbh]
    rfl
  constructor
  · intro z w hzw
    apply D.injective
    apply Subtype.ext
    exact (hD z).trans (hzw.trans (hD w).symm)
  · intro z
    refine ⟨D.symm ⟨z, hm z⟩, ?_⟩
    rw [← hD]
    exact congrArg Subtype.val (D.apply_symm_apply ⟨z, hm z⟩)

end HodgeLean.Foundations.Program
