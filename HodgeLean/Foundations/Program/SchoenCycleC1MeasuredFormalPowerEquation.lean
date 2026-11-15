import HodgeLean.Foundations.Program.SchoenCycleC1ActualFormalParameterAction
import HodgeLean.Foundations.Program.SchoenCycleC1EquivariantPowerSeriesCoordinates
import HodgeLean.Foundations.Program.SchoenCycleC1FiniteCharacterAlgebra
import HodgeLean.Foundations.Program.SchoenCycleC1MeasuredFormalPointValues
import HodgeLean.Foundations.Program.SchoenCycleC1InvariantCoordinateValues
import HodgeLean.Foundations.Program.SchoenCycleC1InverseInvariantValues

/-! # The power equation of the actual curve quotient formal pullback -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- Measured faithful deck data give the actual formal power equation over a
normal affine base chart, retaining the specified projection stalk pullback. -/
theorem s2e_c1_measured_actual_formal_power_equation
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u) (hinj : Function.Injective a)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hg : q.left (genericPoint X.left) = genericPoint Y.left)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    [Nonempty U] [Nonempty (q.left ⁻¹ᵁ U)] [IsIntegrallyClosed Γ(Y.left, U)]
    (x : ComplexPoint X) (hx : x.underlying ∈ q.left ⁻¹ᵁ U)
    (hcx : IsClosed ({x.underlying} : Set X.left))
    (hcy : IsClosed ({q.left x.underlying} : Set Y.left)) :
    letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      q.left.stalkMap (genericPoint X.left)).hom
    letI := φ.toAlgebra
    ∀ [Module.Finite Y.left.functionField X.left.functionField]
      (ρ : G →* (X.left.functionField ≃ₐ[Y.left.functionField] X.left.functionField)),
      Function.Injective ρ → Module.finrank Y.left.functionField X.left.functionField = Nat.card G →
      (∀ g, (ρ g).toRingHom = s2e_step1_fieldPullback X.left (a g⁻¹).left) →
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    let P := ((hU.preimage q.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal
    let o : MulAction.orbit G P := ⟨P, MulAction.mem_orbit_self P⟩
    let H := MulAction.stabilizer G o
    let S := Y.left.presheaf.stalk (q.left x.underlying)
    letI : Algebra ℂ S := (HodgeLean.Foundations.Curves.stalkC (q.left x.underlying)).toAlgebra
    let R := X.left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ u : Rˣ,
    ∃ ER : PowerSeries ℂ ≃ₐ[ℂ] AdicCompletion (IsLocalRing.maximalIdeal R) R,
    ∃ ES : PowerSeries ℂ ≃ₐ[ℂ] AdicCompletion (IsLocalRing.maximalIdeal S) S,
      (∀ p : Polynomial ℂ, ER (p : PowerSeries ℂ) = AdicCompletion.of _ _
        (Polynomial.aeval (s2e_native_curve_parameter X x * (u : R)) p)) ∧
      ∀ f, s2e_formal_stalk_pullback X Y q x.underlying (ES f) =
        ER (PowerSeries.expand (Nat.card H) Nat.card_pos.ne' f) := by
  classical
  letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    q.left.stalkMap (genericPoint X.left)).hom
  letI := φ.toAlgebra
  dsimp only
  intro hfinite ρ hρ hdeg hρval
  letI := hfinite
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  let P := ((hU.preimage q.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal
  let o : MulAction.orbit G P := ⟨P, MulAction.mem_orbit_self P⟩
  let H := MulAction.stabilizer G o
  let R := X.left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  let S := Y.left.presheaf.stalk (q.left x.underlying)
  letI : Algebra ℂ S := (HodgeLean.Foundations.Curves.stalkC (q.left x.underlying)).toAlgebra
  obtain ⟨hfix, Q, hQ⟩ := s2e_c1_measured_formal_point_values
    X Y G a ha1 hamul q hinv hg U hU x hx hcx hcy ρ hρ hdeg hρval
  let ak : H → (X ⟶ X) := fun g => a g
  have hkfix (g : H) : (ak g).left x.underlying = x.underlying := by
    simpa only [Subgroup.coe_inv, inv_inv] using hfix g⁻¹
  have hk1 : ak 1 = 𝟙 X := ha1
  have hkmul (g h : H) : ak (g * h) = ak h ≫ ak g := hamul g h
  have hkinj : Function.Injective ak := fun g h he => Subtype.ext (hinj he)
  obtain ⟨χ, hχ, u, hα, E, hval, hact⟩ := s2e_c1_actual_fixed_formal_parameter_action
    X H ak hk1 hkmul hkinj x hkfix
  obtain ⟨C, hC, hCact⟩ := s2e_c1_equivariant_power_series_coordinates ℂ
  let ER := C.trans E
  let β (g : H) : R →ₐ[ℂ] R :=
    { toRingHom := s2e_fixed_point_stalkPullback X.left (a g.val⁻¹).left x.underlying (hfix g)
      commutes' := s2e_fixed_point_stalkPullback_scalars X (a g.val⁻¹) x.underlying (hfix g) }
  let βhat (g : H) := s2e_adic_algebra_map _ _ (β g)
    (s2e_fixed_point_stalkPullback_power X.left (a g.val⁻¹).left x.underlying (hfix g))
  have hER (g : H) : (βhat g).comp ER.toAlgHom =
      ER.toAlgHom.comp (PowerSeries.rescaleAlgHom (χ g⁻¹ : ℂ)) := by
    apply AlgHom.ext
    intro z
    have h1 := DFunLike.congr_fun (hact g⁻¹) (C z)
    have h2 := DFunLike.congr_fun (hCact (χ g⁻¹ : ℂ) (hα g⁻¹)) z
    change βhat g (E (C z)) = E (C (PowerSeries.rescaleAlgHom (χ g⁻¹ : ℂ) z))
    change βhat g (E (C z)) = E (_) at h1
    rw [h1]
    exact congrArg E h2
  let F := s2e_intertwining_invariant_algebras_equiv ER
    (fun g : H => PowerSeries.rescaleAlgHom (χ g⁻¹ : ℂ)) βhat hER
  have hFval (z) : (F z).val = ER z.val :=
    s2e_c1_intertwining_invariant_coordinates_val ER _ βhat hER z
  obtain ⟨D, hD⟩ := s2e_c1_finite_character_invariant_algebra χ hχ
  let V := s2e_inverse_indexed_invariant_equiv
    (fun g : H => PowerSeries.rescaleAlgHom (χ g : ℂ))
  let ES := ((D.trans V).trans F).trans Q.symm
  refine ⟨u, ER, ES, ?_, ?_⟩
  · intro p
    change E (C (p : PowerSeries ℂ)) = _
    rw [hC, hval]
  · intro f
    change s2e_formal_stalk_pullback X Y q x.underlying (Q.symm (F (V (D f)))) = _
    rw [← hQ, Q.apply_symm_apply]
    rw [hFval]
    have hv : (V (D f)).val = (D f).val :=
      s2e_c1_inverse_indexed_invariant_val _ (D f)
    rw [hv, hD]

end HodgeLean.Foundations.Program
