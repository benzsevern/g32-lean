import HodgeLean.Foundations.Program.G32SelectedRealizationImageFamily
import HodgeLean.Foundations.Program.G32SelectedRealizationProjector
import HodgeLean.Foundations.Program.G32SelectedRealizationCharacters

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

theorem g32x_modelOperator_id (Λ : Type) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    b63g_modelOperator Λ F hF Q hQ (AddMonoidHom.id Λ) = LinearMap.id := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  apply LinearMap.ext
  intro x
  apply (abelianPeriodEquiv _).injective
  change abelianPeriodEquiv _ ((abelianPeriodEquiv _).symm
    ((abelianPeriodEquiv _ x).comp (b63g_modelMap Λ F hF Q hQ (AddMonoidHom.id Λ)))) = _
  rw [LinearEquiv.apply_symm_apply]
  ext l
  simp [b63g_modelMap]

theorem g32x_modelOperator_comp (Λ : Type) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q)
    (φ ψ : Λ →+ Λ) :
    b63g_modelOperator Λ F hF Q hQ (φ.comp ψ) =
      b63g_modelOperator Λ F hF Q hQ ψ ∘ₗ b63g_modelOperator Λ F hF Q hQ φ := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  apply LinearMap.ext
  intro x
  simp only [b63g_modelOperator, b63g_dualOperator, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  apply (abelianPeriodEquiv _).injective
  simp only [LinearEquiv.apply_symm_apply]
  ext l
  simp [b63g_precomp, b63g_modelMap]

theorem g32x_modelOperator_sum (Λ : Type) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q)
    {Idx : Type} [Fintype Idx] (n : Idx → ℤ) (φ : Idx → Λ →+ Λ) :
    b63g_modelOperator Λ F hF Q hQ (∑ i, n i • φ i) =
      ∑ i, n i • b63g_modelOperator Λ F hF Q hQ (φ i) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  apply LinearMap.ext
  intro x
  apply (abelianPeriodEquiv _).injective
  ext l
  simp [b63g_modelOperator, b63g_dualOperator, b63g_precomp, b63g_modelMap,
    LinearMap.comp_apply]

set_option maxRecDepth 2048 in
theorem g32x_exists_end_of_filtration (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsCommMonObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (hφ : b2_abelianF X ≤ (b2_abelianF X).comap (b2_cplxMap φ)) :
    ∃ f : AbelianEnd X, homPullback f.hom 1 = b63g_dualOperator X φ := by
  let e := b2a_evalEquiv X
  let A := e.toLinearMap ∘ₗ
    (b2_abelianF X).mapQ (b2_abelianF X) (b2_cplxMap φ) hφ ∘ₗ
      e.symm.toLinearMap
  have hA (l : b2_abelianLattice X) : A l = φ l := by
    have he (k : b2_abelianLattice X) :
        e (Submodule.Quotient.mk ((1 : ℂ) ⊗ₜ[ℤ] k)) = k := by
      change b2_abelianEval X ((1 : ℂ) ⊗ₜ[ℤ] k) = _
      simp [b2_abelianEval]
    rw [← he l]
    simp only [A, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    change e (Submodule.Quotient.mk ((1 : ℂ) ⊗ₜ[ℤ] φ l)) = _
    exact he _
  obtain ⟨f, hf⟩ := spec_exists_abelianEnd_of_lattice X (gagam_hAlg X) A
    (fun l hl ↦ by rw [hA ⟨l, hl⟩]; exact (φ ⟨l, hl⟩).property)
  obtain ⟨ψ, hψ⟩ := spec_abelianEndAction_period X f
  have heq : ψ = φ := by
    apply AddMonoidHom.ext
    intro l
    apply Subtype.ext
    exact (spec_latticeRepresentation_eq_analytic X f A hf ψ hψ l).trans (hA l)
  refine ⟨f, LinearMap.ext fun x ↦ (abelianPeriodEquiv X).injective ?_⟩
  apply AddMonoidHom.ext
  intro l
  have hp := Classical.choose_spec (spec_abelianPeriod_equiv X)
  change abelianPeriodEquiv X (abelianEndAction X f x) l =
    abelianPeriodEquiv X (b63g_dualOperator X φ x) l
  calc
    _ = abelianPeriod X x (φ l) := (hp _ l).trans (by rw [hψ, heq])
    _ = _ := by
      simp only [b63g_dualOperator, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
      exact (hp x (φ l)).symm

theorem g32x_deck_realization_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    ∃ f : g32p_G → AbelianEnd (g32x_J D t),
      ∀ a, homPullback (f a).hom 1 = g32x_deck D t a := by
  have h (a : g32p_G) : ∃ f : AbelianEnd (g32x_J D t),
      homPullback f.hom 1 = g32x_deck D t a := by
    apply g32x_exists_end_of_filtration
    apply b63g_modelMap_filtration
    exact b4_cplxAct_periodF (D.hG t) a⁻¹
  choose f hf using h
  exact ⟨f, hf⟩

set_option maxHeartbeats 400000 in
theorem g32x_deck_laws_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    (f 1).hom = 𝟙 (g32x_J D t) ∧
      ∀ a b, (f (a * b)).hom = (f a).hom ≫ (f b).hom := by
  have hone : g32x_deck D t 1 = LinearMap.id := by
    unfold g32x_deck
    rw [inv_one, b4_latticeAct_one (D.hG t)]
    exact g32x_modelOperator_id _ _ _ _ _
  have hmul (a b : g32p_G) :
      g32x_deck D t (a * b) = g32x_deck D t a ∘ₗ g32x_deck D t b := by
    unfold g32x_deck
    rw [mul_inv_rev, b4_latticeAct_mul (D.hG t)]
    exact g32x_modelOperator_comp _ _ _ _ _ _ _
  have hfaith (u v : AbelianEnd (g32x_J D t))
      (h : homPullback u.hom 1 = homPullback v.hom 1) : u.hom = v.hom :=
    congrArg AbelianEnd.hom (spec_abelianEndAction_injective _ h)
  constructor
  · apply hfaith (f 1) 1
    change homPullback (f 1).hom 1 = homPullback (𝟙 (g32x_J D t)) 1
    rw [hf, hone, spec_homPullback_id]
  · intro a b
    apply hfaith (f (a * b)) (f b * f a)
    change homPullback (f (a * b)).hom 1 =
      homPullback ((f a).hom ≫ (f b).hom) 1
    rw [spec_homPullback_comp, hf, hf, hf, hmul]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 400000 in
theorem g32x_multiplicity_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    ∀ τ : FDRep ℂ g32p_G, Simple τ → (∃ a, τ.ρ a ≠ 1) →
      g32p_multiplicity (fun a ↦ (f a).hom) τ = g32p_cwMult τ := by
  intro τ hs hnon
  letI := g32x_irreducible_of_simple τ hs
  letI := D.fibreFaithful t
  have hn : ∃ (a : b4b_Group) (v : τ), τ.ρ a v ≠ v := by
    obtain ⟨a, ha⟩ := hnon
    have hh : ¬ ∀ v : τ, τ.ρ a v = v := fun h ↦ ha (LinearMap.ext h)
    obtain ⟨v, hv⟩ := not_forall.mp hh
    exact ⟨a, v, hv⟩
  have hc := b63d_finite_topCW (b65z_fibre c D.C t) (D.hG t)
    (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Set.Subset.refl _) t)
    (D.hk t) (D.hsurj t) (D.hgal t) (b6_branch t.val)
    ((b6t_polydisc_neighbourhood c D.atlas.hb).2.2.2 t.property)
    g (D.hbranch t) (D.hrot t) τ.ρ hn
  have hci : (Module.finrank ℂ (b4_HomG τ.ρ
      (fun a ↦ b4_cplxAct ℂ (C := b65z_fibre c D.C t) a) ⊤) : ℤ) =
      ((∑ j : Fin 13, Module.finrank ℂ (LinearMap.range (τ.ρ (g j) - LinearMap.id)) : ℕ) : ℤ) -
        2 * (Module.finrank ℂ τ : ℤ) := by
    exact_mod_cast hc
  rw [g32x_nielsen_rank_sum g hg τ] at hci
  have hcw : (Module.finrank ℂ (b4_HomG τ.ρ
      (fun a ↦ b4_cplxAct ℂ (C := b65z_fibre c D.C t) a) ⊤) : ℤ) =
      g32p_cwMult τ := by
    unfold g32p_cwMult
    push_cast at hci
    simp only [← Module.End.one_eq_id] at hci
    linarith
  have ht (a : g32p_G) : LinearMap.trace ℚ (HQ (g32x_J D t) 1) (g32x_deck D t a) =
      (LinearMap.trace ℤ (g32x_L D t) (b4_latticeAct ℂ a⁻¹).toIntLinearMap : ℚ) :=
    g32x_modelOperator_trace (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t))
      (b3_isWeightOne (by simp)) (D.Q t)
      (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t)) _
  have he : g32p_multiplicity (fun a ↦ (f a).hom) τ =
      (Module.finrank ℂ (b4_HomG τ.ρ
        (fun a ↦ b4_cplxAct ℂ (C := b65z_fibre c D.C t) a) ⊤) : ℂ) := by
    unfold g32p_multiplicity
    simp_rw [hf, ht]
    push_cast
    exact g32x_period_character_average (b65z_fibre c D.C t) (D.hG t) τ
  rw [he]
  exact_mod_cast hcw

open HodgeLean.Foundations.AppellHumbert

theorem g32x_latticeClass_invariant {Λ : Type} [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (E : Λ →+ Λ →+ ℤ) (φ : Λ →+ Λ)
    (hφ : ∀ l m, E (φ l) (φ m) = E l m) :
    exteriorPower.map 2 (b63g_precomp φ) (latticeClass E) = latticeClass E := by
  letI : FiniteDimensional ℚ (Λ →+ ℚ) := Module.Finite.of_basis latticeDualBasisQ
  apply contract_injective
  rw [contract_map]
  ext ψ x
  simp only [LinearMap.comp_apply]
  change contract (latticeClass E) ((b63g_precomp φ).dualMap ψ) (φ x) =
    contract (latticeClass E) ψ x
  rw [b63g_contract_latticeClass, b63g_contract_latticeClass]
  apply congrArg ψ
  ext y
  change (((E (φ y) (φ x) - E (φ x) (φ y) : ℤ) : ℚ) / 2) = _
  rw [hφ, hφ]
  rfl

set_option maxRecDepth 2048 in
theorem g32x_classHQ_invariant (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (u : X ⟶ X) (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (hu : homPullback u 1 = b63g_dualOperator X φ)
    (E : b2_abelianLattice X →+ b2_abelianLattice X →+ ℤ)
    (hφ : ∀ l m, E (φ l) (φ m) = E l m) :
    homPullback u 2 (latticeClassHQ X E) = latticeClassHQ X E := by
  unfold latticeClassHQ
  rw [← LinearMap.comp_apply, spec_homPullback_cupWedgeMap,
    LinearMap.comp_apply, hu]
  congr 1
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  have hc : b63g_dualOperator X φ ∘ₗ (abelianPeriodEquiv X).symm.toLinearMap =
      (abelianPeriodEquiv X).symm.toLinearMap ∘ₗ b63g_precomp φ := by
    ext v
    simp [b63g_dualOperator, LinearMap.comp_apply]
  rw [hc, exteriorPower.map_comp, LinearMap.comp_apply,
    g32x_latticeClass_invariant E φ hφ]

theorem g32x_modelClass_fixed (Λ : Type) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q)
    (φ : Λ →+ Λ) (hφ : ∀ l m, Q (φ l) (φ m) = Q l m) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    ∀ u : b5_model Λ F hF Q ⟶ b5_model Λ F hF Q,
      homPullback u 1 = b63g_modelOperator Λ F hF Q hQ φ →
      homPullback u 2 (b63g_modelClass Λ F hF Q hQ) =
        b63g_modelClass Λ F hF Q hQ := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  intro u hu
  apply g32x_classHQ_invariant _ u (b63g_modelMap Λ F hF Q hQ φ) hu
  intro l m
  simpa [b63g_modelMap, b63g_modelForm, b2_bilinToAddHom] using
    hφ ((b5_periodEquiv Λ F hF Q hQ).symm l)
      ((b5_periodEquiv Λ F hF Q hQ).symm m)

set_option maxHeartbeats 400000 in
set_option maxRecDepth 2048 in
theorem g32x_theta_invariant_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    ∃ hn : IsNondegenerate
        (polarizationVec (torusCohomology_cupProductOf (g32x_J D t)) (g32x_theta D t)),
      PolarizationPositive (finiteBetti_abelian (g32x_J D t))
        (spec_bettiDeRhamIso_abelian (g32x_J D t))
        (hodgeDecomposition_of_abelian (g32x_J D t))
        (torusCohomology_cupProductOf (g32x_J D t)) hn ∧
      ∀ a, homPullback (f a).hom 2 (g32x_theta D t) = g32x_theta D t := by
  let F := b3_periodF ℂ (b65z_fibre c D.C t)
  have hF : b2_IsWeightOne (g32x_L D t) F := b3_isWeightOne (by simp)
  have hQ : b2_IsRiemannForm (g32x_L D t) F (D.Q t) :=
    b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t)
  letI := b5_groupObj (g32x_L D t) F hF (D.Q t) hQ
  letI : IsIntegral (b5_model (g32x_L D t) F hF (D.Q t)).left :=
    b5_integral (g32x_L D t) F hF (D.Q t) hQ
  letI := b5_smooth (g32x_L D t) F hF (D.Q t) hQ
  letI := b5_projective (g32x_L D t) F hF (D.Q t) hQ
  have hR := b63g_modelForm_riemann (g32x_L D t) F hF (D.Q t) hQ
  have hn := b2_abelian_nondegenerate (b5_model (g32x_L D t) F hF (D.Q t))
    (b63g_modelForm (g32x_L D t) F hF (D.Q t) hQ) hR
  have hp := b63g4_abelian_positive (b5_model (g32x_L D t) F hF (D.Q t))
    (b63g_modelForm (g32x_L D t) F hF (D.Q t) hQ) hR
  refine ⟨hn, hp, ?_⟩
  intro a
  exact g32x_modelClass_fixed (g32x_L D t) F hF (D.Q t) hQ
    (b4_latticeAct ℂ a⁻¹)
    (b4_intersectionForm_invariant (by simp) (D.hG t) (D.Q t) (D.hQ t) a⁻¹)
    (f a).hom (hf a)

theorem g32x_projector_eq_deck_sum {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    g32x_projector D t = ∑ a : g32p_G, b4b_projectorCoeff a • g32x_deck D t a := by
  unfold g32x_projector g32x_operator b4_groupEnd
  rw [g32x_modelOperator_sum]
  exact Fintype.sum_equiv (Equiv.inv g32p_G) _ _ (fun a ↦ by
    simp only [Equiv.inv_apply, g32x_deck, g32x_operator,
      inv_inv, b63l_projectorCoeff_inverse]
    rfl)

set_option maxHeartbeats 400000 in
set_option maxRecDepth 2048 in
theorem g32x_image_comparison_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c)))
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    ∃ i : (b65z_fiber D B t).X ⟶ g32x_J D t,
    ∃ q : g32x_J D t ⟶ (b65z_fiber D B t).X,
    ∃ N : ℕ, 0 < N ∧ IsMonHom i ∧ IsMonHom q ∧
      i ≫ q = 𝟙 (b65z_fiber D B t).X ^ N ∧
      (∃ z : g32p_G → ℤ, q ≫ i = ∏ a, (f a).hom ^ z a) ∧
      LinearMap.range (homPullback q 1) = LinearMap.range (g32x_projector D t) := by
  obtain ⟨i, q, hiMon, hqMon, hret, hU⟩ := g32x_image_maps D t B
  letI := hiMon
  letI := hqMon
  let X := g32x_J D t
  let Y := (b65z_fiber D B t).X
  have hR : homPullback (∏ a : g32p_G, (f a).hom ^ b4b_projectorCoeff a) 1 =
      g32x_projector D t := by
    rw [g32x_homPullback_prod, g32x_projector_eq_deck_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [hf, Int.cast_smul_eq_zsmul]
  letI := g32x_isMonHom_groupRing X (fun a : g32p_G ↦ (f a).hom)
    (fun a ↦ (f a).isMonHom) b4b_projectorCoeff
  have hgroup : q ≫ i = ∏ a : g32p_G, (f a).hom ^ b4b_projectorCoeff a := by
    let u : AbelianEnd X := ⟨q ≫ i, inferInstance⟩
    let v : AbelianEnd X := ⟨∏ a : g32p_G, (f a).hom ^ b4b_projectorCoeff a, inferInstance⟩
    exact congrArg AbelianEnd.hom (spec_abelianEndAction_injective X
      (a₁ := u) (a₂ := v) (hU.trans hR.symm))
  refine ⟨i, q, 116640, by norm_num, hiMon, hqMon, hret, ⟨b4b_projectorCoeff, hgroup⟩, ?_⟩
  have hgf : homPullback i 1 ∘ₗ homPullback q 1 = (116640 : ℚ) • LinearMap.id := by
    rw [← spec_homPullback_comp, hret]
    rw [g32x_homPullback_pow, spec_homPullback_id]
    norm_num
  have hr := g32x_range_comp_of_scalar_retraction (homPullback q 1) (homPullback i 1)
    (116640 : ℚ) (by norm_num) hgf
  rw [← spec_homPullback_comp, hU] at hr
  exact hr.symm

set_option maxRecDepth 2048 in
theorem g32x_rho_image_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    ∀ x ∈ LinearMap.range (g32x_projector D t),
      g32p_rhoProjector (fun a ↦ (f a).hom) ((1 : ℂ) ⊗ₜ[ℚ] x) =
        (1 : ℂ) ⊗ₜ[ℚ] x := by
  have laws := g32x_deck_laws_aux D t f hf
  let ρ : Representation ℂ g32p_G (ℂ ⊗[ℚ] HQ (g32x_J D t) 1) :=
    { toFun := fun a ↦ (homPullback (f a).hom 1).baseChange ℂ
      map_one' := by
        rw [laws.1, spec_homPullback_id, LinearMap.baseChange_id]
        rfl
      map_mul' := fun a b ↦ by
        rw [laws.2, spec_homPullback_comp, LinearMap.baseChange_comp]
        rfl }
  have hsum : (g32x_projector D t).baseChange ℂ =
      ∑ a : g32p_G, (b4b_projectorCoeff a : ℂ) • ρ a := by
    rw [g32x_projector_eq_deck_sum, g32x_baseChange_zsum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← hf a]
    rfl
  have hc : (((4 : ℂ) / Fintype.card g32p_G) • ∑ a : g32p_G,
      ((b4b_toMatrix a).trace + star (b4b_toMatrix a).trace) • ρ a) =
      g32p_rhoProjector (fun a ↦ (f a).hom) := rfl
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  have he := LinearMap.congr_fun (g32x_representation_central_fixed ρ)
    ((1 : ℂ) ⊗ₜ[ℚ] y)
  rw [hc, ← hsum] at he
  simpa only [Module.End.mul_apply, LinearMap.baseChange_tmul] using he

end HodgeLean.Foundations.Program
