import HodgeLean.Adapters.NormalConeB4aGysinOpenSupportNormal
import HodgeLean.Adapters.NormalConeB4aGysinChartSupportRegion
import HodgeLean.Adapters.NormalConeB4aGysinChartFamily
import HodgeLean.Adapters.NormalConeB4aGysinDiskDerivative
import HodgeLean.Adapters.NormalConeB4aGysinAffineShiftedLength
import HodgeLean.Adapters.NormalConeB4aGysinOpenSourceConservation
import HodgeLean.Adapters.NormalConeB4aGysinEtaleSourceLength
import HodgeLean.Adapters.NormalConeB4aGysinPolynomialSourceOpen
import HodgeLean.Adapters.NormalConeB4aGysinExactModel
import HodgeLean.Adapters.NormalConeB4aGysinSourceConservation
import HodgeLean.Adapters.NormalConeB4aGysinLocalizedModelSourcePoint
import HodgeLean.Adapters.NormalConeB4aGysinEtaleEvaluationLength
import HodgeLean.Adapters.NormalConeB4aGysinChartIntersections
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion
import HodgeLean.Adapters.NormalConeB4aGysinBridgeSums
import HodgeLean.Adapters.NormalConeB4aGysinBridgeDisks
import HodgeLean.Adapters.NormalConeB4aGysinBridgeDefs
import HodgeLean.Adapters.NormalConeB4aGysinNormalCycles
import HodgeLean.Adapters.NormalConeB4aGysinBaseChangeInjective

/-! # Bridge stage of A3-B4a: proof obligations -/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular ComplexAlgHom
open scoped TensorProduct Topology

theorem a3b4a_gysin_exists_baseChange_chart_homeomorph_aux
    {n : ℕ} (T S : Type) [CommRing T] [CommRing S] [Algebra ℂ T] [Algebra ℂ S]
    [Algebra (complexPolynomialRing n) T] [Algebra (complexPolynomialRing n) S]
    [IsScalarTower ℂ (complexPolynomialRing n) T] [IsScalarTower ℂ (complexPolynomialRing n) S]
    [Algebra.Etale (complexPolynomialRing n) T] (u : T →ₐ[ℂ] ℂ) :
    let L := (Algebra.TensorProduct.includeLeft :
      T →ₐ[complexPolynomialRing n] TensorProduct (complexPolynomialRing n) T S).restrictScalars ℂ
    let E := etaleAlgHomProjectionChart (n := n) T u
    ∃ e : {g : TensorProduct (complexPolynomialRing n) T S →ₐ[ℂ] ℂ // g.comp L ∈ E.source} ≃ₜ
      {w : S →ₐ[ℂ] ℂ // mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom S w) ∈ E.target},
      ∀ g, ∀ s : S, (e g).val s = g.val (1 ⊗ₜ[complexPolynomialRing n] s) := by
  classical
  let L := (Algebra.TensorProduct.includeLeft :
    T →ₐ[complexPolynomialRing n] TensorProduct (complexPolynomialRing n) T S).restrictScalars ℂ
  let R := (Algebra.TensorProduct.includeRight :
    S →ₐ[complexPolynomialRing n] TensorProduct (complexPolynomialRing n) T S).restrictScalars ℂ
  let E := etaleAlgHomProjectionChart (n := n) T u
  let B := fun w : S →ₐ[ℂ] ℂ => mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom (n := n) S w)
  have hB : Continuous B := (mvPolynomialAlgHomHomeomorph n).continuous.comp
    (continuous_induced_rng.mpr (continuous_pi fun d =>
      ComplexPoint.continuous_affineAlgebraHom_apply S
        (algebraMap (complexPolynomialRing n) S d)))
  let Y := {w : S →ₐ[ℂ] ℂ // B w ∈ E.target}
  let V : Y → (T →ₐ[ℂ] ℂ) := fun w => E.symm (B w.val)
  have hV : Continuous V := E.continuousOn_symm.comp_continuous
    (hB.comp continuous_subtype_val) (fun w => w.property)
  have hv (w : Y) : V w ∈ E.source := E.map_target w.property
  have hb (w : Y) : etaleBaseAlgHom (n := n) T (V w) = etaleBaseAlgHom (n := n) S w.val := by
    apply (mvPolynomialAlgHomHomeomorph n).injective
    rw [← etaleAlgHomProjectionChart_apply_of_mem T u (V w) (hv w)]
    exact E.right_inv w.property
  obtain ⟨G, hG, hGval⟩ := a3b4a_gysin_exists_continuous_tensor_evaluation
    V (fun w : Y => w.val) hV continuous_subtype_val
    (fun w d => congrArg (fun f : complexPolynomialRing n →ₐ[ℂ] ℂ => f d) (hb w))
  have hGL (w : Y) : (G w).comp L = V w := by
    apply AlgHom.ext
    intro t
    change G w (t ⊗ₜ[complexPolynomialRing n] 1) = V w t
    rw [hGval, map_one, mul_one]
  have hGR (w : Y) : (G w).comp R = w.val := by
    apply AlgHom.ext
    intro t
    change G w (1 ⊗ₜ[complexPolynomialRing n] t) = w.val t
    rw [hGval, map_one, one_mul]
  have hproj (g : TensorProduct (complexPolynomialRing n) T S →ₐ[ℂ] ℂ) :
      etaleBaseAlgHom (n := n) T (g.comp L) = etaleBaseAlgHom (n := n) S (g.comp R) := by
    apply AlgHom.ext
    intro d
    change g ((Algebra.TensorProduct.includeLeft :
      T →ₐ[complexPolynomialRing n] TensorProduct (complexPolynomialRing n) T S)
        (algebraMap (complexPolynomialRing n) T d)) =
      g ((Algebra.TensorProduct.includeRight :
      S →ₐ[complexPolynomialRing n] TensorProduct (complexPolynomialRing n) T S)
        (algebraMap (complexPolynomialRing n) S d))
    rw [AlgHom.commutes, AlgHom.commutes]
  let X := {g : TensorProduct (complexPolynomialRing n) T S →ₐ[ℂ] ℂ // g.comp L ∈ E.source}
  let f : X → Y := fun g => ⟨g.val.comp R, by
    change mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom (n := n) S (g.val.comp R)) ∈ E.target
    rw [← hproj, ← etaleAlgHomProjectionChart_apply_of_mem T u _ g.property]
    exact E.map_source g.property⟩
  let j : Y → X := fun w => ⟨G w, by rw [hGL]; exact hv w⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro s
    exact (ComplexPoint.continuous_affineAlgebraHom_apply _ (R s)).comp continuous_subtype_val
  refine ⟨{
    toFun := f
    invFun := j
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := hf
    continuous_invFun := hG.subtype_mk _ }, ?_⟩
  · intro g
    apply Subtype.ext
    apply a3b4a_gysin_baseChange_projection_injective T S u
      _ _ (j (f g)).property g.property
    intro s
    exact congrArg (fun v : S →ₐ[ℂ] ℂ => v s) (hGR (f g))
  · intro w
    exact Subtype.ext (hGR w)
  · intro g s
    rfl


open Topology in
/-- Restricting a localized base change to an etale parameter chart makes
its original source projection an open embedding on complex evaluations. -/
theorem a3b4a_gysin_localized_baseChange_projection_isOpenEmbedding
    {n : ℕ} (T S : Type) [CommRing T] [CommRing S] [Algebra ℂ T] [Algebra ℂ S]
    [Algebra (complexPolynomialRing n) T] [Algebra (complexPolynomialRing n) S]
    [IsScalarTower ℂ (complexPolynomialRing n) T] [IsScalarTower ℂ (complexPolynomialRing n) S]
    [Algebra.Etale (complexPolynomialRing n) T] (u : T →ₐ[ℂ] ℂ)
    (e : TensorProduct (complexPolynomialRing n) T S) :
    let A := TensorProduct (complexPolynomialRing n) T S
    let L := (Algebra.TensorProduct.includeLeft : T →ₐ[complexPolynomialRing n] A).restrictScalars ℂ
    let R := (Algebra.TensorProduct.includeRight : S →ₐ[complexPolynomialRing n] A).restrictScalars ℂ
    let E := etaleAlgHomProjectionChart (n := n) T u
    let N := {v : Localization.Away e →ₐ[ℂ] ℂ |
      (localizationAwayAlgHomMap A e v).comp L ∈ E.source}
    IsOpen N ∧ IsOpenEmbedding (fun v : N => (localizationAwayAlgHomMap A e v.val).comp R) := by
  classical
  let A := TensorProduct (complexPolynomialRing n) T S
  let L := (Algebra.TensorProduct.includeLeft : T →ₐ[complexPolynomialRing n] A).restrictScalars ℂ
  let R := (Algebra.TensorProduct.includeRight : S →ₐ[complexPolynomialRing n] A).restrictScalars ℂ
  let E := etaleAlgHomProjectionChart (n := n) T u
  let ℓ := localizationAwayAlgHomMap A e
  let D := {g : A →ₐ[ℂ] ℂ | g.comp L ∈ E.source}
  let N := ℓ ⁻¹' D
  have hℓ : IsOpenEmbedding ℓ := isOpenEmbedding_localizationAwayAlgHomMap A e
  have hleft : Continuous (fun g : A →ₐ[ℂ] ℂ => g.comp L) := by
    apply continuous_induced_rng.mpr
    exact continuous_pi fun t => ComplexPoint.continuous_affineAlgebraHom_apply A (L t)
  have hD : IsOpen D := E.open_source.preimage hleft
  have hN : IsOpen N := hD.preimage hℓ.continuous
  obtain ⟨H, hH⟩ := a3b4a_gysin_exists_baseChange_chart_homeomorph_aux (n := n) T S u
  let B := fun w : S →ₐ[ℂ] ℂ => mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom S w)
  have hB : Continuous B := (mvPolynomialAlgHomHomeomorph n).continuous.comp
    (continuous_induced_rng.mpr (continuous_pi fun d =>
      ComplexPoint.continuous_affineAlgebraHom_apply S
        (algebraMap (complexPolynomialRing n) S d)))
  have hY : IsOpen (B ⁻¹' E.target) := E.open_target.preimage hB
  have hmaps : Set.MapsTo ℓ N D := fun v hv => hv
  let j := hmaps.restrict
  have hj : IsOpenEmbedding j := hℓ.restrict hmaps hN
  have hcomp := hY.isOpenEmbedding_subtypeVal.comp (H.isOpenEmbedding.comp hj)
  change IsOpenEmbedding (fun v : N => (H (j v)).val) at hcomp
  have hEq : (fun v : N => (H (j v)).val) = (fun v : N => (ℓ v.val).comp R) := by
    funext v
    apply AlgHom.ext
    intro s
    exact hH (j v) s
  rw [hEq] at hcomp
  exact ⟨hN, hcomp⟩


open Topology in
/-- A finite localized comparison factor conserves the full quotient
lengths of original source evaluations on every smaller source neighborhood. -/
theorem a3b4a_gysin_localized_model_source_length_conservation
    {n : ℕ} (T S : Type) [CommRing T] [CommRing S] [Algebra ℂ T] [Algebra ℂ S]
    [Algebra (complexPolynomialRing n) T] [Algebra (complexPolynomialRing n) S]
    [IsScalarTower ℂ (complexPolynomialRing n) T] [IsScalarTower ℂ (complexPolynomialRing n) S]
    [Algebra.Etale (complexPolynomialRing n) T]
    (e : TensorProduct (complexPolynomialRing n) T S)
    [Module.Finite T (Localization.Away e)] [Module.Flat T (Localization.Away e)]
    (P : Ideal T) [P.IsPrime] [IsLocalRing (P.Fiber (Localization.Away e))]
    (u : T →ₐ[ℂ] ℂ) (hu : RingHom.ker u = P)
    (hzero : mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom T u) = 0)
    (w₀ : S →ₐ[ℂ] ℂ)
    (Q : Ideal (TensorProduct (complexPolynomialRing n) T S)) [Q.IsPrime] [Q.LiesOver P]
    (hQ : Q.comap Algebra.TensorProduct.includeRight.toRingHom = RingHom.ker w₀)
    (he : e ∉ Q) :
    ∃ N₀ : Set (S →ₐ[ℂ] ℂ), IsOpen N₀ ∧ w₀ ∈ N₀ ∧
      ∀ N : Set (S →ₐ[ℂ] ℂ), IsOpen N → w₀ ∈ N → N ⊆ N₀ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ →
          ∃ F : Finset (S →ₐ[ℂ] ℂ),
            (∀ w, w ∈ F ↔ w ∈ N ∧ ∀ j,
              w (algebraMap (complexPolynomialRing n) S (MvPolynomial.X j)) = a j) ∧
            ∑ w ∈ F, a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) w =
              Module.length (P.Fiber (Localization.Away e)) (P.Fiber (Localization.Away e)) := by
  classical
  let A := complexPolynomialRing n
  let D := TensorProduct A T S
  let J := Localization.Away e
  letI : Algebra S D := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower ℂ S D := IsScalarTower.of_algebraMap_eq'
    ((Algebra.TensorProduct.includeRight : S →ₐ[A] D).restrictScalars ℂ).comp_algebraMap.symm
  letI : IsScalarTower ℂ S J := IsScalarTower.to₁₂₄ ℂ S D J
  letI : IsScalarTower A S J := IsScalarTower.to₁₂₄ A S D J
  letI : Algebra.Etale S D :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.commRight A S T)
  letI : Algebra.Etale S J := inferInstance
  letI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing A T
  letI : Module.FinitePresentation T J := Module.finitePresentation_of_finite T J
  obtain ⟨v₀, hv₀B, hv₀S⟩ :=
    a3b4a_gysin_exists_localized_model_source_evaluation e P u hu w₀ Q hQ he
  let β := fun v : J →ₐ[ℂ] ℂ => v.comp (IsScalarTower.toAlgHom ℂ T J)
  let π := fun v : J →ₐ[ℂ] ℂ => v.comp (IsScalarTower.toAlgHom ℂ S J)
  let L := (Algebra.TensorProduct.includeLeft : T →ₐ[A] D).restrictScalars ℂ
  let R := (Algebra.TensorProduct.includeRight : S →ₐ[A] D).restrictScalars ℂ
  let ℓ := localizationAwayAlgHomMap D e
  let E := etaleAlgHomProjectionChart (n := n) T u
  let V := {v : J →ₐ[ℂ] ℂ | (ℓ v).comp L ∈ E.source}
  have hβ (v : J →ₐ[ℂ] ℂ) : β v = (ℓ v).comp L := by
    apply AlgHom.ext
    intro t
    change v (algebraMap T J t) = v (algebraMap D J (algebraMap T D t))
    rw [IsScalarTower.algebraMap_apply T D J]
  have hπeq (v : J →ₐ[ℂ] ℂ) : π v = (ℓ v).comp R := by
    apply AlgHom.ext
    intro s
    change v (algebraMap S J s) = v (algebraMap D J (algebraMap S D s))
    rw [IsScalarTower.algebraMap_apply S D J]
  obtain ⟨hV, hπV'⟩ := a3b4a_gysin_localized_baseChange_projection_isOpenEmbedding
    (n := n) T S u e
  have hπV : IsOpenEmbedding (fun v : V => π v.val) := by
    convert hπV' using 1
    funext v
    exact hπeq v.val
  have hπ : Continuous π := by
    apply continuous_induced_rng.mpr
    exact continuous_pi fun s => ComplexPoint.continuous_affineAlgebraHom_apply J (algebraMap S J s)
  have hv₀V : v₀ ∈ V := by
    change (ℓ v₀).comp L ∈ E.source
    rw [← hβ v₀]
    have hv : β v₀ = u := hv₀B
    rw [hv]
    exact mem_etaleAlgHomProjectionChart_source (n := n) T u
  let b := fun z : T →ₐ[ℂ] ℂ => mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom T z)
  let g := fun z : S →ₐ[ℂ] ℂ => mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom S z)
  have hb : Set.InjOn b E.source := by
    intro x hx y hy hxy
    exact E.injOn hx hy
      ((etaleAlgHomProjectionChart_apply_of_mem T u x hx).trans
        (hxy.trans (etaleAlgHomProjectionChart_apply_of_mem T u y hy).symm))
  have hβV : ∀ v ∈ V, β v ∈ E.source := by
    intro v hv
    rw [hβ v]
    exact hv
  have hcomm : ∀ v, b (β v) = g (π v) := by
    intro v
    apply congrArg (mvPolynomialAlgHomHomeomorph n)
    apply AlgHom.ext
    intro d
    change v (algebraMap T J (algebraMap A T d)) = v (algebraMap S J (algebraMap A S d))
    rw [← IsScalarTower.algebraMap_apply A T J, ← IsScalarTower.algebraMap_apply A S J]
  obtain ⟨U, hU, h0U, F, hF, hF0, hbase, hcons⟩ :=
    a3b4a_gysin_etale_parameter_length_trapping P u hu hzero v₀ hv₀B
  let U' := U ∩ F ⁻¹' E.source
  have hU' : IsOpen U' := hF.isOpen_inter_preimage hU E.open_source
  have h0U' : (0 : Fin n → ℂ) ∈ U' := by
    refine ⟨h0U, ?_⟩
    change F 0 ∈ E.source
    rw [hF0]
    exact mem_etaleAlgHomProjectionChart_source (n := n) T u
  obtain ⟨η, hη, hηU'⟩ := Metric.isOpen_iff.mp hU' 0 h0U'
  have hFD : ∀ a ∈ U', F a ∈ E.source := fun _ ha => ha.2
  have hbF : ∀ a ∈ U', b (F a) = a := by
    intro a ha
    change mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom T (F a)) = a
    rw [hbase a ha.1, Homeomorph.apply_symm_apply]
  have hweight : ∀ a ∈ U', ∀ v ∈ V, β v = F a →
      a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) (π v) =
        a3b4a_gysin_evaluationSliceLength (F a) v := by
    intro a ha v _ hv
    have h := a3b4a_gysin_etale_evaluation_slice_length
      (A := A) (B := T) (S := S) (T := J) (F a) v hv
    have haeval : (F a).comp (IsScalarTower.toAlgHom ℂ A T) = MvPolynomial.aeval a :=
      hbase a ha.1
    rw [haeval] at h
    exact h
  have hcons' : ∀ M : Set (J →ₐ[ℂ] ℂ), IsOpen M → v₀ ∈ M →
      ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ → a ∈ U' ∧
        ∃ K : Finset (J →ₐ[ℂ] ℂ), (∀ v, v ∈ K ↔ v ∈ M ∧ β v = F a) ∧
          ∑ v ∈ K, a3b4a_gysin_evaluationSliceLength (F a) v =
            Module.length (P.Fiber J) (P.Fiber J) := by
    intro M hM hvM
    obtain ⟨δ, hδ, hc⟩ := hcons M hM hvM
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro a ha
    obtain ⟨_, K, hK, hsum⟩ := hc a (lt_of_lt_of_le ha (min_le_left _ _))
    have haU' : a ∈ U' := hηU' (by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le ha (min_le_right _ _))
    exact ⟨haU', K, hK, hsum⟩
  obtain ⟨N₀, hN₀, hvN₀, hsource⟩ := a3b4a_gysin_source_chart_length_conservation
    π hπ β b g V hV hπV E.source hb hβV hcomm v₀ hv₀V U' F hFD hbF
    (fun z v => a3b4a_gysin_evaluationSliceLength z v)
    (fun a w => a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) w)
    (Module.length (P.Fiber J) (P.Fiber J)) hweight hcons'
  have hπ₀ : π v₀ = w₀ := hv₀S
  refine ⟨N₀, hN₀, ?_, ?_⟩
  · rwa [hπ₀] at hvN₀
  · intro N hN hwN hNN₀
    obtain ⟨δ, hδ, hc⟩ := hsource N hN (hπ₀.symm ▸ hwN) hNN₀
    refine ⟨δ, hδ, ?_⟩
    intro a ha
    obtain ⟨K, hK, hsum⟩ := hc a ha
    refine ⟨K, ?_, hsum⟩
    intro w
    rw [hK w]
    exact and_congr_right (fun _ =>
      ⟨fun h j => congrFun h j, fun h => funext h⟩)

/-- A flat polynomial source at a rational quasi-finite point supplies
exact local slice-length conservation on the original complex source. -/
theorem a3b4a_gysin_flat_polynomial_source_length_conservation
    {n : ℕ} (S : Type) [CommRing S] [Algebra ℂ S]
    [Algebra (complexPolynomialRing n) S] [IsScalarTower ℂ (complexPolynomialRing n) S]
    [Algebra.FiniteType (complexPolynomialRing n) S] [Module.Flat (complexPolynomialRing n) S]
    (q : Ideal S) [q.IsPrime] [Algebra.QuasiFiniteAt (complexPolynomialRing n) q]
    (w₀ : S →ₐ[ℂ] ℂ) (hw₀ : RingHom.ker w₀ = q)
    (hzero : w₀.comp (IsScalarTower.toAlgHom ℂ (complexPolynomialRing n) S) =
      MvPolynomial.aeval (0 : Fin n → ℂ))
    (m : ℕ) (hlen : a3b4a_gysin_evaluationSliceLength
      (MvPolynomial.aeval (0 : Fin n → ℂ)) w₀ = m) :
    ∃ N₀ : Set (S →ₐ[ℂ] ℂ), IsOpen N₀ ∧ w₀ ∈ N₀ ∧
      ∀ N : Set (S →ₐ[ℂ] ℂ), IsOpen N → w₀ ∈ N → N ⊆ N₀ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ →
          ∃ F : Finset (S →ₐ[ℂ] ℂ),
            (∀ w, w ∈ F ↔ w ∈ N ∧ ∀ j,
              w (algebraMap (complexPolynomialRing n) S (MvPolynomial.X j)) = a j) ∧
            ∑ w ∈ F, a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) w = m := by
  subst q
  let A := complexPolynomialRing n
  let v : A →ₐ[ℂ] ℂ := MvPolynomial.aeval (0 : Fin n → ℂ)
  let p := RingHom.ker v
  let q := RingHom.ker w₀
  letI : p.IsPrime := RingHom.ker_isPrime v
  letI : q.LiesOver p := by
    constructor
    change p = (RingHom.ker w₀.toRingHom).comap (algebraMap A S)
    rw [RingHom.comap_ker]
    exact (congrArg (fun f : A →ₐ[ℂ] ℂ => RingHom.ker f.toRingHom) hzero).symm
  obtain ⟨T, _, _, _, P, _, _, e, _, hfin, hflat, hlocal, hres, hpoint, hlength⟩ :=
    a3b4a_gysin_exists_exact_local_model p q
  letI : Algebra ℂ T := ((algebraMap A T).comp (algebraMap ℂ A)).toAlgebra
  letI : IsScalarTower ℂ A T := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨u, hu, hrestrict⟩ := a3b4a_gysin_exists_rational_comparison_point p P v rfl hres
  have hbaseu : etaleBaseAlgHom (n := n) T u = v := AlgHom.ext hrestrict
  have hzeroU : mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom T u) = 0 := by
    rw [hbaseu]
    exact (mvPolynomialAlgHomHomeomorph n).apply_symm_apply 0
  obtain ⟨Q, hQprime, hQP, hQS, heQ⟩ := hpoint
  letI := hQprime
  letI := hQP
  letI : Module.Finite T (Localization.Away e) := hfin
  letI : Module.Flat T (Localization.Away e) := hflat
  letI : IsLocalRing (P.Fiber (Localization.Away e)) := hlocal
  have hmodel := a3b4a_gysin_localized_model_source_length_conservation
    (n := n) T S e P u hu hzeroU w₀ Q hQS heQ
  let L := Localization.AtPrime q
  let I := p.map (algebraMap A L)
  change Module.length L (L ⧸ I) = m at hlen
  have hself : Module.length (L ⧸ I) (L ⧸ I) = (m : ℕ∞) :=
    (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm.trans hlen
  have hmP : Module.length (P.Fiber (Localization.Away e))
      (P.Fiber (Localization.Away e)) = (m : ℕ∞) := hlength.trans hself
  rw [hmP] at hmodel
  exact hmodel

/-- A finite-length regular coordinate slice constructs exact conserved
source fibre lengths without assuming global flatness of the source. -/
theorem a3b4a_gysin_regular_polynomial_source_length_conservation
    {n : ℕ} (S : Type) [CommRing S] [Algebra ℂ S] [Algebra.FiniteType ℂ S]
    [Algebra (complexPolynomialRing n) S] [IsScalarTower ℂ (complexPolynomialRing n) S]
    (q : Ideal S) [q.IsPrime] (w₀ : S →ₐ[ℂ] ℂ) (hw₀ : RingHom.ker w₀ = q)
    (hzero : ∀ j : Fin n, w₀ (algebraMap (complexPolynomialRing n) S (MvPolynomial.X j)) = 0)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime q)
      (List.ofFn (fun j : Fin n => algebraMap (complexPolynomialRing n)
        (Localization.AtPrime q) (MvPolynomial.X j))))
    (m : ℕ) (hlen : Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ Ideal.ofList
        (List.ofFn (fun j : Fin n => algebraMap (complexPolynomialRing n)
          (Localization.AtPrime q) (MvPolynomial.X j)))) = m) :
    ∃ N₀ : Set (S →ₐ[ℂ] ℂ), IsOpen N₀ ∧ w₀ ∈ N₀ ∧
      ∀ N : Set (S →ₐ[ℂ] ℂ), IsOpen N → w₀ ∈ N → N ⊆ N₀ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ →
          ∃ F : Finset (S →ₐ[ℂ] ℂ),
            (∀ w, w ∈ F ↔ w ∈ N ∧ ∀ j,
              w (algebraMap (complexPolynomialRing n) S (MvPolynomial.X j)) = a j) ∧
            ∑ w ∈ F, a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) w = m := by
  classical
  subst q
  let A := complexPolynomialRing n
  let q := RingHom.ker w₀
  let v : A →ₐ[ℂ] ℂ := MvPolynomial.aeval (0 : Fin n → ℂ)
  let L := Localization.AtPrime q
  letI : Algebra.FiniteType A S := Algebra.FiniteType.of_restrictScalars_finiteType ℂ A S
  letI : Algebra.QuasiFiniteAt A q :=
    a3b4a_gysin_polynomial_slice_quasiFinite q w₀ rfl hzero m hlen
  have hid : (RingHom.ker v).map (algebraMap A L) =
      Ideal.ofList (List.ofFn (fun j : Fin n => algebraMap A L (MvPolynomial.X j))) := by
    rw [← a3b4a_gysin_zero_parameter_ideal n, Ideal.map_ofList, List.map_ofFn]
    rfl
  have hlenEval : a3b4a_gysin_evaluationSliceLength v w₀ = (m : ℕ∞) := by
    change Module.length L (L ⧸ (RingHom.ker v).map (algebraMap A L)) = m
    rw [hid]
    exact hlen
  obtain ⟨f, hf, hflat⟩ := a3b4a_gysin_polynomial_source_flat_neighborhood
    q w₀ rfl hzero hreg m hlen
  have hfzero : w₀ f ≠ 0 := hf
  let Sf := Localization.Away f
  letI : Module.Flat A Sf := hflat
  letI : IsScalarTower ℂ A Sf := IsScalarTower.to₁₂₄ ℂ A S Sf
  letI : Algebra.FiniteType A Sf := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType A S) (inferInstance : Algebra.FiniteType S Sf)
  let w₁ : Sf →ₐ[ℂ] ℂ := (localizationAwayAlgHomHomeomorph S f).symm ⟨w₀, hfzero⟩
  let π := localizationAwayAlgHomMap S f
  have hw₁ (s : S) : w₁ (algebraMap S Sf s) = w₀ s :=
    nonvanishingAlgHomExtension_algebraMap S f ⟨w₀, hfzero⟩ s
  have hres : w₁.comp (IsScalarTower.toAlgHom ℂ S Sf) = w₀ := AlgHom.ext hw₁
  have hπ₀ : π w₁ = w₀ := hres
  let q₁ := RingHom.ker w₁
  letI : q₁.IsPrime := RingHom.ker_isPrime w₁
  letI : q₁.LiesOver q := by
    constructor
    change q = (RingHom.ker w₁.toRingHom).comap (algebraMap S Sf)
    rw [RingHom.comap_ker]
    exact (congrArg (fun z : S →ₐ[ℂ] ℂ => RingHom.ker z.toRingHom) hres).symm
  letI : Algebra.QuasiFiniteAt A q₁ := Algebra.QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver
    (R := A) q (RingHom.surjectiveOnStalks_of_isLocalization (Submonoid.powers f) Sf) q₁
  have hzero₁ : w₁.comp (IsScalarTower.toAlgHom ℂ A Sf) = MvPolynomial.aeval (0 : Fin n → ℂ) := by
    apply MvPolynomial.algHom_ext
    intro j
    change w₁ (algebraMap A Sf (MvPolynomial.X j)) = MvPolynomial.aeval (0 : Fin n → ℂ) (MvPolynomial.X j)
    rw [IsScalarTower.algebraMap_apply A S Sf, hw₁, MvPolynomial.aeval_X]
    exact hzero j
  have hlen₁ : a3b4a_gysin_evaluationSliceLength v w₁ = (m : ℕ∞) := by
    have hs := a3b4a_gysin_etale_source_evaluation_slice_length (A := A) (S := S) (T := Sf) v w₁
    rw [hres] at hs
    exact hs.symm.trans hlenEval
  have hc := a3b4a_gysin_flat_polynomial_source_length_conservation
    (n := n) Sf q₁ w₁ rfl hzero₁ m hlen₁
  let gX := fun w : Sf →ₐ[ℂ] ℂ => fun j : Fin n => w (algebraMap A Sf (MvPolynomial.X j))
  let gY := fun w : S →ₐ[ℂ] ℂ => fun j : Fin n => w (algebraMap A S (MvPolynomial.X j))
  have hparam : ∀ w, gY (π w) = gX w := by
    intro w
    funext j
    change w (algebraMap S Sf (algebraMap A S (MvPolynomial.X j))) = w (algebraMap A Sf (MvPolynomial.X j))
    rw [← IsScalarTower.algebraMap_apply A S Sf]
  have hweight : ∀ a w, gX w = a →
      a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) (π w) =
        a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) w := by
    intro a w _
    exact a3b4a_gysin_etale_source_evaluation_slice_length
      (A := A) (S := S) (T := Sf) (MvPolynomial.aeval a) w
  have hcX : ∃ N₀ : Set (Sf →ₐ[ℂ] ℂ), IsOpen N₀ ∧ w₁ ∈ N₀ ∧
      ∀ N : Set (Sf →ₐ[ℂ] ℂ), IsOpen N → w₁ ∈ N → N ⊆ N₀ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ →
          ∃ K : Finset (Sf →ₐ[ℂ] ℂ), (∀ w, w ∈ K ↔ w ∈ N ∧ gX w = a) ∧
            ∑ w ∈ K, a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) w = m := by
    obtain ⟨N₀, hN₀, hwN₀, hNcons⟩ := hc
    refine ⟨N₀, hN₀, hwN₀, ?_⟩
    intro N hN hwN hNN₀
    obtain ⟨δ, hδ, hδc⟩ := hNcons N hN hwN hNN₀
    refine ⟨δ, hδ, ?_⟩
    intro a ha
    obtain ⟨K, hK, hsum⟩ := hδc a ha
    refine ⟨K, ?_, hsum⟩
    intro w
    rw [hK w]
    exact and_congr_right (fun _ => ⟨fun h => funext h, fun h j => congrFun h j⟩)
  obtain ⟨N₀, hN₀, hwN₀, hNcons⟩ := a3b4a_gysin_openEmbedding_length_conservation
    π (isOpenEmbedding_localizationAwayAlgHomMap S f) gX gY hparam
    (fun a w => a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) w)
    (fun a w => a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) w)
    hweight w₁ (m : ℕ∞) hcX
  refine ⟨N₀, hN₀, ?_, ?_⟩
  · rwa [hπ₀] at hwN₀
  · intro N hN hwN hNN₀
    obtain ⟨δ, hδ, hδc⟩ := hNcons N hN (hπ₀.symm ▸ hwN) hNN₀
    refine ⟨δ, hδ, ?_⟩
    intro a ha
    obtain ⟨K, hK, hsum⟩ := hδc a ha
    refine ⟨K, ?_, hsum⟩
    intro w
    rw [hK w]
    exact and_congr_right (fun _ => ⟨fun h j => congrFun h j, fun h => funext h⟩)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency.types false in
theorem a3b4a_gysin_slice_exact_model_aux
    {Z K : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)} [IsNoetherian Z]
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (i : K ⟶ Z) (hi : IsClosedImmersion i) {n : ℕ}
    (U : Z.Opens) (hU : IsAffineOpen U) (g : Fin n → Γ(Z, U))
    (wC : ComplexPoint (Over.mk (i ≫ q))) (hw : i.base wC.underlying ∈ U)
    (hg0 : ∀ j, Point.evaluate (X := Over.mk q) U (g j) (a3b4_anMap (q := i ≫ q) (q' := q) i rfl
        wC) = 0)
    (hreg : RingTheory.Sequence.IsRegular (K.presheaf.stalk wC.underlying)
      (a3b4a_gysin_sliceSequence q i U g 0 wC.underlying hw))
    (m : ℕ) (hm : a3b4a_gysin_sliceLength q i U g 0 wC = m) :
    ∃ N₀ : Set (ComplexPoint (Over.mk (i ≫ q))), IsOpen N₀ ∧ wC ∈ N₀ ∧
      N₀ ⊆ {w | a3b4_anMap (q := i ≫ q) (q' := q) i rfl w ∈ Point.overOpen (X := Over.mk q) U} ∧
      ∀ N : Set (ComplexPoint (Over.mk (i ≫ q))), IsOpen N → wC ∈ N → N ⊆ N₀ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ →
          ∃ T : Finset (ComplexPoint (Over.mk (i ≫ q))),
            (∀ w, w ∈ T ↔ w ∈ N ∧ ∀ j, Point.evaluate (X := Over.mk q) U (g j) (a3b4_anMap (q := i
                ≫ q) (q' := q) i rfl w) = a j) ∧
            ∑ w ∈ T, a3b4a_gysin_sliceLength q i U g a w = m := by
  classical
  letI := hi
  let V := i ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage i
  let R := Γ(K, V)
  let A := MvPolynomial (Fin n) ℂ
  letI : Algebra ℂ R := overSpecAlgebra (Over.mk (i ≫ q)) V
  let φ : A →ₐ[ℂ] R := MvPolynomial.aeval (fun j => i.app U (g j))
  letI : Algebra A R := φ.toAlgebra
  haveI : IsScalarTower ℂ A R := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  haveI : LocallyOfFiniteType (i ≫ q) := inferInstance
  haveI : Algebra.FiniteType ℂ R := by
    rw [← RingHom.finiteType_algebraMap]
    change (algebraMap ℂ R).FiniteType
    apply ((i ≫ q).finiteType_appLE (isAffineOpen_top (Spec (CommRingCat.of ℂ))) hV
      (by simp only [Scheme.Hom.preimage_top, le_top])).comp
    exact RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective
  let p := (hV.primeIdealOf ⟨wC.underlying, hw⟩).asIdeal
  let E : R →ₐ[ℂ] ℂ := a3b4a_gysin_affine_evaluation (i ≫ q) V wC hw
  have hE (s : R) : E s = Point.evaluate (X := Over.mk (i ≫ q)) V s wC :=
    Point.evaluationHom_apply (X := Over.mk (i ≫ q)) V ⟨wC, hw⟩ s
  have hkernel : RingHom.ker E = p := a3b4a_gysin_affine_point_kernel V hV wC hw
  have hzeroR (j : Fin n) : E (algebraMap A R (MvPolynomial.X j)) = 0 := by
    change E (φ (MvPolynomial.X j)) = 0
    rw [MvPolynomial.aeval_X, hE]
    let f : Over.mk (i ≫ q) ⟶ Over.mk q := Over.homMk i rfl
    have he := Point.evaluate_map f U (g j) wC
    exact he.symm.trans (hg0 j)
  let L := Localization.AtPrime p
  have hcoord (j : Fin n) : algebraMap A L (MvPolynomial.X j) =
      algebraMap R L (i.app U (g j)) := by
    rw [IsScalarTower.algebraMap_apply A R L]
    change algebraMap R L (φ (MvPolynomial.X j)) = _
    rw [MvPolynomial.aeval_X]
  obtain ⟨hregEq, hlengthEq⟩ :=
    a3b4a_gysin_affine_slice_data V hV wC.underlying hw (fun j => i.app U (g j))
  have hseq : a3b4a_gysin_sliceSequence q i U g 0 wC.underlying hw =
      List.ofFn (fun j => K.presheaf.germ V wC.underlying hw (i.app U (g j))) := by
    simp only [a3b4a_gysin_sliceSequence, Pi.zero_apply, map_zero, sub_zero]
    rfl
  have hreg₀ := hreg
  rw [hseq] at hreg₀
  have hlen₀ := hm
  rw [a3b4a_gysin_sliceLength, dif_pos hw, hseq] at hlen₀
  have hregular := hregEq.mp hreg₀
  have hlength := hlengthEq.symm.trans hlen₀
  have hgl : List.ofFn (fun j : Fin n => algebraMap A L (MvPolynomial.X j)) =
      List.ofFn (fun j => algebraMap R L (i.app U (g j))) := congrArg List.ofFn (funext hcoord)
  have hc := a3b4a_gysin_regular_polynomial_source_length_conservation
    (n := n) R p E hkernel hzeroR (by
      change RingTheory.Sequence.IsRegular L
        (List.ofFn (fun j : Fin n => algebraMap A L (MvPolynomial.X j)))
      rw [hgl]
      exact hregular) m (by
      change Module.length L (L ⧸ Ideal.ofList
        (List.ofFn (fun j : Fin n => algebraMap A L (MvPolynomial.X j)))) = m
      rw [hgl]
      exact hlength)
  let e := a3b4a_gysin_affine_point_homeomorph (i ≫ q) V hV
  let π := fun z : R →ₐ[ℂ] ℂ => (e.symm z).val
  have hπ : Topology.IsOpenEmbedding π :=
    (Point.isOpen_overOpen (X := Over.mk (i ≫ q)) V).isOpenEmbedding_subtypeVal.comp
      e.symm.isOpenEmbedding
  have heval (z : {z : ComplexPoint (Over.mk (i ≫ q)) // z.underlying ∈ V}) :
      a3b4a_gysin_affine_evaluation (i ≫ q) V z.val z.property = e z := by
    apply AlgHom.ext
    intro s
    change Point.evaluationHom (X := Over.mk (i ≫ q)) V z s = e z s
    rw [Point.evaluationHom_apply]
    exact (a3b4a_gysin_affine_point_homeomorph_apply (i ≫ q) V hV z s).symm
  have hevalx (z : R →ₐ[ℂ] ℂ) :
      a3b4a_gysin_affine_evaluation (i ≫ q) V (π z) (e.symm z).property = z :=
    (heval (e.symm z)).trans (e.apply_symm_apply z)
  have hπ₀ : π E = wC := by
    have he₀ : E = e ⟨wC, hw⟩ := heval ⟨wC, hw⟩
    change (e.symm E).val = wC
    rw [he₀]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨wC, hw⟩)
  let gX := fun z : R →ₐ[ℂ] ℂ => fun j : Fin n => z (algebraMap A R (MvPolynomial.X j))
  let gY := fun z : ComplexPoint (Over.mk (i ≫ q)) => fun j : Fin n =>
    Point.evaluate (X := Over.mk q) U (g j) (a3b4_anMap (q := i ≫ q) (q' := q) i rfl z)
  have hparam : ∀ z, gY (π z) = gX z := by
    intro z
    funext j
    change Point.evaluate (X := Over.mk q) U (g j)
      (a3b4_anMap (q := i ≫ q) (q' := q) i rfl (π z)) = z (φ (MvPolynomial.X j))
    rw [MvPolynomial.aeval_X]
    let f : Over.mk (i ≫ q) ⟶ Over.mk q := Over.homMk i rfl
    have hs := a3b4a_gysin_affine_point_homeomorph_apply (i ≫ q) V hV (e.symm z) (i.app U (g j))
    exact (Point.evaluate_map f U (g j) (π z)).trans
      (hs.symm.trans (congrArg (fun v : R →ₐ[ℂ] ℂ => v (i.app U (g j))) (e.apply_symm_apply z)))
  have hweight : ∀ a z, gX z = a → a3b4a_gysin_sliceLength q i U g a (π z) =
      a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) z := by
    intro a z _
    have hs := a3b4a_gysin_affine_shifted_slice_length q i hi U hU g a (π z) (e.symm z).property
    exact hs.trans (congrArg (a3b4a_gysin_evaluationSliceLength (B := A) (T := R)
      (MvPolynomial.aeval a)) (hevalx z))
  have hcX : ∃ N₀ : Set (R →ₐ[ℂ] ℂ), IsOpen N₀ ∧ E ∈ N₀ ∧
      ∀ N : Set (R →ₐ[ℂ] ℂ), IsOpen N → E ∈ N → N ⊆ N₀ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ →
          ∃ K : Finset (R →ₐ[ℂ] ℂ), (∀ z, z ∈ K ↔ z ∈ N ∧ gX z = a) ∧
            ∑ z ∈ K, a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) z = m := by
    obtain ⟨N₀, hN₀, hEN₀, hNcons⟩ := hc
    refine ⟨N₀, hN₀, hEN₀, ?_⟩
    intro N hN hEN hNN₀
    obtain ⟨δ, hδ, hδc⟩ := hNcons N hN hEN hNN₀
    refine ⟨δ, hδ, ?_⟩
    intro a ha
    obtain ⟨K, hK, hsum⟩ := hδc a ha
    refine ⟨K, ?_, hsum⟩
    intro z
    rw [hK z]
    exact and_congr_right (fun _ => ⟨fun h => funext h, fun h j => congrFun h j⟩)
  obtain ⟨N₀, hN₀, hEN₀, hNcons⟩ := a3b4a_gysin_openEmbedding_length_conservation
    π hπ gX gY hparam
    (fun a z => a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) z)
    (fun a z => a3b4a_gysin_sliceLength q i U g a z)
    hweight E (m : ℕ∞) hcX
  refine ⟨N₀ ∩ Point.overOpen (X := Over.mk (i ≫ q)) V,
    hN₀.inter (Point.isOpen_overOpen (X := Over.mk (i ≫ q)) V), ⟨hπ₀ ▸ hEN₀, hw⟩, ?_, ?_⟩
  · intro z hz
    let f : Over.mk (i ≫ q) ⟶ Over.mk q := Over.homMk i rfl
    exact (Point.mem_overOpen_map_iff f z U).mpr hz.2
  · intro N hN hwN hNN₀
    obtain ⟨δ, hδ, hδc⟩ := hNcons N hN (hπ₀.symm ▸ hwN) (fun z hz => (hNN₀ hz).1)
    refine ⟨δ, hδ, ?_⟩
    intro a ha
    obtain ⟨K, hK, hsum⟩ := hδc a ha
    refine ⟨K, ?_, hsum⟩
    intro z
    rw [hK z]
    exact and_congr_right (fun _ => ⟨fun h j => congrFun h j, fun h => funext h⟩)

theorem a3b4a_gysin_model_intersections_equiv_aux
    {Z K : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)} [IsNoetherian Z]
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (i : K ⟶ Z) (hi : IsClosedImmersion i) (c : ℕ) {n : ℕ}
    (U : Z.Opens) (hU : IsAffineOpen U) (g : Fin n → Γ(Z, U))
    (wC : ComplexPoint (Over.mk (i ≫ q))) (hw : i.base wC.underlying ∈ U)
    (m : ℕ) (hm : a3b4a_gysin_sliceLength q i U g 0 wC = m)
    (Φ : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦU : Φ.source ⊆ Point.overOpen (X := Over.mk q) U)
    (hΦg : ∀ z ∈ Φ.source, ∀ j, (Φ z).1 j = Point.evaluate (X := Over.mk q) U (g j) (z))
    (hΦw : a3b4_anMap (q := i ≫ q) (q' := q) i rfl wC ∈ Φ.source) (hΦ0 : Φ (a3b4_anMap (q := i ≫ q)
        (q' := q) i rfl wC) = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ v ∈ Metric.closedBall (0 : Fin c → ℂ) ρ, ((0 : Fin n → ℂ), v) ∈ Φ.target) ∧
      (∀ v ∈ Metric.closedBall (0 : Fin c → ℂ) ρ, Φ.symm (0, v) ∈ a3b4_cycleSupport q
          (a3b3_imageCycle i inferInstance) → v = 0) ∧
      ∃ N₁ : Set (ComplexPoint (Over.mk (i ≫ q))), IsOpen N₁ ∧ wC ∈ N₁ ∧
        ∀ N : Set (ComplexPoint (Over.mk (i ≫ q))), IsOpen N → wC ∈ N → N ⊆ N₁ →
          ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ →
            ∃ E : {w : ComplexPoint (Over.mk (i ≫ q)) //
                w ∈ N ∧ ∀ j, Point.evaluate (X := Over.mk q) U (g j) (a3b4_anMap (q := i ≫ q) (q'
                    := q) i rfl w) = a j} ≃
              {v : Fin c → ℂ // v ∈ Metric.ball 0 ρ ∧ (a, v) ∈ Φ.target ∧
                Φ.symm (a, v) ∈ a3b4_cycleSupport q (a3b3_imageCycle i inferInstance)},
              ∀ w, Φ.symm (a, (E w).1) = a3b4_anMap (q := i ≫ q) (q' := q) i rfl w.1 := by
  classical
  letI := hi
  let j : Over.mk (i ≫ q) ⟶ Over.mk q := Over.homMk i rfl
  letI : IsClosedImmersion j.left := hi
  let f := a3b4_anMap (q := i ≫ q) (q' := q) i rfl
  let χ := fun w : ComplexPoint (Over.mk (i ≫ q)) =>
    fun j : Fin n => Point.evaluate (X := Over.mk q) U (g j) (f w)
  have hcoord : ∀ w, f w ∈ Φ.source → (Φ (f w)).1 = χ w := by
    intro w hw'
    exact funext (hΦg (f w) hw')
  have hf : Topology.IsClosedEmbedding f :=
    ComplexPoint.isClosedEmbedding_map_of_closedImmersion j
  have hs : a3b4_cycleSupport q (a3b3_imageCycle i inferInstance) = Set.range f := by
    rw [a3b4a_gysin_imageCycle_support]
    exact (ComplexPoint.range_map_of_closedImmersion j).symm
  have hzero : ∀ j, Point.evaluate (X := Over.mk q) U (g j) (f wC) = 0 := by
    intro j
    exact (hΦg (f wC) hΦw j).symm.trans
      (congrArg (fun z : (Fin n → ℂ) × (Fin c → ℂ) => z.1 j) hΦ0)
  obtain ⟨N₀, hN₀, hwN₀, _, hisolate⟩ :=
    a3b4a_gysin_affine_slice_isolated i hi U hU g wC hw hzero m hm
  have hχ : ∀ w ∈ N₀, χ w = 0 → w = wC := by
    intro w hw' hg
    exact hisolate w hw' (fun j => congrFun hg j)
  obtain ⟨ρ, hρ, hball, hiso⟩ := a3b4a_gysin_chart_isolated_normal_radius
    f hf χ Φ hcoord wC hΦw hΦ0 N₀ hN₀ hwN₀ hχ
  rw [hs]
  refine ⟨ρ, hρ, hball, hiso, ?_⟩
  obtain ⟨N₁, hN₁, hwN₁, htrap⟩ := a3b4a_gysin_chart_trapped_intersection_equiv
    f hf χ Φ hcoord wC hΦw hΦ0 ρ hρ hball hiso
  refine ⟨N₁, hN₁, hwN₁, ?_⟩
  intro N hN hwN hNN₁
  obtain ⟨δ, hδ, hequiv⟩ := htrap N hN hwN hNN₁
  refine ⟨δ, hδ, ?_⟩
  intro a ha
  obtain ⟨E, hE⟩ := hequiv a ha
  let E₀ : {w : ComplexPoint (Over.mk (i ≫ q)) // w ∈ N ∧
      ∀ j, Point.evaluate (X := Over.mk q) U (g j) (f w) = a j} ≃
      {w : ComplexPoint (Over.mk (i ≫ q)) // w ∈ N ∧ χ w = a} :=
    Equiv.subtypeEquivRight (fun w => and_congr_right (fun _ =>
      ⟨fun h => funext h, fun h j => congrFun h j⟩))
  exact ⟨E₀.trans E, fun w => hE (E₀ w)⟩

theorem a3b4a_gysin_slice_regular_endpoint_aux
    {Z K : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)} [IsNoetherian Z]
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (i : K ⟶ Z) (hi : IsClosedImmersion i) (c : ℕ)
    (hc : ∀ ξ ∈ (a3b3_imageCycle i inferInstance).support, (c : ℕ∞) ≤ Order.coheight ξ)
    {n : ℕ} (Φ : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin n → ℂ) × (Fin c → ℂ))) (hΦ
        : a3b4_IsHolChart q Φ)
    (ρ : ℝ) (hρ : ∀ v ∈ Metric.closedBall (0 : Fin c → ℂ) ρ, ((0 : Fin n → ℂ), v) ∈ Φ.target) :
    ∃ (F : C((Fin n → ℂ) × (Fin c → ℂ), ComplexPoint (Over.mk q))) (δ : ℝ), 0 < δ ∧
      (∀ a : Fin n → ℂ, ‖a‖ < δ → ∀ v ∈ Metric.closedBall (0 : Fin c → ℂ) ρ,
        (a, v) ∈ Φ.target ∧ F (a, v) = Φ.symm (a, v)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ a : Fin n → ℂ, ‖a‖ < ε ∧
        ∀ v ∈ Metric.ball (0 : Fin c → ℂ) ρ, F (a, v) ∈ a3b4_cycleSupport q (a3b3_imageCycle i
            inferInstance) →
          ∃ C : A3b4aGysinNormalChart q (a3b3_imageCycle i inferInstance) c, F (a, v) = C.point ∧
          ∃ A : Matrix (Fin c) (Fin c) ℂ, A.det ≠ 0 ∧
            HasFDerivAt (fun v' => (C.chart (F (a, v' + v))).2)
              (A.mulVecLin.toContinuousLinearMap : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) 0 := by
  letI : LocallyOfFiniteType (Over.mk q).hom := ‹LocallyOfFiniteType q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  obtain ⟨U, hU, hdim⟩ := a3b4a_gysin_chart_support_dimension_region
    (Over.mk q) (a3b3_imageCycle i inferInstance) hc Φ hΦ
  obtain ⟨B, hB, hnormal⟩ := a3b4a_gysin_open_support_normal_parameters
    (Over.mk q) (a3b3_imageCycle i inferInstance) U n c hdim Φ hΦ
  obtain ⟨F, δ, hδ, hF⟩ := a3b4a_gysin_chart_continuous_disk_family Φ ρ hρ
  refine ⟨F, δ, hδ, hF, ?_⟩
  intro ε hε
  obtain ⟨a, ha, hnot⟩ := a3b4a_gysin_small_parameter_avoiding_null_sets
    (fun _ : Unit => B) (fun _ => hB) (min ε δ) (lt_min hε hδ)
  have haδ : ‖a‖ < δ := ha.trans_le (min_le_right ε δ)
  refine ⟨a, ha.trans_le (min_le_left ε δ), ?_⟩
  intro v hv hs
  obtain ⟨htarget, heq⟩ := hF a haδ v (Metric.ball_subset_closedBall hv)
  have hy : F (a, v) ∈ Φ.source := heq.symm ▸ Φ.map_target htarget
  have hcoord : Φ (F (a, v)) = (a, v) := by rw [heq, Φ.right_inv htarget]
  have hn : (Φ (F (a, v))).1 ∉ B := by
    rw [hcoord]
    exact hnot ()
  obtain ⟨C, hC, hd⟩ := hnormal (F (a, v)) hy (hU _ hy) hs hn
  simp only [hcoord] at hd
  refine ⟨C, hC.symm, 1, by simp only [Matrix.det_one, ne_eq, one_ne_zero, not_false_eq_true], ?_⟩
  have hder := a3b4a_gysin_disk_family_derivative Φ F ρ a v hv
    (fun u hu => (hF a haδ u hu).2) (fun y => (C.chart y).2)
    (ContinuousLinearMap.id ℂ (Fin c → ℂ)) hd
  have hid : ((1 : Matrix (Fin c) (Fin c) ℂ).mulVecLin.toContinuousLinearMap :
      (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) = ContinuousLinearMap.id ℂ (Fin c → ℂ) := by
    ext u k
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_one,
      LinearMap.id_apply, ContinuousLinearMap.id_apply]
  rw [hid]
  exact hder

theorem a3b4a_gysin_normal_evaluation_good_locus_aux
    {Z K : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)} [IsNoetherian Z]
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (h : Z ⟶ a3b2_line ℂ) [Smooth h] (hq : h ≫ a3b2_lineToBase ℂ = q)
    (i : K ⟶ Z) (hi : IsClosedImmersion i) (hK : K ⟶ a3b2_line ℂ) (hiK : i ≫ h = hK)
    (hflat : Flat hK) (c : ℕ)
    (hc : ∀ ξ ∈ (a3b3_imageCycle i inferInstance).support, (c : ℕ∞) ≤ Order.coheight ξ)
    (s : ℂ) (r : ℕ)
    (e : OpenPartialHomeomorph
      (ComplexPoint (Over.mk (pullback.fst h (a3b2_point ℂ s) ≫ q)))
      ((Fin r → ℂ) × (Fin c → ℂ)))
    (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport (pullback.fst h (a3b2_point ℂ s) ≫ q)
      (a3b3_imageCycle (a3b4a_fibreMap i h hK hiK s) (a3b4a_fibre_isNoetherian h s)) ↔
        (e y).2 = 0)
    (he : a3b4_IsHolChart (pullback.fst h (a3b2_point ℂ s) ≫ q) e)
    (y : ComplexPoint (Over.mk (pullback.fst h (a3b2_point ℂ s) ≫ q))) (hy : y ∈ e.source)
    (hyS : y ∈ a3b4_cycleSupport (pullback.fst h (a3b2_point ℂ s) ≫ q)
      (a3b3_imageCycle (a3b4a_fibreMap i h hK hiK s) (a3b4a_fibre_isNoetherian h s)))
    (m : ℕ) (hmult : a3b4_multiplicity (pullback.fst h (a3b2_point ℂ s) ≫ q) (a3b3_imageCycle
        (a3b4a_fibreMap i h hK hiK s) (a3b4a_fibre_isNoetherian h s)) y = m)
    (U : Z.Opens) (g : Fin (r + 1) → Γ(Z, U)) (wC : ComplexPoint (Over.mk (i ≫ q)))
    (Φ : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin (r + 1) → ℂ) × (Fin c → ℂ)))
    (g₀ : (Fin c → ℂ) → ComplexPoint (Over.mk (pullback.fst h (a3b2_point ℂ s) ≫ q)))
    (V : Set (Fin c → ℂ)) (hV : IsOpen V) (h0V : 0 ∈ V) (hg₀ : ContinuousOn g₀ V)
    (hg₀0 : g₀ 0 = y)
    (hΦV : ∀ v ∈ V, ((0 : Fin (r + 1) → ℂ), v) ∈ Φ.target ∧ Φ.symm (0, v) = a3b4_anMap (q' := q)
        (pullback.fst h (a3b2_point ℂ s)) rfl (g₀ v))
    (A : Matrix (Fin c) (Fin c) ℂ) (hA : A.det ≠ 0)
    (hderiv : HasFDerivAt (fun v => (e (g₀ v)).2) (A.mulVecLin.toContinuousLinearMap : (Fin c → ℂ)
        →L[ℂ] (Fin c → ℂ)) 0)
    (N₀ : Set (ComplexPoint (Over.mk (i ≫ q)))) (hN₀ : IsOpen N₀) (hwN₀ : wC ∈ N₀)
    (hcons : ∀ N : Set (ComplexPoint (Over.mk (i ≫ q))), IsOpen N → wC ∈ N → N ⊆ N₀ →
      ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin (r + 1) → ℂ, ‖a‖ < δ →
        ∃ T : Finset (ComplexPoint (Over.mk (i ≫ q))),
          (∀ w, w ∈ T ↔ w ∈ N ∧ ∀ j, Point.evaluate (X := Over.mk q) U (g j) (a3b4_anMap (q := i ≫
              q) (q' := q) i rfl w) = a j) ∧
          ∑ w ∈ T, a3b4a_gysin_sliceLength q i U g a w = m)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hiso : ∀ v ∈ Metric.closedBall (0 : Fin c → ℂ) ρ, Φ.symm (0, v) ∈ a3b4_cycleSupport q
        (a3b3_imageCycle i inferInstance) → v = 0)
    (N₁ : Set (ComplexPoint (Over.mk (i ≫ q)))) (hN₁ : IsOpen N₁) (hwN₁ : wC ∈ N₁)
    (hident : ∀ N : Set (ComplexPoint (Over.mk (i ≫ q))), IsOpen N → wC ∈ N → N ⊆ N₁ →
      ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin (r + 1) → ℂ, ‖a‖ < δ →
        ∃ E : {w : ComplexPoint (Over.mk (i ≫ q)) //
            w ∈ N ∧ ∀ j, Point.evaluate (X := Over.mk q) U (g j) (a3b4_anMap (q := i ≫ q) (q' := q)
                i rfl w) = a j} ≃
          {v : Fin c → ℂ // v ∈ Metric.ball 0 ρ ∧ (a, v) ∈ Φ.target ∧
            Φ.symm (a, v) ∈ a3b4_cycleSupport q (a3b3_imageCycle i inferInstance)},
          ∀ w, Φ.symm (a, (E w).1) = a3b4_anMap (q := i ≫ q) (q' := q) i rfl w.1)
    (F : C((Fin (r + 1) → ℂ) × (Fin c → ℂ), ComplexPoint (Over.mk q))) (δ : ℝ) (hδ : 0 < δ)
    (hF : ∀ a : Fin (r + 1) → ℂ, ‖a‖ < δ → ∀ v ∈ Metric.closedBall (0 : Fin c → ℂ) ρ,
      (a, v) ∈ Φ.target ∧ F (a, v) = Φ.symm (a, v))
    (htrans : ∀ ε : ℝ, 0 < ε → ∃ a : Fin (r + 1) → ℂ, ‖a‖ < ε ∧
      ∀ v ∈ Metric.ball (0 : Fin c → ℂ) ρ, F (a, v) ∈ a3b4_cycleSupport q (a3b3_imageCycle i
          inferInstance) →
        ∃ C : A3b4aGysinNormalChart q (a3b3_imageCycle i inferInstance) c, F (a, v) = C.point ∧
        ∃ A : Matrix (Fin c) (Fin c) ℂ, A.det ≠ 0 ∧
          HasFDerivAt (fun v' => (C.chart (F (a, v' + v))).2)
            (A.mulVecLin.toContinuousLinearMap : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) 0)
    (N₂ : Set (ComplexPoint (Over.mk (i ≫ q)))) (hN₂ : IsOpen N₂) (hwN₂ : wC ∈ N₂)
    (hweight : ∀ w ∈ N₂, ∀ (a : Fin (r + 1) → ℂ) (v : Fin c → ℂ), (a, v) ∈ Φ.target →
      a3b4_anMap (q := i ≫ q) (q' := q) i rfl w = Φ.symm (a, v) →
      ∀ C : A3b4aGysinNormalChart q (a3b3_imageCycle i inferInstance) c, a3b4_anMap (q := i ≫ q)
          (q' := q) i rfl w = C.point →
      ∀ A : Matrix (Fin c) (Fin c) ℂ, A.det ≠ 0 →
        HasFDerivAt (fun v' => (C.chart (Φ.symm (a, v' + v))).2) (A.mulVecLin.toContinuousLinearMap
            : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) 0 →
        ∃ k : ℕ, a3b4a_gysin_sliceLength q i U g a w = k ∧
          a3b4_multiplicity q (a3b3_imageCycle i inferInstance) (a3b4_anMap (q := i ≫ q) (q' := q)
              i rfl w) = k) :
    letI := a3b4a_gysin_ambient_smooth h hq
    let γs := a3b3_imageCycle (a3b4a_fibreMap i h hK hiK s) (a3b4a_fibre_isNoetherian h s)
    let qs := pullback.fst h (a3b2_point ℂ s) ≫ q
    let S := a3b4_cycleSupport qs γs
    relativeCohomologyEquivDualHomology ℚ _ (2 * c)
      (relativeCohomologyMap ℚ (2 * c)
        (a3b4_neighborhoodPairMap (flattenedSupportNeighborhood (Fin r → ℂ) c e y hy) S)
        (relativeCohomologyMap ℚ (2 * c)
          (a3b4_supportPairMap
            (a3b4_anMap (q' := q) (pullback.fst h (a3b2_point ℂ s)) rfl)
            S (a3b4_cycleSupport q (a3b3_imageCycle i inferInstance))
            (fun y hy => (a3b4a_gysin_fibre_support q i h hK hiK s y).mp hy))
          (a3b4a_gysin_fundamentalClass q i c hc)))
      (flattenedSupportNormalClass (Fin r → ℂ) c e y hy S hS ((hS y hy).mp hyS)) =
        a3b4_multiplicity qs γs y := by
  classical
  letI := a3b4a_gysin_ambient_smooth h hq
  let γ := a3b3_imageCycle i inferInstance
  let γs := a3b3_imageCycle (a3b4a_fibreMap i h hK hiK s) (a3b4a_fibre_isNoetherian h s)
  let qs := pullback.fst h (a3b2_point ℂ s) ≫ q
  let S := a3b4_cycleSupport qs γs
  let T := a3b4_cycleSupport q γ
  let β := a3b4a_gysin_fundamentalClass q i c hc
  have hβ := a3b4a_gysin_fundamentalClass_normalized q i c hc
  have hzero : ‖(0 : Fin (r + 1) → ℂ)‖ < δ := by simpa only [norm_zero] using hδ
  have hisoF : ∀ v ∈ Metric.closedBall (0 : Fin c → ℂ) ρ, F (0, v) ∈ T → v = 0 := by
    intro v hv hs
    rw [(hF 0 hzero v hv).2] at hs
    exact hiso v hv hs
  obtain ⟨ε, hε, heval⟩ := a3b4a_gysin_small_transverse_deformation_evaluation γ c F ρ hρ
    hisoF β hβ
  let N := (N₀ ∩ N₁) ∩ N₂
  have hN : IsOpen N := (hN₀.inter hN₁).inter hN₂
  have hwN : wC ∈ N := ⟨⟨hwN₀, hwN₁⟩, hwN₂⟩
  obtain ⟨δ₀, hδ₀, hcon⟩ := hcons N hN hwN (fun _ hx => hx.1.1)
  obtain ⟨δ₁, hδ₁, hid⟩ := hident N hN hwN (fun _ hx => hx.1.2)
  obtain ⟨a, ha, hat⟩ := htrans (min δ (min ε (min δ₀ δ₁)))
    (lt_min hδ (lt_min hε (lt_min hδ₀ hδ₁)))
  have haδ : ‖a‖ < δ := lt_of_lt_of_le ha (min_le_left _ _)
  have haε : ‖a‖ < ε := lt_of_lt_of_le ha ((min_le_right _ _).trans (min_le_left _ _))
  have ha₀ : ‖a‖ < δ₀ := lt_of_lt_of_le ha
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ha₁ : ‖a‖ < δ₁ := lt_of_lt_of_le ha
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨P, hP, hsum⟩ := hcon a ha₀
  obtain ⟨E, hE⟩ := hid a ha₁
  obtain ⟨Q, hQball, hQ, hQeval⟩ := heval a haε hat
  have htar (v : Fin c → ℂ) :
      (v ∈ Metric.ball 0 ρ ∧ (a, v) ∈ Φ.target ∧ Φ.symm (a, v) ∈ T) ↔ v ∈ Q := by
    constructor
    · rintro ⟨hv, _, hs⟩
      apply (hQ v hv).mp
      rw [(hF a haδ v (Metric.ball_subset_closedBall hv)).2]
      exact hs
    · intro hv
      have hb := hQball hv
      refine ⟨hb, (hF a haδ v (Metric.ball_subset_closedBall hb)).1, ?_⟩
      rw [← (hF a haδ v (Metric.ball_subset_closedBall hb)).2]
      exact (hQ v hb).mpr hv
  let EP : P ≃ Q := (Equiv.subtypeEquivRight hP).trans
    (E.trans (Equiv.subtypeEquivRight htar))
  have hEP (w : P) : Φ.symm (a, (EP w).1) =
      a3b4_anMap (q := i ≫ q) (q' := q) i rfl w.1 := hE _
  have hweights (w : P) : ∃ k : ℕ,
      a3b4a_gysin_sliceLength q i U g a w.1 = k ∧
        a3b4_multiplicity q γ (F (a, (EP w).1)) = k := by
    let v := (EP w).1
    have hv : v ∈ Metric.ball 0 ρ := hQball (EP w).2
    have hsup : F (a, v) ∈ T := (hQ v hv).mpr (EP w).2
    obtain ⟨C, hC, B, hB, hd⟩ := hat v hv hsup
    have hfv : F (a, v) = Φ.symm (a, v) := (hF a haδ v (Metric.ball_subset_closedBall hv)).2
    have heq : (fun v' => (C.chart (Φ.symm (a, v' + v))).2) =ᶠ[𝓝 0]
        (fun v' => (C.chart (F (a, v' + v))).2) := by
      have ht : Filter.Tendsto (fun v' : Fin c → ℂ => v' + v) (𝓝 0) (𝓝 v) := by
        have hc : Continuous (fun v' : Fin c → ℂ => v' + v) := continuous_add_const v
        convert hc.tendsto (0 : Fin c → ℂ) using 1 <;> rw [zero_add]
      filter_upwards [ht (Metric.isOpen_ball.mem_nhds hv)] with v' hv'
      rw [(hF a haδ (v' + v) (Metric.ball_subset_closedBall hv')).2]
    obtain ⟨k, hk, hmult⟩ := hweight w.1 ((hP w.1).mp w.2).1.2 a v
      (hF a haδ v (Metric.ball_subset_closedBall hv)).1 (hEP w).symm C
      ((hEP w).symm.trans (hfv.symm.trans hC)) B hB (hd.congr_of_eventuallyEq heq)
    refine ⟨k, hk, ?_⟩
    rw [hfv, hEP w]
    exact hmult
  have hsumn : ∑ w : P, a3b4a_gysin_sliceLength q i U g a w.1 = m := by
    simpa only [Finset.sum_coe_sort] using hsum
  have hsumQ : ∑ v : Q, a3b4_multiplicity q γ (F (a, v.1)) = m :=
    a3b4a_gysin_sum_weights_of_length_equiv EP
      (fun w => a3b4a_gysin_sliceLength q i U g a w.1)
      (fun v => a3b4_multiplicity q γ (F (a, v.1))) m hsumn hweights
  let f := a3b4_anMap (q' := q) (pullback.fst h (a3b2_point ℂ s)) rfl
  let F₀ : C((Fin c → ℂ), ComplexPoint (Over.mk q)) :=
    ⟨fun v => F (0, v), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  obtain ⟨z, hz, hclass⟩ := a3b4a_gysin_disk_image_normalClass e S T hS y hy hyS
    f.hom (fun y hy => (a3b4a_gysin_fibre_support q i h hK hiK s y).mp hy)
    g₀ V hV h0V hg₀ hg₀0 A hA hderiv F₀ ρ hρ
    (by
      intro v hv
      exact ((hF 0 hzero v (Metric.ball_subset_closedBall hv.2)).2).trans (hΦV v hv.1).2)
    (fun v hv hs => hisoF v (Metric.ball_subset_closedBall hv) hs)
  have hvalue := (hQeval z hz).trans hsumQ
  dsimp only
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    relativeCohomologyEquivDualHomology_relativeCohomologyMap]
  rw [hmult]
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap, hclass] at hvalue
  exact hvalue

end HodgeLean.Adapters
