import HodgeLean.Adapters.PWTheorem42EisensteinDefs
import HodgeLean.Adapters.AbelianPowerHodge
import HodgeLean.Adapters.PowersVocabulary
import HodgeLean.Adapters.AbelianHomPullbackDegrees
import HodgeLean.Adapters.F1575PowersFix

/-! # Theorem 4.2 at `L = k = ℚ(√-3)`, stage F1: proof obligations

One `_aux` theorem per statement of `PWTheorem42Eisenstein.lean`, all open. HC no distance; AV
milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Adapters

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]
variable {L : Type*} [Field L] [Algebra ℚ L]

theorem f1_hodgeLieIsGk_iff_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u)) :
    letI := (finiteBetti_abelian A).finite 1
    HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u) ↔
      complexSpan (hodgeLieAlgebra (abelianWeightOneHodgeStructure A).H
          (abelianWeightOneHodgeStructure A).isInternal).toSubmodule =
        (complexSU (polarizationForm (torusCohomology_cupProductOf A) hη)
          (nondegenerate_polarizationForm (torusCohomology_cupProductOf A) hη)
          (f1_weilAction A θ u 3 hu).J (f1_weilAction A θ u 3 hu).J_sq
          (polarizationForm_skew (torusCohomology_cupProductOf A) hη hRos)).toSubmodule := by
  let _ := (finiteBetti_abelian A).finite 1
  rw [spec_g4_pwActionRange_eq_adjoin A θ u hL]
  exact spec_pw0_hodgeLieIsGk_adjoin_iff _ _ _ _
    (isAlt_polarizationForm (torusCohomology_cupProductOf A) hη) _ _ _

theorem f1_rationalExteriorHodge_eq_divisorPulledWeilSpan_aux (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (m k : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal m k =
      divisorPulledWeilSpan (pwAction A θ u)
        (rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
          (abelianWeightOneHodgeStructure A).isInternal m 2)
        ((f1_weilAction A θ u 3 hu).weilClasses
          (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
            (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A))
          (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
            (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
              (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)) k := by
  let _ := (finiteBetti_abelian A).finite 1
  exact spec_pw0_rationalExteriorHodge_eq_divisorPulledWeilSpan (f1_weilAction A θ u 3 hu) _ _
    (polarizationForm (torusCohomology_cupProductOf A) hη)
    (nondegenerate_polarizationForm (torusCohomology_cupProductOf A) hη)
    (polarizationForm_skew (torusCohomology_cupProductOf A) hη hRos)
    ((f1_hodgeLieIsGk_iff_aux A θ u hu hL pol hη hRos).1 hGk) m k

variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

theorem f1_pwPowerSpan_zero_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
    (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) :
    pwPowerSpan A θ u d hu hW P 0 = ⊤ := by
  let _ := (finiteBetti_abelian A).finite 1
  unfold pwPowerSpan
  rw [eq_top_iff]
  rintro y -
  obtain ⟨v, rfl⟩ := (spec_g2_cohomologyMap_bijective P (2 * 0)).2 y
  refine Submodule.mem_map_of_mem ?_
  have hspan := exteriorPower.ιMulti_span (R := ℚ) (n := 0)
    (M := HQ A 1 ⊗[ℚ] (Fin r → ℚ))
  have hv : v ∈ Submodule.span ℚ (Set.range (exteriorPower.ιMulti ℚ 0)) := hspan ▸ trivial
  refine Submodule.span_le.2 ?_ hv
  rintro _ ⟨f, rfl⟩
  rw [Subsingleton.elim f Fin.elim0]
  exact Submodule.mem_iInf _ |>.2 fun F => Submodule.mem_iInf _ |>.2 fun hF => hF.unit_mem

theorem pw_thm_4_2_generation_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(Y; ℚ) = pwPowerSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P p := by
  let := (finiteBetti_abelian A).finite 1
  intro p
  have hR := spec_g4_pwActionRange_eq_adjoin A θ u hL
  have hGk' : HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
      (abelianWeightOneHodgeStructure A).isInternal
      (polarizationForm (torusCohomology_cupProductOf A) hη)
      (Algebra.adjoin ℚ {(f1_weilAction A θ u 3 hu).J}) (f1_weilAction A θ u 3 hu).J :=
    hR ▸ hGk
  rw [← spec_g2_rationalExteriorHodge_map_eq P p,
    spec_pw0_rationalExteriorHodge_eq_cmPowerSpan (f1_weilAction A θ u 3 hu)
      (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A))
      (polarizationForm (torusCohomology_cupProductOf A) hη)
      (nondegenerate_polarizationForm (torusCohomology_cupProductOf A) hη)
      (isAlt_polarizationForm (torusCohomology_cupProductOf A) hη)
      (polarizationForm_skew (torusCohomology_cupProductOf A) hη hRos) hGk' r (2 * p)]
  exact congrArg (fun R => (cmPowerSpan R _ _ (2 * p)).map (P.cohomologyMap (2 * p))) hR.symm

set_option maxRecDepth 2000 in
omit [IsCommMonObj A] in
/-- `P.cohomologyMap` turns the wedge product of the model into the cup product of `Y`. -/
private theorem f1_cohomologyMap_wedge (P : AbelianPowerData A Y r) (i j : ℕ)
    (v : ⋀[ℚ]^i (HQ A 1 ⊗[ℚ] (Fin r → ℚ))) (w : ⋀[ℚ]^j (HQ A 1 ⊗[ℚ] (Fin r → ℚ))) :
    P.cohomologyMap (i + j) (exteriorPower.wedge ℚ _ i j v w) =
      (cupProductOf Y).cup rfl (P.cohomologyMap i v) (P.cohomologyMap j w) := by
  simp only [AbelianPowerData.cohomologyMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TorusCohomology.cupWedgeEquiv_apply, exteriorPower_map_wedge]
  exact CupProduct.cupWedgeMap_wedge _ i j _ _

set_option maxRecDepth 2000 in
omit [IsCommMonObj Y] in
/-- Rational Hodge classes of `Y` are closed under the cup product. -/
private theorem f1_cup_mem_hdg {p q : ℕ} (h : 2 * p + 2 * q = 2 * (p + q)) (a : HQ Y (2 * p))
    (b : HQ Y (2 * q)) (ha : (a : H^(2 * p)(Y; ℚ)) ∈ Hdg^p(Y; ℚ))
    (hb : (b : H^(2 * q)(Y; ℚ)) ∈ Hdg^q(Y; ℚ)) :
    ((cupProductOf Y).cup h a b : H^(2 * (p + q))(Y; ℚ)) ∈ Hdg^(p + q)(Y; ℚ) := by
  rw [mem_hodgeClasses_iff_tmul_mem] at ha hb ⊢
  have hp : ((p : ℤ), (p : ℤ)).1 + ((p : ℤ), (p : ℤ)).2 = ((2 * p : ℕ) : ℤ) := by push_cast; ring
  have hq : ((q : ℤ), (q : ℤ)).1 + ((q : ℤ), (q : ℤ)).2 = ((2 * q : ℕ) : ℤ) := by push_cast; ring
  have hpq : (((p + q : ℕ) : ℤ), ((p + q : ℕ) : ℤ)).1 + (((p + q : ℕ) : ℤ), ((p + q : ℕ) : ℤ)).2 =
      ((2 * (p + q) : ℕ) : ℤ) := by push_cast; ring
  rw [cohomologyHodgePiece, ite_eq_left_of_eq_true _ _ (eq_true hp), Submodule.mem_comap] at ha
  rw [cohomologyHodgePiece, ite_eq_left_of_eq_true _ _ (eq_true hq), Submodule.mem_comap] at hb
  rw [cohomologyHodgePiece, ite_eq_left_of_eq_true _ _ (eq_true hpq), Submodule.mem_comap]
  have := (cupFiltered_cupProductOf_of_abelian Y).mem_hodgePiece h _ _ ha hb
  rw [CupProduct.cupC_tmul, one_mul] at this
  rw [Nat.cast_add]
  exact this

omit [GrpObj Y] [IsCommMonObj Y] in
/-- Recasting the degree commutes with the pullback. -/
private theorem f1_castEquiv_homPullback {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : Y ⟶ X) {m n : ℕ} (h : m = n) (x : HQ X m) :
    HQ.castEquiv Y h (homPullback f m x) = homPullback f n (HQ.castEquiv X h x) := by
  subst h
  rw [HQ.castEquiv_apply_self, HQ.castEquiv_apply_self]

/-- The pulled-Weil cup span is itself a closed family. -/
private theorem f1_isPulledWeilClosed_span (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
    (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) (D : Submodule ℚ (HQ Y (2 * 1))) :
    f1_IsPulledWeilClosed A θ u d hu hW P D (f1_pulledWeilCupSpan A θ u d hu hW P D) where
  unit_mem := (Submodule.mem_iInf _).mpr fun _ => (Submodule.mem_iInf _).mpr fun hF =>
    hF.unit_mem
  divisor_le := le_iInf₂ fun _ hF => hF.divisor_le
  pullback_le a := le_iInf₂ fun _ hF => hF.pullback_le a
  cup_mem h a b ha hb := (Submodule.mem_iInf _).mpr fun F => (Submodule.mem_iInf _).mpr
    fun hF => hF.cup_mem h a b ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp ha F) hF)
      ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hb F) hF)


omit [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] in
/-- Membership survives recasting along an equation of the index. -/
private theorem f1_castEquiv_mem (S : ∀ p : ℕ, Submodule ℚ (HQ Y (2 * p))) (k₁ k₂ : ℕ)
    (hk : k₁ = k₂) (h₂ : 2 * k₁ = 2 * k₂) (z : HQ Y (2 * k₁)) (hz : z ∈ S k₁) :
    HQ.castEquiv Y h₂ z ∈ S k₂ := by
  subst hk
  simpa using hz

set_option maxRecDepth 2000 in
omit [GrpObj Y] [IsCommMonObj Y] in
/-- Transport of a pulled-back Weil class along an equation of the Weil degree. -/
private theorem f1_pullback_transport {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (cp : CupProduct X) (f : Y ⟶ X)
    (S : ∀ p : ℕ, Submodule ℚ (HQ Y (2 * p))) (k₁ k₂ : ℕ) (hk : k₁ = k₂)
    (W₁ : Submodule ℚ (⋀[ℚ]^(k₁ + k₁) (HQ X 1))) (h₂ : 2 * k₁ = 2 * k₂)
    (hle : ∀ v ∈ W₁, HQ.castEquiv Y h₂ (homPullback f (2 * k₁)
      (HQ.castEquiv X (two_mul k₁).symm (cp.cupWedgeMap (k₁ + k₁) v))) ∈ S k₂)
    (w : ⋀[ℚ]^(k₂ + k₂) (HQ X 1)) (hw : ∀ h : k₂ + k₂ = k₁ + k₁, h ▸ w ∈ W₁) :
    HQ.castEquiv Y (two_mul k₂).symm (homPullback f (k₂ + k₂) (cp.cupWedgeMap (k₂ + k₂) w)) ∈
      S k₂ := by
  subst hk
  have := hle w (hw rfl)
  rw [HQ.castEquiv_apply_self] at this
  rw [f1_castEquiv_homPullback]
  simpa using this

/-- A model pullback with coefficients in the image of `L` comes from coefficients in `L`. -/
private theorem f1_cmPowerPullback_eq (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (a : Fin r → pwActionRange A θ) :
    ∃ b : Fin r → L, cmPowerPullback (pwActionRange A θ) a = pwPowerPullback A θ b := by
  have h : ∀ i, ∃ y : L, pwAction A θ y = (a i : Module.End ℚ (HQ A 1)) := fun i => (a i).2
  choose b hb using h
  refine ⟨b, ?_⟩
  unfold pwPowerPullback
  congr 1
  funext i
  exact Subtype.ext (hb i).symm

set_option maxRecDepth 2000 in
/-- The model image of a Weil pullback with coefficients in `𝒪` lies in the even transport of a
closed family. -/
private theorem f1_pullback_mem (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
    (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) (D : Submodule ℚ (HQ Y (2 * 1)))
    (S : ∀ p : ℕ, Submodule ℚ (HQ Y (2 * p))) (hSc : f1_IsPulledWeilClosed A θ u d hu hW P D S)
    (a : Fin r → L) (ha : ∀ i, a i ∈ pwOrder A θ)
    (w : letI := (finiteBetti_abelian A).finite 1
      ⋀[ℚ]^(Module.finrank ℂ ↥((f1_weilAction A θ u d hu).Vs ⊓
          (abelianWeightOneHodgeStructure A).H (1, 0)) +
        Module.finrank ℂ ↥((f1_weilAction A θ u d hu).Vs ⊓
          (abelianWeightOneHodgeStructure A).H (1, 0))) (HQ A 1))
    (hw : letI := (finiteBetti_abelian A).finite 1
      w ∈ (f1_weilAction A θ u d hu).weilClasses
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) hW) :
    P.cohomologyMap _ (exteriorPower.map _ (pwPowerPullback A θ a) w) ∈
      f1575EvenCohomologySpanQ S _ := by
  let := (finiteBetti_abelian A).finite 1
  let a' : Fin r → pwOrder A θ := fun i => ⟨a i, ha i⟩
  have key := LinearMap.congr_fun (spec_g2_homPullback_pwSumMap_degree P θ a' _) w
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at key
  change P.cohomologyMap _ (exteriorPower.map _ (pwPowerPullback A θ fun i => (a' i : L)) w) ∈ _
  rw [← key]
  refine Or.inr ⟨_, (two_mul _).symm, ?_⟩
  rw [LinearEquiv.coe_coe, TorusCohomology.cupWedgeEquiv_apply]
  exact f1_pullback_transport (cupProductOf A) (P.pwSumMap θ a') S
    (Module.finrank ℂ ↥(@HodgeBlocks.WeilAction.Vs _ _ _ _ (abelianVarietyCohomologyOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)).weight1 d (f1_weilAction A θ u d hu) ⊓
      (abelianVarietyCohomologyOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)).weight1.H (1, 0)))
    (Module.finrank ℂ ↥((f1_weilAction A θ u d hu).Vs ⊓ (abelianWeightOneHodgeStructure A).H (1, 0)))
    rfl ((f1_weilAction A θ u d hu).weilClasses
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) hW)
    rfl (fun v hv => hSc.pullback_le a' (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hv)))
    w (fun _ => hw)

set_option maxRecDepth 2000 in
/-- The even transport of a closed family, pulled back to the model, is `IsCMPowerClosed`. -/
private theorem f1_isCMPowerClosed_comap (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
    (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) (S : ∀ p : ℕ, Submodule ℚ (HQ Y (2 * p)))
    (hSc : f1_IsPulledWeilClosed A θ u d hu hW P Hdg^1(Y; ℚ) S) :
    letI := (finiteBetti_abelian A).finite 1
    IsCMPowerClosed (pwActionRange A θ)
      (rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal r 2)
      ((f1_weilAction A θ u d hu).weilClasses
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) hW)
      (fun k => (f1575EvenCohomologySpanQ S k).comap (P.cohomologyMap k)) := by
  let := (finiteBetti_abelian A).finite 1
  refine { unit_mem := ?_, divisor_le := ?_, pullback_mem := ?_, wedge_mem := ?_ }
  · refine Or.inr ⟨0, rfl, ?_⟩
    rw [HQ.castEquiv_apply_self, spec_g2_cohomologyMap_zero]
    exact hSc.unit_mem
  · intro v hv
    refine Or.inr ⟨1, rfl, ?_⟩
    rw [HQ.castEquiv_apply_self]
    apply hSc.divisor_le
    rw [← spec_g2_rationalExteriorHodge_map_eq P 1]
    exact ⟨v, hv, rfl⟩
  · intro a w hw
    obtain ⟨b, hb⟩ := f1_cmPowerPullback_eq A θ a
    rw [hb]
    have hmem : exteriorPower.map _ (pwPowerPullback A θ b) w ∈
        Submodule.span ℚ {y | ∃ a : Fin r → L, (∀ i, a i ∈ pwOrder A θ) ∧
          ∃ w ∈ (f1_weilAction A θ u d hu).weilClasses
            (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
              (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) hW,
            exteriorPower.map _ (pwPowerPullback A θ a) w = y} := by
      rw [spec_g4_span_pwOrder_eq]
      exact Submodule.subset_span ⟨b, w, hw, rfl⟩
    change _ ∈ (f1575EvenCohomologySpanQ S _).comap (P.cohomologyMap _)
    refine Submodule.span_le.mpr ?_ hmem
    rintro _ ⟨a', ha', w', hw', rfl⟩
    exact f1_pullback_mem A θ u d hu hW P _ S hSc a' ha' w' hw'
  · intro i j v w hv hw
    change P.cohomologyMap (i + j) _ ∈ f1575EvenCohomologySpanQ S (i + j)
    rw [f1_cohomologyMap_wedge]
    exact f1575EvenCohomologySpanQ_cup S (fun h a b ha hb => hSc.cup_mem h a b ha hb) rfl hv hw

set_option maxRecDepth 2000 in
/-- Under the generation statement, the rational Hodge classes of `Y` form a closed family. -/
private theorem f1_isPulledWeilClosed_hdg (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
    (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) (hgen : ∀ p : ℕ, Hdg^p(Y; ℚ) = pwPowerSpan A θ u d hu hW P p) :
    f1_IsPulledWeilClosed A θ u d hu hW P Hdg^1(Y; ℚ) (fun p => Hdg^p(Y; ℚ)) := by
  let := (finiteBetti_abelian A).finite 1
  refine { unit_mem := ?_, divisor_le := le_rfl, pullback_le := ?_, cup_mem := ?_ }
  · change _ ∈ Hdg^0(Y; ℚ)
    rw [hgen 0, f1_pwPowerSpan_zero_aux]
    trivial
  · intro a
    have : IsMonHom (P.pwSumMap θ a) := spec_g4_isMonHom_sumMap P _
    rintro _ ⟨x, hx, rfl⟩
    exact f1_castEquiv_mem (fun p => Hdg^p(Y; ℚ))
      (Module.finrank ℂ ↥(@HodgeBlocks.WeilAction.Vs _ _ _ _ (abelianVarietyCohomologyOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)).weight1 d (f1_weilAction A θ u d hu) ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)).weight1.H (1, 0)))
      (Module.finrank ℂ ↥((f1_weilAction A θ u d hu).Vs ⊓
        (abelianWeightOneHodgeStructure A).H (1, 0))) rfl rfl _
      (spec_homPullback_hodgeClasses (P.pwSumMap θ a) _ x
        (weilClassOf_le_hdg _ _ _ _ (cupFiltered_cupProductOf_of_abelian A) _ hW hx))
  · intro p q h a b ha hb
    exact f1_cup_mem_hdg h a b ha hb

/-- `cmPowerSpan` lies in every closed family. -/
private theorem f1_cmPowerSpan_le {V : Type*} [AddCommGroup V] [Module ℚ V]
    {R : Subalgebra ℚ (Module.End ℚ V)} {m n : ℕ}
    {D : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin m → ℚ)))} {W : Submodule ℚ (⋀[ℚ]^n V)}
    {F : ∀ k, Submodule ℚ (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ)))} (hF : IsCMPowerClosed R D W F)
    (k : ℕ) : cmPowerSpan R D W k ≤ F k :=
  iInf₂_le F hF

/-- The cup form of the generation statement, from the generation statement through the model. -/
private theorem f1_hdg_eq_pulledWeilCupSpan_of_eq (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
    (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) (hgen : ∀ p : ℕ, Hdg^p(Y; ℚ) = pwPowerSpan A θ u d hu hW P p) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) = f1_pulledWeilCupSpan A θ u d hu hW P Hdg^1(Y; ℚ) p := by
  intro p
  apply le_antisymm
  · rw [hgen p, pwPowerSpan]
    apply Submodule.map_le_iff_le_comap.mpr
    have hle := f1_cmPowerSpan_le (f1_isCMPowerClosed_comap A θ u d hu hW P _
      (f1_isPulledWeilClosed_span A θ u d hu hW P Hdg^1(Y; ℚ))) (2 * p)
    simpa only [f1575EvenCohomologySpanQ_even] using hle
  · exact iInf₂_le (fun p => Hdg^p(Y; ℚ)) (f1_isPulledWeilClosed_hdg A θ u d hu hW P hgen)

theorem pw_thm_4_2_generation_cup_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(Y; ℚ) = f1_pulledWeilCupSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      P Hdg^1(Y; ℚ) p :=
  f1_hdg_eq_pulledWeilCupSpan_of_eq A θ u 3 hu _ P
    (pw_thm_4_2_generation_aux A θ u hu hL pol hη hRos hGk P)

theorem f1_hdg_le_pulledWeilCupSpan_divisor_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (h11 : LefschetzOneOneHyp) (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ f1_pulledWeilCupSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      P (algebraicCycleClassSpan Y 1) p := by
  intro p
  refine (pw_thm_4_2_generation_cup_aux A θ u hu hL pol hη hRos hGk P p).le.trans ?_
  exact le_iInf₂ fun F hF => iInf₂_le F
    ⟨hF.unit_mem, (h11.holds Y).trans hF.divisor_le, hF.pullback_le, hF.cup_mem⟩

theorem pw_thm_4_2_hc_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hWA : letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u 3 hu)
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk))
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q)
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p := by
  intro p
  refine (f1_hdg_le_pulledWeilCupSpan_divisor_aux A θ u hu hL pol hη hRos hGk h11 P p).trans ?_
  refine iInf₂_le (fun q => algebraicCycleClassSpan Y q) ⟨unitClass_mem_algebraicCycleClassSpan,
    le_rfl, fun a => (Submodule.map_mono hWA).trans (hPull a _), fun h a b ha hb => hC9.mem h a b ha hb⟩

end HodgeLean.Adapters
