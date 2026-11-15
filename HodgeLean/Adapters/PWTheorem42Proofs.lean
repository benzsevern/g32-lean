import HodgeLean.Adapters.PWTheorem42Eisenstein
import HodgeLean.Foundations.CMModelAssembly

/-! # Theorem 4.2 for a general CM field, stage F2: proof obligations

One `_aux` theorem per statement of `PWTheorem42.lean`, all open. Helpers are to be prefixed
`f2_`. F1's private helpers (`f1_hdg_eq_pulledWeilCupSpan_of_eq`, `f1_pullback_transport`,
`f1_castEquiv_mem`, …) are stated for any field `L` and any `d`; they are restated here with an
`f2_` prefix where needed. HC no distance; AV milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic NumberField

namespace HodgeLean.Adapters

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]
variable {L : Type*} [Field L] [NumberField L] [IsCMField L]

private theorem f2_complexConj_u (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) : IsCMField.complexConj L u = -u := by
  have hsq : IsCMField.complexConj L u ^ 2 = u ^ 2 := by
    have hc_rat : IsCMField.complexConj L (algebraMap ℚ L d) = algebraMap ℚ L d := by
      have hA : algebraMap ℚ L = Rat.castHom L := Subsingleton.elim _ _
      rw [hA]
      exact map_ratCast (IsCMField.complexConj L) d
    calc
      IsCMField.complexConj L u ^ 2 = IsCMField.complexConj L (u ^ 2) := (map_pow _ _ _).symm
      _ = u ^ 2 := by rw [hu, map_neg, hc_rat]
  have hprod : (IsCMField.complexConj L u - u) * (IsCMField.complexConj L u + u) = 0 := by
    calc
      _ = IsCMField.complexConj L u ^ 2 - u ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hprod with hminus | hplus
  · have hfixed : IsCMField.complexConj L u = u := sub_eq_zero.mp hminus
    have humem : u ∈ maximalRealSubfield L :=
      (IsCMField.complexConj_eq_self_iff (K := L) u).mp hfixed
    let uR : maximalRealSubfield L := ⟨u, humem⟩
    let w : InfinitePlace (maximalRealSubfield L) := Classical.choice inferInstance
    let φ : maximalRealSubfield L →+* ℝ :=
      w.embedding_of_isReal (IsTotallyReal.isReal w)
    have huR : uR ^ 2 = algebraMap ℚ (maximalRealSubfield L) (-d) := by
      apply Subtype.ext
      simpa [uR, map_neg] using hu
    have hreal := congrArg φ huR
    have hnonneg : 0 ≤ φ uR ^ 2 := sq_nonneg _
    have hneg : φ uR ^ 2 < 0 := by
      rw [map_pow] at hreal
      have heq : φ uR ^ 2 = -d := by
        calc
          φ uR ^ 2 = φ (algebraMap ℚ (maximalRealSubfield L) (-d)) := hreal
          _ = ((-d : ℚ) : ℝ) := by
            have hAF : algebraMap ℚ (maximalRealSubfield L) =
                Rat.castHom (maximalRealSubfield L) := Subsingleton.elim _ _
            rw [hAF]
            exact map_ratCast φ (-d)
          _ = -(d : ℝ) := by norm_num
      rw [heq]
      exact neg_neg_of_pos (Rat.cast_pos.mpr hd)
    exact (not_lt_of_ge hnonneg hneg).elim
  · exact eq_neg_of_add_eq_zero_left hplus

private theorem f2_one_u_linearIndependent (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) : LinearIndependent ℚ ![1, u] := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega)] at hu
    have : d = 0 := (algebraMap ℚ L).injective (by simpa using hu.symm)
    linarith
  rw [LinearIndependent.pair_iff]
  intro p q hpq
  have hc := congrArg (IsCMField.complexConj L) hpq
  simp only [map_add, map_smul, map_one, f2_complexConj_u u hd hu, map_neg, map_zero,
    map_rat_smul, one_smul] at hc
  rw [smul_neg] at hc
  have hqu : q • u = 0 := by linear_combination (hpq - hc) / 2
  have hq : q = 0 := (smul_eq_zero.mp hqu).resolve_right hu0
  subst q
  simpa using hpq

theorem f2_rosati_of_finrank_two_aux (hL : Module.finrank ℚ L = 2) (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u)) :
    ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y) := by
  have hli := f2_one_u_linearIndependent u hd hu
  have hspan : Submodule.span ℚ {1, u} = (⊤ : Submodule ℚ L) := by
    rw [show ({1, u} : Set L) = {u, 1} by ext; simp [or_comm]]
    simpa using hli.span_eq_top_of_card_eq_finrank' (by simp [hL])
  intro a x y
  have ha : a ∈ Submodule.span ℚ {1, u} := by rw [hspan]; trivial
  rw [Submodule.mem_span_pair] at ha
  obtain ⟨p, q, rfl⟩ := ha
  have hskew := polarizationForm_skew (torusCohomology_cupProductOf A) hη hRos
  have hconj : IsCMField.complexConj L (p • (1 : L) + q • u) =
      p • (1 : L) + q • (-u) := by
    rw [map_add, map_rat_smul, map_one, map_rat_smul, f2_complexConj_u u hd hu]
  rw [hconj]
  simp only [map_add, map_smul, map_one, map_neg,
    LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.neg_apply,
    smul_eq_mul, hskew]

theorem f2_isRosatiSkew_of_rosati_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y)) :
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u) := by
  apply (isRosatiSkew_iff_dualForm hη _).2
  intro x y
  change polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ u x) y =
    -polarizationForm (torusCohomology_cupProductOf A) hη x (pwAction A θ u y)
  rw [hRos u x y, f2_complexConj_u u hd hu, map_neg, LinearMap.neg_apply]
  exact map_neg _ _

variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

theorem pw_thm_4_2_generation_general_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
    (hd : 0 < d) (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(Y; ℚ) = pwPowerSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P p := by
  letI := (finiteBetti_abelian A).finite 1
  intro p
  rw [← spec_g2_rationalExteriorHodge_map_eq P p,
    spec_a6_rationalExteriorHodge_eq_cmPowerSpan (pwAction A θ) (f1_weilAction A θ u d hu) u rfl
      (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A))
      (polarizationForm (torusCohomology_cupProductOf A) hη)
      (nondegenerate_polarizationForm (torusCohomology_cupProductOf A) hη)
      (isAlt_polarizationForm (torusCohomology_cupProductOf A) hη) hRos hd
      (by rw [hu, map_neg]) hGk r (2 * p)]
  rfl

set_option maxRecDepth 2000 in
omit [IsCommMonObj A] in
/-- `P.cohomologyMap` turns the wedge product of the model into the cup product of `Y`. -/
private theorem f2_cohomologyMap_wedge (P : AbelianPowerData A Y r) (i j : ℕ)
    (v : ⋀[ℚ]^i (HQ A 1 ⊗[ℚ] (Fin r → ℚ))) (w : ⋀[ℚ]^j (HQ A 1 ⊗[ℚ] (Fin r → ℚ))) :
    P.cohomologyMap (i + j) (exteriorPower.wedge ℚ _ i j v w) =
      (cupProductOf Y).cup rfl (P.cohomologyMap i v) (P.cohomologyMap j w) := by
  simp only [AbelianPowerData.cohomologyMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TorusCohomology.cupWedgeEquiv_apply, exteriorPower_map_wedge]
  exact CupProduct.cupWedgeMap_wedge _ i j _ _

set_option maxRecDepth 2000 in
omit [IsCommMonObj Y] in
/-- Rational Hodge classes of `Y` are closed under the cup product. -/
private theorem f2_cup_mem_hdg {p q : ℕ} (h : 2 * p + 2 * q = 2 * (p + q)) (a : HQ Y (2 * p))
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
private theorem f2_castEquiv_homPullback {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : Y ⟶ X) {m n : ℕ} (h : m = n) (x : HQ X m) :
    HQ.castEquiv Y h (homPullback f m x) = homPullback f n (HQ.castEquiv X h x) := by
  subst h
  rw [HQ.castEquiv_apply_self, HQ.castEquiv_apply_self]

omit [IsCMField L] in
/-- The pulled-Weil cup span is itself a closed family. -/
private theorem f2_isPulledWeilClosed_span (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
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
private theorem f2_castEquiv_mem (S : ∀ p : ℕ, Submodule ℚ (HQ Y (2 * p))) (k₁ k₂ : ℕ)
    (hk : k₁ = k₂) (h₂ : 2 * k₁ = 2 * k₂) (z : HQ Y (2 * k₁)) (hz : z ∈ S k₁) :
    HQ.castEquiv Y h₂ z ∈ S k₂ := by
  subst hk
  simpa using hz

set_option maxRecDepth 2000 in
omit [GrpObj Y] [IsCommMonObj Y] in
/-- Transport of a pulled-back Weil class along an equation of the Weil degree. -/
private theorem f2_pullback_transport {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
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
  rw [f2_castEquiv_homPullback]
  simpa using this

omit [IsCMField L] in
/-- A model pullback with coefficients in the image of `L` comes from coefficients in `L`. -/
private theorem f2_cmPowerPullback_eq (θ : L →ₐ[ℚ] AbelianEnd0 A)
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
omit [IsCMField L] in
/-- The model image of a Weil pullback with coefficients in `𝒪` lies in the even transport of a
closed family. -/
private theorem f2_pullback_mem (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
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
  exact f2_pullback_transport (cupProductOf A) (P.pwSumMap θ a') S
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
omit [IsCMField L] in
/-- The even transport of a closed family, pulled back to the model, is `IsCMPowerClosed`. -/
private theorem f2_isCMPowerClosed_comap (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
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
    obtain ⟨b, hb⟩ := f2_cmPowerPullback_eq A θ a
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
    exact f2_pullback_mem A θ u d hu hW P _ S hSc a' ha' w' hw'
  · intro i j v w hv hw
    change P.cohomologyMap (i + j) _ ∈ f1575EvenCohomologySpanQ S (i + j)
    rw [f2_cohomologyMap_wedge]
    exact f1575EvenCohomologySpanQ_cup S (fun h a b ha hb => hSc.cup_mem h a b ha hb) rfl hv hw

set_option maxRecDepth 2000 in
omit [IsCMField L] in
/-- Under the generation statement, the rational Hodge classes of `Y` form a closed family. -/
private theorem f2_isPulledWeilClosed_hdg (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
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
    exact f2_castEquiv_mem (fun p => Hdg^p(Y; ℚ))
      (Module.finrank ℂ ↥(@HodgeBlocks.WeilAction.Vs _ _ _ _ (abelianVarietyCohomologyOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)).weight1 d (f1_weilAction A θ u d hu) ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)).weight1.H (1, 0)))
      (Module.finrank ℂ ↥((f1_weilAction A θ u d hu).Vs ⊓
        (abelianWeightOneHodgeStructure A).H (1, 0))) rfl rfl _
      (spec_homPullback_hodgeClasses (P.pwSumMap θ a) _ x
        (weilClassOf_le_hdg _ _ _ _ (cupFiltered_cupProductOf_of_abelian A) _ hW hx))
  · intro p q h a b ha hb
    exact f2_cup_mem_hdg h a b ha hb

/-- `cmPowerSpan` lies in every closed family. -/
private theorem f2_cmPowerSpan_le {V : Type*} [AddCommGroup V] [Module ℚ V]
    {R : Subalgebra ℚ (Module.End ℚ V)} {m n : ℕ}
    {D : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin m → ℚ)))} {W : Submodule ℚ (⋀[ℚ]^n V)}
    {F : ∀ k, Submodule ℚ (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ)))} (hF : IsCMPowerClosed R D W F)
    (k : ℕ) : cmPowerSpan R D W k ≤ F k :=
  iInf₂_le F hF

omit [IsCMField L] in
/-- The cup form of the generation statement, from the generation statement through the model. -/
private theorem f2_hdg_eq_pulledWeilCupSpan_of_eq (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
    (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) (hgen : ∀ p : ℕ, Hdg^p(Y; ℚ) = pwPowerSpan A θ u d hu hW P p) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) = f1_pulledWeilCupSpan A θ u d hu hW P Hdg^1(Y; ℚ) p := by
  intro p
  apply le_antisymm
  · rw [hgen p, pwPowerSpan]
    apply Submodule.map_le_iff_le_comap.mpr
    have hle := f2_cmPowerSpan_le (f2_isCMPowerClosed_comap A θ u d hu hW P _
      (f2_isPulledWeilClosed_span A θ u d hu hW P Hdg^1(Y; ℚ))) (2 * p)
    simpa only [f1575EvenCohomologySpanQ_even] using hle
  · exact iInf₂_le (fun p => Hdg^p(Y; ℚ)) (f2_isPulledWeilClosed_hdg A θ u d hu hW P hgen)

theorem pw_thm_4_2_generation_cup_general_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
    (hd : 0 < d) (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(Y; ℚ) = f1_pulledWeilCupSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      P Hdg^1(Y; ℚ) p :=
  f2_hdg_eq_pulledWeilCupSpan_of_eq A θ u d hu _ P
    (pw_thm_4_2_generation_general_aux A θ u hd hu pol hη hRos hGk P)

theorem f2_hdg_le_pulledWeilCupSpan_divisor_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
    (hd : 0 < d) (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (h11 : LefschetzOneOneHyp) (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ f1_pulledWeilCupSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      P (algebraicCycleClassSpan Y 1) p := by
  intro p
  refine (pw_thm_4_2_generation_cup_general_aux A θ u hd hu pol hη hRos hGk P p).le.trans ?_
  exact le_iInf₂ fun F hF => iInf₂_le F
    ⟨hF.unit_mem, (h11.holds Y).trans hF.divisor_le, hF.pullback_le, hF.cup_mem⟩

theorem pw_thm_4_2_hc_general_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
    (hd : 0 < d) (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hWA : letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u d hu)
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk))
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q)
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p := by
  intro p
  refine (f2_hdg_le_pulledWeilCupSpan_divisor_aux A θ u hd hu pol hη hRos hGk h11 P p).trans ?_
  refine iInf₂_le (fun q => algebraicCycleClassSpan Y q) ⟨unitClass_mem_algebraicCycleClassSpan,
    le_rfl, fun a => (Submodule.map_mono hWA).trans (hPull a _), fun h a b ha hb => hC9.mem h a b ha hb⟩

end HodgeLean.Adapters
