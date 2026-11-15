import HodgeLean.Foundations.Program.SchoenCycleC1ActualFinalWeightedChart
import HodgeLean.Foundations.Program.SchoenCycleC1InitialAllLabelKummerCharts
import HodgeLean.Foundations.Program.SchoenCycleC1ActualMarkedWeightedNormalizationOpen
import HodgeLean.Foundations.Program.SchoenCycleC1EarlierMapsPartialIso
import HodgeLean.Foundations.Program.SchoenCycleC1EarlierMapsUnique
import HodgeLean.Foundations.Program.SchoenTowerN2b
import HodgeLean.Foundations.Program.SchoenCycleC1ComplexChartDegreeUnit
import HodgeLean.Foundations.Program.SchoenTowerL1bWeightedTransformStep
import HodgeLean.Foundations.Program.SchoenTowerL1bExceptionalEquations
import HodgeLean.Foundations.Program.SchoenTowerL1bBranchEquations
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerInitial
import HodgeLean.Foundations.Program.SchoenTowerL1bTowerStepRefinement

/-! # Final weighted equations away from retained strict branches -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- Every final complex point outside the retained strict branches has an
affine neighbourhood with etale full normalization, using the original
marked Kummer coordinate and the actual weighted tower equation. -/
theorem s2e_c1_actual_final_weighted_etale_open
    (S : g32p_Supplier) (Y Z W₀ B₀ : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W₀.left] [IsProjective W₀.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom] [IsProjective B₀.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p₀ : Y ⟶ Z) [IsFinite p₀.left]
    (hp₀ : ∀ u, a u ≫ p₀ = p₀)
    (hpsurj : Function.Surjective (Point.map p₀))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (r : ℕ) (σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length)
    (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C)
    (rot : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker)
    (hrot : ∀ t, b4_IsRotGen ℂ (y t) (rot t) ∧
      e (rot t) = Multiplicative.ofAdd ((g32p_exponents S)[t] : ZMod S.m))
    (hy : Function.Injective (fun t => Point.map p₀ (eY (y t))))
    (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t)))
    (hexp : ∀ t : Fin (g32p_exponents S).length, 0 < (g32p_exponents S)[t] ∧ (g32p_exponents S)[t] < S.m)
    (hpair : ∀ i : Fin r,
      (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩] +
      (g32p_exponents S)[σ ⟨2 * i.val + 1, by omega⟩] = S.m)
    (h : ℕ) (hh : 0 < h + 1)
    (q₀ : g3_power Y (h + 1) ⟶ W₀) [IsFinite q₀.left]
    (hqsurj : Function.Surjective (Point.map q₀))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q₀ = q₀)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f)
    (β₀ : W₀ ⟶ B₀) [IsFinite β₀.left]
    (hβ₀ : q₀ ≫ β₀ = s2_powerMap p₀ (h + 1) ≫ γ)
    (d₀ : W₀ ⟶ W₀) (hd₀ : d₀ ≫ β₀ = β₀)
    (hgenerator : q₀ ≫ d₀ =
      s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q₀)
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, Smooth (B i).hom]
    [∀ i, IsProjective (B i).hom]
    (e₀ : B 0 ≅ B₀) (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (hD₀ : ∀ t, D 0 t =
      (s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ t))))).comap e₀.hom.left)
    (htransform : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩))
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U)))
    (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (hη₀ : η 0 ≫ e₀.hom.left = W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀)
    (heW : eW.hom ≫ β₀ = s2b_normalizationMap (B 0) (η 0) ≫ e₀.hom)
    (hgeneric : (η 0).toNormalization ≫ eW.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left))
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization)
    (d : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ s2b_normalizationOver (B i) (η i))
    (hd : ∀ i, d i ≫ s2b_normalizationMap (B i) (η i) = s2b_normalizationMap (B i) (η i))
    (hdinit : d 0 ≫ eW.hom = eW.hom ≫ d₀)
    (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (horder : ∀ i, (End.of (d i)) ^ S.m = 1)
    (x : ComplexPoint (B (Fin.last r)))
    (havoid : ∀ t, x.underlying ∉ (D (Fin.last r) t).support)
    : ∃ U : (B (Fin.last r)).left.affineOpens,
      x.underlying ∈ U.1 ∧ Etale ((η (Fin.last r)).fromNormalization ∣_ U.1) := by
  classical
  letI : SmoothOfRelativeDimension 1 Z.hom := by rw [← hdimZ]; infer_instance
  letI : Surjective β₀.left := s2e_c1_retained_projection_surjective
    Y Z W₀ B₀ p₀ hpsurj (h + 1) q₀ γ hγsurj β₀ hβ₀
  letI : Surjective p₀.left := s2e_c11_surjective_of_point_surjective Y Z p₀ hpsurj
  let marks := fun i : Fin (2 * r) => Point.map p₀ (eY (y (σ i)))
  have hmarks : Function.Injective marks := hy.comp σ.injective
  have hbranch' : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔ ∃ i, Point.map p₀ (eY z) = marks i := by
    intro z
    rw [hbranch]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨σ.symm i, by simpa [marks] using hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨σ i, hi⟩
  have hdorder : End.of d₀ ^ S.m = 1 := by
    have hpow := s2e_c1_transport_generator_order eW.symm (d 0) S.m (horder 0)
    change End.of (eW.inv ≫ d 0 ≫ eW.hom) ^ S.m = 1 at hpow
    simpa only [hdinit, eW.inv_hom_id_assoc] using hpow
  obtain ⟨χ, fY, cZ, z, dB, n, sgn, hχ, hfY, hcZ, hz, hdB, hfc, hpower,
      heig, hcurve, hdiv, hres, hcharts⟩ := s2e_c1_initial_all_label_kummer_charts
    S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit
    (rsq_Quot S.χ.ker C) (Fin (2 * r)) eY hpointAction marks hmarks hbranch'
    (fun i => y (σ i)) (fun i => rot (σ i)) (fun i => (g32p_exponents S)[σ i])
    (fun _ => rfl) (fun i => hrot (σ i)) h hh q₀ hqsurj hqinv hq
    γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hdorder hgenerator
  obtain ⟨c, hc, hb⟩ := s2v_l1b_earlier_maps r B b
  let F := c 0 ≫ e₀.hom
  obtain ⟨tuple, htuple⟩ := hγsurj (Point.map F x)
  obtain ⟨V, hxV, _, bV, uV, α, hbV, hα, hcoeff, P, hgen, hdim, hroot⟩ :=
    hcharts tuple ⊤ (by trivial)
  letI : Nonempty V.1 := ⟨⟨γ.left tuple.underlying, hxV⟩⟩
  have hxpre : x.underlying ∈ F.left ⁻¹ᵁ V.1 := by
    change F.left x.underlying ∈ V.1
    have he := congrArg (fun p : ComplexPoint B₀ => p.underlying) htuple
    change γ.left tuple.underlying = F.left x.underlying at he
    rw [← he]
    exact hxV
  obtain ⟨c', U, g, eE, hc', hb', hxU, hUV, hg, hE, hfinal, hweighted⟩ :=
    s2e_c1_actual_final_weighted_chart S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder x havoid (F.left ⁻¹ᵁ V.1) hxpre
  have hcc := s2e_c1_earlier_maps_unique B b c' c hc' hc hb' hb
  subst c'
  letI : Nonempty U.1 := ⟨⟨x.underlying, hxU⟩⟩
  have hsteps (i : Fin r) : ∃ Q : (B i.succ).left.PartialIso (B i.castSucc).left,
      Q.iso.hom ≫ Q.target.ι = Q.source.ι ≫ (b i).left := by
    obtain ⟨E, hE, _⟩ := s2v_n1a_blowup_complement_iso S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
    obtain ⟨_, hDense, _, hDense'⟩ := s2v_n1b_centre_complements S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
    let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔ D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let O : (B i.castSucc).left.Opens := ⟨(I.support : Set _)ᶜ, I.support.isClosed.isOpen_compl⟩
    refine ⟨⟨(b i).left ⁻¹ᵁ O, hDense', O, hDense, E⟩, ?_⟩
    change E.hom ≫ O.ι = ((b i).left ⁻¹ᵁ O).ι ≫ (b i).left
    rw [hE, morphismRestrict_ι]
  choose Q hQ using hsteps
  obtain ⟨Q₀, hQ₀⟩ := s2e_c1_earlier_maps_partial_iso (fun i => (B i).left)
    (fun i => (b i).left) (fun i => (c i).left)
    (congrArg Over.Hom.left hc) (fun i => congrArg Over.Hom.left (hb i)) Q hQ 0
  let E₀ := Scheme.PartialIso.ofIso (asIso e₀.hom.left)
  have hQF : Q₀.IsOver F.left e₀.hom.left := by
    simpa only [F, Over.comp_left, Scheme.PartialIso.IsOver, Category.assoc] using
      congrArg (fun f => f ≫ e₀.hom.left) hQ₀
  have hE₀ : E₀.IsOver e₀.hom.left (𝟙 _) := by
    simp [E₀, Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso]
  have hPF : (Q₀.trans E₀).iso.hom ≫ (Q₀.trans E₀).target.ι =
      (Q₀.trans E₀).source.ι ≫ F.left := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using hQF.trans hE₀
  let I := fun j : Fin r => D j.castSucc ⟨2 * j.val, by omega⟩ ⊔
    D j.castSucc ⟨2 * j.val + 1, by omega⟩
  letI : ∀ i, IsDominant (η i) := s2v_l1b_original_tower_generic_dominant
    p₀ hpsurj (h + 1) q₀ γ hγsurj β₀ hβ₀ B e₀ b I hcartier hblowup η hη₀ hη
  have hηc := s2v_l1b_earlier_maps_generic (fun i => (B i).left)
    (fun i => (b i).left) (fun i => (c i).left)
    (congrArg Over.Hom.left hc) (fun i => congrArg Over.Hom.left (hb i))
    _ η hη 0
  have hηF : η (Fin.last r) ≫ F.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left := by
    change η (Fin.last r) ≫ ((c 0).left ≫ e₀.hom.left) = _
    rw [← Category.assoc, hηc, hη₀]
  haveI : IsDominant (η (Fin.last r) ≫ F.left) := by
    change IsDominant (η (Fin.last r) ≫ ((c 0).left ≫ e₀.hom.left))
    rw [← Category.assoc, hηc]
    infer_instance
  haveI : IsDominant F.left := IsDominant.of_comp (η (Fin.last r)) F.left
  let hgβ := s2e_c1_dominant_generic_point β₀.left
  let βstar := (eqToHom (congrArg B₀.left.presheaf.stalk hgβ.symm) ≫
    β₀.left.stalkMap (genericPoint W₀.left)).hom
  letI := βstar.toAlgebra
  let coeff : B₀.left.functionField := B₀.left.germToFunctionField V.1 (uV : Γ(B₀.left, V.1)) *
    ∏ i, (B₀.left.germToFunctionField V.1 (bV i)) ^ n (marks i)
  have hPB : P.gen ^ S.m = βstar coeff := by rw [hgen]; exact hroot
  let UX : Over (Spec ↧ℂ) := Over.mk (U.1.ι ≫ (B (Fin.last r)).hom)
  letI : IsAffine U.1.toScheme := U.property
  letI : Nonempty (⊤ : U.1.toScheme.Opens) := ⟨⟨genericPoint _, by trivial⟩⟩
  haveI : IsIntegrallyClosed Γ(U.1.toScheme, ⊤) :=
    s2_affineOpen_sections_integrallyClosed
      (zmtiso_normal_of_smooth U.1.toScheme (U.1.ι ≫ (B (Fin.last r)).hom)) (isAffineOpen_top _)
  letI : Algebra ℂ U.1.toScheme.functionField :=
    (HodgeLean.Foundations.Curves.stalkC (X := UX) (genericPoint U.1.toScheme)).toAlgebra
  haveI : CharZero U.1.toScheme.functionField :=
    charZero_of_injective_algebraMap (algebraMap ℂ U.1.toScheme.functionField).injective
  obtain ⟨degree, hdegree⟩ := s2e_c1_complex_chart_degree_unit
    (B (Fin.last r)) U.property.fromSpec S.m (by have := S.three_le; omega)
  have hDV (i : Fin (2 * r)) :
      ((s2c_branchIdeal Z B₀ h γ (marks i)).comap F.left).ideal U = Ideal.span {g i} := by
    have hi := hg i
    rw [hD₀ i, ← Scheme.IdealSheafData.comap_comp] at hi
    exact hi
  refine ⟨U, hxU, ?_⟩
  apply s2e_c1_actual_marked_weighted_normalization_open_etale F.left (Q₀.trans E₀) hPF
    W₀.left.functionField (η (Fin.last r))
    (W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left) hηF βstar
    (s2e_c1_genericStalkMap_square β₀.left hgβ) U P coeff S.m
    (by have := S.three_le; omega) hdim hPB
    (Fin (2 * r)) (Fin (2 * r)) id Function.injective_id Finset.univ
    (fun i => s2c_branchIdeal Z B₀ h γ (marks i)) V hUV
    (fun j => bV j.val) g (fun j => (hbV j.val).2)
    (fun i _ => (hbV i).1) (fun i hi => False.elim (hi (Finset.mem_univ i)))
    hDV (fun i => (g32p_exponents S)[σ i])
    (fun i => n (marks i)) (∏ j, eE j) sgn hres hweighted uV degree hdegree
  dsimp [coeff]
  congr 1
  simpa using (Finset.prod_coe_sort Finset.univ
      (fun i => (B₀.left.germToFunctionField V.1 (bV i)) ^ n (marks i))).symm

end HodgeLean.Foundations.Program
