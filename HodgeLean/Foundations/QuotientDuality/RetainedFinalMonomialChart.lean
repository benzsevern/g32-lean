import HodgeLean.Foundations.QuotientDuality.RetainedStrictKummerFieldChart
import HodgeLean.Foundations.QuotientDuality.MonomialPairedResidueWeights
import HodgeLean.Foundations.QuotientDuality.MonomialCoordinateWeights
import HodgeLean.Foundations.QuotientDuality.RetainedFinalComplexWeightedChart
import HodgeLean.Foundations.Program.SchoenCycleC1ActualFinalWeightedEtaleOpen
import HodgeLean.Foundations.QuotientDuality.RetainedBaseComplexBranchCoordinates
import HodgeLean.Foundations.QuotientDuality.RetainedComplexCoordinateRestriction
import HodgeLean.Foundations.QuotientDuality.RetainedArbitraryWeights
import HodgeLean.Foundations.QuotientDuality.RetainedBaseBranchCoordinates
import HodgeLean.Foundations.QuotientDuality.RetainedWeightedStrictIdentity
import HodgeLean.Foundations.Program.SchoenCycleC1ActualFinalWeightedChart
import HodgeLean.Foundations.QuotientDuality.LocalComplexNormalization
import HodgeLean.Foundations.QuotientDuality.LocalDenseChartCalibration
import HodgeLean.Foundations.QuotientDuality.RetainedZeroTowerOrientation
import HodgeLean.Foundations.QuotientDuality.RetainedModificationLocalWitness
import HodgeLean.Foundations.QuotientDuality.ModificationPushforwardOrientation
import HodgeLean.Foundations.QuotientDuality.LocalRetainedConnectedness
import HodgeLean.Foundations.QuotientDuality.LocalAlgebraicOrientation
import HodgeLean.Foundations.QuotientDuality.LocalTrace
import HodgeLean.Foundations.QuotientDuality.LocalCupCompatibility
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Basis
import HodgeLean.Foundations.Topology.RationalSheafComparison
import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers
import HodgeLean.Foundations.Analytic.Analytification
import HodgeLean.Adapters.RationalSheafComparisonDefs
import HodgeLean.Foundations.Singular.Cup
import HodgeLean.Foundations.QuotientDuality.ComparisonCupDefs

/-! # Retained quotient orientations and normalized traces

The tower, deck maps and modification are the retained algebraic constructions.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Analytic
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.QuotientDuality

variable
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
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (eFinal : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W)

include S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal


theorem retained_final_monomial_chart
    (x : ComplexPoint (B (Fin.last r)))
    (U₀ : (B (Fin.last r)).left.Opens) (hx₀ : x.underlying ∈ U₀) :
    ∃ (U : (B (Fin.last r)).left.affineOpens) (hxU : x.underlying ∈ U.1)
      (hηU : η (Fin.last r) ⁻¹ᵁ U.1 = ⊤),
      letI : Nonempty U.1 := ⟨⟨x.underlying, hxU⟩⟩
      letI : Algebra Γ((B (Fin.last r)).left, U) W₀.left.functionField :=
        ((η (Fin.last r)).app U.1 ≫
          (s2v_fieldSourceSectionsIso (η (Fin.last r)) U.1 hηU).hom).hom.toAlgebra
      ∃ (z : Fin (h + 1) → Γ((B (Fin.last r)).left, U)) (α : Fin (h + 1) → ℕ)
        (ε : Γ((B (Fin.last r)).left, U)ˣ) (v : W₀.left.functionField),
        U.1 ≤ U₀ ∧ (MvPolynomial.eval₂Hom (complexAffineCoefficient (B (Fin.last r)) U) z).Etale ∧
        v ^ S.m = algebraMap Γ((B (Fin.last r)).left, U) W₀.left.functionField (ε : Γ((B (Fin.last r)).left, U)) *
          ∏ i, (algebraMap Γ((B (Fin.last r)).left, U) W₀.left.functionField (z i)) ^ α i ∧
        Subfield.closure (Set.range (algebraMap Γ((B (Fin.last r)).left, U) W₀.left.functionField) ∪ {v}) = ⊤ := by
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
  have hm : 0 < S.m := by have := S.three_le; omega
  let αres : Fin (2 * r) → ℕ := fun t => (n (marks t) % (S.m : ℤ)).toNat
  have hweights : ∀ i : Fin r, ∃ q : ℕ,
      αres ⟨2 * i.val, by omega⟩ + αres ⟨2 * i.val + 1, by omega⟩ = q * S.m := by
    intro i
    exact paired_residue_weights_covering_multiple S.m hm
      (n (marks ⟨2 * i.val, by omega⟩)) (n (marks ⟨2 * i.val + 1, by omega⟩)) sgn
      (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩]
      (g32p_exponents S)[σ ⟨2 * i.val + 1, by omega⟩] (hpair i)
      (hres ⟨2 * i.val, by omega⟩) (hres ⟨2 * i.val + 1, by omega⟩)
  choose q hweights using hweights
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
  obtain ⟨c', U, zU, A, ι, g, eE, s, hc', hb', hxU, hUO,
      hEtU, hsPresent, hsAbsent, hg, hE, hfinal, hweighted⟩ :=
    retained_final_complex_weighted_chart S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal αres q hweights x
      ((F.left ⁻¹ᵁ V.1) ⊓ U₀) ⟨hxpre, hx₀⟩
  have hUV : U.1 ≤ F.left ⁻¹ᵁ V.1 := hUO.trans inf_le_left
  have hUU₀ : U.1 ≤ U₀ := hUO.trans inf_le_right
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
  have hDV (i : Fin (2 * r)) :
      ((s2c_branchIdeal Z B₀ h γ (marks i)).comap F.left).ideal U = Ideal.span {g i} := by
    have hi := hg i
    rw [hD₀ i, ← Scheme.IdealSheafData.comap_comp] at hi
    exact hi
  let hgF := s2e_c1_dominant_generic_point F.left
  let ψ := (eqToHom (congrArg B₀.left.presheaf.stalk hgF.symm) ≫
    F.left.stalkMap (genericPoint (B (Fin.last r)).left)).hom
  have hψ := s2e_c1_generic_stalk_map_local_square F.left hgF
  have hrepr : coeff = B₀.left.germToFunctionField V.1 (uV : Γ(B₀.left, V.1)) *
      ∏ j ∈ Finset.univ.filter (fun j : (Finset.univ : Finset (Fin (2 * r))) =>
        ∃ i : Fin (2 * r), j.val = id i),
        (B₀.left.germToFunctionField V.1 (bV j.val)) ^ n (marks j.val) := by
    dsimp [coeff]
    congr 1
    simpa using (Finset.prod_coe_sort Finset.univ
      (fun i => (B₀.left.germToFunctionField V.1 (bV i)) ^ n (marks i))).symm
  obtain ⟨uU, hgne, hcoeffU⟩ := s2e_c1_actual_marked_coefficient_transport F.left ψ hψ
    (id : Fin (2 * r) → Fin (2 * r)) Function.injective_id Finset.univ
    (fun i => s2c_branchIdeal Z B₀ h γ (marks i)) V U hUV
    (fun j => bV j.val) g (fun j => (hbV j.val).2)
    (fun i _ => (hbV i).1) (fun i hi => False.elim (hi (Finset.mem_univ i)))
    hDV (fun i => n (marks i)) uV coeff (by simpa only [id_eq] using hrepr)
  have hηpoint : η (Fin.last r) (IsLocalRing.closedPoint W₀.left.functionField) =
      genericPoint (B (Fin.last r)).left :=
    (congrArg (η (Fin.last r)) (Subsingleton.elim _
      (genericPoint (Spec (CommRingCat.of W₀.left.functionField))))).trans
      (s2e_c1_dominant_generic_point (η (Fin.last r)))
  have hηU : η (Fin.last r) ⁻¹ᵁ U.1 = ⊤ := by
    apply Scheme.preimage_eq_top_of_closedPoint_mem
    rw [hηpoint]
    exact ((genericPoint_spec (B (Fin.last r)).left).mem_open_set_iff U.1.isOpen).mpr
      (by simpa only [Set.univ_inter] using
        (show (U.1 : Set (B (Fin.last r)).left).Nonempty from ⟨x.underlying, hxU⟩))
  letI : Algebra Γ((B (Fin.last r)).left, U) W₀.left.functionField :=
    ((η (Fin.last r)).app U.1 ≫
      (s2v_fieldSourceSectionsIso (η (Fin.last r)) U.1 hηU).hom).hom.toAlgebra
  obtain ⟨ε, v, hv, hvgen⟩ := retained_strict_kummer_field_chart
    F.left (Q₀.trans E₀) hPF W₀.left.functionField (η (Fin.last r))
    (W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left) hηF βstar
    (s2e_c1_genericStalkMap_square β₀.left hgβ) S.m hm U hηU
    g s hgne (fun i => n (marks i)) (∏ j, eE j ^ q j) uU P coeff hPB hcoeffU hweighted
  obtain ⟨β, hβ⟩ := branch_product_coordinate_weights A ι zU s αres hsPresent hsAbsent
  have hprod : (∏ j, (algebraMap Γ((B (Fin.last r)).left, U) W₀.left.functionField (s j)) ^ αres j) =
      ∏ i, (algebraMap Γ((B (Fin.last r)).left, U) W₀.left.functionField (zU i)) ^ β i := by
    simpa only [map_prod, map_pow] using
      congrArg (algebraMap Γ((B (Fin.last r)).left, U) W₀.left.functionField) hβ
  refine ⟨U, hxU, hηU, zU, β, ε, v, hUU₀, hEtU, ?_, hvgen⟩
  exact hv.trans (congrArg (fun t : W₀.left.functionField =>
    algebraMap Γ((B (Fin.last r)).left, U) W₀.left.functionField (ε : Γ((B (Fin.last r)).left, U)) * t) hprod)

#print axioms retained_final_monomial_chart
end HodgeLean.Foundations.QuotientDuality
