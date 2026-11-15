import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.TransportChartHelpers
import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.LocalizedCoordinates

/-! # Curve coordinate transport in positive degree

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
attribute [local instance] overSpecAlgebra

/-- Actual common curve parameters retain the elementary-symmetric formula on a quotient neighborhood in positive degree.
Source: Milne, Jacobian Varieties, §3; SGA 1, Exposé V, §1.
HC no distance; AV milestone no distance.
-/
theorem curve_transport_positive
    (C B : Over (Spec ↧ℂ)) [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    [SmoothOfRelativeDimension 1 C.hom] (n : ℕ) (hn : 0 < n)
    (γ : g3_power C n ⟶ B) [IsFinite γ.left]
    (hinv : ∀ σ, s2_permute C n σ ≫ γ = γ)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (z : Fin n → ComplexPoint C) :
    ∃ (U : C.left.Opens) (t : U.toScheme ⟶ (affine 1).left)
      (u : Fin n → (Spec ↧ℂ ⟶ U.toScheme))
      (V : B.left.Opens)
      (v : Spec ↧ℂ ⟶ V.toScheme) (c : V.toScheme ⟶ (affine n).left),
      IsAffineOpen U ∧ Etale t ∧ Etale c ∧
      t ≫ (affine 1).hom = U.ι ≫ C.hom ∧
      c ≫ (affine n).hom = V.ι ≫ B.hom ∧
      (∀ i, u i ≫ U.ι = (z i).left) ∧
      v ≫ V.ι = (s2_lift n z ≫ γ).left ∧
      (∀ i j, u i ≫ t = u j ≫ t ↔ z i = z j) ∧
      ∀ (y : Fin n → ComplexPoint C) (uy : Fin n → (Spec ↧ℂ ⟶ U.toScheme))
        (w : Spec ↧ℂ ⟶ V.toScheme),
        (∀ i, uy i ≫ U.ι = (y i).left) →
        w ≫ V.ι = (s2_lift n y ≫ γ).left →
        ∀ j : Fin n,
          (Scheme.ΓSpecIso ↧ℂ).hom
            ((w ≫ c).appTop ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin n) ℂ)).inv
              (MvPolynomial.X j))) =
          MvPolynomial.eval (fun i => (Scheme.ΓSpecIso ↧ℂ).hom
            ((uy i ≫ t).appTop ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin 1) ℂ)).inv
              (MvPolynomial.X (0 : Fin 1)))))
            (MvPolynomial.esymm (Fin n) ℂ (j.val+1)) := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  classical
  obtain ⟨A, hA, a, _, ya, s, ha, _, hya, hs, _, _, hsep, _, _⟩ :=
    s2v_i2a_branch_and_tuple_curve_parameters C (SmoothOfRelativeDimension.dim_eq C.hom 1)
      (fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i) h z
  letI := hA
  letI := ha
  letI : Mono a := Over.mono_of_mono_left a
  letI := overSpecAlgebra A ⊤
  let x := s2_lift (h+1) z
  have hya' (i : Fin (h+1)) : Point.map a (ya i) = Point.map (g3_proj C (h+1) i) x := by
    rw [show Point.map (g3_proj C (h+1) i) x = z i from s2_check_lift_proj (h+1) z i]
    exact hya i
  obtain ⟨O, j, q, p, c, d, hj, hjSquare, hp, hqSquare, hd, hEt, hc⟩ :=
    curve_coefficient_neighborhood C B A h a γ hinv huniv x ya hya' s hs (by
      intro i l hil
      rw [show Point.map (g3_proj C (h+1) i) x = z i from s2_check_lift_proj (h+1) z i,
        show Point.map (g3_proj C (h+1) l) x = z l from s2_check_lift_proj (h+1) z l]
      exact (hsep i l).mp hil)
  let Y := ComplexPoint.openScheme B O.1
  let X := ComplexPoint.openScheme (g3_power C (h+1)) (γ.left ⁻¹ᵁ O.1)
  let vX : X ⟶ g3_power C (h+1) := ComplexPoint.openInclusion _ (γ.left ⁻¹ᵁ O.1)
  let vY : Y ⟶ B := ComplexPoint.openInclusion B O.1
  letI : IsAffine Y.left := O.2
  letI := overSpecAlgebra Y ⊤
  let W := Y.left.basicOpen d
  let T := ComplexPoint.openScheme Y W
  let r : T ⟶ Y := ComplexPoint.openInclusion Y W
  letI : IsOpenImmersion r.left := inferInstanceAs (IsOpenImmersion W.ι)
  letI : IsOpenImmersion vY.left := inferInstanceAs (IsOpenImmersion O.1.ι)
  let rB := r ≫ vY
  letI : IsOpenImmersion rB.left := inferInstanceAs (IsOpenImmersion (r.left ≫ vY.left))
  obtain ⟨f, hf, hfv⟩ := principal_section_coordinates Y (h+1) c d hEt
  letI := hf
  have hW : (Point.map q p).underlying ∈ W :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero d (Point.map q p) (by trivial)).mpr hd
  let pt := ComplexPoint.asOpenPoint Y W (Point.map q p) hW
  have hpt : Point.map r pt = Point.map q p := by
    apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac Y W _ hW
  let G := MvPolynomial.aeval (R := ℂ) (fun _ : Fin 1 => s)
  have hGC : G.toRingHom.Etale := by
    rw [s2v_l1a_structure_section_coefficients] at hs
    exact (s2v_l1a_etale_eval_change_coefficients_iff _ _ _).mp hs
  let fA : A ⟶ affine 1 := s2e_section_defined_affine_map A _ G
  haveI : Etale fA.left := by
    haveI : Etale (Spec.map (CommRingCat.ofHom G.toRingHom)) :=
      HasRingHomProperty.Spec_iff.mpr hGC
    change Etale (A.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom G.toRingHom))
    infer_instance
  have hval (y : ComplexPoint A) : coordinateValue 1 (Point.map fA y) 0 = Point.evaluate ⊤ s y := by
    rw [section_map_coordinate_value]
    change Point.evaluate ⊤ ((MvPolynomial.aeval (R := ℂ) (fun _ : Fin 1 => s)) (MvPolynomial.X 0)) y = _
    rw [MvPolynomial.aeval_X]
  let U := a.left.opensRange
  let eA := IsOpenImmersion.isoOfRangeEq a.left U.ι (by rw [Scheme.Opens.range_ι]; rfl)
  have heA : eA.hom ≫ U.ι = a.left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have heiA : eA.inv ≫ a.left = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  let V := rB.left.opensRange
  let eT := IsOpenImmersion.isoOfRangeEq rB.left V.ι (by rw [Scheme.Opens.range_ι]; rfl)
  have heT : eT.hom ≫ V.ι = rB.left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have heiT : eT.inv ≫ rB.left = V.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  refine ⟨U, eA.inv ≫ fA.left, (fun i => (ya i).left ≫ eA.hom), V,
    pt.left ≫ eT.hom, eT.inv ≫ f.left, isAffineOpen_opensRange a.left,
    inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, Over.w fA, ← Over.w a, ← Category.assoc, heiA]
  · change eT.inv ≫ (f.left ≫ (affine (h+1)).hom) = V.ι ≫ B.hom
    rw [Over.w f, ← Over.w rB, ← Category.assoc, heiT]
  · intro i
    rw [Category.assoc, heA]
    exact congrArg (fun t : ComplexPoint C => t.left) (hya i)
  · rw [Category.assoc, heT]
    change ((pt ≫ r) ≫ vY).left = _
    rw [show pt ≫ r = p ≫ q from hpt, Category.assoc, ← hqSquare, ← Category.assoc]
    exact congrArg (fun t : ComplexPoint B => t.left) (congrArg (fun t => t ≫ γ) hp)
  · intro i l
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    constructor
    · intro H
      have H' : Point.map fA (ya i) = Point.map fA (ya l) := Over.OverMorphism.ext H
      have Hv := congrArg (fun t : ComplexPoint (affine 1) => coordinateValue 1 t 0) H'
      rw [hval, hval] at Hv
      exact (hsep i l).mp Hv
    · intro H
      have Hy : ya i = ya l := by
        apply (cancel_mono a).mp
        exact (hya i).trans (H.trans (hya l).symm)
      rw [Hy]
  · intro yy uy w huy hw l
    let yyA (i : Fin (h+1)) : ComplexPoint A := Over.homMk (uy i ≫ eA.inv) (by
      have H : (uy i ≫ eA.inv) ≫ a.left = (yy i).left := by
        rw [Category.assoc, heiA, huy]
      rw [← Over.w a, ← Category.assoc, H]
      exact (yy i).w)
    have hyyA (i : Fin (h+1)) : Point.map a (yyA i) = yy i := by
      apply Over.OverMorphism.ext
      exact (Category.assoc _ _ _).trans ((congrArg (fun t => uy i ≫ t) heiA).trans (huy i))
    have hwt : (w ≫ eT.inv) ≫ rB.left = (s2_lift (h+1) yy ≫ γ).left := by
      rw [Category.assoc, heiT, hw]
    let wT : ComplexPoint T := Over.homMk (w ≫ eT.inv) (by
      rw [← Over.w rB, ← Category.assoc, hwt]
      exact (s2_lift (h+1) yy ≫ γ).w)
    let wY := Point.map r wT
    let xy : ComplexPoint (g3_power C (h+1)) := s2_lift (h+1) yy
    have hwY : Point.map vY wY = Point.map γ xy := by
      apply Over.OverMorphism.ext
      exact (Category.assoc _ _ _).trans hwt
    have hxyO : xy.underlying ∈ γ.left ⁻¹ᵁ O.1 := by
      change γ.left xy.underlying ∈ O.1
      have H := congrArg (fun t : ComplexPoint B => t.underlying) hwY
      change (Point.map γ xy).underlying ∈ O.1
      rw [← H]
      exact (wY.underlying).2
    let py := ComplexPoint.asOpenPoint (g3_power C (h+1)) (γ.left ⁻¹ᵁ O.1) xy hxyO
    have hpy : Point.map vX py = xy := by
      apply Over.OverMorphism.ext
      exact ComplexPoint.liftToOpen_fac (g3_power C (h+1)) (γ.left ⁻¹ᵁ O.1) xy hxyO
    have hqpy : Point.map q py = wY := by
      apply (cancel_mono vY).mp
      change (py ≫ q) ≫ vY = wY ≫ vY
      rw [Category.assoc, ← hqSquare, ← Category.assoc]
      change Point.map γ (Point.map vX py) = Point.map vY wY
      rw [hpy, hwY]
    have hcoord (i : Fin (h+1)) : (j ≫ g3_proj A (h+1) i) ≫ a = vX ≫ g3_proj C (h+1) i := by
      have H : s2_powerMap a (h+1) ≫ g3_proj C (h+1) i = g3_proj A (h+1) i ≫ a :=
        s2_check_lift_proj (h+1) _ i
      rw [Category.assoc, ← H, ← Category.assoc, hjSquare]
    have heval := s2v_i2a_curve_coordinate_evaluations A X C (h+1) a vX
      (fun i => j ≫ g3_proj A (h+1) i) hcoord py xy hpy yyA (by
        intro i
        rw [hyyA]
        exact (s2_check_lift_proj (h+1) yy i).symm) s
    have H := elementary_section_values X Y q (h+1)
      (fun i => (j ≫ g3_proj A (h+1) i).left.appTop.hom s) c hc py l
    rw [hqpy] at H
    have Hfinal : coordinateValue (h+1) (Point.map f wT) l =
        MvPolynomial.eval (fun i => coordinateValue 1 (Point.map fA (yyA i)) 0)
          (MvPolynomial.esymm (Fin (h+1)) ℂ (l.val+1)) := by
      rw [hfv wT l, H]
      apply congrArg (fun ev : Fin (h+1) → ℂ =>
        MvPolynomial.eval ev (MvPolynomial.esymm (Fin (h+1)) ℂ (l.val+1)))
      funext i
      rw [heval i, hval]
    convert! Hfinal using 1 <;>
      simp only [coordinateValue, Point.map, Over.comp_left, wT, yyA,
        Over.homMk_left, Category.assoc]

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
