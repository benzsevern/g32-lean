import HodgeLean.Foundations.Program.SchoenTowerL1bKummerActionPowers
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorOriginalDegree
import HodgeLean.Foundations.Program.SchoenTowerL1bRotationChosenCharacter
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportCharacterRoot
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportConstants
import HodgeLean.Foundations.Program.SchoenTowerL1bDeckPowers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The original cover has a nonzero binomial function for the specified signed character. -/
theorem s2v_l1b_divisor_original_generator
    (S : g32p_Supplier) (Y Z : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p : Y ⟶ Z) [IsFinite p.left] (hp : ∀ u, a u ≫ p = p)
    (hpsurj : Function.Surjective (Point.map p))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (s : ℤ) (hs : s = 1 ∨ s = -1) :
    ∃ (κ : Z.left.functionField ⟶ Y.left.functionField)
      (τ : Y.left.functionField ≃+* Y.left.functionField)
      (u : Y.left.functionField) (v : Z.left.functionField),
      (Spec.map κ ≫ Z.left.fromSpecStalk (genericPoint Z.left) =
        Y.left.fromSpecStalk (genericPoint Y.left) ≫ p.left) ∧
      (Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        Y.left.fromSpecStalk (genericPoint Y.left) =
        Y.left.fromSpecStalk (genericPoint Y.left) ≫
          (a (e.symm (Multiplicative.ofAdd (1 : ZMod S.m)))).left) ∧
      u ≠ 0 ∧ u ^ S.m = κ.hom v ∧
      τ u = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫
        Y.left.germToFunctionField ⊤).hom
        (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (S.m : ℂ))) * u := by
  haveI : IsDominant p.left := n1bc_dominant_of_points_surjective p hpsurj
  obtain ⟨κ, hκ, hdata⟩ :=
    s2v_l1b_divisor_original_degree S Y Z a e ha1 hamul hinj p hp hpsurj hporbit
  have hκeq : κ = s2v_l1b_functionFieldPullback p.left := by
    apply Spec.map_injective
    apply (cancel_mono (Z.left.fromSpecStalk (genericPoint Z.left))).mp
    rw [hκ, s2v_l1b_functionFieldPullback_generic_square]
  rw [hκeq] at hdata
  letI := (s2v_l1b_functionFieldPullback p.left).hom.toAlgebra
  haveI : Module.Finite Z.left.functionField Y.left.functionField := hdata.1
  haveI : IsGalois Z.left.functionField Y.left.functionField := hdata.2.1
  let g := e.symm (Multiplicative.ofAdd (1 : ZMod S.m))
  let ρ := s2v_l1b_divisor_original_action S Y a ha1 hamul
  haveI : IsIso (a g) := inferInstanceAs (IsIso (ρ g).asIso.hom)
  haveI : IsIso (a g).left := inferInstance
  obtain ⟨τA, hτA⟩ := s2v_l1b_cover_field_algEquiv p.left (a g).left
    (congrArg Over.Hom.left (hp g))
  have hsquare : Spec.map (CommRingCat.ofHom τA.toRingHom) ≫
      Y.left.fromSpecStalk (genericPoint Y.left) =
      Y.left.fromSpecStalk (genericPoint Y.left) ≫ (a g).left := by
    rw [show CommRingCat.ofHom τA.toRingHom = s2v_l1b_functionFieldPullback (a g).left from
      congrArg CommRingCat.ofHom hτA]
    exact s2v_l1b_functionFieldPullback_generic_square (a g).left
  let E := Y.left.functionField
  let F := Z.left.functionField
  let embed : (E ≃ₐ[F] E) →* End E :=
    { toFun := fun u => End.of (CommRingCat.ofHom u.toRingHom)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hemb : Function.Injective embed := by
    intro u v huv
    apply AlgEquiv.ext
    intro z
    exact congrArg (fun k : End E => k.asHom z) huv
  let deck : (S.H ⧸ S.χ.ker) →* End Y :=
    { toFun := fun u => End.of (a u)
      map_one' := End.ext ha1
      map_mul' := fun u v => End.ext (hamul u v) }
  have hdeck : Function.Injective deck := by
    intro u v huv
    exact hinj (congrArg End.asHom huv)
  have hforget : orderOf (End.of (a g).left) = orderOf (End.of (a g)) := by
    apply orderOf_injective ((Over.forget _).mapEnd Y) _ (End.of (a g))
    intro u v huv
    apply End.ext
    apply Over.OverMorphism.ext
    exact congrArg End.asHom huv
  have hgorder : orderOf g = S.m := by
    rw [← e.orderOf_eq, show e g = Multiplicative.ofAdd (1 : ZMod S.m) from e.apply_symm_apply _,
      orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have horder : orderOf τA = S.m :=
    (orderOf_injective embed hemb τA).symm.trans
      ((s2v_l1b_generic_order_eq Y.hom (embed τA) (End.of (a g).left)
        (Over.w (a g)) hsquare).trans
          (hforget.trans ((orderOf_injective deck hdeck g).trans hgorder)))
  let cZ : CommRingCat.of ℂ ⟶ Z.left.functionField :=
    (Scheme.ΓSpecIso ↧ℂ).inv ≫ Z.hom.appTop ≫ Z.left.germToFunctionField ⊤
  let cY : CommRingCat.of ℂ ⟶ Y.left.functionField :=
    (Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫ Y.left.germToFunctionField ⊤
  let ζ := Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (S.m : ℂ))
  have hζ : IsPrimitiveRoot (cZ.hom ζ) (Module.finrank F E) := by
    rw [hdata.2.2.2]
    exact (s2v_l1b_signed_character_primitive S.m (NeZero.ne S.m) s hs).map_of_injective
      cZ.hom.injective
  obtain ⟨u, hu, hueigen, hupow, _⟩ := s2v_l1b_rotation_degree_order_character_generator τA
    (horder.trans hdata.2.2.2.symm) hζ
  obtain ⟨v, hv⟩ := hupow
  have hconst : cZ ≫ s2v_l1b_functionFieldPullback p.left = cY := by
    apply s2v_l1b_generic_constants Z Y _
    rw [s2v_l1b_functionFieldPullback_generic_square, Category.assoc, Over.w p]
  have hscalar : algebraMap F E (cZ.hom ζ) = cY.hom ζ :=
    congrArg (fun f : CommRingCat.of ℂ ⟶ E => f.hom ζ) hconst
  refine ⟨κ, τA.toRingEquiv, u, v, hκ, hsquare, hu, ?_, ?_⟩
  · rw [hκeq, ← hdata.2.2.2]
    exact hv.symm
  · change τA u = cY.hom ζ * u
    rw [hueigen, Algebra.smul_def, hscalar]

end HodgeLean.Foundations.Program
