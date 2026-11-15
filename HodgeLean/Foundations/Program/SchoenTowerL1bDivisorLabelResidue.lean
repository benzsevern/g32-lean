import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCurveResidue
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCharacterPowers
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorSignedScalar
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorExpansionParameter
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportConstants
import HodgeLean.Foundations.Program.SchoenCycleCurveStalkJets
import HodgeLean.Foundations.Program.SchoenFiniteMorphisms

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
attribute [local instance] AlgebraicGeometry.overSpecAlgebra
  HodgeLean.Foundations.Curves.functionFieldAlgebra
namespace HodgeLean.Foundations.Program

/-- A specified signed character gives the labelled residue on the original curve. -/
theorem s2v_l1b_divisor_label_residue
    (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [SmoothOfRelativeDimension 1 X.hom] [SmoothOfRelativeDimension 1 Y.hom]
    (G : Type) [Group G] [Finite G] {m : ℕ} (hm : m ≠ 0)
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (e : G ≃* Multiplicative (ZMod m))
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left] [IsDominant q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hsurj : Function.Surjective (Point.map q))
    (horbit : ∀ x y : ComplexPoint X, Point.map q x = Point.map q y ↔
      ∃ g, Point.map (a g) x = y)
    (C : Type) [TopologicalSpace C] [MulAction G C]
    (eX : C ≃ₜ ComplexPoint X)
    (hpoint : ∀ g y, Point.map (a g) (eX y) = eX (g • y))
    (y : C) (g : G) (hgy : g • y = y)
    (horder : orderOf g = Nat.card (MulAction.stabilizer G y))
    (k : ℕ) (hlabel : e g = Multiplicative.ofAdd (k : ZMod m))
    (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hp : (a g).left (eX y).underlying = (eX y).underlying)
    (ι : X.left.presheaf.stalk (eX y).underlying →+* PowerSeries ℂ)
    (hι : Function.Injective ι) (hX : ∃ t, ι t = PowerSeries.X)
    (hc : ∀ c, ι (HodgeLean.Foundations.Curves.stalkC (eX y).underlying c) = PowerSeries.C c)
    (hcomparison : ∀ v, ι (s2e_fixed_point_stalkPullback X.left (a g).left
      (eX y).underlying hp v) = PowerSeries.rescale
        (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (orderOf g : ℂ))) (ι v))
    (τ : X.left.functionField ≃+* X.left.functionField)
    (hτ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      X.left.fromSpecStalk (genericPoint X.left) = X.left.fromSpecStalk (genericPoint X.left) ≫
        (a (e.symm (Multiplicative.ofAdd (1 : ZMod m)))).left)
    (u : X.left.functionField) (hu : u ≠ 0)
    (heigen : τ u = algebraMap ℂ X.left.functionField
      (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (m : ℂ))) * u)
    (A B : Y.left.presheaf.stalk (q.left (eX y).underlying)) (hA : A ≠ 0) (hB : B ≠ 0)
    (hpow : u ^ m = s2v_l1b_functionFieldPullback q.left
      (algebraMap _ Y.left.functionField A / algebraMap _ Y.left.functionField B))
    (p : Y.left.presheaf.stalk (q.left (eX y).underlying)) (hprime : Prime p) :
    Int.ModEq (m : ℤ)
      (((emultiplicity p A).toNat : ℤ) - ((emultiplicity p B).toNat : ℤ)) (k : ℤ) := by
  classical
  letI : NeZero m := ⟨hm⟩
  letI : Surjective q.left := ⟨s2_surjective_of_point_surjective q hsurj⟩
  letI : IsDominant q.left := inferInstance
  letI := s2e_smooth_curve_point_stalk_dvr X (eX y)
  letI : IsDiscreteValuationRing (Y.left.presheaf.stalk (q.left (eX y).underlying)) := by
    simpa only [Point.underlying_map] using s2e_smooth_curve_point_stalk_dvr Y (Point.map q (eX y))
  let H := MulAction.stabilizer G y
  have hH (g : G) : Point.map (a g) (eX y) = eX y ↔ g ∈ H := by
    rw [hpoint]
    exact eX.injective.eq_iff
  have hcard : Nat.card G = m := (Nat.card_congr e.toEquiv).trans (by simp [Nat.card_eq_fintype_card])
  obtain ⟨w, hw⟩ : Nat.card H ∣ m := hcard ▸ H.card_subgroup_dvd_card
  have hme : m = Nat.card H * w := hw
  have hd : Nat.card H ≠ 0 := Nat.card_pos.ne'
  obtain ⟨t, ht, htX⟩ := s2v_l1b_divisor_expansion_parameter ι
    (HodgeLean.Foundations.Curves.stalkC (eX y).underlying) hc hX
  have hclosed : IsClosed ({(eX y).underlying} : Set X.left) := by
    haveI : IsClosedImmersion ((eX y).left ≫ X.hom) := by
      rw [Over.w]
      change IsClosedImmersion (𝟙 (Spec ↧ℂ))
      infer_instance
    haveI : IsClosedImmersion (eX y).left := IsClosedImmersion.of_comp (eX y).left X.hom
    change IsClosed {(eX y).left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using (eX y).left.isClosedMap
      {IsLocalRing.closedPoint ℂ} (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  let ξ := Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (m : ℂ))
  have hscalar := s2v_l1b_divisor_signed_scalar_power hm hd hme s
  have hcomp : ∀ v, ι (s2e_fixed_point_stalkPullback X.left (a g).left
      (eX y).underlying hp v) = PowerSeries.rescale (ξ ^ w) (ι v) := by
    intro v
    rw [hcomparison, horder]
    rw [hscalar]
  let g₀ := e.symm (Multiplicative.ofAdd (1 : ZMod m))
  have hgp : g₀ ^ k = g := by
    apply e.injective
    rw [map_pow, hlabel]
    simp only [g₀, e.apply_symm_apply, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]
  have hconstants := s2v_l1b_generic_constants X X (CommRingCat.ofHom τ.toRingHom) (by
    rw [hτ, Category.assoc, Over.w])
  have hξ : τ (algebraMap ℂ X.left.functionField ξ) = algebraMap ℂ X.left.functionField ξ :=
    by
      change τ (X.left.germToFunctionField ⊤
        (X.hom.appLE ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso ↧ℂ).inv.hom ξ))) =
        X.left.germToFunctionField ⊤
          (X.hom.appLE ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso ↧ℂ).inv.hom ξ))
      simpa [CommRingCat.hom_comp, Scheme.Hom.appLE] using
        congrArg (fun f : CommRingCat.of ℂ ⟶ X.left.functionField => f.hom ξ) hconstants
  have he := s2v_l1b_divisor_character_power X G a ha1 hamul g₀ τ hτ u
    (algebraMap ℂ X.left.functionField ξ) hξ heigen k
  rw [hgp] at he
  apply s2v_l1b_divisor_curve_residue X Y G a ha1 hamul q hinv
    (s2v_l1b_divisor_original_quotient X Y G a ha1 hamul q hsurj hinv horbit)
    (eX y) hclosed H hH ι hι t ht htX g hgy ξ hm hme
    (s2v_l1b_signed_character_primitive m hm s hs) hcomp
    (HodgeLean.Foundations.Curves.stalkC (eX y).underlying (ξ ^ k)) (hc _) u hu
    (by rw [HodgeLean.Foundations.Curves.algebraMap_stalkC, map_pow]; exact he)
    A B hA hB hpow p hprime

end HodgeLean.Foundations.Program
