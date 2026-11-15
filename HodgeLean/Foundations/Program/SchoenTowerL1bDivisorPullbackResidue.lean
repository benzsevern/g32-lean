import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorStalkPullback
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorOrders

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pulling back a rational weighted divisor equation preserves its prime residues for total ideal generators. -/
theorem s2v_l1b_divisor_pullback_residue
    {K R J : Type} [Field K] [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [Fintype J]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (κX : X.functionField ⟶ CommRingCat.of K)
    (κY : Y.functionField ⟶ CommRingCat.of K)
    (hsq : Spec.map κX ≫ X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map κY ≫ Y.fromSpecStalk (genericPoint Y))
    (x : X) (eR : R ≃+* X.presheaf.stalk x)
    (I : J → Y.IdealSheafData)
    (U : X.affineOpens) (hxU : x ∈ U.1) (g : J → Γ(X, U))
    (hg : ∀ j, ((I j).comap f).ideal U = Ideal.span {g j})
    (V : Y.affineOpens) (hxV : f x ∈ V.1) (g₀ : J → Γ(Y, V))
    (hg₀ : ∀ j, (I j).ideal V = Ideal.span {g₀ j})
    (ε : (Y.presheaf.stalk (f x))ˣ) (A B : Y.presheaf.stalk (f x))
    (hA : A ≠ 0) (hB : B ≠ 0) (n : J → ℕ) (m : ℕ)
    (t : K) (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hf : ∀ j, eR.symm ((X.presheaf.germ U.1 x hxU).hom (g j)) ≠ 0)
    (ht : t ^ m = ((s2v_l1b_kval_stalkMap X x κX).comp eR.toRingHom) a /
      ((s2v_l1b_kval_stalkMap X x κX).comp eR.toRingHom) b)
    (he : let ρ₀ := s2v_l1b_kval_stalkMap Y (f x) κY
      t ^ m * (ρ₀ B) ^ m = ρ₀ (ε : Y.presheaf.stalk (f x)) *
        (∏ j, ρ₀ ((Y.presheaf.germ V.1 (f x) hxV).hom (g₀ j)) ^ n j) * (ρ₀ A) ^ m)
    (p : R) (hp : Prime p) :
    Int.ModEq (m : ℤ)
      (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ))
      (∑ j, (n j : ℤ) *
        ((emultiplicity p (eR.symm ((X.presheaf.germ U.1 x hxU).hom (g j)))).toNat : ℤ)) := by
  let ρ := (s2v_l1b_kval_stalkMap X x κX).comp eR.toRingHom
  let φ := eR.symm.toRingHom.comp (f.stalkMap x).hom
  let F := fun j => eR.symm ((X.presheaf.germ U.1 x hxU).hom (g j))
  let F₀ := fun j => φ ((Y.presheaf.germ V.1 (f x) hxV).hom (g₀ j))
  have hρ : Function.Injective ρ :=
    (κX.hom.injective.comp (IsFractionRing.injective _ _)).comp eR.injective
  have hcomp : ρ.comp φ = s2v_l1b_kval_stalkMap Y (f x) κY := by
    ext v
    change s2v_l1b_kval_stalkMap X x κX (eR (eR.symm ((f.stalkMap x).hom v))) = _
    rw [eR.apply_symm_apply]
    exact DFunLike.congr_fun (s2v_l1b_divisor_stalk_pullback f κX κY hsq x) v
  have hφ : Function.Injective φ := by
    intro u v huv
    apply (κY.hom.injective.comp (IsFractionRing.injective _ _))
    change s2v_l1b_kval_stalkMap Y (f x) κY u = s2v_l1b_kval_stalkMap Y (f x) κY v
    rw [← hcomp]
    exact congrArg ρ huv
  have hfg : ∀ j, Ideal.span {F₀ j} = Ideal.span {F j} := by
    intro j
    apply Ideal.span_singleton_eq_span_singleton.mpr
    exact (s2v_l1b_divisor_pullback_generators f (I j) x U hxU V hxV
      (g₀ j) (g j) (hg₀ j) (hg j)).map eR.symm.toMonoidHom
  obtain ⟨δ, hδ⟩ := s2v_l1b_weighted_generators_unit F₀ F n hfg
  apply s2v_l1b_divisor_equation_orders ρ hρ hp ha hb
    (by simpa only [map_zero] using hφ.ne hA)
    (by simpa only [map_zero] using hφ.ne hB)
    (Units.map φ ε * δ) F n hf m
  have hpoint (v : Y.presheaf.stalk (f x)) : ρ (φ v) =
      s2v_l1b_kval_stalkMap Y (f x) κY v := DFunLike.congr_fun hcomp v
  have hδ' := congrArg ρ hδ
  simp only [map_prod, map_pow, map_mul] at hδ'
  change (ρ a / ρ b) * ρ (φ B) ^ m = _
  rw [← ht, hpoint, he]
  change _ = ρ (φ (ε : Y.presheaf.stalk (f x)) * (δ : R)) *
    (∏ j, ρ (F j) ^ n j) * ρ (φ A) ^ m
  rw [map_mul, hpoint, hpoint, mul_assoc _ (ρ ↑δ), ← hδ']
  simp only [F₀, hpoint]

end HodgeLean.Foundations.Program
