import HodgeLean.Foundations.Program.G32Native.JointSelectedPrefix

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure G32JointBase {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) where
  B : Fin (R.r + 1) → Over (Spec ↧ℂ)
  [inst20 : ∀ i, IsIntegral (B i).left]
  [inst21 : ∀ i, Smooth (B i).hom]
  [inst22 : ∀ i, IsProjective (B i).hom]
  e₀ : B 0 ≅ R.B₀
  b : ∀ i : Fin R.r, B i.succ ⟶ B i.castSucc
  D : ∀ i, Fin (2 * R.r) → (B i).left.IdealSheafData
  hD₀ : ∀ t, D 0 t =
      (s2c_branchIdeal R.Z R.B₀ R.h R.γ (Point.map R.p₀ (R.eY (R.y (R.σ t))))).comap e₀.hom.left
  htransform : ∀ (i : Fin R.r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩)
  hcartier : ∀ (i : Fin R.r) (x : (B i.succ).left),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U))
  hblowup : ∀ (i : Fin R.r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f
  η : ∀ i, Spec R.W₀.left.functionField ⟶ (B i).left
  [inst23 : ∀ i, QuasiCompact (η i)]
  [inst24 : ∀ i, QuasiSeparated (η i)]
  hη₀ : η 0 ≫ e₀.hom.left = R.W₀.left.fromSpecStalk (genericPoint R.W₀.left) ≫ R.β₀.left
  hη : ∀ i : Fin R.r, η i.succ ≫ (b i).left = η i.castSucc
  eW : s2b_normalizationOver (B 0) (η 0) ≅ R.W₀
  heW : eW.hom ≫ R.β₀ = s2b_normalizationMap (B 0) (η 0) ≫ e₀.hom
  hgeneric : (η 0).toNormalization ≫ eW.hom.left =
      R.W₀.left.fromSpecStalk (genericPoint R.W₀.left)
  w : ∀ i : Fin R.r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc)
  hw : ∀ i : Fin R.r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization
  d : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ s2b_normalizationOver (B i) (η i)
  hd : ∀ i, d i ≫ s2b_normalizationMap (B i) (η i) = s2b_normalizationMap (B i) (η i)
  hdinit : d 0 ≫ eW.hom = eW.hom ≫ R.d₀
  hdw : ∀ i : Fin R.r, d i.succ ≫ w i = w i ≫ d i.castSucc
  horder : ∀ i, (End.of (d i)) ^ S.m = 1

end HodgeLean.Foundations.Program
