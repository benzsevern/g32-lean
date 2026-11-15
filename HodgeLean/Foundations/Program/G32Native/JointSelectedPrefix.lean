import HodgeLean.Foundations.Program.SchoenCyclePushDefs

noncomputable section
set_option maxRecDepth 4000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Papers
open scoped BigOperators Manifold ContDiff OnePoint TensorProduct
namespace HodgeLean.Foundations.Program
/- Retained data shared by both alternatives of the joint caller. -/
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure G32JointPrefix (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) where
  Y : Over (Spec ↧ℂ)
  Z : Over (Spec ↧ℂ)
  W₀ : Over (Spec ↧ℂ)
  B₀ : Over (Spec ↧ℂ)
  [inst1 : IsIntegral Y.left]
  [inst2 : Smooth Y.hom]
  [inst3 : IsProjective Y.hom]
  [inst4 : IsIntegral Z.left]
  [inst5 : Smooth Z.hom]
  [inst6 : IsProjective Z.hom]
  [inst7 : IsIntegral W₀.left]
  [inst8 : IsProjective W₀.hom]
  [inst9 : IsIntegral B₀.left]
  [inst10 : Smooth B₀.hom]
  [inst11 : IsProjective B₀.hom]
  hdimY : TopologicalSpace.dim Y.left = 1
  hdimZ : TopologicalSpace.dim Z.left = 1
  a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y)
  e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m)
  ha1 : a 1 = 𝟙 Y
  hamul : ∀ u v, a (u * v) = a v ≫ a u
  hinj : Function.Injective a
  p₀ : Y ⟶ Z
  [inst12 : IsFinite p₀.left]
  hp₀ : ∀ u, a u ≫ p₀ = p₀
  hpsurj : Function.Surjective (Point.map p₀)
  hporbit : ∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
      ∃ u, Point.map (a u) x = y
  C : Type
  [inst13 : TopologicalSpace C]
  [inst14 : MulAction g32p_G C]
  [inst15 : ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
  [inst16 : IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
  eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y
  hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y)
  r : ℕ
  σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length
  y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C
  rot : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker
  hrot : ∀ t, b4_IsRotGen ℂ (y t) (rot t) ∧
      e (rot t) = Multiplicative.ofAdd ((g32p_exponents S)[t] : ZMod S.m)
  hy : Function.Injective (fun t => Point.map p₀ (eY (y t)))
  hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t))
  hexp : ∀ t : Fin (g32p_exponents S).length, 0 < (g32p_exponents S)[t] ∧ (g32p_exponents S)[t] < S.m
  hpair : ∀ i : Fin r,
      (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩] +
      (g32p_exponents S)[σ ⟨2 * i.val + 1, by omega⟩] = S.m
  h : ℕ
  hh : 0 < h + 1
  q₀ : g3_power Y (h + 1) ⟶ W₀
  [inst17 : IsFinite q₀.left]
  hqsurj : Function.Surjective (Point.map q₀)
  hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q₀ = q₀
  hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f
  γ : g3_power Z (h + 1) ⟶ B₀
  [inst18 : IsFinite γ.left]
  hγsurj : Function.Surjective (Point.map γ)
  hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ
  hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f
  β₀ : W₀ ⟶ B₀
  [inst19 : IsFinite β₀.left]
  hβ₀ : q₀ ≫ β₀ = s2_powerMap p₀ (h + 1) ≫ γ
  d₀ : W₀ ⟶ W₀
  hd₀ : d₀ ≫ β₀ = β₀
  hgenerator : q₀ ≫ d₀ =
      s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q₀
  C₀ : Over (Spec ↧ℂ)
  [inst25 : IsIntegral C₀.left]
  [inst26 : Smooth C₀.hom]
  [inst27 : IsProjective C₀.hom]
  P : g32p_Part J aut S
  qC : C₀ ⟶ Y
  jC : C₀ ⟶ J
  eC : C ≃ₜ ComplexPoint C₀
  eZ : rsq_Quot S.H C ≃ₜ ComplexPoint Z
  hqC : ∀ x, Point.map qC (eC x) = eY (rsq_proj S.χ.ker C x)
  hpC : ∀ z, Point.map p₀ (eY z) = eZ (rsq_coarsen S.χ.ker z)
  hχ : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u
  hjC : Function.Bijective (homPullback jC 1)
  primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))
  hprimitive : ∀ v, homPullback qC 1 (primitive v) =
      homPullback jC 1 (homPullback P.proj 1 v)
  hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v) =
        (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1)
  hrank : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m
  hselected : h + 1 = 2 * P.k
  [inst28 : ChartedSpace ℂ (rsq_Quot S.H C)]
  [inst29 : IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.H C)]
  hgenus : 2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
      (g32p_exponents S).length
  horder₀ : (End.of d₀ ^ S.m).asHom = 𝟙 W₀

end HodgeLean.Foundations.Program
