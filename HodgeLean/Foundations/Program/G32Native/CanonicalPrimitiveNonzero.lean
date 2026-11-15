import HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero.TopHyperplanePower
import HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero.ComplexOrbitRestriction
import HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero.Generator

/-! # Canonical primitive nonvanishing in native coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
open scoped BigOperators Manifold ContDiff OnePoint TensorProduct
namespace HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero

/-- The normalized top hyperplane power and every primitive weighted inverse-pullback class are nonzero.
Source: Schoen (1988), Lemma 2.6; Fulton, Intersection Theory, §19.1.
HC no distance; AV milestone no distance. -/
theorem g32w_canonical_primitive_nonzero
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
    (C₀ J : Over (Spec ↧ℂ))
    [IsIntegral C₀.left] [Smooth C₀.hom] [IsProjective C₀.hom]
    [GrpObj J] [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (P : g32p_Part J aut S)
    (qC : C₀ ⟶ Y) (jC : C₀ ⟶ J)
    (eC : C ≃ₜ ComplexPoint C₀) (eZ : rsq_Quot S.H C ≃ₜ ComplexPoint Z)
    (hqC : ∀ x, Point.map qC (eC x) = eY (rsq_proj S.χ.ker C x))
    (hpC : ∀ z, Point.map p₀ (eY z) = eZ (rsq_coarsen S.χ.ker z))
    (hχ : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (hjC : Function.Bijective (homPullback jC 1))
    (primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hprimitive : ∀ v, homPullback qC 1 (primitive v) =
      homPullback jC 1 (homPullback P.proj 1 v))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v) =
        (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1))
    (hrank : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m)
    (hselected : h + 1 = 2 * P.k)
    [ChartedSpace ℂ (rsq_Quot S.H C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.H C)]
    (hgenus : 2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
      (g32p_exponents S).length)
    (hr : r = 0)
    (hZ : SmoothOfRelativeDimension 1 Z.hom)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ)) ⟶ B₀)
    (hℓ : IsClosedImmersion ℓ.left)
    (hcanonical : letI := hZ
      ∀ b : ComplexPoint B₀, b ∈ Set.range (Point.map ℓ) ↔
        ∃ z : Fin (h + 1) → ComplexPoint Z,
          Point.map γ (s2_lift (h + 1) z) = b ∧
          ∃ θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z), θ ≠ 0 ∧
            b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
              (hE := Module.finrank_fin_fun (n := 1) ℂ) θ = ∑ t, Finsupp.single (z t) (1 : ℤ))
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ)))
    (ι : Q ⟶ W₀) (hι : IsClosedImmersion ι.left)
    (hιβ : ι ≫ β₀ = eQ.hom ≫ ℓ)
    (c : s2e_supportedClass W₀ (s2e_componentCycle ι ℚ) P.k)
    (hc : a3b4_IsCycleClass W₀.hom (s2e_componentCycle ι ℚ) P.k c)
    (hH : IsIntegral (s2c_subscheme Q ((s2e_hyperplaneIdeal P.k).comap eQ.hom.left)).left)
    (cH : letI := hH
      s2e_supportedClass Q
        (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal P.k).comap eQ.hom.left)) ℚ) 1)
    (hcH : letI := hH
      a3b4_IsCycleClass Q.hom
        (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal P.k).comap eQ.hom.left)) ℚ) 1 cH)
    (horbits : (∀ s t : Fin S.m, s ≠ t → Disjoint
        (Set.range (ι ≫ (End.of d₀ ^ s.val).asHom).left)
        (Set.range (ι ≫ (End.of d₀ ^ t.val).asHom).left)) ∧
      (β₀.left ⁻¹' Set.range ℓ.left =
        ⋃ t : Fin S.m, Set.range (ι ≫ (End.of d₀ ^ t.val).asHom).left))
    (hnormal : letI := hH
      s2e_normalEuler ι P.k c = (-1 : ℚ) ^ P.k •
        s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) (s2e_classToAbsolute Q
        (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal P.k).comap eQ.hom.left)) ℚ) 1 cH) P.k) :
    letI := hH
    s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) (s2e_classToAbsolute Q
        (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal P.k).comap eQ.hom.left)) ℚ) 1 cH) P.k ≠ 0 ∧
    (∀ ζ : ℂ, IsPrimitiveRoot ζ S.m →
      s2e_weightedSum S.m (fun t : ZMod S.m => ζ ^ t.val)
        (fun t : Fin S.m => TensorProduct.tmul ℚ (1 : ℂ)
          (s2e_pullback ℚ ((End.of d₀ ^ (S.m - t.val)).asHom) (2 * P.k) (s2e_classToAbsolute W₀ (s2e_componentCycle ι ℚ) P.k c))) ≠ 0) := by
  letI := hH
  have htop := normalized_hyperplane_top_ne_zero Q P.k (by omega) eQ hH cH hcH
  refine ⟨htop, ?_⟩
  have hperiod := generator_period S Y W₀ a e ha1 hamul (h + 1) hh q₀ hqsurj d₀ hgenerator
  letI := hι
  have hnormal_ne : s2e_normalEuler ι P.k c ≠ 0 := by
    rw [hnormal]
    exact smul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero : (1 : ℚ) ≠ 0))) htop
  intro ζ hζ
  exact complex_inverse_orbit_ne_zero ι d₀ S.m (NeZero.pos S.m) hperiod horbits.1
    (fun t : ZMod S.m => ζ ^ t.val) (by simp only [ZMod.val_zero, pow_zero]) P.k c hnormal_ne


#print axioms g32w_canonical_primitive_nonzero
end HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero
