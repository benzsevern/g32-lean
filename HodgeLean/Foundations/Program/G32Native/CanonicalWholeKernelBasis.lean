import HodgeLean.Foundations.Program.G32Native.U15Generator
import HodgeLean.Foundations.Program.SchoenTransferR2PullbackPowers
import HodgeLean.Foundations.Program.G32Native.U15QuotientPrimitiveRank
import HodgeLean.Foundations.Program.G32Native.U15RationalOrbitBasis

/-! # Whole cyclotomic kernel on the selected power quotient -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program
open scoped BigOperators TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
attribute [local irreducible] cupProductOf homPullback

/-- Native U08 and U10 with the inverse-orbit coefficients retained for U09.
The weighted nonzero premise is the U07 output for the same absolute class. -/
theorem canonical_whole_kernel_basis
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
    (h : ℕ) (hh : 0 < h + 1)
    (q₀ : g3_power Y (h + 1) ⟶ W₀) [IsFinite q₀.left]
    (hqsurj : Function.Surjective (Point.map q₀))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q₀ = q₀)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f)
    (d₀ : W₀ ⟶ W₀)
    (hgenerator : q₀ ≫ d₀ =
      s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q₀)
    (C₀ J : Over (Spec ↧ℂ))
    [IsIntegral C₀.left] [Smooth C₀.hom] [IsProjective C₀.hom]
    [GrpObj J] [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (P : g32p_Part J aut S)
    (qC : C₀ ⟶ Y) (jC : C₀ ⟶ J)
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
    (cl : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W₀)) (2 * P.k))
    (hweighted : ∀ ζ : ℂ, IsPrimitiveRoot ζ S.m →
      s2e_weightedSum S.m (fun t : ZMod S.m => ζ ^ t.val)
        (fun t : Fin S.m => TensorProduct.tmul ℚ (1 : ℂ)
          (s2e_pullback ℚ ((End.of d₀ ^ (S.m - t.val)).asHom) (2 * P.k) cl)) ≠ 0) :
    let H₀ := AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W₀)) (2 * P.k)
    ∃ (a : Fin (Nat.totient S.m) → Fin S.m → ℚ)
      (v : Fin (Nat.totient S.m) → H₀),
      LinearIndependent ℚ v ∧
      Submodule.span ℚ (Set.range v) = LinearMap.ker
        (Polynomial.aeval (s2e_pullback ℚ d₀ (2 * P.k)) (Polynomial.cyclotomic S.m ℚ)) ∧
      (∀ j, v j = ∑ t : Fin S.m, a j t •
        s2e_pullback ℚ ((End.of d₀ ^ (S.m - t.val)).asHom) (2 * P.k) cl) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ S.m →
        (∃ u : ℂ ⊗[ℚ] H₀, u ≠ 0 ∧
          (s2e_pullback ℚ d₀ (2 * P.k)).baseChange ℂ u = ζ • u) ∧
        (∀ u : ℂ ⊗[ℚ] H₀,
          (s2e_pullback ℚ d₀ (2 * P.k)).baseChange ℂ u = ζ • u →
          ∃ b : Fin (Nat.totient S.m) → ℂ,
            u = ∑ j, b j • TensorProduct.tmul ℚ (1 : ℂ) (v j)) := by
  let F := (LinearMap.ker (Polynomial.aeval
    (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
    (Polynomial.cyclotomic S.m ℚ))).subtype.comp primitive.toLinearMap
  have hinjF : Function.Injective F := Subtype.val_injective.comp primitive.injective
  have himage : LinearMap.range F = LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (primitive v).property
    · intro hx
      refine ⟨primitive.symm ⟨x, hx⟩, ?_⟩
      exact congrArg Subtype.val (primitive.apply_symm_apply ⟨x, hx⟩)
  have hbound := quotient_primitive_rank_bound S Y hdimY (h + 1) P.k hselected
    (by omega) hh a e hχ ha1 hamul P.act.cyc_coordinates F hinjF himage hscalar
    W₀ q₀ hqsurj hqinv hq d₀ hgenerator
  letI : Module.Finite ℚ (AlgebraicTopology.Singular.Cohomology ℚ
      (TopCat.of (ComplexPoint W₀)) (2 * P.k)) :=
    quotient_cohomology_finite S Y a e ha1 hamul (h + 1) W₀ q₀ hqsurj hqinv hq (2 * P.k)
  have hperiod := generator_period S Y W₀ a e ha1 hamul (h + 1) hh q₀ hqsurj d₀ hgenerator
  let T := s2e_pullback ℚ d₀ (2 * P.k)
  let seed := cl
  have hT : T ^ S.m = 1 := by
    dsimp only [T]
    rw [← s4_assembly_pullback_pow, hperiod]
    change AlgebraicTopology.Singular.cohomologyMap ℚ (2 * P.k)
      (𝟙 (TopCat.of (ComplexPoint W₀))) = 1
    rw [AlgebraicTopology.Singular.cohomologyMap_id]
    rfl
  have hne (ζ : ℂ) (hζ : IsPrimitiveRoot ζ S.m) :
      primitiveOrbit (T.baseChange ℂ) S.m (fun t : ZMod S.m => ζ ^ t.val)
        (TensorProduct.tmul ℚ (1 : ℂ) seed) ≠ 0 := by
    have he := hweighted ζ hζ
    simpa only [primitiveOrbit, s2e_weightedSum, T, seed,
      ← LinearMap.baseChange_pow, LinearMap.baseChange_tmul,
      ← s4_assembly_pullback_pow] using he
  obtain ⟨aa, vv, hlin, hspan, hav, heig⟩ := rational_inverse_orbit_basis T S.m
    (by have := S.three_le; omega) hT seed hbound hne
  refine ⟨aa, vv, hlin, hspan, ?_, heig⟩
  intro j
  simpa only [T, seed, ← s4_assembly_pullback_pow] using hav j

#print axioms canonical_whole_kernel_basis
end HodgeLean.Foundations.Program.G32Native
