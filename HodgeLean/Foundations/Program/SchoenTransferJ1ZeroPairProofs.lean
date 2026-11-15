import HodgeLean.Foundations.WitnessSelection.StageTwo.Defs
import HodgeLean.Foundations.Program.SchoenTransferQ2cApplications
import HodgeLean.Foundations.Program.SchoenTransferSupport
/-! # S4 selected witness applications

Implications from the literal retained S2 alternatives and realization choices.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Papers
open scoped BigOperators Manifold ContDiff OnePoint TensorProduct
namespace HodgeLean.Foundations.Program
/-- Canonical zero-pair supported basis refinement for J1.3.
Source: Schoen (1988), Theorem 2.0, unramified case; Fulton, §19.1.
Example: SchoenTransferJ1Checks.row1_construction.
HC no distance; AV milestone no distance. -/
theorem s4_chain_selected_zero_pair_supported_basis_aux
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
    (hS2 :
    Etale β₀.left ∧
    ∃ hZ : SmoothOfRelativeDimension 1 Z.hom,
    letI := hZ
    let PP : Over (Spec ↧ℂ) := Over.mk
      (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ))
    let X₀ := TopCat.of (ComplexPoint W₀)
    let H₀ := AlgebraicTopology.Singular.Cohomology ℚ X₀ (2 * P.k)
    ∃ (ℓ : PP ⟶ B₀), IsClosedImmersion ℓ.left ∧
      (∀ b : ComplexPoint B₀, b ∈ Set.range (Point.map ℓ) ↔
        ∃ z : Fin (h + 1) → ComplexPoint Z,
          Point.map γ (s2_lift (h + 1) z) = b ∧
          ∃ θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z), θ ≠ 0 ∧
            b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
              (hE := Module.finrank_fin_fun (n := 1) ℂ) θ = ∑ t, Finsupp.single (z t) (1 : ℤ)) ∧
    ∃ (Q : Over (Spec ↧ℂ)) (hQ : IsIntegral Q.left)
      (hQs : Smooth Q.hom) (hQp : IsProjective Q.hom),
    letI := hQ
    letI := hQs
    letI := hQp
    ∃ (eQ : Q ≅ PP) (ι : Q ⟶ W₀),
      IsClosedImmersion ι.left ∧ ι ≫ β₀ = eQ.hom ≫ ℓ ∧
      (∀ s t : Fin S.m, s ≠ t → Disjoint
        (Set.range (ι ≫ (End.of d₀ ^ s.val).asHom).left)
        (Set.range (ι ≫ (End.of d₀ ^ t.val).asHom).left)) ∧
      (β₀.left ⁻¹' Set.range ℓ.left =
        ⋃ t : Fin S.m, Set.range (ι ≫ (End.of d₀ ^ t.val).asHom).left) ∧
      (∀ x : Q.left, ∃ U : Q.left.Opens, x ∈ U ∧
        Nonempty (Scheme.Modules.restrict (s2c_conormal ι.left) U.ι ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin P.k) : U.toScheme.Modules))) ∧
      ∃ c, a3b4_IsCycleClass W₀.hom (s2e_componentCycle ι ℚ) P.k c ∧
      let cl := AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ _ (2 * P.k) c
      let HI := (s2e_hyperplaneIdeal P.k).comap eQ.hom.left
      let QH := s2c_subscheme Q HI
      let jH := s2c_subschemeι Q HI
      ∃ (hH : IsIntegral QH.left),
      letI := hH
      ∃ cH, a3b4_IsCycleClass Q.hom (s2e_componentCycle jH ℚ) 1 cH ∧
      let H := AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ _ 2 cH
      s2e_normalEuler ι P.k c = (-1 : ℚ) ^ P.k •
        s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H P.k ∧
      s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H P.k ≠ 0 ∧
      (∀ ζ : ℂ, IsPrimitiveRoot ζ S.m →
        s2e_weightedSum S.m (fun t : ZMod S.m => ζ ^ t.val)
          (fun t : Fin S.m => TensorProduct.tmul ℚ (1 : ℂ)
            (s2e_pullback ℚ ((End.of d₀ ^ (S.m - t.val)).asHom) (2 * P.k) cl)) ≠ 0) ∧
    ∃ (a : Fin (Nat.totient S.m) → Fin S.m → ℚ)
      (v : Fin (Nat.totient S.m) → H₀),
      LinearIndependent ℚ v ∧
      Submodule.span ℚ (Set.range v) = LinearMap.ker
        (Polynomial.aeval (s2e_pullback ℚ d₀ (2 * P.k)) (Polynomial.cyclotomic S.m ℚ)) ∧
      (∀ j,
        let γ := s2e_rationalOrbitCycle ι d₀ S.m (a j)
        (∀ x ∈ γ.support, Order.coheight x = P.k) ∧
        ∃ cj, a3b4_IsCycleClass W₀.hom γ P.k cj ∧
          AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ _ _ cj = v j) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ S.m →
        (∃ u : ℂ ⊗[ℚ] H₀, u ≠ 0 ∧
          (s2e_pullback ℚ d₀ (2 * P.k)).baseChange ℂ u = ζ • u) ∧
        (∀ u : ℂ ⊗[ℚ] H₀,
          (s2e_pullback ℚ d₀ (2 * P.k)).baseChange ℂ u = ζ • u →
          ∃ b : Fin (Nat.totient S.m) → ℂ,
            u = ∑ j, b j • TensorProduct.tmul ℚ (1 : ℂ) (v j))) :
    Etale β₀.left ∧
    ∃ hZ : SmoothOfRelativeDimension 1 Z.hom,
    letI := hZ
    let PP : Over (Spec ↧ℂ) := Over.mk
      (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ))
    let X₀ := TopCat.of (ComplexPoint W₀)
    let H₀ := AlgebraicTopology.Singular.Cohomology ℚ X₀ (2 * P.k)
    ∃ (ℓ : PP ⟶ B₀), IsClosedImmersion ℓ.left ∧
      (∀ b : ComplexPoint B₀, b ∈ Set.range (Point.map ℓ) ↔
        ∃ z : Fin (h + 1) → ComplexPoint Z,
          Point.map γ (s2_lift (h + 1) z) = b ∧
          ∃ θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z), θ ≠ 0 ∧
            b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
              (hE := Module.finrank_fin_fun (n := 1) ℂ) θ = ∑ t, Finsupp.single (z t) (1 : ℤ)) ∧
    ∃ (Q : Over (Spec ↧ℂ)) (hQ : IsIntegral Q.left)
      (hQs : Smooth Q.hom) (hQp : IsProjective Q.hom),
    letI := hQ
    letI := hQs
    letI := hQp
    ∃ (eQ : Q ≅ PP) (ι : Q ⟶ W₀),
      IsClosedImmersion ι.left ∧ ι ≫ β₀ = eQ.hom ≫ ℓ ∧
      (∀ s t : Fin S.m, s ≠ t → Disjoint
        (Set.range (ι ≫ (End.of d₀ ^ s.val).asHom).left)
        (Set.range (ι ≫ (End.of d₀ ^ t.val).asHom).left)) ∧
      (β₀.left ⁻¹' Set.range ℓ.left =
        ⋃ t : Fin S.m, Set.range (ι ≫ (End.of d₀ ^ t.val).asHom).left) ∧
      (∀ x : Q.left, ∃ U : Q.left.Opens, x ∈ U ∧
        Nonempty (Scheme.Modules.restrict (s2c_conormal ι.left) U.ι ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin P.k) : U.toScheme.Modules))) ∧
      ∃ c, a3b4_IsCycleClass W₀.hom (s2e_componentCycle ι ℚ) P.k c ∧
      let cl := AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ _ (2 * P.k) c
      let HI := (s2e_hyperplaneIdeal P.k).comap eQ.hom.left
      let QH := s2c_subscheme Q HI
      let jH := s2c_subschemeι Q HI
      ∃ (hH : IsIntegral QH.left),
      letI := hH
      ∃ cH, a3b4_IsCycleClass Q.hom (s2e_componentCycle jH ℚ) 1 cH ∧
      let H := AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ _ 2 cH
      s2e_normalEuler ι P.k c = (-1 : ℚ) ^ P.k •
        s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H P.k ∧
      s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H P.k ≠ 0 ∧
      (∀ ζ : ℂ, IsPrimitiveRoot ζ S.m →
        s2e_weightedSum S.m (fun t : ZMod S.m => ζ ^ t.val)
          (fun t : Fin S.m => TensorProduct.tmul ℚ (1 : ℂ)
            (s2e_pullback ℚ ((End.of d₀ ^ (S.m - t.val)).asHom) (2 * P.k) cl)) ≠ 0) ∧
    ∃ (a : Fin (Nat.totient S.m) → Fin S.m → ℚ)
      (v : Fin (Nat.totient S.m) → H₀),
      LinearIndependent ℚ v ∧
      Submodule.span ℚ (Set.range v) = LinearMap.ker
        (Polynomial.aeval (s2e_pullback ℚ d₀ (2 * P.k)) (Polynomial.cyclotomic S.m ℚ)) ∧
      (∀ j,
        let γ := s2e_rationalOrbitCycle ι d₀ S.m (a j)
        (∀ x ∈ γ.support, Order.coheight x = P.k ∧
          ∃ U : W₀.left.Opens, x ∈ U ∧ Smooth (U.ι ≫ W₀.hom)) ∧
        ∃ cj, a3b4_IsCycleClass W₀.hom γ P.k cj ∧
          AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ _ _ cj = v j) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ S.m →
        (∃ u : ℂ ⊗[ℚ] H₀, u ≠ 0 ∧
          (s2e_pullback ℚ d₀ (2 * P.k)).baseChange ℂ u = ζ • u) ∧
        (∀ u : ℂ ⊗[ℚ] H₀,
          (s2e_pullback ℚ d₀ (2 * P.k)).baseChange ℂ u = ζ • u →
          ∃ b : Fin (Nat.totient S.m) → ℂ,
            u = ∑ j, b j • TensorProduct.tmul ℚ (1 : ℂ) (v j)) := by
  haveI : Etale β₀.left := hS2.1
  haveI : Smooth (β₀.left ≫ B₀.hom) := inferInstance
  haveI : Smooth W₀.hom := by
    simpa only [Over.w β₀] using (inferInstance : Smooth (β₀.left ≫ B₀.hom))
  simp_rw [s4_support_codimension_smooth_iff]
  exact hS2

end HodgeLean.Foundations.Program
