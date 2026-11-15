import HodgeLean.Foundations.Program.SchoenSelectedGeometryProofs

/-! # Selected Schoen geometry and choice interface (FROZEN SPEC)

Implication from retained family geometry to a realization with deck provenance,
analytic supplier quotients, and comparison of primitive choices. The explicit-family
Proposition 4.6 successor retains Schoen, Milne and the character comparison as inputs.
Algebraic supplier curves, local exponents and primitive comparisons are included.
No cycle construction is asserted here.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

/-- A retained realization exporting its actual deck action, theta class and Prym image.
The comparison maps and every primitive part remain fields of this very witness.
Source: G32 v0.16, §3.2 and §4.1; Birkenhake–Lange, §11.4 and Ch. 12;
`g32y_cover_aux`, with the construction's equalities retained. -/
theorem s0_cover {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c))) :
    ∃ (f : g32p_G → AbelianEnd (g32x_J D t))
      (R : g32p_Cover (b65z_fiber D B t)),
      (∀ a, homPullback (f a).hom 1 = g32x_deck D t a) ∧
      R.J = g32x_J D t ∧ HEq R.aut (fun a ↦ (f a).hom) ∧
      HEq R.pol (g32x_theta D t) ∧
      HEq (LinearMap.range (homPullback R.projA 1))
        (LinearMap.range (g32x_projector D t)) :=
  s0_cover_aux D t hg B

example := @s0_cover

/-- Analytic quotient curves and their cyclic deck action on the actual retained fibre.
Source: G32 v0.16, §4.1; Miranda, Algebraic Curves and Riemann Surfaces,
Ch. III, Theorem 3.4; `rsq_exists_manifold`, `rsq_faithful_quotient`. -/
theorem s0_supplier_curve {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (S : g32p_Supplier) :
    let C := b65z_fibre c D.C t
    let Y := rsq_Quot S.χ.ker C
    let Z := rsq_Quot S.H C
    ∃ e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m),
      (∀ h : S.H, e (QuotientGroup.mk h) = S.χ h) ∧
      FaithfulSMul (S.H ⧸ S.χ.ker) Y ∧
      ∃ cy : ChartedSpace ℂ Y, ∃ cz : ChartedSpace ℂ Z,
        letI := cy
        letI := cz
        IsManifold 𝓘(ℂ, ℂ) ω Y ∧ IsManifold 𝓘(ℂ, ℂ) ω Z ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_proj S.χ.ker C) ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_proj S.H C) ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_coarsen (X := C) S.χ.ker) ∧
        (∀ a : S.H ⧸ S.χ.ker,
          ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun y : Y ↦ a • y)) ∧
        (∀ x : C, rsq_coarsen S.χ.ker (rsq_proj S.χ.ker C x) = rsq_proj S.H C x) :=
  s0_supplier_curve_aux D t S

example := @s0_supplier_curve

/-- Any two primitive images of the same action are related by the displayed cross map.
Source: Birkenhake–Lange, Complex Abelian Varieties, §5.3; G32 v0.16, §4.1. -/
theorem s0_part_isogeny
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier)
    (P Q : g32p_Part J aut S) :
    IsMonHom (P.incl ≫ Q.proj) ∧ ccm2_IsogenyOnPoints (P.incl ≫ Q.proj) ∧
      Function.Bijective (homPullback (P.incl ≫ Q.proj) 1) ∧ P.k = Q.k ∧
      ∀ a : cyc_Field S.m,
        homPullback (P.incl ≫ Q.proj) 1 ∘ₗ cyc_scalar Q.act.cyc_coordinates a =
          cyc_scalar P.act.cyc_coordinates a ∘ₗ homPullback (P.incl ≫ Q.proj) 1 :=
  s0_part_isogeny_aux J aut S P Q

example := @s0_part_isogeny

/-- Algebraicity is invariant under all primitive-image, retraction and coordinate choices.
The statement compares the full determinant spaces, not a chosen generator.
Source: Schoen (1988), Corollary 3.1; Fulton, Intersection Theory, §1.7 and §19.1;
Birkenhake–Lange, Complex Abelian Varieties, §5.3. -/
theorem s0_part_algebraic_iff
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier)
    (P Q : g32p_Part J aut S) :
    cyc_Algebraic (cupProductOf P.P) P.act.cyc_coordinates ↔
      cyc_Algebraic (cupProductOf Q.P) Q.act.cyc_coordinates :=
  s0_part_algebraic_iff_aux J aut S P Q

example := @s0_part_algebraic_iff

/-- Explicit-family successor retaining the actual deck action and image comparison.
Source: G32 v0.16, Proposition 4.6; `g32c_weilLine_algebraic`,
`g32h46_weilAlg_of_line_aux`, `b65z_IsLocalPrym`. -/
theorem s0_prop46 {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c)))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (X : ∀ t : b6t_polydisc c, g32p_Cover (b65z_fiber D B t))
    (f : ∀ t : b6t_polydisc c, g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ t a, homPullback (f t a).hom 1 = g32x_deck D t a)
    (hJ : ∀ t, (X t).J = g32x_J D t)
    (hdeck : ∀ t, HEq (X t).aut (fun a ↦ (f t a).hom))
    (hpol : ∀ t, HEq (X t).pol (g32x_theta D t))
    (himage : ∀ t, HEq (LinearMap.range (homPullback (X t).projA 1))
      (LinearMap.range (g32x_projector D t))) :
    ∀ (_hS : ∀ t, g32p_SchoenSupplier (X t))
      (_hM : ∀ t, g32p_MilneInvariance (X t).J (X t).pol
        (X t).pol_nondeg (X t).pol_pos)
    (_hComparison : ∃ (S : Fin 51 → g32p_Supplier) (χc : ∀ i, (S i).H →* ℂˣ)
      (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G),
      (∀ j, Simple (τ j) ∧ Simple (τbar j) ∧ ¬ g32p_SelfDual (τ j) ∧
        (∀ g, (τbar j).character g = star ((τ j).character g)) ∧ 0 < g32p_cwMult (τ j)) ∧
      (∀ j, Simple (θ j) ∧ g32p_Quaternionic (θ j) ∧ 0 < g32p_cwMult (θ j)) ∧
      (∀ j k, j ≠ k → IsEmpty (τ j ≅ τ k) ∧ IsEmpty (τ j ≅ τbar k)) ∧
      (∀ j k : Fin 4, j ≠ k → IsEmpty (θ j ≅ θ k)) ∧
      Nonempty (τ 2 ≅ g32p_rho) ∧
      (∀ σ : FDRep ℂ g32p_G, Simple σ → 0 < g32p_cwMult σ →
        (¬ g32p_SelfDual σ → ∃ j, Nonempty (σ ≅ τ j) ∨ Nonempty (σ ≅ τbar j)) ∧
        (g32p_Quaternionic σ → ∃ j, Nonempty (σ ≅ θ j))) ∧
      ∀ i : Fin 51,
        (∀ h, ((χc i h : ℂˣ) : ℂ) =
          g32p_root (S i).m ^ (Multiplicative.toAdd ((S i).χ h)).val) ∧
        (∃ r ∈ g32WitnessTable, r.i = i.val + 1 ∧ r.m = (S i).m ∧
          r.orderH = Nat.card (S i).H ∧ (g32p_exponents (S i)).Perm (expandExps r.exps)) ∧
        ∃ v ∈ g32VectorTable, v.i = i.val + 1 ∧
          papersA τ τbar θ (S i).H (χc i) = g32SparseVec v.coords),
    g32s_Prop46 P :=
  s0_prop46_aux D hg B P hP X f hf hJ hdeck hpol himage

example := @s0_prop46

/-- Algebraic supplier quotients with local monodromy and the exact primitive comparison.
Source: G32 v0.16, §4.1; Miranda, Algebraic Curves and Riemann Surfaces,
Ch. III, Theorem 3.4; Birkenhake–Lange, Complex Abelian Varieties, §11.4 and Ch. 12. -/
theorem s0_supplier_algebraic {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (S : g32p_Supplier)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    let C := b65z_fibre c D.C t
    let Y := rsq_Quot S.χ.ker C
    let Z := rsq_Quot S.H C
    ∃ (C₀ Y₀ Z₀ : Over (Spec ↧ℂ)),
      ∃ (_ : IsIntegral C₀.left) (_ : Smooth C₀.hom) (_ : IsProjective C₀.hom),
      ∃ (_ : IsIntegral Y₀.left) (_ : Smooth Y₀.hom) (_ : IsProjective Y₀.hom),
      ∃ (_ : IsIntegral Z₀.left) (_ : Smooth Z₀.hom) (_ : IsProjective Z₀.hom),
      TopologicalSpace.dim C₀.left = 1 ∧ TopologicalSpace.dim Y₀.left = 1 ∧
      TopologicalSpace.dim Z₀.left = 1 ∧
      ∃ (q : C₀ ⟶ Y₀) (p : Y₀ ⟶ Z₀) (j : C₀ ⟶ g32x_J D t)
        (a : (S.H ⧸ S.χ.ker) → (Y₀ ⟶ Y₀))
        (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
        (eC : C ≃ₜ ComplexPoint C₀) (eY : Y ≃ₜ ComplexPoint Y₀)
        (eZ : Z ≃ₜ ComplexPoint Z₀),
      (∀ h : S.H, e (QuotientGroup.mk h) = S.χ h) ∧
      a 1 = 𝟙 Y₀ ∧ (∀ u v, a (u * v) = a v ≫ a u) ∧
      Function.Injective a ∧ (∀ u, a u ≫ p = p) ∧
      (∀ x, Point.map q (eC x) = eY (rsq_proj S.χ.ker C x)) ∧
      (∀ y, Point.map p (eY y) = eZ (rsq_coarsen S.χ.ker y)) ∧
      (∀ u y, Point.map (a u) (eY y) = eY (u • y)) ∧
      Function.Bijective (homPullback j 1) ∧
      ∃ cy : ChartedSpace ℂ Y, ∃ cz : ChartedSpace ℂ Z,
        letI := cy
        letI := cz
        ∃ (_ : IsManifold 𝓘(ℂ, ℂ) ω Y) (_ : IsManifold 𝓘(ℂ, ℂ) ω Z),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim C₀.left) → ℂ) ω eC ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim C₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eC.symm ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim Y₀.left) → ℂ) ω eY ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim Y₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eY.symm ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim Z₀.left) → ℂ) ω eZ ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim Z₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eZ.symm ∧
        (∃ (y : Fin (g32p_exponents S).length → Y)
          (r : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker),
          Function.Injective (fun i ↦ rsq_coarsen S.χ.ker (y i)) ∧
          (∀ i, b4_IsRotGen ℂ (y i) (r i) ∧
            e (r i) = Multiplicative.ofAdd ((g32p_exponents S)[i] : ZMod S.m)) ∧
          (∀ z : Y, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
            ∃ i, rsq_coarsen S.χ.ker z = rsq_coarsen S.χ.ker (y i))) ∧
        (let V := LinearMap.ker
          (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
            (Polynomial.cyclotomic S.m ℚ))
        ∀ P : g32p_Part (g32x_J D t) (fun h ↦ (f h).hom) S,
          ∃ E : HQ P.P 1 ≃ₗ[ℚ] V,
            (∀ v, homPullback q 1 (E v) = homPullback j 1 (homPullback P.proj 1 v)) ∧
            (∀ (h : S.H) v,
              homPullback (a ((QuotientGroup.mk h)⁻¹)) 1 (E v) =
                (E (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S h) v) : HQ Y₀ 1)) ∧
            Module.finrank ℚ V = 2 * P.k * Nat.totient S.m ∧
            2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ Z) +
              (g32p_exponents S).length) :=
  s0_supplier_algebraic_aux D t hg S f hf

example := @s0_supplier_algebraic

#print axioms s0_supplier_algebraic

#print axioms s0_cover
#print axioms s0_supplier_curve
#print axioms s0_part_isogeny
#print axioms s0_part_algebraic_iff
#print axioms s0_prop46
end HodgeLean.Foundations.Program
