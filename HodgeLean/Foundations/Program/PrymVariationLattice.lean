import HodgeLean.Foundations.Program.PrymVariationLatticeProofs

/-! # B6-3b–3c: primitive integral images and their transported forms

Implication from the marked B6-2 moving covers and their holomorphic deck actions
to integral primitive image transport, fibrewise weight-one splitting and the
original restricted Riemann form. The four finite coefficient identities are
included as arithmetic obligations. The statements do not assert flatness of
the Hodge filtration, holomorphic period frames, ranks, or algebraic models.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The floor coefficients equal the printed real matrix coefficients.
Source: G32 v0.16, Definition 3.2 and Appendix A; `b4b_projectorCoeff`. -/
theorem b63l_projectorCoeff_cast (g : b4b_Group) :
    (b4b_projectorCoeff g : ℝ) = 6 * (b4b_toMatrix g⁻¹ 0 0).re :=
  b63l_projectorCoeff_cast_aux g

example (g : b4b_Group) :
    (b4b_projectorCoeff g : ℝ) = 6 * (b4b_toMatrix g⁻¹ 0 0).re :=
  b63l_projectorCoeff_cast g

/-- The integral coefficient function is invariant under inversion.
Source: G32 v0.16, §3.2–3.3, invariant Hermitian form. -/
theorem b63l_projectorCoeff_inverse (g : b4b_Group) :
    b4b_projectorCoeff g⁻¹ = b4b_projectorCoeff g :=
  b63l_projectorCoeff_inverse_aux g

example (g : b4b_Group) :
    b4b_projectorCoeff g⁻¹ = b4b_projectorCoeff g :=
  b63l_projectorCoeff_inverse g

/-- The integral group-algebra element squares to its denominator times itself.
Source: Serre, *Linear Representations of Finite Groups*, §2.2; G32 v0.16, Definition 3.2. -/
theorem b63l_projector_convolution (h : b4b_Group) :
    ∑ g : b4b_Group, b4b_projectorCoeff g * b4b_projectorCoeff (g⁻¹ * h) =
      b4b_projectorDenominator * b4b_projectorCoeff h :=
  b63l_projector_convolution_aux h

example (h : b4b_Group) :
    ∑ g : b4b_Group, b4b_projectorCoeff g * b4b_projectorCoeff (g⁻¹ * h) =
      b4b_projectorDenominator * b4b_projectorCoeff h :=
  b63l_projector_convolution h

/-- The natural representation sees the specified first-coordinate primitive projector.
Source: Serre, §2.2; G32 v0.16, Definition 3.2 with v = e₀. -/
theorem b63l_projector_matrix  :
    ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b4b_toMatrix g =
      (b4b_projectorDenominator : ℂ) •
        (Matrix.single 0 0 1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  b63l_projector_matrix_aux 

example  :
    ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b4b_toMatrix g =
      (b4b_projectorDenominator : ℂ) •
        (Matrix.single 0 0 1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  b63l_projector_matrix 

/-- The same scaled idempotent acts integrally on every moving fibre.
Source: Serre, §2.2; Hatcher, §2.1, functoriality of singular homology. -/
theorem b63l_fibreOperator_sq (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) (x : b6m_H1 (b6m_Fibre b C t)) :
    b63l_fibreOperator b C hC t (b63l_fibreOperator b C hC t x) =
      b4b_projectorDenominator • b63l_fibreOperator b C hC t x :=
  b63l_fibreOperator_sq_aux b C hC t x

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) (x : b6m_H1 (b6m_Fibre b C t)) :
    b63l_fibreOperator b C hC t (b63l_fibreOperator b C hC t x) =
      b4b_projectorDenominator • b63l_fibreOperator b C hC t x :=
  b63l_fibreOperator_sq b C hC t x

/-- The saturated fibre lattice is primitive, rationalizes to the specified projector image,
and is preserved by forward and inverse filled transport. Rank one refers to the
natural representation in `b63l_projector_matrix`, not to the homology image dimension.
Source: Bourbaki, *Algebra*, Ch. VII, §1; Serre, §2.2;
Birkenhake–Lange, §12.2; Hatcher, §2.1. -/
theorem b63l_fibre_primitive_rationalization (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (s t : b6t_polydisc b) :
    (∀ (n : ℤ), n ≠ 0 → ∀ x : b6m_H1 (b6m_Fibre b C s),
      n • x ∈ b63l_fibreLattice b C hC s → x ∈ b63l_fibreLattice b C hC s) ∧
    Function.Injective (b63l_fibreRationalInclusion b C hC s) ∧
    LinearMap.range (b63l_fibreRationalInclusion b C hC s) =
      LinearMap.range (b63l_fibreProjector b C hC s) ∧
    (∀ x, b63l_fibreProjector b C hC s (b63l_fibreProjector b C hC s x) =
      b63l_fibreProjector b C hC s x) ∧
    (∀ x : b6m_H1 (b6m_Fibre b C s),
      b6m_H1Equiv (b6m_transport b C s t) x ∈ b63l_fibreLattice b C hC t ↔
        x ∈ b63l_fibreLattice b C hC s) ∧
    (∀ y : b6m_H1 (b6m_Fibre b C t),
      b6m_H1Equiv (b6m_transport b C t s) y ∈ b63l_fibreLattice b C hC s ↔
        y ∈ b63l_fibreLattice b C hC t) :=
  b63l_fibre_primitive_rationalization_aux b C hC s t

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (s t : b6t_polydisc b) :
    (∀ (n : ℤ), n ≠ 0 → ∀ x : b6m_H1 (b6m_Fibre b C s),
      n • x ∈ b63l_fibreLattice b C hC s → x ∈ b63l_fibreLattice b C hC s) ∧
    Function.Injective (b63l_fibreRationalInclusion b C hC s) ∧
    LinearMap.range (b63l_fibreRationalInclusion b C hC s) =
      LinearMap.range (b63l_fibreProjector b C hC s) ∧
    (∀ x, b63l_fibreProjector b C hC s (b63l_fibreProjector b C hC s x) =
      b63l_fibreProjector b C hC s x) ∧
    (∀ x : b6m_H1 (b6m_Fibre b C s),
      b6m_H1Equiv (b6m_transport b C s t) x ∈ b63l_fibreLattice b C hC t ↔
        x ∈ b63l_fibreLattice b C hC s) ∧
    (∀ y : b6m_H1 (b6m_Fibre b C t),
      b6m_H1Equiv (b6m_transport b C t s) y ∈ b63l_fibreLattice b C hC s ↔
        y ∈ b63l_fibreLattice b C hC t) :=
  b63l_fibre_primitive_rationalization b C hC s t

/-- Filled transport and its inverse restrict to the saturated integral images.
Source: `b6m_homology_equivariant`; Hatcher, §2.1; Harris–Morrison, §1.G. -/
theorem b63l_fibre_image_transport (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (s t : b6t_polydisc b) :
    (∀ x : b6m_H1 (b6m_Fibre b C s),
      b6m_H1Equiv (b6m_transport b C s t) (b63l_fibreOperator b C hC s x) =
        b63l_fibreOperator b C hC t (b6m_H1Equiv (b6m_transport b C s t) x)) ∧
    ∃ T : b63l_fibreLattice b C hC s ≃ₗ[ℤ] b63l_fibreLattice b C hC t,
      (∀ x, (T x).val = b6m_H1Equiv (b6m_transport b C s t) x.val) ∧
      (∀ y, (T.symm y).val = b6m_H1Equiv (b6m_transport b C t s) y.val) :=
  b63l_fibre_image_transport_aux b C hC s t

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (s t : b6t_polydisc b) :
    (∀ x : b6m_H1 (b6m_Fibre b C s),
      b6m_H1Equiv (b6m_transport b C s t) (b63l_fibreOperator b C hC s x) =
        b63l_fibreOperator b C hC t (b6m_H1Equiv (b6m_transport b C s t) x)) ∧
    ∃ T : b63l_fibreLattice b C hC s ≃ₗ[ℤ] b63l_fibreLattice b C hC t,
      (∀ x, (T x).val = b6m_H1Equiv (b6m_transport b C s t) x.val) ∧
      (∀ y, (T.symm y).val = b6m_H1Equiv (b6m_transport b C t s) y.val) :=
  b63l_fibre_image_transport b C hC s t

/-- The period comparison identifies the saturated singular image with the saturated period lattice.
Source: Farkas–Kra, *Riemann Surfaces*, Ch. III; Hatcher, §2.A;
Birkenhake–Lange, §12.1–12.2; `b6m_period_comparison` on main. -/
theorem b63l_period_image_comparison (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) :
    ∃ P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C,
      (∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ) ∧
      (∀ x, P (b63l_homologyOperator C (fun g ↦ (hG g).continuous) x) =
        b4_groupEnd ℂ (C := C) b4b_projectorCoeff (P x)) ∧
      ∃ E : b63l_saturation (LinearMap.range (b63l_homologyOperator C (fun g ↦ (hG g).continuous)))
          ≃ₗ[ℤ] b63l_periodLattice C,
        ∀ x, (E x).val = P x.val :=
  b63l_period_image_comparison_aux C hG

example (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) :
    ∃ P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C,
      (∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ) ∧
      (∀ x, P (b63l_homologyOperator C (fun g ↦ (hG g).continuous) x) =
        b4_groupEnd ℂ (C := C) b4b_projectorCoeff (P x)) ∧
      ∃ E : b63l_saturation (LinearMap.range (b63l_homologyOperator C (fun g ↦ (hG g).continuous)))
          ≃ₗ[ℤ] b63l_periodLattice C,
        ∀ x, (E x).val = P x.val :=
  b63l_period_image_comparison C hG

/-- The self-adjoint primitive image has weight-one splitting and the original integral Riemann form.
Source: Birkenhake–Lange, §5.1, §5.3 and §12.2; `b4_groupEnd_adjoint`,
`b4_groupEnd_periodF`, `b2_image_isWeightOne`, `b2_image_isRiemannForm`. -/
theorem b63l_image_riemann (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q) :
    (∀ x y : b3_periodLattice ℂ C,
      Q (b4_groupEnd ℂ b4b_projectorCoeff x) y =
        Q x (b4_groupEnd ℂ b4b_projectorCoeff y)) ∧
    b2_IsWeightOne (b63l_periodLattice C) (b63l_periodF C) ∧
    b2_IsRiemannForm (b63l_periodLattice C) (b63l_periodF C)
      (b63l_periodQ C Q) :=
  b63l_image_riemann_aux C hG Q hQ

example (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q) :
    (∀ x y : b3_periodLattice ℂ C,
      Q (b4_groupEnd ℂ b4b_projectorCoeff x) y =
        Q x (b4_groupEnd ℂ b4b_projectorCoeff y)) ∧
    b2_IsWeightOne (b63l_periodLattice C) (b63l_periodF C) ∧
    b2_IsRiemannForm (b63l_periodLattice C) (b63l_periodF C)
      (b63l_periodQ C Q) :=
  b63l_image_riemann C hG Q hQ

/-- The marked geometric comparison preserves the unscaled restricted integral pairing.
Source: `b6m_intersection_transport` on main; Farkas–Kra, Ch. III;
Harris–Morrison, §1.G; Birkenhake–Lange, §5.3 and §12.2. -/
theorem b63l_image_pairing_transport (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b)
    (C D : Type) [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D] [MulAction b4b_Group C] [MulAction b4b_Group D]
    (hC : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (hD : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : D ↦ g • x))
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (hs : Function.Surjective f)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (heG : ∀ (g : b4b_Group) (x : C), e (g • x) = g • e x)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (R : LinearMap.BilinForm ℤ (b3_periodLattice ℂ D)) (hR : b3_IsIntersectionForm ℂ R) :
    ∃ (P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C)
      (S : b6m_H1 D ≃ₗ[ℤ] b3_periodLattice ℂ D)
      (T : b63l_periodLattice C ≃ₗ[ℤ] b63l_periodLattice D),
      (∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ) ∧
      (∀ γ : b3_SmoothLoop ℂ D, S (b6m_loopClass D γ) = b3_latticePeriod ℂ D γ) ∧
      (∀ x, (T x).val = S (b6m_H1Equiv e (P.symm x.val))) ∧
      (∀ y, (T.symm y).val = P (b6m_H1Equiv e.symm (S.symm y.val))) ∧
      ∀ x y, b63l_periodQ D R (T x) (T y) =
        b63l_periodQ C Q x y :=
  b63l_image_pairing_transport_aux b hb t ht C D hC hD f k hf hk hs e he heG Q hQ R hR

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b)
    (C D : Type) [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D] [MulAction b4b_Group C] [MulAction b4b_Group D]
    (hC : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (hD : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : D ↦ g • x))
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (hs : Function.Surjective f)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (heG : ∀ (g : b4b_Group) (x : C), e (g • x) = g • e x)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (R : LinearMap.BilinForm ℤ (b3_periodLattice ℂ D)) (hR : b3_IsIntersectionForm ℂ R) :
    ∃ (P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C)
      (S : b6m_H1 D ≃ₗ[ℤ] b3_periodLattice ℂ D)
      (T : b63l_periodLattice C ≃ₗ[ℤ] b63l_periodLattice D),
      (∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ) ∧
      (∀ γ : b3_SmoothLoop ℂ D, S (b6m_loopClass D γ) = b3_latticePeriod ℂ D γ) ∧
      (∀ x, (T x).val = S (b6m_H1Equiv e (P.symm x.val))) ∧
      (∀ y, (T.symm y).val = P (b6m_H1Equiv e.symm (S.symm y.val))) ∧
      ∀ x y, b63l_periodQ D R (T x) (T y) =
        b63l_periodQ C Q x y :=
  b63l_image_pairing_transport b hb t ht C D hC hD f k hf hk hs e he heG Q hQ R hR

end HodgeLean.Foundations.Program
