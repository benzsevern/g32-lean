import HodgeLean.Foundations.Program.PrymVariationCentreProofs

/-! # B6-3d: centre action and moving Hodge ranks

Implication from holomorphic G32 actions on the actual marked moving fibres,
with the stated sphere projection and root rotation data, to rank twelve,
complex dimension six and central Hodge ranks (3,3). Chevalley–Weil and the
restriction of the centre are proof obligations. No algebraic model,
holomorphic frame or period map is selected here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The central deck action restricts to the saturated integral fibre lattice.
Source: G32 v0.16, §3.3 and Appendix A; Birkenhake–Lange, §12.2. -/
theorem b63d_centre_range (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    ∃ Z : b63l_parameterLattice b C hC V hV t →ₗ[ℤ] b63l_parameterLattice b C hC V hV t,
      ∀ x, (Z x).val = b63d_centre b C hC V hV t x.val :=
  b63d_centre_range_aux b C hC V hV t

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    ∃ Z : b63l_parameterLattice b C hC V hV t →ₗ[ℤ] b63l_parameterLattice b C hC V hV t,
      ∀ x, (Z x).val = b63d_centre b C hC V hV t x.val :=
  b63d_centre_range b C hC V hV t

/-- The integral expression 1 + 2ω restricts and squares to minus three on each fibre.
Source: G32 v0.16, §3.2–3.3; Serre, §2.2; Hatcher, §3.A. -/
theorem b63d_prymOperator_sq (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x)) :
    ∃ J : b63l_parameterLattice b C hC V hV t →ₗ[ℤ] b63l_parameterLattice b C hC V hV t,
      (∀ x, (J x).val = b63d_operator b C hC V hV t x.val) ∧
      ∀ x, J (J x) = (-3 : ℤ) • x :=
  b63d_prymOperator_sq_aux b C hC V hV t hG

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x)) :
    ∃ J : b63l_parameterLattice b C hC V hV t →ₗ[ℤ] b63l_parameterLattice b C hC V hV t,
      (∀ x, (J x).val = b63d_operator b C hC V hV t x.val) ∧
      ∀ x, J (J x) = (-3 : ℤ) • x :=
  b63d_prymOperator_sq b C hC V hV t hG

/-- The central period action and 1 + 2ω restrict to the saturation and preserve its filtration.
Source: G32 v0.16, §3.2–3.3; Birkenhake–Lange, §12.2; `b4_groupEnd_periodF`. -/
theorem b63d_prymOperator_filtration (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x)) :
    ∃ (Z J : b63l_periodLattice (b63l_parameterFibre b C V hV t) →ₗ[ℤ] b63l_periodLattice (b63l_parameterFibre b C V hV t)),
      (∀ x, (Z x).val = b4b_centreAct (b63l_parameterFibre b C V hV t) hG x.val) ∧
      J = LinearMap.id + 2 • Z ∧
      (∀ x, (J x).val = b63d_periodOperator (b63l_parameterFibre b C V hV t) hG x.val) ∧
      b63l_periodF (b63l_parameterFibre b C V hV t) ≤ (b63l_periodF (b63l_parameterFibre b C V hV t)).comap (J.baseChange ℂ) :=
  b63d_prymOperator_filtration_aux b C hC V hV t hG

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x)) :
    ∃ (Z J : b63l_periodLattice (b63l_parameterFibre b C V hV t) →ₗ[ℤ] b63l_periodLattice (b63l_parameterFibre b C V hV t)),
      (∀ x, (Z x).val = b4b_centreAct (b63l_parameterFibre b C V hV t) hG x.val) ∧
      J = LinearMap.id + 2 • Z ∧
      (∀ x, (J x).val = b63d_periodOperator (b63l_parameterFibre b C V hV t) hG x.val) ∧
      b63l_periodF (b63l_parameterFibre b C V hV t) ≤ (b63l_periodF (b63l_parameterFibre b C V hV t)).comap (J.baseChange ℂ) :=
  b63d_prymOperator_filtration b C hC V hV t hG

/-- The same quadratic identity holds on the saturated period lattice in ambient coordinates.
Source: G32 v0.16, §3.3; Serre, §2.2; Birkenhake–Lange, §12.2. -/
theorem b63d_periodOperator_sq (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (x : b63l_periodLattice (b63l_parameterFibre b C V hV t)) :
    b63d_periodOperator (b63l_parameterFibre b C V hV t) hG (b63d_periodOperator (b63l_parameterFibre b C V hV t) hG x.val) = (-3 : ℤ) • x.val :=
  b63d_periodOperator_sq_aux b C hC V hV t hG x

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (x : b63l_periodLattice (b63l_parameterFibre b C V hV t)) :
    b63d_periodOperator (b63l_parameterFibre b C V hV t) hG (b63d_periodOperator (b63l_parameterFibre b C V hV t) hG x.val) = (-3 : ℤ) • x.val :=
  b63d_periodOperator_sq b C hC V hV t hG x

/-- Chevalley–Weil gives both central Hodge ranks on every moving marked fibre.
Source: G32 v0.16, Proposition 3.1 and Lemma 3.3; `b4_chevalleyWeil_holo`, `b4_chevalleyWeil_top`. -/
theorem b63d_chevalleyWeil_hodge (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    [FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hs : Function.Surjective (b63d_projection b C f V hV t))
    (hgal : b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ i : Fin 13, ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i)) :
    (Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) hG (g32h_omega)) : ℝ) = g32h_holoCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) ∧
    (Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) hG (star g32h_omega)) : ℝ) =
      (g32h_multCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) : ℝ) - g32h_holoCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) ∧
    Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) hG (g32h_omega)) = 3 ∧
    Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) hG (star g32h_omega)) = 3 :=
  b63d_chevalleyWeil_hodge_aux b C hC V hV t hG hb f hf hs hgal hbranch hrot

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    [FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hs : Function.Surjective (b63d_projection b C f V hV t))
    (hgal : b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ i : Fin 13, ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i)) :
    (Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) hG (g32h_omega)) : ℝ) = g32h_holoCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) ∧
    (Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) hG (star g32h_omega)) : ℝ) =
      (g32h_multCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) : ℝ) - g32h_holoCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) ∧
    Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) hG (g32h_omega)) = 3 ∧
    Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) hG (star g32h_omega)) = 3 :=
  b63d_chevalleyWeil_hodge b C hC V hV t hG hb f hf hs hgal hbranch hrot

/-- The actual singular and period saturations are free integral lattices of rank twelve.
Source: G32 v0.16, Proposition 3.1 and Lemma 3.3; Hatcher, §3.A; Birkenhake–Lange, §12.2. -/
theorem b63d_lattice_rank (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    [FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hs : Function.Surjective (b63d_projection b C f V hV t))
    (hgal : b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ i : Fin 13, ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i)) :
    Nonempty (Module.Basis (Fin 12) ℤ (b63l_parameterLattice b C hC V hV t)) ∧
    Nonempty (Module.Basis (Fin 12) ℤ (b63l_periodLattice (b63l_parameterFibre b C V hV t))) :=
  b63d_lattice_rank_aux b C hC V hV t hG hb f hf hs hgal hbranch hrot

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    [FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hs : Function.Surjective (b63d_projection b C f V hV t))
    (hgal : b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ i : Fin 13, ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i)) :
    Nonempty (Module.Basis (Fin 12) ℤ (b63l_parameterLattice b C hC V hV t)) ∧
    Nonempty (Module.Basis (Fin 12) ℤ (b63l_periodLattice (b63l_parameterFibre b C V hV t))) :=
  b63d_lattice_rank b C hC V hV t hG hb f hf hs hgal hbranch hrot

/-- The tangent quotient of the saturated moving Prym has complex dimension six.
Source: G32 v0.16, Proposition 3.1 and Lemma 3.3; Birkenhake–Lange, §1.1 and §12.2. -/
theorem b63d_dim_eq (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    [FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hs : Function.Surjective (b63d_projection b C f V hV t))
    (hgal : b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ i : Fin 13, ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i)) :
    (Module.finrank ℂ ((ℂ ⊗[ℤ] b63l_periodLattice (b63l_parameterFibre b C V hV t)) ⧸ (b63l_periodF (b63l_parameterFibre b C V hV t))) : ℤ) =
      g32h_multCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) ∧
    Module.finrank ℂ ((ℂ ⊗[ℤ] b63l_periodLattice (b63l_parameterFibre b C V hV t)) ⧸ (b63l_periodF (b63l_parameterFibre b C V hV t))) = 6 ∧
    Module.finrank ℂ (b63l_periodF (b63l_parameterFibre b C V hV t)) = 6 :=
  b63d_dim_eq_aux b C hC V hV t hG hb f hf hs hgal hbranch hrot

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    [FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hs : Function.Surjective (b63d_projection b C f V hV t))
    (hgal : b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ i : Fin 13, ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i)) :
    (Module.finrank ℂ ((ℂ ⊗[ℤ] b63l_periodLattice (b63l_parameterFibre b C V hV t)) ⧸ (b63l_periodF (b63l_parameterFibre b C V hV t))) : ℤ) =
      g32h_multCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) ∧
    Module.finrank ℂ ((ℂ ⊗[ℤ] b63l_periodLattice (b63l_parameterFibre b C V hV t)) ⧸ (b63l_periodF (b63l_parameterFibre b C V hV t))) = 6 ∧
    Module.finrank ℂ (b63l_periodF (b63l_parameterFibre b C V hV t)) = 6 :=
  b63d_dim_eq b C hC V hV t hG hb f hf hs hgal hbranch hrot

/-- The central action commutes with the marked integral transport at every pair of parameters.
Source: Hatcher, §2.1; Harris–Morrison, §1.G; `b6m_homology_equivariant`. -/
theorem b63d_centre_transport (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    (s : V) (x : b6m_H1 (b63l_parameterFibre b C V hV s)) :
    b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩)
      (b63d_centre b C hC V hV s x) =
    b63d_centre b C hC V hV t
      (b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩) x) :=
  b63d_centre_transport_aux b C hC V hV t s x

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    (s : V) (x : b6m_H1 (b63l_parameterFibre b C V hV s)) :
    b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩)
      (b63d_centre b C hC V hV s x) =
    b63d_centre b C hC V hV t
      (b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩) x) :=
  b63d_centre_transport b C hC V hV t s x

end HodgeLean.Foundations.Program
