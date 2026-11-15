import HodgeLean.Foundations.Program.PrymParabolicIntersectionWalkDuality
import HodgeLean.Foundations.Program.PrymParabolicIntersectionConnected

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace HodgeLean.Foundations.Program

attribute [local instance] b3Forms_isManifold_real b4cov_sphChartedSpace b4cov_sph_isManifold

/-! ## The realization in a parameter fibre -/

section Fibre

variable (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
  (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
  (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
  (u₀ : π ⁻¹' {y₀}) (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
  (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
  (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
  (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction b4b_Group C]
  (hC : ∀ h : b4b_Group, Continuous (fun c : C ↦ h • c))
  (f : C → OnePoint ℂ) (hf : Continuous f)
  (hfinv : ∀ (h : b4b_Group) (c : C), f (h • c) = f c)
  (hftr : ∀ c c' : C, f c = f c' → ∃ h : b4b_Group, h • c = c')
  (hstab : ∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
    Nat.card (MulAction.stabilizer b4b_Group c) = orderOf (b4b_root j))
  (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
  (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
  (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : b4b_Group) (u : U), ι (h • u) = h • ι u)
  (L : hg2_Tri b4b_Group 13 → C(Convexity.StdSimplex ℝ (Fin 3), C))
  (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
    L τ (Convexity.StdSimplex.single 0) = hg5_triSheet τ • ι u₀)
  (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)

/-- **Cell facts in the fibre.** The realization of `X̃(b4b_root)` in a parameter fibre has open
triangle interiors avoiding the edges, and embedded edges with disjoint interiors.
Source: `hg8_tri_attach`, `hg8_skel_cells`, `hg8_edge_embed`, transported by the product
coordinate `b6m_coordinate`. -/
theorem hga_fibre_cells :
    hga_Cells (hga_fibreMap (hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv
      hftr hstab ι hι hιr hfι hιG L hL) V hV t) := by
  let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr
    hfι hιG L hL
  let H := b6m_coordinate mr_base C ⟨t.val, hV t.property⟩
  have hcellc := (hg8_skel_cells U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab
    ι hι hιr hfι hιG L hL).1
  obtain ⟨-, hemb, hvert⟩ := hg8_edge_embed U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv
    hftr hstab ι hι hιr hfι hιG L hL
  have hatt := hg8_tri_attach U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab
    ι hι hιr hfι hιG L hL
  refine ⟨fun τ ↦ ?_, fun τ a ha ε θ h ↦ ?_, fun ε ε' θ θ' hθ h ↦ ?_⟩
  · have e : (hga_fibreMap F V hV t).tri τ '' {a | ∀ k, 0 < Convexity.StdSimplex.weights a k} =
        H.symm '' (L τ '' {a | ∀ k, 0 < Convexity.StdSimplex.weights a k}) := by
      rw [Set.image_image]
      rfl
    rw [e]
    exact H.symm.isOpenMap _ (hatt τ).2.1
  · have h' : L τ a = hg5_liftEdge L ε θ := H.symm.injective h
    have h1 : L τ a ∈ (hg8_skel1 F)ᶜ := by
      rw [hcellc]
      exact Set.mem_iUnion.2 ⟨τ, a, ha, rfl⟩
    exact h1 (Or.inr (Set.mem_iUnion.2 ⟨ε, θ, h'.symm⟩))
  · have h' : hg5_liftEdge L ε θ = hg5_liftEdge L ε' θ' := H.symm.injective h
    have hθI : θ ∈ Set.Ioo (0 : unitInterval) 1 := ⟨hθ.1, hθ.2⟩
    by_cases hθ' : θ' ∈ Set.Ioo (0 : unitInterval) 1
    · exact hemb ε ε' θ θ' hθI hθ' h'
    · exfalso
      have h01 : θ' = 0 ∨ θ' = 1 := by
        rcases eq_or_lt_of_le θ'.2.1 with h0 | h0
        · exact Or.inl (Subtype.ext h0.symm)
        · rcases eq_or_lt_of_le θ'.2.2 with h1 | h1
          · exact Or.inr (Subtype.ext h1)
          · exact absurd ⟨h0, h1⟩ hθ'
      rcases h01 with rfl | rfl
      · exact hvert ε θ hθI _ (h'.trans (F.ends ε').1)
      · exact hvert ε θ hθI _ (h'.trans (F.ends ε').2)

variable [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
  [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
  (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))

include hk in
/-- **Window facts in the fibre.**
Source: `hga_fibre_cells`, `hga_dualWin_good`, `hga_primWin_good`, `hga_windows_cross`,
`hga_windows_sign`. -/
theorem hga_fibre_winFacts :
    hga_WinFacts (hga_fibreMap (hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv
      hftr hstab ι hι hιr hfι hιG L hL) V hV t) := by
  let T := b63l_parameterFibre mr_base C V hV t
  let H : T ≃ₜ C := b6m_coordinate mr_base C ⟨t.val, hV t.property⟩
  letI : PathConnectedSpace C := hga_lift_pathConnected U π hπ y₀ hy₀ u₀ γ hγ hroot
    C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  letI : PathConnectedSpace T := H.symm.pathConnectedSpace
  letI : CompactSpace T := H.symm.compactSpace
  letI : T2Space T := H.symm.t2Space
  let D := hga_fibreMap (hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv
      hftr hstab ι hι hιr hfι hιG L hL) V hV t
  have hD : ∀ τ a, f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ (D.tri τ a)) =
      hg5_tri (hg5_triBase τ) a := fun τ a ↦ (hL τ).1 a
  refine ⟨hga_fibre_cells U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG
      L hL V hV t, fun ε ↦ ?_, fun ε ↦ ?_, fun ε x y h ↦ ?_, fun ε ↦ ?_⟩
  · exact hga_dualWin_good U π hπ C f ι hι hιr hfι V hV t hk hD (hga_spec_τo b4b_root ε)
      (hga_spec_τi ε) (hga_W_fo D ε) (hga_W_fi D ε)
  · exact hga_primWin_good U π hπ C f ι hι hιr hfι V hV t hk hD (τe := hga_triArc ε)
      (hga_spec_τe ε) (hga_W_fe D ε)
  · exact hga_windows_cross (fun x ↦ f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ x)) hD
      (hga_spec_τo b4b_root ε) (hga_spec_τi ε) (hga_triArc ε) (hga_spec_τe ε)
      (hga_W_fe D ε) x y h
  · exact hga_windows_sign U π hπ C f ι hι hιr hfι V hV t hk hD (hga_spec_τo b4b_root ε)
      (hga_spec_τi ε) (hga_W_fo D ε) (hga_W_fi D ε) (hga_spec_τe ε)
      (hga_W_fe D ε)

include hk in
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular in
/-- **Duality for the barycentric dual cycle in the fibre** (statement 4 of the plan): for every
singular `1`-cocycle `φ` and every singular `1`-cycle `z` of the fibre,
`Q(P [dual φ], P [z]) = φ z`.
Source: Hatcher, *Algebraic Topology*, §3.3; Farkas–Kra, III.1; Guillemin–Pollack, Ch. 3 §3. -/
theorem hga_fibre_duality
    (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t),
      P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : b3_IsIntersectionForm ℂ Q)
    (φ : Simplicial.Cochain ℤ
      (TopCat.toSSet.obj (TopCat.of (b63l_parameterFibre mr_base C V hV t))) 1)
    (hφ : φ ∘ₗ Simplicial.boundary ℤ 1 = 0)
    (z : LinearMap.ker
      ((SingularChainComplex ℤ (TopCat.of (b63l_parameterFibre mr_base C V hV t))).sc 1).g.hom) :
    Q (P (((SingularChainComplex ℤ (TopCat.of (b63l_parameterFibre mr_base C V hV t))).sc 1
        ).moduleCatHomologyClass (hga_dual_fundCycle (hga_fibreMap (hg8_liftMap U π hπ y₀ hy₀ u₀
          b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL) V hV t) φ hφ)))
      (P (((SingularChainComplex ℤ (TopCat.of (b63l_parameterFibre mr_base C V hV t))).sc 1
        ).moduleCatHomologyClass z)) = φ z.1 := by
  let T := b63l_parameterFibre mr_base C V hV t
  let H : T ≃ₜ C := b6m_coordinate mr_base C ⟨t.val, hV t.property⟩
  letI : T2Space T := H.symm.t2Space
  let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr
    hfι hιG L hL
  have hsurj : Function.Surjective (hg8_H1map (hga_fibreMap F V hV t)) := by
    intro y
    obtain ⟨x₁, hx₁⟩ := (b6m_H1Equiv H.symm).surjective y
    obtain ⟨x, hx⟩ := (hg8_H1map_bijective U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv
      hftr hstab ι hι hιr hfι hιG L hL).2 x₁
    refine ⟨x, ?_⟩
    rw [hga_H1map_fibre]
    change (b6m_H1Equiv H.symm) (hg8_H1map F x) = y
    rw [hx, hx₁]
  exact hga_duality_of_winFacts (hga_fibreMap F V hV t)
    (hga_fibre_winFacts U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG
      L hL V hV t hk) hsurj P hP Q hQ φ hφ z

end Fibre

end HodgeLean.Foundations.Program
