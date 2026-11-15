import HodgeLean.Foundations.Program.PrymParabolicIntersectionDefs

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.Program

theorem hga_edge_joined {G : Type} [Group G] {r : ℕ} {g : Fin r → G}
    {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap g T) (ε : hg2_Edge G r) :
    Joined (F.vert (hg2_src g ε)) (F.vert (hg2_tgt g ε)) := by
  exact ⟨{ __ := F.edge ε, source' := (F.ends ε).1, target' := (F.ends ε).2 }⟩

theorem hga_root_step_joined {G : Type} [Group G] {r : ℕ} {g : Fin r → G}
    {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap g T) (x : G) (i : Fin r) :
    Joined (F.vert (Sum.inl x)) (F.vert (Sum.inl (x * g i))) := by
  have h1 := hga_edge_joined F (Sum.inl (i, x))
  have h2 := hga_edge_joined F (Sum.inl (i, x * g i))
  have hc : ((x * g i : G) : G ⧸ Subgroup.zpowers (g i)) = (x : G ⧸ _) := by
    rw [QuotientGroup.eq]
    simp
  simp only [hg2_src, hg2_tgt, hc] at h1 h2
  exact h1.trans h2.symm

theorem hga_joined_base_vertices {G : Type} [Group G] {r : ℕ} {g : Fin r → G}
    {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap g T)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (x : G) :
    Joined (F.vert (Sum.inl 1)) (F.vert (Sum.inl x)) := by
  let S : Subgroup G :=
    { carrier := {a | ∀ y : G, Joined (F.vert (Sum.inl y)) (F.vert (Sum.inl (y * a)))}
      one_mem' := by
        intro y
        simpa only [mul_one] using Joined.refl (F.vert (Sum.inl y))
      mul_mem' := by
        intro a b ha hb y
        simpa only [mul_assoc] using (ha y).trans (hb (y * a))
      inv_mem' := by
        intro a ha y
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using (ha (y * a⁻¹)).symm }
  have hle : Subgroup.closure (Set.range g) ≤ S := by
    apply (Subgroup.closure_le S).mpr
    rintro _ ⟨i, rfl⟩ y
    exact hga_root_step_joined F y i
  rw [hgen] at hle
  have hx : x ∈ S := hle (by trivial)
  change ∀ y : G, Joined (F.vert (Sum.inl y)) (F.vert (Sum.inl (y * x))) at hx
  simpa only [one_mul] using hx 1

theorem hga_pathConnected_of_triangles {G : Type} [Group G] {r : ℕ} {g : Fin r → G}
    {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap g T)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hcover : ∀ t : T, ∃ (τ : hg2_Tri G r) (a : StdSimplex ℝ (Fin 3)), F.tri τ a = t) :
    PathConnectedSpace T := by
  have hj (t : T) : Joined (F.vert (Sum.inl 1)) t := by
    obtain ⟨τ, a, rfl⟩ := hcover t
    have hv : ∃ x : G, F.tri τ (StdSimplex.single 0) = F.vert (Sum.inl x) := by
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩ <;> refine ⟨x, ?_⟩ <;>
        exact (hg5_face_vertex (F.tri _)).1.symm.trans
          ((congrArg (fun p : C(unitInterval, T) ↦ p 0) (F.faces _).2.2).trans (F.ends _).1)
    obtain ⟨x, hx⟩ := hv
    have hpath : Joined (F.tri τ (StdSimplex.single 0)) (F.tri τ a) :=
      (PathConnectedSpace.joined _ _).map (F.tri τ).continuous
    rw [hx] at hpath
    exact (hga_joined_base_vertices F hgen x).trans hpath
  exact ⟨⟨F.vert (Sum.inl 1)⟩, fun x y ↦ (hj x).symm.trans (hj y)⟩

theorem hga_lift_pathConnected (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    (L : hg2_Tri b4b_Group 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) :
    PathConnectedSpace C := by
  let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  exact hga_pathConnected_of_triangles F b63d_root_subgroup
    (hg5_lift_cells U π hπ y₀ hy₀ u₀ C hC f hf hfinv hftr ι hι hιr hfι hιG L hL).1

#print axioms hga_edge_joined
#print axioms hga_root_step_joined
#print axioms hga_joined_base_vertices
#print axioms hga_pathConnected_of_triangles
#print axioms hga_lift_pathConnected

end HodgeLean.Foundations.Program
