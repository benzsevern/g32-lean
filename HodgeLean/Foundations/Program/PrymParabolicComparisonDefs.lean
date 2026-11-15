import HodgeLean.Foundations.Program.ParabolicCohomologyDefs

/-! # Definitions for stage H3a: the lifted Δ-complex of G32 Figure 1

For a group `G` and a tuple `g₀, …, g_{r−1}` in `G`, the Δ-complex of G32 Figure 1 on the sphere
(vertices `b₀`, `b_∞`, `p₀, …, p_{r−1}`; edges `e_i : b₀ → p_i`, `f_i : b₀ → b_∞`,
`h_i : p_i → b_∞`; triangles `A_i = [b₀, p_i, b_∞]` with faces `h_i, f_i, e_i` and
`B_i = [b₀, p_i, b_∞]` with faces `h_i, f_{i+1}, e_i`, indices mod `r`), lifted to the `G`-cover
branched over the `p_i` with monodromy `g`. Every cell over `b₀`, `b_∞`, an edge or a triangle
is labelled by a sheet `x ∈ G`; the cells over `p_i` are the cosets `x⟨g_i⟩`. The deck group
acts by left multiplication on labels. Crossing `h_i` from `A_i` to `B_i` multiplies the label
on the right by `g_i`, so the loop `f_i f_{i+1}⁻¹` around `p_i` has monodromy `x ↦ x g_i`.

On this explicit complex: cellular cochains with coefficients in a module, the two coboundary
maps, cellular `H⁰` and `H¹`, the `σ`-equivariant cochains for a representation
`σ : G →* Matrix ι ι K`, their cohomology, an explicit linear map from the parameters of
`ParabolicCohomologyDefs` to equivariant `1`-cochains (Shapiro's lemma made explicit), the
cellular cup product of `1`-cochains with a fibre form, and its evaluation on the orientation
cycle `Σ_x Σ_i (A_i(x) − B_i(x))`.

Nothing here identifies the realization of the complex with a compact marked cover `C_t` of
B6-2, its cellular cohomology with singular (co)homology, or the equivariant part with the
B6-3 Prym lattice (later stages of H3). HC no distance; AV milestone no distance.
-/

noncomputable section

open Matrix

namespace HodgeLean.Foundations.Program

/-- The vertices of the lifted complex: `b₀(x)` (`Sum.inl x`), `b_∞(x)` (`Sum.inr (Sum.inl x)`)
and `p_i(x⟨g_i⟩)` (`Sum.inr (Sum.inr ⟨i, x⟨g_i⟩⟩)`).
Source: G32 v0.16, Lemma 6.2 and Figure 1; Hatcher, *Algebraic Topology*, §2.1 (Δ-complexes)
and §1.3 (covering spaces); a branched cover has `|G|/ord(g_i)` points over `p_i`. -/
abbrev hg_Vert {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) : Type _ :=
  G ⊕ G ⊕ (Σ i : Fin r, G ⧸ Subgroup.zpowers (g i))

example {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (x : G) : hg_Vert g := Sum.inl x

/-- The edges of the lifted complex: `e_i(x)` (`Sum.inl (i, x)`), `f_i(x)`
(`Sum.inr (Sum.inl (i, x))`) and `h_i(x)` (`Sum.inr (Sum.inr (i, x))`).
Source: G32 v0.16, Lemma 6.2 and Figure 1; Hatcher, §2.1. -/
abbrev hg_Edge (G : Type*) (r : ℕ) : Type _ := (Fin r × G) ⊕ (Fin r × G) ⊕ (Fin r × G)

example (G : Type*) (x : G) : hg_Edge G 1 := Sum.inl (0, x)

/-- The triangles of the lifted complex: `A_i(x)` (`Sum.inl (i, x)`) and `B_i(x)`
(`Sum.inr (i, x)`), both with vertices `[b₀, p_i, b_∞]` in this order.
Source: G32 v0.16, Lemma 6.2 and Figure 1 (`2r` triangles on the sphere); Hatcher, §2.1. -/
abbrev hg_Tri (G : Type*) (r : ℕ) : Type _ := (Fin r × G) ⊕ (Fin r × G)

example (G : Type*) (x : G) : hg_Tri G 1 := Sum.inr (0, x)

/-- `Q_i = g₀ ⋯ g_{i−1}` in `G` (so `Q₀ = 1`), the group-level form of `pc_Q`.
Source: G32 v0.16, before Lemma 6.2 ("Put `Q_i = T₁ ⋯ T_{i−1}`"). -/
def hg_Q {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (i : Fin r) : G :=
  (((List.finRange r).filter fun j => j < i).map g).prod

example {G : Type*} [Group G] {r : ℕ} (g : Fin (r + 1) → G) : hg_Q g 0 = 1 := by
  simp [hg_Q]

/-- The initial vertex of an edge: `e_i(x), f_i(x)` start at `b₀(x)`, `h_i(x)` at `p_i(x⟨g_i⟩)`.
Source: G32 v0.16, Figure 1; Hatcher, §2.1 (edges of a Δ-complex are ordered). -/
def hg_src {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) : hg_Edge G r → hg_Vert g
  | Sum.inl (_, x) => Sum.inl x
  | Sum.inr (Sum.inl (_, x)) => Sum.inl x
  | Sum.inr (Sum.inr (i, x)) => Sum.inr (Sum.inr ⟨i, (x : G ⧸ Subgroup.zpowers (g i))⟩)

example {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (i : Fin r) (x : G) :
    hg_src g (Sum.inl (i, x)) = Sum.inl x := rfl

/-- The terminal vertex of an edge: `e_i(x)` ends at `p_i(x⟨g_i⟩)`; `f_i(x)` and `h_i(x)` end at
`b_∞(x Q_i⁻¹)`.
Source: G32 v0.16, Figure 1; the sheet labels over `b_∞` are read off around `b_∞`. -/
def hg_tgt {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) : hg_Edge G r → hg_Vert g
  | Sum.inl (i, x) => Sum.inr (Sum.inr ⟨i, (x : G ⧸ Subgroup.zpowers (g i))⟩)
  | Sum.inr (Sum.inl (i, x)) => Sum.inr (Sum.inl (x * (hg_Q g i)⁻¹))
  | Sum.inr (Sum.inr (i, x)) => Sum.inr (Sum.inl (x * (hg_Q g i)⁻¹))

example {G : Type*} [Group G] (g : Fin 1 → G) (x : G) :
    hg_tgt g (Sum.inr (Sum.inl (0, x))) = Sum.inr (Sum.inl x) := by
  simp [hg_tgt, hg_Q]

/-- Face `0` of a triangle, the edge `[v₁, v₂]`: `h_i(x)` for `A_i(x)`, and `h_i(x g_i⁻¹)` for
`B_i(x)` (the sheet changes across `h_i`).
Source: G32 v0.16, Figure 1; Hatcher, §2.1 (`∂[v₀, v₁, v₂] = [v₁, v₂] − [v₀, v₂] + [v₀, v₁]`). -/
def hg_face0 {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) : hg_Tri G r → hg_Edge G r
  | Sum.inl (i, x) => Sum.inr (Sum.inr (i, x))
  | Sum.inr (i, x) => Sum.inr (Sum.inr (i, x * (g i)⁻¹))

example {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (i : Fin r) :
    hg_face0 g (Sum.inr (i, g i)) = Sum.inr (Sum.inr (i, 1)) := by
  simp [hg_face0]

/-- Face `1` of a triangle, the edge `[v₀, v₂]`: `f_i(x)` for `A_i(x)`, and `f_{i+1}(x)` for
`B_i(x)`, the index taken mod `r` (`finRotate`).
Source: G32 v0.16, Figure 1; Hatcher, §2.1. -/
def hg_face1 {G : Type*} {r : ℕ} : hg_Tri G r → hg_Edge G r
  | Sum.inl (i, x) => Sum.inr (Sum.inl (i, x))
  | Sum.inr (i, x) => Sum.inr (Sum.inl (finRotate r i, x))

example {G : Type*} (x : G) : hg_face1 (Sum.inr ((1 : Fin 2), x)) = Sum.inr (Sum.inl (0, x)) :=
  rfl

/-- Face `2` of a triangle, the edge `[v₀, v₁]`: `e_i(x)` for both `A_i(x)` and `B_i(x)`.
Source: G32 v0.16, Figure 1; Hatcher, §2.1. -/
def hg_face2 {G : Type*} {r : ℕ} : hg_Tri G r → hg_Edge G r
  | Sum.inl (i, x) => Sum.inl (i, x)
  | Sum.inr (i, x) => Sum.inl (i, x)

example {G : Type*} {r : ℕ} (i : Fin r) (x : G) :
    hg_face2 (Sum.inr (i, x)) = hg_face2 (G := G) (Sum.inl (i, x)) := rfl

/-- The cellular coboundary `δ⁰ : C⁰ → C¹`, `(δ⁰φ)(ε) = φ(tgt ε) − φ(src ε)`, with coefficients in
an `R`-module `M`.
Source: Hatcher, §2.1 and §3.1 (simplicial cochains of a Δ-complex). -/
def hg_delta0 (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    (hg_Vert g → M) →ₗ[R] (hg_Edge G r → M) :=
  LinearMap.funLeft R M (hg_tgt g) - LinearMap.funLeft R M (hg_src g)

example (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    hg_delta0 R R g (fun _ => 1) = 0 := by
  ext ε
  simp [hg_delta0, LinearMap.funLeft]

/-- The cellular coboundary `δ¹ : C¹ → C²`,
`(δ¹c)(τ) = c(face₀ τ) − c(face₁ τ) + c(face₂ τ)`.
Source: Hatcher, §2.1 and §3.1. -/
def hg_delta1 (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    (hg_Edge G r → M) →ₗ[R] (hg_Tri G r → M) :=
  LinearMap.funLeft R M (hg_face0 g) - LinearMap.funLeft R M hg_face1 +
    LinearMap.funLeft R M hg_face2

example (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (c : hg_Edge G r → R) (i : Fin r) (x : G) :
    hg_delta1 R R g c (Sum.inl (i, x)) =
      c (Sum.inr (Sum.inr (i, x))) - c (Sum.inr (Sum.inl (i, x))) + c (Sum.inl (i, x)) := rfl

/-- Cellular `H¹` of the lifted complex with coefficients in a field `K`:
`ker δ¹ / (ker δ¹ ∩ range δ⁰)`.
Source: Hatcher, §3.1 (simplicial cohomology). -/
abbrev hg_H1 (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) : Type _ :=
  LinearMap.ker (hg_delta1 K K g) ⧸
    (LinearMap.range (hg_delta0 K K g)).comap (LinearMap.ker (hg_delta1 K K g)).subtype

example (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    Module K (hg_H1 K g) := inferInstance

/-- The deck action on vertices, by left multiplication on sheet labels and on cosets.
Source: Hatcher, §1.3 (deck transformations of a normal covering). -/
def hg_actVert {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (h : G) :
    hg_Vert g → hg_Vert g
  | Sum.inl x => Sum.inl (h * x)
  | Sum.inr (Sum.inl x) => Sum.inr (Sum.inl (h * x))
  | Sum.inr (Sum.inr ⟨i, c⟩) => Sum.inr (Sum.inr ⟨i, h • c⟩)

example {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (x : G) :
    hg_actVert g 1 (Sum.inl x) = Sum.inl x := by
  simp [hg_actVert]

/-- The deck action on edges, by left multiplication on sheet labels.
Source: Hatcher, §1.3. -/
def hg_actEdge {G : Type*} [Group G] {r : ℕ} (h : G) : hg_Edge G r → hg_Edge G r
  | Sum.inl (i, x) => Sum.inl (i, h * x)
  | Sum.inr (Sum.inl (i, x)) => Sum.inr (Sum.inl (i, h * x))
  | Sum.inr (Sum.inr (i, x)) => Sum.inr (Sum.inr (i, h * x))

example {G : Type*} [Group G] {r : ℕ} (i : Fin r) (h x : G) :
    hg_actEdge h (Sum.inl (i, x)) = Sum.inl (i, h * x) := rfl

/-- The `σ`-equivariant `0`-cochains with values in `ι → K`: `φ(h·v) = σ(h) φ(v)`. They are the
`G`-invariants of `C⁰(X̃; V)` for the diagonal action, i.e. `Hom_G(V^∨, C⁰(X̃; K))`.
Source: Brown, *Cohomology of Groups*, Chapter III, §5 (Shapiro's lemma); Serre, *Linear
Representations of Finite Groups*, §2.6 (isotypic components). -/
def hg_eqCochain0 {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) :
    Submodule K (hg_Vert g → ι → K) where
  carrier := {φ | ∀ h v, φ (hg_actVert g h v) = σ h *ᵥ φ v}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun ha hb h v => by
    simp only [Pi.add_apply, ha h v, hb h v, Matrix.mulVec_add]
  smul_mem' := fun t _ ha h v => by
    simp only [Pi.smul_apply, ha h v, Matrix.mulVec_smul]

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) :
    (0 : hg_Vert g → ι → K) ∈ hg_eqCochain0 σ g := Submodule.zero_mem _

/-- The `σ`-equivariant `1`-cochains with values in `ι → K`: `c(h·ε) = σ(h) c(ε)`.
Source: Brown, Chapter III, §5; Serre, §2.6. -/
def hg_eqCochain1 {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) :
    Submodule K (hg_Edge G r → ι → K) where
  carrier := {c | ∀ h ε, c (hg_actEdge h ε) = σ h *ᵥ c ε}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun ha hb h ε => by
    simp only [Pi.add_apply, ha h ε, hb h ε, Matrix.mulVec_add]
  smul_mem' := fun t _ ha h ε => by
    simp only [Pi.smul_apply, ha h ε, Matrix.mulVec_smul]

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) :
    (0 : hg_Edge G r → ι → K) ∈ hg_eqCochain1 σ := Submodule.zero_mem _

/-- The equivariant `1`-cocycles `C¹_σ ∩ ker δ¹`.
Source: Hatcher, §3.1; Brown, Chapter III, §5. -/
abbrev hg_eqCocycles {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) :
    Submodule K (hg_Edge G r → ι → K) :=
  hg_eqCochain1 σ ⊓ LinearMap.ker (hg_delta1 K (ι → K) g)

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) :
    hg_eqCocycles σ g ≤ hg_eqCochain1 σ := inf_le_left

/-- The coboundaries of equivariant `0`-cochains, `δ⁰(C⁰_σ)`.
Source: Hatcher, §3.1; Brown, Chapter III, §5. -/
abbrev hg_eqCoboundaries {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) :
    Submodule K (hg_Edge G r → ι → K) :=
  (hg_eqCochain0 σ g).map (hg_delta0 K (ι → K) g)

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) :
    (0 : hg_Edge G r → ι → K) ∈ hg_eqCoboundaries σ g := Submodule.zero_mem _

/-- The equivariant cellular cohomology `H¹_σ = (C¹_σ ∩ ker δ¹) / δ⁰(C⁰_σ)` of the lifted
complex, the cellular model of the `σ`-part of `H¹` of the cover.
Source: Brown, Chapter III, §5 (Shapiro's lemma); G32 v0.16, Proposition 6.1 (the Prym part as
the parabolic cohomology of `Hom_G(V, 𝓡 ⊗ K)`). -/
abbrev hg_eqH1 {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) : Type _ :=
  hg_eqCocycles σ g ⧸ (hg_eqCoboundaries σ g).comap (hg_eqCocycles σ g).subtype

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) :
    Module K (hg_eqH1 σ g) := inferInstance

/-- The explicit Shapiro map from parameters `a` (`ParabolicCohomologyDefs`, tuple
`T = pc_tuple σ g`) to `σ`-equivariant `1`-cochains:
`e_i(x) ↦ σ(x) a_i`, `f_i(x) ↦ −σ(x) Q_i⁻¹ F^a_i`, `h_i(x) ↦ −σ(x)(Q_i⁻¹ F^a_i + a_i)`.
The value on `e_i`, the edge from `b₀` to `p_i`, is the parameter `a_i`; the value on the lifted
loop `f_i f_{i+1}⁻¹` from the sheet `1` is `c_i = (1 − T_i) a_i`.
Source: G32 v0.16, Lemma 6.2 (the parameters of a parabolic cocycle); Brown, Chapter III, §5. -/
def hg_shapiroCochain {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) :
    (Fin r → ι → K) →ₗ[K] (hg_Edge G r → ι → K) where
  toFun a
    | Sum.inl (i, x) => σ x *ᵥ a i
    | Sum.inr (Sum.inl (i, x)) => -(σ x *ᵥ (σ (hg_Q g i)⁻¹ *ᵥ pc_F (pc_tuple σ g) a i))
    | Sum.inr (Sum.inr (i, x)) =>
        -(σ x *ᵥ (σ (hg_Q g i)⁻¹ *ᵥ pc_F (pc_tuple σ g) a i + a i))
  map_add' a b := by
    have hF : ∀ i, pc_F (pc_tuple σ g) (a + b) i =
        pc_F (pc_tuple σ g) a i + pc_F (pc_tuple σ g) b i := fun i => by
      simp only [pc_F, pc_c, Pi.add_apply, Matrix.mulVec_add, Finset.sum_add_distrib]
    funext ε
    rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
    · simp only [Pi.add_apply, Matrix.mulVec_add]
    · simp only [hF, Pi.add_apply, Matrix.mulVec_add, neg_add]
    · simp only [hF, Pi.add_apply, Matrix.mulVec_add, neg_add]
      abel
  map_smul' t a := by
    have hF : ∀ i, pc_F (pc_tuple σ g) (t • a) i = t • pc_F (pc_tuple σ g) a i := fun i => by
      simp only [pc_F, pc_c, Pi.smul_apply, Matrix.mulVec_smul, Finset.smul_sum]
    funext ε
    rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
    · simp only [Pi.smul_apply, Matrix.mulVec_smul, RingHom.id_apply]
    · simp only [hF, Pi.smul_apply, Matrix.mulVec_smul, RingHom.id_apply, smul_neg]
    · simp only [hF, Pi.smul_apply, Matrix.mulVec_smul, RingHom.id_apply, smul_neg,
        ← smul_add]

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) (a : Fin r → ι → K)
    (i : Fin r) : hg_shapiroCochain σ g a (Sum.inl (i, 1)) = a i := by
  simp [hg_shapiroCochain]

/-- The explicit Shapiro map lands in the equivariant cochains: `σ(h x) = σ(h) σ(x)`. -/
example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) (a : Fin r → ι → K) :
    hg_shapiroCochain σ g a ∈ hg_eqCochain1 σ := by
  intro h ε
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
    simp [hg_shapiroCochain, hg_actEdge, map_mul, Matrix.mulVec_mulVec, Matrix.mulVec_neg,
      Matrix.mul_assoc]

/-- The cellular cup product of two `1`-cochains with values in `ι → K`, paired by the fibre
form `h(u, v) = star u ⬝ᵥ (H *ᵥ v)` (conjugate-linear in the first slot):
`(α ∪ β)[v₀, v₁, v₂] = h(α[v₀, v₁], β[v₁, v₂])`.
Source: Hatcher, §3.2 (cup product on a Δ-complex); G32 v0.16, proof of Lemma 6.2. -/
def hg_cup {G : Type*} [Group G] {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    {r : ℕ} (g : Fin r → G) (H : Matrix ι ι K) (α β : hg_Edge G r → ι → K) :
    hg_Tri G r → K :=
  fun τ => star (α (hg_face2 τ)) ⬝ᵥ (H *ᵥ β (hg_face0 g τ))

example {G : Type*} [Group G] {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    {r : ℕ} (g : Fin r → G) (H : Matrix ι ι K) (β : hg_Edge G r → ι → K) :
    hg_cup g H 0 β = 0 := by
  funext τ
  simp [hg_cup]

/-- Evaluation of a `2`-cochain on the orientation cycle `Σ_x Σ_i (A_i(x) − B_i(x))` of the lifted
complex (the triangles `A_i` and `B_i` carry opposite orientations of the sphere).
Source: Hatcher, §3.3 (fundamental class); G32 v0.16, Figure 1. -/
def hg_fundEval {G : Type*} [Fintype G] {r : ℕ} {M : Type*} [AddCommGroup M]
    (κ : hg_Tri G r → M) : M :=
  ∑ i, ∑ x, (κ (Sum.inl (i, x)) - κ (Sum.inr (i, x)))

example {G : Type*} [Fintype G] {r : ℕ} : hg_fundEval (fun _ : hg_Tri G r => (1 : ℤ)) = 0 := by
  simp [hg_fundEval]

end HodgeLean.Foundations.Program
