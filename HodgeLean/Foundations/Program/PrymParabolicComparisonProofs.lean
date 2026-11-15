import HodgeLean.Foundations.Program.PrymParabolicComparisonCount

/-! # Proofs for stage H3a: the lifted Δ-complex of G32 Figure 1

The `_aux` theorems that `PrymParabolicComparison.lean` restates. Their proofs use `PrymParabolicComparisonLemmas` and `PrymParabolicComparisonCount`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Matrix

namespace HodgeLean.Foundations.Program

theorem hg_delta_comp_aux {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (hprod : (List.ofFn g).prod = 1) :
    hg_delta1 R M g ∘ₗ hg_delta0 R M g = 0 :=
  hg_delta_comp_lemma g hprod

theorem hg_H0_finrank_aux (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (hr : 0 < r) (hg : Subgroup.closure (Set.range g) = ⊤) :
    Module.finrank K (LinearMap.ker (hg_delta0 K K g)) = 1 :=
  hg_H0_finrank_lemma K g hr hg

theorem hg_H1_finrank_aux (K : Type*) [Field K] {G : Type*} [Group G] [Finite G] {r : ℕ}
    (g : Fin r → G) (hprod : (List.ofFn g).prod = 1)
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    (Module.finrank K (hg_H1 K g) : ℤ) + 2 * Nat.card G +
        ∑ i, (Nat.card (G ⧸ Subgroup.zpowers (g i)) : ℤ) =
      r * Nat.card G + 2 :=
  hg_H1_finrank_lemma K g hprod hg

theorem hg_shapiro_cocycle_aux {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (a : Fin r → ι → K) (ha : a ∈ pc_Z (pc_tuple σ g)) :
    hg_shapiroCochain σ g a ∈ LinearMap.ker (hg_delta1 K (ι → K) g) :=
  hg_shapiro_cocycle_lemma σ g a ha

theorem hg_shapiro_coboundary_iff_aux {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (a : Fin r → ι → K) :
    hg_shapiroCochain σ g a ∈ hg_eqCoboundaries σ g ↔ a ∈ pc_trivialPart (pc_tuple σ g) :=
  hg_shapiro_coboundary_iff_lemma σ g a

theorem hg_shapiro_surjective_aux {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (c : hg_Edge G r → ι → K) (hc : c ∈ hg_eqCocycles σ g) :
    ∃ a ∈ pc_Z (pc_tuple σ g), c - hg_shapiroCochain σ g a ∈ hg_eqCoboundaries σ g :=
  hg_shapiro_surjective_lemma σ g hprod c hc

theorem hg_eqCoboundary_average_aux {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hG : (Fintype.card G : K) ≠ 0) (c : hg_Edge G r → ι → K) (hc : c ∈ hg_eqCochain1 σ)
    (hcb : c ∈ LinearMap.range (hg_delta0 K (ι → K) g)) :
    c ∈ hg_eqCoboundaries σ g :=
  hg_eqCoboundary_average_lemma σ g hG c hc hcb

theorem hg_fundEval_delta1_aux {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {G : Type*} [Group G] [Fintype G] {r : ℕ} (g : Fin r → G)
    (c : hg_Edge G r → M) :
    hg_fundEval (hg_delta1 R M g c) = 0 :=
  hg_fundEval_delta1_lemma (R := R) g c

theorem hg_cup_shapiro_aux {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (H : Matrix ι ι K) (hHerm : Hᴴ = H) (hinv : ∀ x, (σ x)ᴴ * H * σ x = H)
    (a b : Fin r → ι → K) :
    hg_fundEval (hg_cup g H (hg_shapiroCochain σ g a) (hg_shapiroCochain σ g b)) =
      -((Fintype.card G : K) * star (pc_S (pc_tuple σ g) H b a)) :=
  hg_cup_shapiro_lemma σ g H hHerm hinv a b

end HodgeLean.Foundations.Program
