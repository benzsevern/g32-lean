import HodgeLean.Foundations.Program.SchoenTowerN2bSourceCoordinateFields
import HodgeLean.Foundations.Program.SchoenTowerN2bSourceRegularization

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- Regularization preserves each selected coefficient on its own chart. -/
theorem n2b_regularized_chart_coefficient_self
    {X : Scheme.{0}} [IsIntegral X] {n : ℕ} (ψ : X ⟶ g3c_P n)
    {ι κ : Type} (idx : ι → Fin (n + 1))
    [∀ b, Nonempty (n2b_pullbackChart ψ (idx b))]
    (c : κ → ι) (z : ∀ k, Γ(n2b_pullbackChart ψ (idx (c k)), ⊤))
    (N : ℕ) (a : ∀ k b, Γ(n2b_pullbackChart ψ (idx b), ⊤))
    (ha : ∀ k b,
      n2b_openChartRationalMap (n2b_pullbackChartι ψ (idx (c k))) (z k) *
          n2b_pullbackRationalCoord ψ (idx (c k)) (idx b) ^ N =
        n2b_openChartRationalMap (n2b_pullbackChartι ψ (idx b)) (a k b))
    (k : κ) : a k (c k) = z k := by
  apply n2b_openChartRationalMap_injective (n2b_pullbackChartι ψ (idx (c k)))
  have h := ha k (c k)
  rw [n2b_pullbackRationalCoord_self, one_pow, mul_one] at h
  exact h.symm

/-- A pure regularized coefficient is the corresponding normalized coordinate power. -/
theorem n2b_regularized_pure_coefficient
    {X : Scheme.{0}} [IsIntegral X] {n : ℕ} (ψ : X ⟶ g3c_P n)
    (i j : Fin (n + 1)) [Nonempty (n2b_pullbackChart ψ i)]
    [Nonempty (n2b_pullbackChart ψ j)] (N : ℕ)
    (a : Γ(n2b_pullbackChart ψ j, ⊤))
    (ha : n2b_openChartRationalMap (n2b_pullbackChartι ψ i) 1 *
      n2b_pullbackRationalCoord ψ i j ^ N =
        n2b_openChartRationalMap (n2b_pullbackChartι ψ j) a) :
    a = n2b_pullbackChartCoord ψ j i ^ N := by
  apply n2b_openChartRationalMap_injective (n2b_pullbackChartι ψ j)
  rw [map_pow]
  simpa only [map_one, one_mul, n2b_pullbackRationalCoord] using ha.symm

/-- The regularized actual chart coefficients obey the required homogeneous transition equation. -/
theorem n2b_regularized_chart_coefficients_transition
    {X : Scheme.{0}} [IsIntegral X] {n : ℕ} (ψ : X ⟶ g3c_P n)
    {ι κ : Type} (idx : ι → Fin (n + 1))
    [∀ b, Nonempty (n2b_pullbackChart ψ (idx b))]
    (c : κ → ι) (z : ∀ k, Γ(n2b_pullbackChart ψ (idx (c k)), ⊤))
    (N : ℕ) (a : ∀ k b, Γ(n2b_pullbackChart ψ (idx b), ⊤))
    (ha : ∀ k b,
      n2b_openChartRationalMap (n2b_pullbackChartι ψ (idx (c k))) (z k) *
          n2b_pullbackRationalCoord ψ (idx (c k)) (idx b) ^ N =
        n2b_openChartRationalMap (n2b_pullbackChartι ψ (idx b)) (a k b))
    (k : κ) (i j : ι) :
    (pullback.snd (n2b_pullbackChartι ψ (idx i))
        (n2b_pullbackChartι ψ (idx j))).appTop.hom (a k j) =
      (pullback.snd (n2b_pullbackChartι ψ (idx i))
          (n2b_pullbackChartι ψ (idx j))).appTop.hom
            (n2b_pullbackChartCoord ψ (idx j) (idx i)) ^ N *
        (pullback.fst (n2b_pullbackChartι ψ (idx i))
          (n2b_pullbackChartι ψ (idx j))).appTop.hom (a k i) := by
  let p := pullback.fst (n2b_pullbackChartι ψ (idx i)) (n2b_pullbackChartι ψ (idx j))
  let q := pullback.snd (n2b_pullbackChartι ψ (idx i)) (n2b_pullbackChartι ψ (idx j))
  let P : Scheme.{0} := pullback (n2b_pullbackChartι ψ (idx i))
    (n2b_pullbackChartι ψ (idx j))
  letI : Nonempty P := n2b_openChart_overlap_nonempty
    (n2b_pullbackChartι ψ (idx i)) (n2b_pullbackChartι ψ (idx j))
  letI : IsIntegral P := isIntegral_of_isOpenImmersion q
  let φ := n2b_openChartRationalMap (q ≫ n2b_pullbackChartι ψ (idx j))
  have hp : φ (p.appTop.hom (a k i)) =
      n2b_openChartRationalMap (n2b_pullbackChartι ψ (idx i)) (a k i) := by
    simpa only [φ, p, q, pullback.condition] using
      (n2b_openChartRationalMap_restrict p (n2b_pullbackChartι ψ (idx i)) (a k i))
  have hq (v : Γ(n2b_pullbackChart ψ (idx j), ⊤)) :
      φ (q.appTop.hom v) =
        n2b_openChartRationalMap (n2b_pullbackChartι ψ (idx j)) v :=
    n2b_openChartRationalMap_restrict q (n2b_pullbackChartι ψ (idx j)) v
  apply n2b_openChartRationalMap_injective (q ≫ n2b_pullbackChartι ψ (idx j))
  change φ (q.appTop.hom (a k j)) =
    φ (q.appTop.hom (n2b_pullbackChartCoord ψ (idx j) (idx i)) ^ N * p.appTop.hom (a k i))
  rw [map_mul, map_pow, hq, hq, hp]
  change _ = n2b_pullbackRationalCoord ψ (idx i) (idx j) ^ N * _
  rw [← ha k j, ← ha k i,
    n2b_pullbackRationalCoord_transition ψ (idx i) (idx j) (idx (c k)), mul_pow]
  ring

/-- Regularized coordinates differ by a single unit on each actual overlap. -/
theorem n2b_regularized_chart_unit_transition
    {X : Scheme.{0}} [IsIntegral X] {n : ℕ} (ψ : X ⟶ g3c_P n)
    {ι κ : Type} (idx : ι → Fin (n + 1))
    [∀ b, Nonempty (n2b_pullbackChart ψ (idx b))]
    (c : κ → ι) (z : ∀ k, Γ(n2b_pullbackChart ψ (idx (c k)), ⊤))
    (N : ℕ) (a : ∀ k b, Γ(n2b_pullbackChart ψ (idx b), ⊤))
    (ha : ∀ k b,
      n2b_openChartRationalMap (n2b_pullbackChartι ψ (idx (c k))) (z k) *
          n2b_pullbackRationalCoord ψ (idx (c k)) (idx b) ^ N =
        n2b_openChartRationalMap (n2b_pullbackChartι ψ (idx b)) (a k b))
    (i j : ι) :
    ∃ u : Γ(pullback (n2b_pullbackChartι ψ (idx i))
        (n2b_pullbackChartι ψ (idx j)), ⊤)ˣ,
      ∀ k, (pullback.snd (n2b_pullbackChartι ψ (idx i))
          (n2b_pullbackChartι ψ (idx j))).appTop.hom (a k j) =
        (u : Γ(pullback (n2b_pullbackChartι ψ (idx i))
          (n2b_pullbackChartι ψ (idx j)), ⊤)) *
        (pullback.fst (n2b_pullbackChartι ψ (idx i))
          (n2b_pullbackChartι ψ (idx j))).appTop.hom (a k i) := by
  let u := (n2b_pullbackChart_overlap_coordinate_isUnit ψ (idx i) (idx j)).unit ^ N
  refine ⟨u, fun k => ?_⟩
  simpa only [u, Units.val_pow_eq_pow_val, IsUnit.unit_spec] using
    n2b_regularized_chart_coefficients_transition ψ idx c z N a ha k i j

end HodgeLean.Foundations.Program
