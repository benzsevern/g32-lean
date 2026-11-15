import HodgeLean.Foundations.Program.SchoenTowerN2bOverlapLocalization
import HodgeLean.Foundations.Program.SchoenTowerN2bRationalCoordinates
import HodgeLean.Foundations.Program.SchoenTowerN2bOpenChartFields

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Two nonempty integral open charts of the same integral scheme have nonempty overlap. -/
theorem n2b_openChart_overlap_nonempty {U V X : Scheme.{0}}
    [IsIntegral U] [IsIntegral V] [IsIntegral X]
    (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] :
    Nonempty (pullback i j : Scheme.{0}) := by
  have h : genericPoint U ∈ (pullback.fst i j).opensRange := by
    rw [Scheme.Hom.opensRange_pullbackFst]
    change i (genericPoint U) ∈ Set.range j
    rw [genericPoint_eq_of_isOpenImmersion i]
    exact ⟨genericPoint V, genericPoint_eq_of_isOpenImmersion j⟩
  obtain ⟨x, _⟩ := h
  exact ⟨x⟩

/-- Finitely many actual chart sections become regular on every chart after one positive coordinate power. -/
theorem n2b_uniform_chart_rational_representatives
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {X : Scheme.{0}} [IsIntegral X] (U : ι → Scheme.{0})
    [∀ a, IsIntegral (U a)] [∀ a, IsAffine (U a)]
    (f : ∀ a, U a ⟶ X) [∀ a, IsOpenImmersion (f a)]
    (s : ∀ a b, Γ(U b, ⊤))
    (hs : ∀ a b, (pullback.snd (f a) (f b)).opensRange = (U b).basicOpen (s a b))
    (c : κ → ι) (v : ∀ k, Γ(U (c k), ⊤)) :
    ∃ N : ℕ, 0 < N ∧ ∀ k b, ∃ a : Γ(U b, ⊤),
      n2b_openChartRationalMap (f (c k)) (v k) *
          n2b_openChartRationalMap (f b) (s (c k) b) ^ N =
        n2b_openChartRationalMap (f b) a := by
  let L : κ × ι → Type := fun p => Γ(pullback (f (c p.1)) (f p.2), ⊤)
  letI : ∀ p : κ × ι, Algebra Γ(U p.2, ⊤) (L p) :=
    fun p => (pullback.snd (f (c p.1)) (f p.2)).appTop.hom.toAlgebra
  letI : ∀ p : κ × ι, IsLocalization.Away (s (c p.1) p.2) (L p) := fun p =>
    n2b_sections_isLocalization_of_principal_range
      (pullback.snd (f (c p.1)) (f p.2)) (s (c p.1) p.2) (hs (c p.1) p.2)
  obtain ⟨N, hN⟩ := n2b_common_localization_exponent
    (fun p : κ × ι => Γ(U p.2, ⊤)) L (fun p => s (c p.1) p.2)
    (fun p => (pullback.fst (f (c p.1)) (f p.2)).appTop.hom (v p.1))
  refine ⟨N + 1, Nat.succ_pos N, fun k b => ?_⟩
  let P : Scheme.{0} := pullback (f (c k)) (f b)
  let p := pullback.fst (f (c k)) (f b)
  let q := pullback.snd (f (c k)) (f b)
  letI : Nonempty P := n2b_openChart_overlap_nonempty (f (c k)) (f b)
  letI : IsIntegral P := isIntegral_of_isOpenImmersion q
  obtain ⟨a, ha⟩ := hN (k, b)
  change p.appTop.hom (v k) * q.appTop.hom (s (c k) b) ^ N = q.appTop.hom a at ha
  refine ⟨a * s (c k) b, ?_⟩
  have ha' : p.appTop.hom (v k) * q.appTop.hom (s (c k) b) ^ (N + 1) =
      q.appTop.hom (a * s (c k) b) := by
    rw [pow_succ, ← mul_assoc, ha, map_mul]
  let φ := n2b_openChartRationalMap (q ≫ f b)
  have hv : φ (p.appTop.hom (v k)) = n2b_openChartRationalMap (f (c k)) (v k) := by
    simpa only [φ, p, q, pullback.condition] using
      (n2b_openChartRationalMap_restrict p (f (c k)) (v k))
  have h := congrArg φ ha'
  simp only [map_mul, map_pow, hv] at h
  dsimp only [φ] at h
  simpa only [n2b_openChartRationalMap_restrict, map_mul] using h

end HodgeLean.Foundations.Program
