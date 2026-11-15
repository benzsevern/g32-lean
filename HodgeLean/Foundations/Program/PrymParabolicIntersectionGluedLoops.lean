import HodgeLean.Foundations.Program.PrymParabolicIntersectionPathChains
import HodgeLean.Foundations.Program.CurveJacobianRest2Shift
import HodgeLean.Foundations.Program.CurveJacobianRestPoly

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Program

attribute [local instance] b3Forms_isManifold_real

/-- A cyclic family of good paths: `N`-periodic paths `γ k` from `z k` to `z (k + 1)`, each `C¹`
and constant near `0` and near `1`.
Source: B3's good paths (`b3A_IsGoodPath`) glued along the integers, as in
`b3Rest_floorPath_contMDiff`. -/
structure hga_Pieces (T : Type) [TopologicalSpace T] [ChartedSpace ℂ T] where
  N : ℕ
  pos : 0 < N
  γ : ℤ → ℝ → T
  z : ℤ → T
  γ_add : ∀ k, γ (k + N) = γ k
  z_add : ∀ k, z (k + N) = z k
  good : ∀ k, b3A_IsGoodPath (E := ℂ) (γ k) (z k) (z (k + 1))

namespace hga_Pieces

variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) ω T]
variable (A : hga_Pieces T)

/-- The loop `t ↦ γ ⌊N t⌋ (fract (N t))` of a cyclic family of good paths.
Source: `b3Rest_floorPath_contMDiff`. -/
def loop (t : ℝ) : T := A.γ ⌊(A.N : ℝ) * t⌋ (Int.fract ((A.N : ℝ) * t))

theorem loop_periodic : Function.Periodic A.loop 1 := by
  intro t
  simp only [loop, mul_add, mul_one]
  rw [Int.floor_add_natCast, Int.fract_add_natCast, A.γ_add]

theorem loop_contMDiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 A.loop := by
  have h := b3Rest_floorPath_contMDiff (E := ℂ) A.γ A.z A.good
  exact h.comp ((contDiff_const.mul contDiff_id).contMDiff)

/-- The glued loop as a `C¹` loop.
Source: `b3Rest_floorPath_contMDiff`. -/
def smoothLoop : b3_SmoothLoop ℂ T := ⟨A.loop, A.loop_periodic, A.loop_contMDiff⟩

theorem N_pos : (0 : ℝ) < A.N := Nat.cast_pos.2 A.pos

theorem loop_apply (k : ℤ) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) :
    A.loop ((k + σ) / A.N) = A.γ k σ := by
  have hN : (A.N : ℝ) ≠ 0 := A.N_pos.ne'
  have e : (A.N : ℝ) * ((k + σ) / A.N) = k + σ := by field_simp
  show A.γ ⌊(A.N : ℝ) * ((k + σ) / A.N)⌋ (Int.fract ((A.N : ℝ) * ((k + σ) / A.N))) = _
  rw [e]
  rcases hσ.2.lt_or_eq with h1 | h1
  · have hfl : ⌊(k : ℝ) + σ⌋ = k := by
      rw [Int.floor_eq_iff]; constructor <;> linarith [hσ.1]
    rw [Int.fract, hfl]
    congr 1
    ring
  · subst h1
    have hc : (k : ℝ) + 1 = ((k + 1 : ℤ) : ℝ) := by push_cast; ring
    rw [hc, Int.floor_intCast, Int.fract_intCast, (A.good (k + 1)).apply_zero,
      (A.good k).apply_one]

theorem loop_eq_floor (s : ℝ) :
    A.loop s = A.γ ⌊(A.N : ℝ) * s⌋ (Int.fract ((A.N : ℝ) * s)) := rfl

theorem floor_mem {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    0 ≤ ⌊(A.N : ℝ) * s⌋ ∧ ⌊(A.N : ℝ) * s⌋ < A.N := by
  have hN := A.N_pos
  constructor
  · exact Int.floor_nonneg.mpr (mul_nonneg hN.le hs.1)
  · rw [Int.floor_lt]
    push_cast
    nlinarith [hs.2]

theorem eq_floor_fract (s : ℝ) :
    s = (⌊(A.N : ℝ) * s⌋ + Int.fract ((A.N : ℝ) * s)) / A.N := by
  rw [Int.floor_add_fract]
  field_simp [A.N_pos.ne']

theorem velocity_apply (k : ℤ) {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    b3_velocity ℂ T A.loop ((k + σ) / A.N) = (A.N : ℝ) • b3_velocity ℂ T (A.γ k) σ := by
  have hN := A.N_pos
  have heq : A.loop =ᶠ[𝓝 (((k : ℝ) + σ) / A.N)]
      (A.γ k) ∘ (fun s ↦ (A.N : ℝ) * s + (-(k : ℝ))) := by
    have hlo : (k : ℝ) / A.N < ((k : ℝ) + σ) / A.N := by
      rw [div_lt_div_iff_of_pos_right hN]; linarith [hσ.1]
    have hhi : ((k : ℝ) + σ) / A.N < ((k : ℝ) + 1) / A.N := by
      rw [div_lt_div_iff_of_pos_right hN]; linarith [hσ.2]
    filter_upwards [Ioo_mem_nhds hlo hhi] with s hs
    have h1 : (k : ℝ) < A.N * s := by
      have := hs.1; rw [div_lt_iff₀ hN] at this; linarith
    have h2 : (A.N : ℝ) * s < k + 1 := by
      have := hs.2; rw [lt_div_iff₀ hN] at this; linarith
    have hfl : ⌊(A.N : ℝ) * s⌋ = k := by rw [Int.floor_eq_iff]; exact ⟨h1.le, h2⟩
    simp only [loop, Function.comp_apply, hfl, Int.fract]
    congr 1
  rw [b3Forms_velocity_eq_b3, b3Forms_velocity_eq_b3, b3Forms_velocity_congr heq,
    b3Forms_velocity_comp_affine (A.good k).1]
  congr 2
  field_simp
  ring

theorem velocity_periodic (s : ℝ) :
    b3_velocity ℂ T A.loop s = b3_velocity ℂ T A.loop (Int.fract s) := by
  have h := b3Rest2_velocity_add_int (E := ℂ) A.loop_contMDiff A.loop_periodic (Int.fract s) ⌊s⌋
  rw [b3Forms_velocity_eq_b3, b3Forms_velocity_eq_b3, ← h, Int.fract_add_floor]

end hga_Pieces

theorem hga_orient_smul_real (a b : ℝ) (v w : ℂ) :
    b3_orient ℂ (a • v) (b • w) = a * b * b3_orient ℂ v w := by
  obtain ⟨κ, -, hκ⟩ := b6m_orient_complex_coordinates
  rw [hκ, hκ]
  simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) ω T]

/-- A continuous map `ℝ → T` restricted to `[0, 1]`.
Source: Mathlib `unitInterval`, `ContinuousMap.comp`. -/
def hga_unitPath {T : Type} [TopologicalSpace T] (g : ℝ → T) (hg : Continuous g) :
    C(unitInterval, T) :=
  ⟨fun t ↦ g t, hg.comp continuous_subtype_val⟩

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters in
/-- The chain quotient value of the class of a `C¹` loop is the path chain of one period. -/
theorem hga_loopClass_chain (γ : b3_SmoothLoop ℂ T)
    (j : b6m_H1 T →ₗ[ℤ] b6m_chainQuotient (TopCat.toSSet.obj (TopCat.of T)))
    (hj : ∀ z : LinearMap.ker ((SingularChainComplex ℤ (TopCat.of T)).sc 1).g.hom,
      j (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass z) =
        b6m_chainQuotientMap _ z.1) :
    j (b6m_loopClass T γ) = b6m_pathChain (hga_unitPath γ.1 γ.2.2.continuous) := by
  unfold b6m_loopClass
  rw [hj]
  let p : C(UnitAddCircle, T) := ⟨γ.2.1.lift, by
    rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact γ.2.2.continuous⟩
  change b6m_chainQuotientMap _ (Simplicial.chainOfSimplex ℤ (loopSimplex p)) = _
  rw [← b3Rest2_pathSimplex_simplexPath (loopSimplex p), spec_simplexPath_loopSimplex]
  unfold b6m_pathChain
  congr 3

/-- The grid point `k / N` of `[0, 1]` (projected into `[0, 1]`).
Source: Mathlib `Set.projIcc`. -/
def hga_gridPt (N k : ℕ) : unitInterval := Set.projIcc 0 1 zero_le_one ((k : ℝ) / N)

theorem hga_gridPt_val {N k : ℕ} (hk : k ≤ N) : (hga_gridPt N k : ℝ) = k / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : k = 0 := by omega
    subst this
    simp [hga_gridPt]
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [hga_gridPt, Set.projIcc_of_mem]
  constructor
  · positivity
  · rw [div_le_one hN']; exact_mod_cast hk

theorem hga_pathChain_subdivide {X : Type} [TopologicalSpace X] (g : C(unitInterval, X))
    (N : ℕ) (hN : 0 < N) :
    b6m_pathChain g = ∑ k ∈ Finset.range N,
      b6m_pathChain (b3Rest2_restr g (hga_gridPt N k) (hga_gridPt N (k + 1))) := by
  have key : ∀ m, m ≤ N → b6m_pathChain (b3Rest2_restr g 0 (hga_gridPt N m)) =
      ∑ k ∈ Finset.range m,
        b6m_pathChain (b3Rest2_restr g (hga_gridPt N k) (hga_gridPt N (k + 1))) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : hga_gridPt N 0 = 0 := Subtype.ext (by rw [hga_gridPt_val (Nat.zero_le _)]; simp)
      have e : b3Rest2_restr g 0 0 = ContinuousMap.const unitInterval (g 0) := by
        ext t
        simp [b3Rest2_restr, b3Rest2_affI]
      rw [h0, e, b6m_pathChain_const, Finset.sum_range_zero]
    | succ m ih =>
      intro hm
      have h0 : hga_gridPt N 0 = 0 := Subtype.ext (by rw [hga_gridPt_val (Nat.zero_le _)]; simp)
      rw [Finset.sum_range_succ, ← ih (by omega), b6m_pathChain_subdiv g 0 (hga_gridPt N m)
        (hga_gridPt N (m + 1))]
  have h1 : hga_gridPt N N = 1 := Subtype.ext (by
    rw [hga_gridPt_val le_rfl]
    simp [(Nat.cast_pos.2 hN).ne'])
  rw [← key N le_rfl, h1, b3Rest2_restr_zero_one]

namespace hga_Pieces

/-- The `k`-th piece of a cyclic family on `[0, 1]`. -/
def piece (A : hga_Pieces T) (k : ℤ) : C(unitInterval, T) :=
  hga_unitPath (A.γ k) (A.good k).1.continuous

theorem pathChain_loop (A : hga_Pieces T) :
    b6m_pathChain (hga_unitPath A.loop A.loop_contMDiff.continuous) =
      ∑ k ∈ Finset.range A.N, b6m_pathChain (A.piece k) := by
  rw [hga_pathChain_subdivide _ A.N A.pos]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < A.N := Finset.mem_range.mp hk
  apply hga_pathChain_congr
  intro t
  have hN := A.N_pos
  simp only [b3Rest2_restr_apply, b3Rest2_affI, hga_unitPath, piece, ContinuousMap.coe_mk]
  rw [hga_gridPt_val hk'.le, hga_gridPt_val hk']
  have e : (k : ℝ) / A.N + (t : ℝ) * (((k : ℝ) + 1) / A.N - (k : ℝ) / A.N) =
      (((k : ℤ) : ℝ) + t) / A.N := by
    push_cast
    field_simp
    ring
  rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring, e]
  exact A.loop_apply (k : ℤ) ⟨t.2.1, t.2.2⟩

end hga_Pieces

/-- **Crossings of glued loops.** If two pieces of the glued loops meet only for the index pairs
in `S`, each pair at one pair of interior parameters with independent velocities, the loops are
transverse and their intersection number is the sum of the signs over `S`. -/
theorem hga_glued_crossing (A B : hga_Pieces T) (S : Finset (ℤ × ℤ)) (σ θ : ℤ × ℤ → ℝ)
    (hS : ∀ p ∈ S, (0 ≤ p.1 ∧ p.1 < A.N) ∧ (0 ≤ p.2 ∧ p.2 < B.N))
    (hcross : ∀ p ∈ S, σ p ∈ Ioo (0 : ℝ) 1 ∧ θ p ∈ Ioo (0 : ℝ) 1 ∧
      A.γ p.1 (σ p) = B.γ p.2 (θ p) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, A.γ p.1 s = B.γ p.2 t → s = σ p ∧ t = θ p) ∧
      b3_orient ℂ (b3_velocity ℂ T (A.γ p.1) (σ p)) (b3_velocity ℂ T (B.γ p.2) (θ p)) ≠ 0)
    (hdisj : ∀ k l : ℤ, 0 ≤ k → k < A.N → 0 ≤ l → l < B.N → (k, l) ∉ S →
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, A.γ k s ≠ B.γ l t) :
    b3_Transverse ℂ A.smoothLoop B.smoothLoop ∧
      b3_intersection ℂ A.smoothLoop B.smoothLoop =
        ∑ p ∈ S, ((SignType.sign (b3_orient ℂ (b3_velocity ℂ T (A.γ p.1) (σ p))
          (b3_velocity ℂ T (B.γ p.2) (θ p))) : SignType) : ℤ) := by
  classical
  let f : ℤ × ℤ → ℝ × ℝ := fun p ↦ ((p.1 + σ p) / A.N, (p.2 + θ p) / B.N)
  have hfrac : ∀ (P : hga_Pieces T) (k : ℤ) (x : ℝ), x ∈ Ioo (0 : ℝ) 1 →
      ⌊(P.N : ℝ) * ((k + x) / P.N)⌋ = k ∧ Int.fract ((P.N : ℝ) * ((k + x) / P.N)) = x := by
    intro P k x hx
    have e : (P.N : ℝ) * ((k + x) / P.N) = k + x := by field_simp [P.N_pos.ne']
    have hfl : ⌊(k : ℝ) + x⌋ = k := by
      rw [Int.floor_eq_iff]; constructor <;> linarith [hx.1, hx.2]
    rw [e, Int.fract, hfl]
    exact ⟨rfl, by ring⟩
  -- every common point of the loops at parameters in `[0, 1)` is an image point
  have hchar : ∀ s t : ℝ, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      A.loop s = B.loop t → ∃ p ∈ S, f p = (s, t) := by
    intro s t hs ht hst
    set k := ⌊(A.N : ℝ) * s⌋
    set l := ⌊(B.N : ℝ) * t⌋
    have hk := A.floor_mem hs
    have hl := B.floor_mem ht
    have hσ' : Int.fract ((A.N : ℝ) * s) ∈ Icc (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    have hθ' : Int.fract ((B.N : ℝ) * t) ∈ Icc (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    rw [A.loop_eq_floor, B.loop_eq_floor] at hst
    by_cases hp : (k, l) ∈ S
    · obtain ⟨-, -, -, huniq, -⟩ := hcross (k, l) hp
      obtain ⟨h1, h2⟩ := huniq _ hσ' _ hθ' hst
      refine ⟨(k, l), hp, ?_⟩
      simp only [f]
      rw [← h1, ← h2, ← A.eq_floor_fract, ← B.eq_floor_fract]
    · exact absurd hst (hdisj k l hk.1 hk.2 hl.1 hl.2 hp _ hσ' _ hθ')
  have hf_mem : ∀ p ∈ S, f p ∈ b3_crossings ℂ A.smoothLoop B.smoothLoop := by
    intro p hp
    obtain ⟨hσ, hθ, heq, -, -⟩ := hcross p hp
    obtain ⟨⟨hk0, hk1⟩, ⟨hl0, hl1⟩⟩ := hS p hp
    have hN := A.N_pos
    have hM := B.N_pos
    have hk0' : (0 : ℝ) ≤ p.1 := by exact_mod_cast hk0
    have hl0' : (0 : ℝ) ≤ p.2 := by exact_mod_cast hl0
    refine ⟨⟨div_nonneg (by linarith [hσ.1]) hN.le, ?_⟩,
      ⟨div_nonneg (by linarith [hθ.1]) hM.le, ?_⟩, ?_⟩
    · show ((p.1 : ℝ) + σ p) / A.N < 1
      rw [div_lt_one hN]
      have : (p.1 : ℝ) + 1 ≤ A.N := by exact_mod_cast hk1
      linarith [hσ.2]
    · show ((p.2 : ℝ) + θ p) / B.N < 1
      rw [div_lt_one hM]
      have : (p.2 : ℝ) + 1 ≤ B.N := by exact_mod_cast hl1
      linarith [hθ.2]
    · change A.loop ((p.1 + σ p) / A.N) = B.loop ((p.2 + θ p) / B.N)
      rw [A.loop_apply p.1 (Ioo_subset_Icc_self hσ), B.loop_apply p.2 (Ioo_subset_Icc_self hθ)]
      exact heq
  have hset : b3_crossings ℂ A.smoothLoop B.smoothLoop = f '' (S : Set (ℤ × ℤ)) := by
    ext x
    constructor
    · rintro ⟨hs, ht, hst⟩
      obtain ⟨p, hp, hpx⟩ := hchar x.1 x.2 hs ht hst
      exact ⟨p, hp, hpx⟩
    · rintro ⟨p, hp, rfl⟩
      exact hf_mem p hp
  have hinj : Set.InjOn f (S : Set (ℤ × ℤ)) := by
    intro p hp q hq hpq
    obtain ⟨hσp, hθp, -⟩ := hcross p hp
    obtain ⟨hσq, hθq, -⟩ := hcross q hq
    have h1 := congrArg (fun x : ℝ × ℝ ↦ ⌊(A.N : ℝ) * x.1⌋) hpq
    have h2 := congrArg (fun x : ℝ × ℝ ↦ ⌊(B.N : ℝ) * x.2⌋) hpq
    simp only [f] at h1 h2
    rw [(hfrac A p.1 _ hσp).1, (hfrac A q.1 _ hσq).1] at h1
    rw [(hfrac B p.2 _ hθp).1, (hfrac B q.2 _ hθq).1] at h2
    exact Prod.ext h1 h2
  have hvel : ∀ p ∈ S,
      b3_orient ℂ (b3_velocity ℂ T A.loop (f p).1) (b3_velocity ℂ T B.loop (f p).2) =
        (A.N : ℝ) * B.N * b3_orient ℂ (b3_velocity ℂ T (A.γ p.1) (σ p))
          (b3_velocity ℂ T (B.γ p.2) (θ p)) := by
    intro p hp
    obtain ⟨hσ, hθ, -⟩ := hcross p hp
    simp only [f]
    rw [A.velocity_apply p.1 hσ, B.velocity_apply p.2 hθ]
    exact hga_orient_smul_real _ _ _ _
  refine ⟨?_, ?_⟩
  · intro s t hst
    change A.loop s = B.loop t at hst
    have e1 := (A.loop_periodic.int_mul ⌊s⌋) (Int.fract s)
    have e2 := (B.loop_periodic.int_mul ⌊t⌋) (Int.fract t)
    simp only [mul_one, Int.fract_add_floor] at e1 e2
    have hs' : A.loop (Int.fract s) = B.loop (Int.fract t) := by rw [← e1, ← e2]; exact hst
    obtain ⟨p, hp, hpx⟩ := hchar _ _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩ hs'
    change b3_orient ℂ (b3_velocity ℂ T A.loop s) (b3_velocity ℂ T B.loop t) ≠ 0
    rw [A.velocity_periodic s, B.velocity_periodic t]
    have h1 : Int.fract s = (f p).1 := by rw [hpx]
    have h2 : Int.fract t = (f p).2 := by rw [hpx]
    rw [h1, h2, hvel p hp]
    have := A.N_pos
    have := B.N_pos
    exact mul_ne_zero (by positivity) (hcross p hp).2.2.2.2
  · unfold b3_intersection
    rw [hset, finsum_mem_image hinj, finsum_mem_coe_finset]
    apply Finset.sum_congr rfl
    intro p hp
    change ((SignType.sign (b3_orient ℂ (b3_velocity ℂ T A.loop (f p).1)
      (b3_velocity ℂ T B.loop (f p).2)) : SignType) : ℤ) = _
    rw [hvel p hp, sign_mul, sign_pos (by have := A.N_pos; have := B.N_pos; positivity), one_mul]

#print axioms hga_glued_crossing
#print axioms hga_Pieces.pathChain_loop
#print axioms hga_Pieces.piece
#print axioms hga_pathChain_subdivide
#print axioms hga_gridPt_val
#print axioms hga_gridPt
#print axioms hga_loopClass_chain
#print axioms hga_unitPath
#print axioms hga_orient_smul_real
#print axioms hga_Pieces.velocity_periodic
#print axioms hga_Pieces.velocity_apply
#print axioms hga_Pieces.loop_apply
#print axioms hga_Pieces.smoothLoop
#print axioms hga_Pieces.loop_contMDiff
#print axioms hga_Pieces.loop_periodic
#print axioms hga_Pieces.loop
#print axioms hga_Pieces
end HodgeLean.Foundations.Program
