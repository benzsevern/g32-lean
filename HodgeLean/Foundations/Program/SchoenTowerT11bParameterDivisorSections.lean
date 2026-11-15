import HodgeLean.Foundations.Program.SchoenTowerT11bCoefficientRootBounds
import HodgeLean.Foundations.Program.SchoenTowerT11bDivisorSections
import HodgeLean.Foundations.Program.SchoenTowerT11bRadicalZeros

/-! Divisor and atom compatibility over connected parameter spaces.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open Filter
open scoped Topology

/-- A continuously varying coefficient homomorphism gives continuous polynomial values along each continuous section.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, parameter sign-compatibility step. -/
theorem s2v_t11b_ringHom_family_section_continuous {A X : Type*}
    [CommRing A] [TopologicalSpace X] (φ : X → A →+* ℝ)
    (hφ : ∀ c, Continuous (fun t => φ t c)) (P : Polynomial A)
    (ψ : X → ℝ) (hψ : Continuous ψ) :
    Continuous (fun t => P.eval₂ (φ t) (ψ t)) := by
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply continuous_finsetSum
  intro i hi
  exact (hφ (P.coeff i)).mul (hψ.pow i)

/-- A divisor vanishing once on a connected simple-root section vanishes along the whole section.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, factor-continuation step. -/
theorem s2v_t11b_parameter_divisor_root_continuation {A X : Type*}
    [CommRing A] [TopologicalSpace X] [PreconnectedSpace X]
    (φ : X → A →+* ℝ) (hφ : ∀ c, Continuous (fun t => φ t c))
    (P D : Polynomial A) (hdiv : D ∣ P) (ψ : X → ℝ) (hψ : Continuous ψ)
    (hroot : ∀ t : X, P.eval₂ (φ t) (ψ t) = 0)
    (hsimple : ∀ t : X,
      (P.map (φ t)).derivative.eval (ψ t) ≠ 0)
    (a : X) (ha : D.eval₂ (φ a) (ψ a) = 0) :
    ∀ t : X, D.eval₂ (φ t) (ψ t) = 0 := by
  obtain ⟨G, hPG⟩ := hdiv
  let d : X → ℝ := fun t => D.eval₂ (φ t) (ψ t)
  let e : X → ℝ := fun t => G.eval₂ (φ t) (ψ t)
  have hd : Continuous d := s2v_t11b_ringHom_family_section_continuous φ hφ D ψ hψ
  have he : Continuous e := s2v_t11b_ringHom_family_section_continuous φ hφ G ψ hψ
  have hcofactor : ∀ t : X, d t = 0 → e t ≠ 0 := by
    intro t ht hez
    apply hsimple t
    have hz : P.derivative.eval₂ (φ t) (ψ t) = 0 := by
      rw [hPG, Polynomial.derivative_mul, Polynomial.eval₂_add,
        Polynomial.eval₂_mul, Polynomial.eval₂_mul]
      change _ * e t + d t * _ = 0
      rw [ht, hez, mul_zero, zero_mul, zero_add]
    simpa only [Polynomial.eval₂_eq_eval_map, Polynomial.derivative_map] using hz
  let L : Set X := {t | d t = 0}
  have hclosed : IsClosed L := isClosed_eq hd continuous_const
  have hopen : IsOpen L := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hn : ∀ᶠ u in 𝓝 t, e u ≠ 0 :=
      (he.continuousAt.ne_iff_eventually_ne continuousAt_const).mp (hcofactor t ht)
    filter_upwards [hn] with u hu
    have hz : d u * e u = 0 := by
      simpa only [hPG, Polynomial.eval₂_mul] using hroot u
    exact (mul_eq_zero.mp hz).resolve_right hu
  have hL : L = Set.univ := (show IsClopen L from ⟨hclosed, hopen⟩).eq_univ ⟨a, ha⟩
  intro t
  change t ∈ L
  rw [hL]
  exact Set.mem_univ t

/-- Every nonzero divisor of a carrier has constant vanishing along a connected simple-root section of its radical.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, radical atom-compatibility step. -/
theorem s2v_t11b_parameter_radical_atom_zero_iff {A X : Type*}
    [CommRing A] [IsDomain A] [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)] [TopologicalSpace X] [PreconnectedSpace X]
    (φ : X → A →+* ℝ) (hφ : ∀ c, Continuous (fun t => φ t c))
    (P Q : Polynomial A) (hP : P ≠ 0) (hQ : Q ≠ 0) (hdiv : Q ∣ P)
    (ψ : X → ℝ) (hψ : Continuous ψ)
    (hroot : ∀ t, (UniqueFactorizationMonoid.radical P).eval₂ (φ t) (ψ t) = 0)
    (hsimple : ∀ t, ((UniqueFactorizationMonoid.radical P).map (φ t)).derivative.eval (ψ t) ≠ 0)
    (a b : X) : Q.eval₂ (φ a) (ψ a) = 0 ↔ Q.eval₂ (φ b) (ψ b) = 0 := by
  have hzero : ∀ a : X, Q.eval₂ (φ a) (ψ a) = 0 → ∀ b : X, Q.eval₂ (φ b) (ψ b) = 0 := by
    intro a ha
    have hDa : (UniqueFactorizationMonoid.radical Q).eval₂ (φ a) (ψ a) = 0 :=
      (s2v_t11b_radical_map_zero_iff (Polynomial.eval₂RingHom (φ a) (ψ a)) Q hQ).mpr ha
    have hc := s2v_t11b_parameter_divisor_root_continuation φ hφ
      (UniqueFactorizationMonoid.radical P) (UniqueFactorizationMonoid.radical Q)
      (UniqueFactorizationMonoid.radical_dvd_radical hdiv hP) ψ hψ hroot hsimple a hDa
    intro b
    exact (s2v_t11b_radical_map_zero_iff (Polynomial.eval₂RingHom (φ b) (ψ b)) Q hQ).mp (hc b)
  exact ⟨fun h => hzero a h b, fun h => hzero b h a⟩

/-- A nonzero divisor of the carrier has constant sign along each connected simple-root section of the radical.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, radical atom sign-compatibility step. -/
theorem s2v_t11b_parameter_radical_atom_sign {A X : Type*}
    [CommRing A] [IsDomain A] [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)] [TopologicalSpace X] [PreconnectedSpace X]
    (φ : X → A →+* ℝ) (hφ : ∀ c, Continuous (fun t => φ t c))
    (P Q : Polynomial A) (hP : P ≠ 0) (hQ : Q ≠ 0) (hdiv : Q ∣ P)
    (ψ : X → ℝ) (hψ : Continuous ψ)
    (hroot : ∀ t, (UniqueFactorizationMonoid.radical P).eval₂ (φ t) (ψ t) = 0)
    (hsimple : ∀ t, ((UniqueFactorizationMonoid.radical P).map (φ t)).derivative.eval (ψ t) ≠ 0)
    (a b : X) : 0 ≤ Q.eval₂ (φ a) (ψ a) ↔ 0 ≤ Q.eval₂ (φ b) (ψ b) := by
  have hz := s2v_t11b_parameter_radical_atom_zero_iff φ hφ P Q hP hQ hdiv ψ hψ hroot hsimple
  by_cases ha : Q.eval₂ (φ a) (ψ a) = 0
  · rw [ha, (hz a b).mp ha]
  · let g : X → ℝ := fun t => Q.eval₂ (φ t) (ψ t)
    have hg : Continuous g := s2v_t11b_ringHom_family_section_continuous φ hφ Q ψ hψ
    apply s2v_t11b_nonzero_sign Set.univ isPreconnected_univ g hg.continuousOn ?_
      a b (Set.mem_univ a) (Set.mem_univ b)
    intro t _ ht
    exact ha ((hz a t).mpr ht)

end HodgeLean.Foundations.Program
