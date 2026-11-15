import HodgeLean.Foundations.Program.SchoenHomogeneousOrbitProducts
import Mathlib.Algebra.Module.Submodule.Union

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A finite group preserving a vector subspace has one vector whose entire
orbit avoids an ideal whenever that subspace is not contained in the ideal. -/
theorem s2_submodule_orbit_avoidance {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [Algebra K A] [Group G] [Finite G] [MulSemiringAction G A]
    (V : Submodule K A) (hV : ∀ g : G, ∀ a ∈ V, g • a ∈ V)
    (P : Ideal A) (hP : ∃ a : V, (a : A) ∉ P) :
    ∃ a : V, ∀ g : G, g • (a : A) ∉ P := by
  let W (g : G) : Submodule K V :=
    ((P.comap (MulSemiringAction.toRingHom G A g)).restrictScalars K).comap V.subtype
  have hW (g : G) : W g ≠ ⊤ := by
    obtain ⟨a, ha⟩ := hP
    intro heq
    let b : V := ⟨g⁻¹ • (a : A), hV g⁻¹ a a.property⟩
    have hb : b ∈ W g := heq ▸ Submodule.mem_top
    change g • (g⁻¹ • (a : A)) ∈ P at hb
    exact ha (by simpa only [smul_inv_smul] using hb)
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top W hW
  exact ⟨a, ha⟩

/-- A homogeneous piece not contained in a prime contains an orbit product
that is homogeneous, invariant and outside that prime. -/
theorem s2_homogeneous_fixed_prime_avoidance {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n)
    (P : Ideal A) [P.IsPrime] (d : ℕ) (hP : ∃ a : A, a ∈ 𝒜 d ∧ a ∉ P) :
    ∃ b : FixedPoints.subring A G, b.val ∈ 𝒜 (Fintype.card G * d) ∧ b.val ∉ P := by
  let V : Submodule K A :=
    { carrier := (𝒜 d : Set A)
      zero_mem' := (𝒜 d).zero_mem
      add_mem' := fun ha hb => add_mem ha hb
      smul_mem' := fun k a ha => hK d k a ha }
  obtain ⟨a, ha⟩ := s2_submodule_orbit_avoidance V
    (fun g a ha => hgrade g d a ha) P (by
      obtain ⟨a, hmem, hnot⟩ := hP
      exact ⟨⟨a, hmem⟩, hnot⟩)
  exact ⟨⟨∏ g : G, g • (a : A), s2_orbitProduct_fixed (a : A)⟩,
    s2_orbitProduct_homogeneous 𝒜 hgrade a.property,
    s2_orbitProduct_notMem_prime P (a : A) ha⟩

end HodgeLean.Foundations.Program
