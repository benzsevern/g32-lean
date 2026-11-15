import HodgeLean.Foundations.Program.SchoenGradedInvariants

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual graded ring homomorphism supplied by a degree-preserving action element. -/
def s2_gradedActionHom {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n) (g : G) : 𝒜 →+*ᵍ 𝒜 :=
  { MulSemiringAction.toRingHom G A g with map_mem := fun {n} {a} ha => hgrade g n a ha }

/-- The identity group element induces the actual graded identity. -/
theorem s2_gradedActionHom_one {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n) :
    s2_gradedActionHom 𝒜 hgrade (1 : G) = GradedRingHom.id 𝒜 := by
  ext a
  exact one_smul G a

/-- Group multiplication becomes actual graded-ring-map composition. -/
theorem s2_gradedActionHom_mul {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n) (g h : G) :
    s2_gradedActionHom 𝒜 hgrade (g * h) =
      (s2_gradedActionHom 𝒜 hgrade g).comp (s2_gradedActionHom 𝒜 hgrade h) := by
  ext a
  exact mul_smul g h a

end HodgeLean.Foundations.Program
