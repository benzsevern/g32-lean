import HodgeLean.Foundations.Program.SchoenHomogeneousSubringGrading

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The fixed subring inherits a grading from any action preserving the ambient graded pieces. -/
def s2_fixedRingGrading {A : Type} [CommRing A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (G : Type) [Group G] [MulSemiringAction G A]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n) :
    GradedRing (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)) :=
  s2_homogeneousSubringGrading 𝒜 (FixedPoints.subring A G)
    (fun n _ ha => s2_fixedRing_decompose_mem 𝒜 G hgrade ha n)

/-- The actual inclusion of a subring with inherited degree pieces is graded. -/
def s2_subringGradedInclusion {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) (R : Subring A) : s2_subringGradedPiece 𝒜 R →+*ᵍ 𝒜 :=
  { R.subtype with map_mem := fun {_} {_} ha => ha }

end HodgeLean.Foundations.Program
