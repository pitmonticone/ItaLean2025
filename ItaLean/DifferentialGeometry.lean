import Mathlib

open Set ENat ContDiff Manifold Metric Function TopologicalSpace
noncomputable section

/-! # Differential geometry in Lean -/

/-
How do we formalise manifolds in mathlib? Let's ignore boundary and corners at first,
and just think about formalising **charts** and manifolds.

Let `M` be a manifold modelled on the topological space `H`.
-/
variable {M H : Type*} [TopologicalSpace M] [TopologicalSpace H]

/- The naive definition of chart would be "a homeomorphism between open subsets of `M` and `H`". -/
def NaiveChart (s : Opens M) (t : Opens H) := s ≃ₜ t

/- However, this would be rather unpleasant to work with: given a point `p : M`,
to even write to "apply the chart at `p` to `p`", we need to pass a proof that `p` is in the domain
of the chart, *every single time* we apply this. -/

example {s : Opens M} {t : Opens H} {p : M} (hp : p ∈ s) (φ : NaiveChart s t) : H := by
  -- Cannot just apply φ to p; need to pass a proof that `p ∈ s`.
  --let y := φ.toFun p -- errors
  let y := φ.toFun ⟨p, hp⟩
  -- Cannot return `y` directly.
  --apply y -- errors
  apply y.val

/- Solution: use the junk value pattern
Charts map `M` to `H`, but we only prescribe their value on their `source` and `target`.
-/
#check PartialEquiv
#check OpenPartialHomeomorph


/- A topological space is locally euclidean if you have a
partial homeomorphism to `ℝⁿ` around each point in `X`.
We record a preferred chart for each point. -/
#check ChartedSpace



/- A smooth manifold is an charted space structure
such that for any two charts the coordinate change function
between the charts is smooth on their common domain.
We also require that the space is Hausdorff and second-countable. -/
variable {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [SecondCountableTopology M] [T2Space M]
  {e e' : OpenPartialHomeomorph M E}

/- We want to require the following condition for smooth manifolds. -/
#check ContDiffOn ℝ ⊤ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source


/- This is captured by the predicate `HasGroupoid`. -/
#check HasGroupoid

/- We can also equip a manifold with another groupoid structure,
to define the class of `C^k` manifolds or analytic manifolds,
or other classes of manifolds. -/
#check StructureGroupoid


/- Here `contDiffGroupoid` specifies the groupoid structure
on partial homeomorphisms stating that coordinate change functions
must be smooth -/
#check contDiffGroupoid


/- Models with corners allow speaking about manifolds with boundary and corners.
There is a map `I : H → E` where `E` is a normed space over a field `𝕜`.

Example: `E = ℝⁿ`, `H` is a half-space, and `I : H → E` is the inclusion.
This map `I` is called a *model with corners*.
`𝓡 n` is notation for the identity map `ℝⁿ → ℝⁿ`.
`𝓡∂ n` is the inclusion from the half-space into `ℝⁿ` -/

#check ModelWithCorners

variable {n : ℕ}

#check 𝓡 n
#check 𝓡∂ 3


-- Here is how to declare a general manifold with boundary and corners. It's a little verbose.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I n M]
  -- Here's a second one.
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] (J : ModelWithCorners 𝕜 F G)
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J n N]

-- Here's how to access the atlas at a point.
#check atlas H M

-- The preferred chart at x.
variable {x : M} in
#check chartAt H x


-- Differentiability, continuous differentiability etc. all have analogues for manifolds.
variable {f : M → N} {s : Set M} {x : M}

-- `f` is `C^n`
#check ContMDiff I J n f
-- Equivalently, you can write the following:
-- note that you don't need to specify the model with corners any more.
#check CMDiff n f

-- `f` is `C^n` at `x`
#check ContMDiffAt I J n f x
#check CMDiffAt n f x
-- -- `f` is differentiable on `s`
#check MDifferentiableOn I J f s
#check MDiff[s] f

-- If `f` is not differentiable at `x`, then `mfderiv I J f x` is defined to be zero.
example (f : M → N) (_hf : MDifferentiable I J f) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace J (f x) :=
  mfderiv I J f x

-- Here is how to state the chain rule.
example {f g : M → M} (x : M)
    (hg : MDifferentiableAt I I g (f x)) (hf : MDifferentiableAt I I f x) :
    mfderiv I I (g ∘ f) x = (mfderiv I I g (f x)).comp (mfderiv I I f x) :=
  mfderiv_comp x hg hf
-- and once again, with nicer notation
example {f g : M → M} (x : M)
    (hg : MDiffAt g (f x)) (hf : MDiffAt f x) :
    mfderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x) :=
  mfderiv_comp x hg hf
