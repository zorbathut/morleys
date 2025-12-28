# Formalizing Morley's Trisector Theorem in Lean 4

Morley's Trisector Theorem remains **unformalised in Lean** (both Lean 3 and 4), making it a significant target for Mathlib contribution. The theorem has been formalised in three other proof assistants—Isabelle (March 2025), HOL Light, and Coq—providing valuable templates. The most tractable approach for Lean 4 is **Alain Connes' algebraic proof** using the affine group, which avoids geometric case analysis by reducing equilaterality to an elegant algebraic condition involving cube roots of unity.

## The theorem: trisector intersections form an equilateral triangle

**Morley's Trisector Theorem (1899):** In any triangle ABC with angles 3α, 3β, 3γ where α + β + γ = 60°, the intersections of **adjacent** interior angle trisectors form an equilateral triangle with side length **s = 8R sin(α) sin(β) sin(γ)**, where R is the circumradius.

The vertices of the first Morley triangle have trilinear coordinates:
- A-vertex: (1 : 2cos(C/3) : 2cos(B/3))
- B-vertex: (2cos(C/3) : 1 : 2cos(A/3))  
- C-vertex: (2cos(B/3) : 2cos(A/3) : 1)

**Critical edge cases** that any formalization must handle:

- **Non-degeneracy required**: All angles must be strictly positive (α, β, γ > 0). If any angle is 0° or 180°, trisectors are undefined.
- **Point distinctness**: The explicit preconditions A ≠ B, A ≠ C, B ≠ C plus distinctness of Morley triangle vertices must be stated.
- **18 equilateral triangles exist**: Each angle's trisectors can be multiplied by cube roots of unity, yielding 18 total Morley triangles. The "first" Morley triangle uses adjacent interior trisectors—this must be specified explicitly.
- **Euclidean only**: Morley's theorem fails in spherical and hyperbolic geometry—Connes' proof explicitly uses properties unique to the Euclidean affine group.

## Proof approaches ranked by formalization tractability

### Connes' algebraic proof (recommended for Lean 4)

Alain Connes' 1998 proof is the **most formalization-friendly** because it reduces geometry to abstract algebra over any field of characteristic ≠ 3. The Isabelle/AFP formalization (2025) successfully used this approach.

**Setting**: Let G be the affine group over field k, consisting of matrices g = [a b; 0 1] with a ∈ k*, b ∈ k. Define δ(g) = a and fix(g) = b/(1-a) for a ≠ 1.

**Main Theorem**: Let g₁, g₂, g₃ ∈ G such that pairwise products and g₁g₂g₃ are not translations. Let j = δ(g₁g₂g₃). Then the following are equivalent:
- (a) g₁³g₂³g₃³ = 1
- (b) j³ = 1 and **α + jβ + j²γ = 0**

where α = fix(g₁g₂), β = fix(g₂g₃), γ = fix(g₃g₁).

**Deriving Morley**: Take k = ℂ. Let gᵢ be rotations with centers at vertices A, B, C and angles 2α, 2β, 2γ respectively (where 3α, 3β, 3γ are the triangle's angles). Then:
1. g₁³g₂³g₃³ = 1 because each gᵢ³ is the product of reflections along consecutive sides
2. The fixed points α, β, γ of pairwise products are the trisector intersections
3. The condition α + jβ + j²γ = 0 (where j = e^(2πi/3)) is the **classical characterization of equilateral triangles**

**Key advantages for formalization:**
- Works over abstract fields—leverages Mathlib's algebraic infrastructure
- Uses matrix/group operations already well-supported in Mathlib
- The equilateral characterization α + jβ + j²γ = 0 is a single algebraic equation
- Avoids extensive geometric case analysis
- The 18 Morley triangles arise naturally by multiplying each gᵢ by cube roots of unity

### Conway's backward proof (elegant but harder to formalize)

Conway constructs seven triangles around a unit equilateral triangle, showing they assemble into a figure similar to any given triangle ABC.

**The seven triangle types** (using notation x* = x + 60°):
- Central: (0*, 0*, 0*) — the equilateral triangle with side 1
- Single-starred: (α, β*, γ*), (α*, β, γ*), (α*, β*, γ) — scaled so the edge opposite the unstarred angle has length 1
- Double-starred: (α**, β, γ), (α, β**, γ), (α, β, γ**) — constructed with isosceles triangles having legs of length 1

**The isosceles trick**: For triangle (α**, β, γ) at vertex P with angles β at B and γ at C, draw lines from P cutting BC at angle α* in both senses, creating isosceles triangle PYZ with PY = PZ = 1. This enforces the critical congruence ΔBPR ≅ ΔBPZ.

**Formalization difficulty**: While elegant geometrically, this proof requires:
- Proving angles sum to 360° at each internal vertex
- Establishing multiple triangle congruences
- Showing the assembled figure is similar to ABC
- The "fitting together" step involves implicit orientation reasoning

### Trigonometric direct proof

Uses the **triple angle identity** sin(3θ) = 4 sin(θ) sin(60° + θ) sin(120° + θ) with the Laws of Sines and Cosines.

**Outline:**
1. Apply Law of Sines in triangles ARB, BPC, CQA to find trisector intersection distances
2. Apply Law of Cosines to compute PR², PQ², QR²
3. Show the expression is symmetric in α, β, γ, hence PR = PQ = QR

This requires extensive trigonometric infrastructure including triple angle formulas **not currently in Mathlib4**.

## Existing formalizations provide templates

### Isabelle/AFP (March 2025) — most recent and documented

**Author**: Benjamin Puyobro  
**Proof approach**: Connes' algebraic proof  
**Structure** (7 theory files):
- `Complex_Angles.thy` — angle definitions in complex geometry
- `Complex_Triangles_Definitions.thy` — triangles in complex field
- `Complex_Trigonometry.thy` — sine law in complex context
- `Third_Unity_Root.thy` — cube roots of unity (j where j³ = 1)
- `Complex_Triangles.thy` — congruent triangle properties
- `Complex_Axial_Symmetry.thy` — rotations and symmetry
- `Morley.thy` — main theorem

**Key insight**: Rotations are represented as complex multiplication; trisection becomes multiplication by cube roots of unity.

### Coq/Rocq (HighSchoolGeometry library)

```coq
Theorem Morley: forall (a b c : R) (A B C P Q T : PO),
  0 < a -> 0 < b -> 0 < c ->
  (a + b) + c = pisurtrois ->  (* π/3 *)
  A <> B -> A <> C -> B <> C -> B <> P -> B <> Q -> A <> T -> C <> T ->
  image_angle b = cons_AV (vec B C) (vec B P) ->
  (* ... 8 more angle constraints for trisection ... *)
  equilateral P Q T.
```

**Approach**: Trigonometric proof using oriented angles defined via vectors. The helper lemma `sin_3_a: sin(3*a) = sin(a) * (2*cos(2*a) + 1)` is essential.

### HOL Light

```
MORLEY |- !A B C:real^2 P Q R.
    ~collinear{A,B,C} /\
    {P,Q,R} SUBSET convex hull {A,B,C} /\
    angle(A,B,R) = angle(A,B,C) / &3 /\ ...
    ==> dist(R,P) = dist(P,Q) /\ dist(Q,R) = dist(P,Q)
```

Uses the convex hull constraint to specify "adjacent" trisectors, avoiding orientation complexity.

## Mathlib4 geometry infrastructure assessment

### Available tools

**Unoriented angles** (`InnerProductGeometry.angle`):
```lean
def angle (x y : V) : ℝ := Real.arccos (inner ℝ x y / (‖x‖ * ‖y‖))
```
Range [0, π]. For zero vectors, returns π/2. Key properties: `angle_nonneg`, `angle_le_pi`, `cos_angle`, `sin_angle_nonneg`.

**Angle at a point** (`EuclideanGeometry.angle`):
```lean
def angle (p₁ p₂ p₃ : P) : ℝ := InnerProductGeometry.angle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)
```
Notation: `∠ p₁ p₂ p₃` measures the undirected angle at p₂.

**Oriented angles** (`Orientation.oangle`): Requires 2D space with `[Fact (Module.finrank ℝ V = 2)]` and orientation. Returns `Real.Angle` (mod 2π). Results true only mod π use `2 • θ`.

**Triangle theorems**: Law of Cosines (`law_cos`), Law of Sines (`law_sin`), angle sum theorem (`angle_add_angle_add_angle_eq_pi`), isosceles triangle theorem.

**Complex number infrastructure**: `Complex`, roots of unity, matrix operations—strong support for Connes' approach.

### Critical gaps requiring development

**Triple angle formulas are MISSING**:
```lean
-- Need to prove:
theorem sin_three_mul (θ : ℝ) : sin (3 * θ) = 3 * sin θ - 4 * sin θ ^ 3
theorem cos_three_mul (θ : ℝ) : cos (3 * θ) = 4 * cos θ ^ 3 - 3 * cos θ
```

**Angle trisection predicate** needs definition:
```lean
def IsTrisector (p₁ p₂ p₃ q : P) : Prop :=
  3 * angle p₁ p₂ q = angle p₁ p₂ p₃
```

**Equilateral triangle characterization**:
- Via equal angles: all angles = π/3
- Via complex numbers: α + jβ + j²γ = 0 where j = e^(2πi/3)

## Implementation challenges and solutions

### Angle representation choices

| Approach | Pros | Cons |
|----------|------|------|
| Unoriented (`angle`) | Simpler, range [0,π] | More case analysis for orientation |
| Oriented (`oangle`) | Natural for trisection | Requires 2D, mod 2π arithmetic |
| Complex (`Complex.arg`) | Natural for Connes' proof | Different infrastructure |

**Recommendation**: For Connes' proof, work in ℂ and use complex argument; for trigonometric proof, use unoriented angles with explicit orientation predicates.

### Specifying "adjacent" trisectors

The formalization must distinguish between the 18 possible Morley triangles. Options:
- **HOL Light approach**: Require vertices in convex hull of original triangle
- **Coq approach**: Explicit oriented angle equalities for all 9 trisector relationships
- **Connes approach**: The "first" Morley triangle corresponds to not multiplying any gᵢ by non-trivial cube roots

### Non-degeneracy preconditions

Every formalization needs explicit hypotheses:
```lean
variable {A B C P Q R : P}
variable (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)  -- non-degenerate triangle
variable (hα : 0 < angle B A C / 3) -- positive trisector angles (automatic from non-degeneracy)
```

## Recommended formalization strategy for Lean 4

### Phase 1: Infrastructure (estimate: 300-500 lines)

1. **Prove triple angle formulas** (derivable from double-angle):
   ```lean
   theorem sin_three_mul : sin (3 * θ) = 3 * sin θ - 4 * sin θ ^ 3
   theorem cos_three_mul : cos (3 * θ) = 4 * cos θ ^ 3 - 3 * cos θ
   ```

2. **Cube roots of unity properties**:
   ```lean
   def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
   theorem omega_cubed : ω ^ 3 = 1
   theorem one_add_omega_add_omega_sq : 1 + ω + ω ^ 2 = 0
   ```

3. **Equilateral triangle characterization**:
   ```lean
   theorem equilateral_iff_complex (α β γ : ℂ) :
     (dist α β = dist β γ ∧ dist β γ = dist γ α) ↔ α + ω * β + ω ^ 2 * γ = 0
   ```

### Phase 2: Connes' theorem (estimate: 400-600 lines)

4. **Affine group definition** (may already exist as `Matrix.special_linear_group` variant):
   ```lean
   def AffineGroup (k : Type*) [Field k] := { g : Matrix (Fin 2) (Fin 2) k // g 1 0 = 0 ∧ g 1 1 = 1 ∧ g 0 0 ≠ 0 }
   ```

5. **Fixed point map**:
   ```lean
   def fixedPoint (g : AffineGroup k) (h : g.val 0 0 ≠ 1) : k := g.val 0 1 / (1 - g.val 0 0)
   ```

6. **Main algebraic theorem**:
   ```lean
   theorem connes_main (g₁ g₂ g₃ : AffineGroup k) 
     (h₁₂ : (g₁ * g₂).val 0 0 ≠ 1) (h₂₃ : (g₂ * g₃).val 0 0 ≠ 1) 
     (h₃₁ : (g₃ * g₁).val 0 0 ≠ 1) (h₁₂₃ : (g₁ * g₂ * g₃).val 0 0 ≠ 1) :
     let j := (g₁ * g₂ * g₃).val 0 0
     let α := fixedPoint (g₁ * g₂) h₁₂
     let β := fixedPoint (g₂ * g₃) h₂₃  
     let γ := fixedPoint (g₃ * g₁) h₃₁
     g₁^3 * g₂^3 * g₃^3 = 1 ↔ (j^3 = 1 ∧ α + j * β + j^2 * γ = 0)
   ```

### Phase 3: Geometric instantiation (estimate: 200-400 lines)

7. **Rotations as affine group elements**:
   ```lean
   def rotationAsAffine (center : ℂ) (angle : ℝ) : AffineGroup ℂ := ...
   ```

8. **Trisector intersections are fixed points**:
   ```lean
   theorem trisector_intersection_eq_fixedPoint (A B C : ℂ) (hnd : ...) :
     morleyVertex A B C = fixedPoint (rotationAsAffine A (2 * angle A / 3) * rotationAsAffine B (2 * angle B / 3)) ...
   ```

9. **Final theorem**:
   ```lean
   theorem morley_trisector (A B C : ℂ) (hnd : ¬ Collinear A B C) :
     let ⟨P, Q, R⟩ := morleyTriangle A B C
     dist P Q = dist Q R ∧ dist Q R = dist R P
   ```

### Recommended imports

```lean
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.RootsOfUnity
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Complex.Exponential
```

## Conclusion: Connes' proof offers the clearest path

The **Connes algebraic approach** is optimal for Lean 4 formalization because it transforms the geometric theorem into verifiable algebraic identities over the affine group. The key equation α + jβ + j²γ = 0 elegantly captures equilaterality, and the proof works abstractly over any field of characteristic ≠ 3. This matches Mathlib's strengths in abstract algebra while minimizing geometric case analysis. The Isabelle/AFP formalization provides a proven blueprint, and Mathlib4's existing complex number and matrix infrastructure provides most required foundations—with triple angle formulas being the primary gap requiring development.