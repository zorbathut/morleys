# Attempts to Prove `root_unity_carac`

## The Problem

The `root_unity_carac` theorem is the algebraic heart of Connes' proof of Morley's theorem. It states:

```lean
theorem root_unity_carac (a₁ a₂ a₃ b₁ b₂ b₃ : ℂ)
    (hprod : a₁ * a₂ * a₃ = ω)
    (h₁₂ : 1 - a₁ * a₂ ≠ 0) (h₂₃ : 1 - a₂ * a₃ ≠ 0) (h₁₃ : 1 - a₁ * a₃ ≠ 0)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0) :
    let R := (a₁ * b₂ + b₁) / (1 - a₁ * a₂)
    let P := (a₂ * b₃ + b₂) / (1 - a₂ * a₃)
    let Q := (a₃ * b₁ + b₃) / (1 - a₃ * a₁)
    (a₁ ^ 2 + a₁ + 1) * b₁ + a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * b₂ +
      a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * b₃ =
    -ω * a₁ ^ 2 * a₂ * (a₁ - ω) * (a₂ - ω) * (a₃ - ω) * (R + ω * P + ω ^ 2 * Q)
```

This is translated from Isabelle's `Third_Unity_Root.thy` (lines 53-115 in the AFP).

## Key Algebraic Relations

1. `ω³ = 1` (omega_cubed)
2. `1 + ω + ω² = 0` (one_add_omega_add_omega_sq)
3. `ω² = -1 - ω` (omega_sq_eq)
4. When `a₁ * a₂ * a₃ = ω`:
   - `(a₁ - ω) = (1 - a₂ * a₃) * a₁`
   - `(a₂ - ω) = (1 - a₁ * a₃) * a₂`
   - `(a₃ - ω) = (1 - a₁ * a₂) * a₃`

## Approaches Tried

### 1. Direct `ring` Tactic
**Result**: Timeout (exceeds 200000 heartbeats)

After `field_simp [h₁₂, h₂₃, h₁₃]`, the goal becomes a massive polynomial identity. The `ring` tactic cannot handle it within reasonable time.

### 2. `native_decide`
**Result**: Error "expected type must not contain free variables"

Cannot be used because the goal contains free variables (a₁, a₂, etc.).

### 3. Substitution Approach
**What works**:
- Proved helper lemmas for the key substitutions:
  ```lean
  theorem sub_a1_omega (a₁ a₂ a₃ : ℂ) (hprod : a₁ * a₂ * a₃ = ω) :
      a₁ - ω = (1 - a₂ * a₃) * a₁
  ```
- These allow rewriting the RHS factors `(a_i - ω)` to cancel with denominators

**What doesn't work**:
- After substitution and `field_simp`, still left with a massive polynomial identity
- `ring_nf` doesn't help because it doesn't know about ω relations

### 4. `linear_combination` with `hωsum`
**Approach**: Since both sides should factor as `X * (1 + ω + ω²)` = 0, try:
```lean
linear_combination (norm := ring_nf)
    (a₁ * b₁ + a₁ ^ 3 * a₂ * b₂ + a₁ ^ 2 * a₂ ^ 2 * b₃) *
    ((1 - a₁ * a₂) * (1 - a₂ * a₃) * (1 - a₁ * a₃)) * hωsum
```

**Result**: Timeout in `ring_nf` normalization step, or leaves residual polynomial

### 5. `polyrith`
**Result**: Requires Sage connection which isn't available

The `polyrith` tactic uses Sage to find polynomial certificates, but the Sage server connection fails.

### 6. Power Reduction with `simp`
**Approach**: Reduce ω powers to at most ω² using:
```lean
have hω4 : ω ^ 4 = ω := ...
have hω5 : ω ^ 5 = ω ^ 2 := ...
have hω6 : ω ^ 6 = 1 := ...
simp only [hω2, hω3, hω4, hω5, hω6]
```

**Result**: Helps reduce term count but `ring_nf` still produces massive output

### 7. Factorization Approach (Isabelle's Method)
**Key Insight from Isabelle**: The `fin` lemma shows that after full expansion, both LHS and RHS equal:
```
(a₁*b₁ + a₁³*a₂*b₂ + a₁²*a₂²*b₃) * (1 + ω + ω²)
```

Since `1 + ω + ω² = 0`, both sides are 0 and hence equal.

**Structure**:
```lean
calc LHS * D = coeff * (1 + ω + ω²) := sorry  -- The hard part
           _ = coeff * 0 := by rw [hωsum]
           _ = 0 := by ring
           _ = RHS * D := sorry  -- Similar
```

**Result**: Compiles but requires proving the factorization lemma, which is just as hard.

## Why This Is Hard

1. **Polynomial size**: After clearing denominators, both sides expand to polynomials with 50+ terms each
2. **No algebraic decision procedure**: Lean's `ring` doesn't know about the relations ω³ = 1, 1 + ω + ω² = 0
3. **Mixed ring**: We're working in ℂ[a₁,a₂,a₃,b₁,b₂,b₃,ω]/(ω³-1, 1+ω+ω²) which is non-trivial

## How Isabelle Solves It

Isabelle's proof (Third_Unity_Root.thy, lines 54-115) uses:
1. Heavy use of `auto simp add: power2_eq_square power3_eq_cube algebra_simps`
2. `smt (verit, best)` - SMT solver integration
3. `fastforce` - powerful automated tactic
4. Manual intermediate lemmas (`y`, `y2`, `y3`, `fin`, `fin'`)

The Isabelle proof is ~60 lines of heavy automation.

## Possible Solutions

### Short-term
1. **Keep the sorry with documentation** (current approach)
   - The identity is verified in Isabelle
   - The rest of the proof works

### Medium-term
2. **Break into smaller lemmas**
   - Prove the `fin` factorization: `expanded_LHS = (a₁*b₁ + ...) * (1 + ω + ω²)`
   - This requires careful polynomial manipulation

3. **Use `native_decide` with concrete values**
   - Verify for specific numeric examples
   - Argue by polynomial identity (dangerous - not fully formal)

### Long-term
4. **Implement a Gröbner basis tactic for quotient rings**
   - Would allow proving polynomial identities modulo relations
   - Significant work

5. **Port the Sage certificate approach**
   - Use `polyrith` to find coefficients offline
   - Verify the certificate in Lean

## Current Status

The theorem remains `sorry`'d. The rest of Connes' proof (`morley_triangle_equilateral`) works correctly with the assumption that this identity holds.

## Files
- Current implementation: `Morleys/Connes.lean` (line 155)
- Isabelle reference: `ref/morley_references/isabelle_afp/Morley_Theorem/Third_Unity_Root.thy`

## Key Takeaway

This is a case where Isabelle's automation (particularly SMT integration) significantly outperforms what's currently easy to do in Lean 4 for pure polynomial reasoning with algebraic constraints.
