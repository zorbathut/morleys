# Lean 4 Mathematical Theorem Prover Reference

This comprehensive reference documents Lean 4 syntax, tactics, and Mathlib4 usage for transcribing mathematical proofs. **Lean 4** uses dependent type theory where propositions are types and proofs are terms (Curry-Howard correspondence).

---

## Type system fundamentals

Lean 4's type universe hierarchy separates **propositions** (`Prop`) from **data types** (`Type`). Understanding this distinction is essential for writing correct proofs.

| Universe | Also Known As | Purpose |
|----------|---------------|---------|
| `Sort 0` | `Prop` | Propositions (proof-irrelevant) |
| `Sort 1` | `Type` / `Type 0` | Data types |
| `Sort 2` | `Type 1` | Types of types |
| `Sort u` | `Type (u-1)` | Universe polymorphic |

**Prop** contains logical statements where any two proofs are definitionally equal (proof irrelevance). **Type** contains computationally relevant data. The impredicativity of `Prop` means functions returning `Prop` stay in `Prop` regardless of argument universe.

```lean
#check (2 + 2 = 4)       -- Prop
#check And               -- Prop → Prop → Prop  
#check Nat               -- Type
#check Type 1            -- Type 2

-- Universe polymorphism
universe u v
def myPair (α : Type u) (β : Type v) := α × β
```

---

## Defining mathematical objects

### Declaration keywords

| Keyword | Purpose | Body Reducibility |
|---------|---------|-------------------|
| `def` | Functions and values | Reducible |
| `theorem` | Propositions (proofs processed in parallel) | Irreducible |
| `lemma` | Alias for theorem (Mathlib convention) | Irreducible |
| `example` | Anonymous one-off proofs | Not stored |
| `abbrev` | Transparent abbreviations | Always unfolded |
| `axiom` | Postulates without proof (use carefully) | N/A |

```lean
-- def for computational functions
def double (n : Nat) : Nat := n + n

-- theorem for propositions
theorem double_eq (n : Nat) : double n = n + n := rfl

-- example for testing (not stored)
example : 2 + 2 = 4 := rfl

-- abbrev for transparent aliases
abbrev ℕ := Nat
```

### Structures and classes

**Structures** define product types with named fields. **Classes** are structures with instance-implicit arguments for the typeclass system.

```lean
-- Structure: data with named fields
structure Point (α : Type) where
  x : α
  y : α
  deriving Repr

-- Creating instances
def p : Point Nat := { x := 1, y := 2 }
def p' : Point Nat := ⟨1, 2⟩  -- anonymous constructor

-- Class: for typeclass inference
class Add (α : Type) where
  add : α → α → α

instance : Add Nat where
  add := Nat.add

-- Structure inheritance
structure ColorPoint (α : Type) extends Point α where
  color : String
```

### Inductive types

```lean
-- Simple enumeration
inductive Weekday where
  | monday | tuesday | wednesday | thursday | friday | saturday | sunday

-- Recursive type
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

-- Parameterized type
inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

-- Indexed family (proposition)
inductive MyEq {α : Sort u} (a : α) : α → Prop where
  | refl : MyEq a a
```

---

## Function syntax and arguments

### Lambda expressions

```lean
fun x => x + 1           -- basic lambda
fun x : Nat => x + 1     -- with type annotation
fun (x y : Nat) => x + y -- multiple arguments
λ x => x + 1             -- unicode variant
(· + 1)                  -- anonymous placeholder (= fun x => x + 1)
(· + ·)                  -- two placeholders (= fun x y => x + y)
```

### Argument types

```lean
-- Explicit: (x : Type)
def ident1 (α : Type) (x : α) : α := x
#check ident1 Nat 5        -- must provide α

-- Implicit: {x : Type}  
def ident2 {α : Type} (x : α) : α := x
#check ident2 5            -- α inferred automatically

-- Instance implicit: [inst : Class]
def addTwice {α : Type} [Add α] (x : α) : α := x + x

-- @ makes all arguments explicit
#check @ident2             -- {α : Type} → α → α
#check @ident2 Nat 5       -- provide implicit explicitly

-- Named implicit arguments
f (α := Nat) x             -- provide specific implicit by name
```

### Pattern matching

```lean
-- match expression
def isZero (n : Nat) : Bool :=
  match n with
  | 0 => true
  | _ => false

-- Pattern matching in definitions
def fib : Nat → Nat
  | 0 => 1
  | 1 => 1  
  | n + 2 => fib (n + 1) + fib n

-- Multiple discriminants
def foo : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2

-- Recursive definitions with termination
def gcd (m n : Nat) : Nat :=
  if m = 0 then n
  else gcd (n % m) m
termination_by m
```

---

## Code organization

### Namespaces and sections

```lean
namespace MyMath
  def square (x : Nat) := x * x
  
  namespace Internal
    def helper := 42
  end Internal
end MyMath

#check MyMath.square           -- qualified access
#check MyMath.Internal.helper

-- Sections with variables
section GroupTheory
  variable {G : Type*} [Group G]
  
  -- Variables automatically added to declarations that use them
  theorem inv_inv (a : G) : a⁻¹⁻¹ = a := inv_inv a
end GroupTheory
```

### Opening and importing

```lean
-- Import at file start only
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- Open namespace for unqualified access
open Nat in
#check succ              -- instead of Nat.succ

-- Open specific names only
open List (map filter)

-- Scoped open (for notations)
open scoped BigOperators  -- enables ∑, ∏ notation
```

---

## Tactic mode and proof writing

Enter tactic mode with `by`. Tactics manipulate the **proof state** consisting of hypotheses and goals.

### Core tactics catalog

#### Introduction and application

| Tactic | Purpose | Example |
|--------|---------|---------|
| `intro h` | Introduce hypothesis from `∀` or `→` | `intro x hx` |
| `intros` | Introduce multiple hypotheses | `intros x y z` |
| `rintro` | Intro with pattern matching | `rintro ⟨a, b⟩` |
| `apply f` | Apply function, create goals for premises | `apply And.intro` |
| `exact e` | Provide exact proof term | `exact h.symm` |
| `refine e` | Like exact but holes become goals | `refine ⟨?_, h⟩` |
| `use e` | Provide witness for `∃` | `use 5` |

#### Rewriting

| Tactic | Purpose | Example |
|--------|---------|---------|
| `rw [h]` | Rewrite using equation/iff | `rw [add_comm]` |
| `rw [← h]` | Rewrite in reverse direction | `rw [← mul_assoc]` |
| `rw [h] at hyp` | Rewrite in hypothesis | `rw [h] at hx` |
| `simp` | Simplify using `@[simp]` lemmas | `simp` |
| `simp [h1, h2]` | Simp with additional lemmas | `simp [mul_comm]` |
| `simp only [...]` | Simp with only specified lemmas | `simp only [add_zero]` |
| `simp_all` | Simp everything with hypotheses | `simp_all` |
| `dsimp` | Definitional simplification only | `dsimp only` |

#### Arithmetic and decision

| Tactic | Purpose | Example |
|--------|---------|---------|
| `ring` | Polynomial equalities in rings | `ring` |
| `ring_nf` | Normalize polynomial expressions | `ring_nf at h` |
| `linarith` | Linear arithmetic | `linarith [h1, h2]` |
| `nlinarith` | Nonlinear arithmetic | `nlinarith` |
| `omega` | Linear integer/nat arithmetic | `omega` |
| `decide` | Decidable propositions | `decide` |
| `norm_num` | Numerical normalization | `norm_num` |
| `positivity` | Prove positivity/nonnegativity | `positivity` |

#### Logical tactics

| Tactic | Purpose | Example |
|--------|---------|---------|
| `constructor` | Apply first constructor | `constructor` |
| `left` / `right` | Choose disjunct for `∨` | `left` |
| `exfalso` | Change goal to `False` | `exfalso` |
| `by_contra h` | Proof by contradiction | `by_contra hnp` |
| `push_neg` | Push negations inward | `push_neg at h` |
| `contrapose` | Transform to contrapositive | `contrapose!` |

#### Case analysis and induction

| Tactic | Purpose | Example |
|--------|---------|---------|
| `cases h` | Case split on inductive | `cases h with \| inl hp => ... \| inr hq => ...` |
| `rcases h with ⟨a, b⟩` | Recursive case split | `rcases h with ⟨x, hx⟩ \| rfl` |
| `obtain ⟨x, hx⟩ := h` | Combine have and rcases | `obtain ⟨n, hn⟩ := h` |
| `induction n` | Structural induction | `induction n with \| zero => ... \| succ n ih => ...` |
| `by_cases h : P` | Classical case split | `by_cases h : n = 0` |

#### Finishing tactics

| Tactic | Purpose |
|--------|---------|
| `rfl` | Reflexivity |
| `trivial` | Try rfl, assumption, basic automation |
| `assumption` | Find matching hypothesis |
| `contradiction` | Find contradictory hypotheses |
| `exact?` | Search for closing lemma |
| `apply?` | Search for applicable lemma |

### Tactic combinators

```lean
-- Semicolon: apply second tactic to ALL subgoals from first
constructor <;> assumption

-- Sequential: second applies to first subgoal only
constructor; exact hp; exact hq

-- Control flow
try tac              -- succeeds even if tac fails
first | tac1 | tac2  -- tries tactics in order
repeat tac           -- repeats until failure
all_goals tac        -- applies to all goals
any_goals tac        -- succeeds if any goal succeeds

-- Focus with dot
example (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp    -- focused on first goal
  · exact hq    -- focused on second goal
```

### Structured proofs

```lean
-- have: intermediate results
example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a = c := by
  have hab : a = b := h1
  have hbc : b = c := h2
  exact hab.trans hbc

-- suffices: work backwards
example (hp : p) (hpq : p → q) (hqr : q → r) : r := by
  suffices hq : q by exact hqr hq
  exact hpq hp

-- show: type ascription
example (n : ℕ) : n + 0 = n := by
  show n + 0 = n
  rfl

-- calc: equational reasoning
example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a = c :=
  calc a = b := h1
       _ = c := h2

-- calc with mixed relations
example (a b c : ℕ) (h1 : a ≤ b) (h2 : b < c) : a < c :=
  calc a ≤ b := h1
       _ < c := h2
```

### Term mode vs tactic mode

**Term mode** (direct proof terms) works well for simple proofs:
```lean
example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
example : p → q → p := fun hp _ => hp
example (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩
```

**Tactic mode** works well for complex proofs with automation:
```lean
example (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring
example (h : n < m) (h' : m ≤ k) : n < k := by omega
```

**Mix both** freely:
```lean
example (h : p ∧ (q ∨ r)) : (p ∧ q) ∨ (p ∧ r) := by
  obtain ⟨hp, hqr⟩ := h
  cases hqr with
  | inl hq => exact Or.inl ⟨hp, hq⟩
  | inr hr => exact Or.inr ⟨hp, hr⟩
```

---

## The simp tactic in depth

`simp` is a **conditional term rewriting system** that repeatedly applies `@[simp]` lemmas left-to-right until no more rewrites apply.

```lean
simp                      -- use all @[simp] lemmas
simp [h1, h2]             -- also use h1, h2
simp [← h]                -- use h in reverse direction
simp [-lemma_name]        -- exclude specific lemma
simp [*]                  -- also use all hypotheses
simp only [h1, h2]        -- ONLY specified lemmas (stable)
simp at h                 -- simplify hypothesis h
simp at h1 h2 ⊢           -- simplify h1, h2, and goal
simp?                     -- shows what lemmas simp would use

-- Best practice: terminal simps are fine
example : (1 : ℕ) + 1 = 2 := by simp

-- Non-terminal simps should use simp only
example (h : P) : Q := by
  simp only [some_lemma]  -- stable, explicit
  exact h
```

**Mark lemmas for simp** with `@[simp]`:
```lean
@[simp] theorem add_zero (n : ℕ) : n + 0 = n := rfl
```

---

## Mathlib4 orientation

### Key directories

| Directory | Contents |
|-----------|----------|
| `Mathlib/Algebra` | Groups, rings, fields, modules, linear algebra |
| `Mathlib/Analysis` | Real/complex analysis, calculus, normed spaces |
| `Mathlib/Data` | Core types: Nat, Int, Rat, Real, List, Set, Finset |
| `Mathlib/NumberTheory` | Primes, arithmetic, algebraic number theory |
| `Mathlib/Order` | Orderings, lattices |
| `Mathlib/Tactic` | Proof automation |
| `Mathlib/Topology` | Topological spaces, continuity |

### Important namespaces

| Namespace | Key Contents |
|-----------|--------------|
| `Nat` | `succ`, `add`, `mul`, `div`, `mod`, `gcd`, `Prime` |
| `Int` | `ofNat`, `neg`, `natAbs`, `sign` |
| `Real` | `sqrt`, `exp`, `log`, `sin`, `cos` |
| `Set` | `mem`, `union`, `inter`, `compl`, `image`, `preimage` |
| `Finset` | `card`, `sum`, `prod`, `filter`, `map` |
| `List` | `map`, `filter`, `foldl`, `length`, `append` |
| `Function` | `Injective`, `Surjective`, `Bijective`, `comp` |

### Naming conventions for finding lemmas

**Capitalization**: Proofs use `snake_case`; Types/Classes use `UpperCamelCase`.

**Symbol-to-name dictionary**:

| Symbol | Name | Symbol | Name |
|--------|------|--------|------|
| `+` | `add` | `∧` | `and` |
| `-` (unary) | `neg` | `∨` | `or` |
| `-` (binary) | `sub` | `→` | `of` / `imp` |
| `*` | `mul` | `↔` | `iff` |
| `/` | `div` | `¬` | `not` |
| `⁻¹` | `inv` | `∀` | `all` / `forall` |
| `^` | `pow` | `∃` | `exists` |
| `<` | `lt` | `∈` | `mem` |
| `≤` | `le` | `∪` | `union` |
| `0` | `zero` | `∩` | `inter` |
| `1` | `one` | `ᶜ` | `compl` |

**Common suffixes**:

| Suffix | Meaning | Example |
|--------|---------|---------|
| `_comm` | Commutativity | `add_comm : a + b = b + a` |
| `_assoc` | Associativity | `mul_assoc : (a*b)*c = a*(b*c)` |
| `_zero` | Involves zero | `add_zero : a + 0 = a` |
| `_one` | Involves one | `mul_one : a * 1 = a` |
| `_left`/`_right` | Left/right variant | `add_le_add_left` |
| `_self` | Same element | `sub_self : a - a = 0` |
| `_of_*` | From hypotheses | `lt_of_le_of_ne` |

**Pattern**: conclusion_of_hypothesis1_of_hypothesis2
```lean
#check lt_of_le_of_ne      -- a ≤ b → a ≠ b → a < b
#check add_sub_cancel      -- a + b - b = a
```

### Finding lemmas

```lean
-- In-editor tactics
exact?     -- search for lemma that closes goal
apply?     -- search for applicable lemma
rw?        -- search for rewrite lemma
simp?      -- show what simp would use

-- Commands
#check Nat.add_comm       -- check type
#print Nat.add            -- print definition
```

**External search tools**:
- **Loogle** (https://loogle.lean-lang.org/): Pattern-based search
- **Moogle** (https://www.moogle.ai/): Natural language search
- **Mathlib docs** (https://leanprover-community.github.io/mathlib4_docs/)

### Key Mathlib tactics

| Tactic | Purpose |
|--------|---------|
| `ring` | Polynomial equalities in commutative rings |
| `field_simp` | Clear denominators in field expressions |
| `group` | Non-commutative group identities |
| `abel` | Abelian group identities |
| `gcongr` | Generalized congruence for inequalities |
| `positivity` | Prove positivity/nonnegativity |
| `polyrith` | Polynomial arithmetic (requires SageMath) |
| `fun_prop` | Function properties (continuity, measurability) |

---

## Common proof patterns

### Equality proofs

```lean
-- rfl for definitional equality
example : 2 + 2 = 4 := rfl

-- rw for rewriting
example (a b c : ℕ) (h : a = b) : a + c = b + c := by rw [h]

-- calc for chains
example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a = c :=
  calc a = b := h1
       _ = c := h2

-- trans and symm
example (h1 : a = b) (h2 : b = c) : a = c := h1.trans h2
example (h : a = b) : b = a := h.symm
```

### Logical connectives

```lean
-- And (∧)
example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
example (h : p ∧ q) : p := h.left   -- or h.1
example (h : p ∧ q) : q := h.right  -- or h.2

-- Or (∨)
example (hp : p) : p ∨ q := Or.inl hp
example (hq : q) : p ∨ q := Or.inr hq
example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

-- Negation (¬)  -- ¬p is defined as p → False
example (h : ¬¬p) : p := by
  by_contra hnp
  exact h hnp

-- Iff (↔)
example (p q : Prop) : p ∧ q ↔ q ∧ p :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
```

### Quantifiers

```lean
-- Universal (∀): introduce with intro, use by application
example : ∀ n : Nat, n = n := fun n => rfl

example (h : ∀ x, P x) : P a := h a

-- Existential (∃): introduce with use, eliminate with obtain
example : ∃ x : Nat, x > 0 := ⟨1, Nat.one_pos⟩

example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  obtain ⟨x, _, hqx⟩ := h
  exact ⟨x, hqx⟩

-- Negating quantifiers
#check not_forall  -- ¬(∀ x, P x) ↔ ∃ x, ¬P x
#check not_exists  -- ¬(∃ x, P x) ↔ ∀ x, ¬P x
-- push_neg applies these automatically
```

### Set theory

```lean
import Mathlib.Data.Set.Basic

-- Membership
example (x : α) (s : Set α) (P : α → Prop) : x ∈ {y | P y} ↔ P x := Iff.rfl

-- Subset (A ⊆ B means ∀ x, x ∈ A → x ∈ B)
example (h : ∀ x, x ∈ s → x ∈ t) : s ⊆ t := h

-- Set equality via extensionality
example (s t : Set α) : s ∩ t = t ∩ s := by
  ext x
  simp [and_comm]

-- Union/intersection
#check Set.mem_union    -- x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t
#check Set.mem_inter_iff -- x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t
```

### Number theory

```lean
-- Natural induction
theorem sum_to_n (n : Nat) : 2 * (Finset.range (n+1)).sum id = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ]; omega

-- Divisibility (x ∣ y means ∃ k, y = x * k)
example : 3 ∣ 12 := ⟨4, rfl⟩
#check Nat.dvd_trans  -- a ∣ b → b ∣ c → a ∣ c

-- omega for linear arithmetic
example (x y : Nat) (h : x < y) : x + 1 ≤ y := by omega
```

### Algebraic proofs

```lean
-- ring tactic for polynomial identities
example (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring
example (a b : ℝ) : (a - b) * (a + b) = a^2 - b^2 := by ring

-- field_simp for fractions
example (a b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) : 
    a / b + a / c = a * (b + c) / (b * c) := by
  field_simp
  ring

-- abel for abelian groups
example [AddCommGroup G] (a b c : G) : a + b + c = c + b + a := by abel
```

### Inequalities

```lean
-- Transitivity lemmas
example (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := le_trans h1 h2
example (h1 : a < b) (h2 : b ≤ c) : a < c := lt_of_lt_of_le h1 h2

-- linarith for linear arithmetic
example (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) 
    (h3 : 12*y - 4*z < 0) : False := by linarith

-- positivity
example (a : ℝ) : 0 ≤ a^2 := by positivity
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by positivity

-- gcongr for monotonicity
example (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by gcongr

-- calc for inequality chains
example (a b : ℝ) : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ (a - b)^2 := sq_nonneg (a - b)
  calc 2*a*b = a^2 + b^2 - (a - b)^2 := by ring
           _ ≤ a^2 + b^2 := by linarith
```

---

## Type classes and mathematical structures

### Typeclass basics

Classes enable ad-hoc polymorphism through automatic instance resolution:

```lean
class Add (α : Type) where
  add : α → α → α

instance : Add Nat where
  add := Nat.add

-- Instance arguments use square brackets
def double {α : Type} [Add α] (x : α) : α := Add.add x x

-- Lean automatically finds instances
#eval double 5  -- finds Add Nat instance
```

### Mathematical typeclass hierarchy

**Algebraic structures** (multiplicative naming):
```
Semigroup → Monoid → Group → CommGroup
                  ↘ CommMonoid ↗
```

**Ring hierarchy**:
```
Semiring → Ring → CommRing → Field
                ↘ DivisionRing ↗
```

**Order hierarchy**:
```
LE/LT → Preorder → PartialOrder → LinearOrder
```

**Common typeclasses**:

| Class | Purpose |
|-------|---------|
| `Add`, `Mul`, `Neg`, `Inv` | Basic operations |
| `Zero`, `One` | Identity elements |
| `AddCommGroup` | Abelian additive group |
| `Ring`, `CommRing`, `Field` | Ring structures |
| `Module R M` | R-module structure on M |
| `Fintype` | Finite type with enumeration |
| `Decidable` | Computable truth value |
| `TopologicalSpace` | Open set structure |

### Defining custom structures

```lean
-- Pattern: structure + instances
structure MyGroup (G : Type*) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  inv_mul_cancel : ∀ a, mul (inv a) a = one

-- Make it work with standard notation
instance (g : MyGroup G) : Mul G where mul := g.mul
instance (g : MyGroup G) : One G where one := g.one
```

### Coercions

```lean
-- ↑ notation for explicit coercion
def n : Nat := 5
def i : Int := ↑n  -- Nat coerced to Int

-- Common Mathlib coercions
-- Nat → Int, List → Set, Subtype → parent type
```

---

## Lean 4 vs Lean 3 quick reference

| Feature | Lean 3 | Lean 4 |
|---------|--------|--------|
| Lambda | `λ x, f x` | `fun x => f x` |
| Tactic mode | `begin ... end` | `by ...` (indentation-based) |
| Tactic separator | `,` | newline or `;` |
| Focus | `{ }` | `·` |
| Refine | `refine` | `refine'` |
| Cases | `cases` | `cases'` or new syntax |
| Rewrite | `rw h` | `rw [h]` (brackets required) |
| Holes | `_` | `?_` for goals, `_` for inference |
| Structure update | `{..s, field := v}` | `{s with field := v}` |

---

## Debugging and troubleshooting

### Essential commands

```lean
#check expr            -- show type
#check @func           -- show all arguments including implicits
#print def             -- show definition  
#print axioms thm      -- show axioms used
#eval expr             -- evaluate expression
#reduce expr           -- kernel reduction (slow)
```

### Common errors and fixes

| Error | Meaning | Fix |
|-------|---------|-----|
| `unknown identifier` | Name not found | Check spelling, imports, use qualified name |
| `type mismatch` | Wrong type | Add type annotations, use `@`, check instances |
| `failed to synthesize instance` | Typeclass not found | Import module, provide instance explicitly |
| `function expected` | Applied non-function | Check parentheses, types |

### Debugging options

```lean
set_option pp.explicit true     -- show implicit arguments
set_option pp.universes true    -- show universe levels
set_option pp.all true          -- show everything
set_option trace.Meta.synthInstance true  -- trace typeclass search
```

### Placeholders

```lean
sorry     -- placeholder proof (shows warning)
_         -- hole for inference
?_        -- named hole, creates subgoal
?myGoal   -- named subgoal for later
```

---

## Best practices and style

### Idiomatic style

- **100 character line limit**
- **2-space indentation** for proof content
- **Terminal simps are fine**; non-terminal simps should use `simp only [...]`
- **Use `simp?`** to generate minimal, stable simp calls
- **Prefer tactic mode** for complex proofs, term mode for simple ones

### Documentation

```lean
/-- This is a docstring for a declaration. -/
theorem myTheorem : P := ...

/-! 
# Section Header

This is a module docstring for documentation.
-/
```

### Performance tips

- Replace expensive `simp` with `simp only [specific_lemmas]`
- Use `decide` for small decidable props, `native_decide` for larger ones
- Cache expensive computations with `have`
- Provide typeclass instances explicitly when resolution is slow

---

## Quick reference card

### Most-used tactics

```lean
intro h              -- introduce hypothesis
apply f              -- apply function/lemma
exact e              -- provide exact proof term
rw [h]               -- rewrite with equation
simp [h]             -- simplify
cases h              -- case analysis
induction n          -- induction
constructor          -- apply constructor
use e                -- provide existential witness
obtain ⟨x, hx⟩ := h  -- destruct existential
have h : P := pf     -- intermediate result
calc a = b := h1     -- calculational proof
       _ = c := h2
ring                 -- polynomial equality
linarith             -- linear arithmetic
omega                -- integer/nat arithmetic
exact?               -- search for closing lemma
```

### Anonymous constructor `⟨...⟩`

```lean
⟨a, b⟩        -- And.intro, Exists.intro, structure constructor
h.1, h.2      -- And.left, And.right (or h.left, h.right)
```

### Import patterns

```lean
import Mathlib.Tactic        -- tactics only
import Mathlib.Data.Nat.Basic -- specific module
import Mathlib                -- everything (slow)
```