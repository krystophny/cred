# Building Mathematics on Cred

## The Vision

Build mathematics in the graded setting:
- Numbers, functions, structures with graded properties
- Theorems with credences
- Proofs that increase credence

Crisp mathematics (classical) is a special case.

## Natural Numbers

The natural numbers ℕ = {0, 1, 2, ...} exist with credence 1.

```
cred(n ∈ ℕ) = 1  for n = 0, 1, 2, ...
```

Arithmetic operations are crisp:
```
cred(2 + 3 = 5) = 1
cred(2 + 3 = 6) = 0
```

Basic arithmetic is fully graded to {0, 1}. The graded structure appears in:
- Statements ABOUT numbers
- Properties that may be uncertain
- Conjectures

## Graded Properties of Numbers

```
Prime : ℕ → {0, 1}           -- crisp, decidable
Prime(7) = 1
Prime(6) = 0

"Interesting" : ℕ → [0, 1]    -- graded, subjective
Interesting(1729) = 0.9       -- taxicab number
Interesting(1730) = 0.1       -- unremarkable

Goldbach : ℕ → [0, 1]         -- graded, unknown
Goldbach(n) = cred(n is sum of two primes | n even, n > 2)
Goldbach(4) = 1               -- verified: 4 = 2 + 2
Goldbach(10^100) = 0.999...   -- unverified but very likely
```

## Functions

A function f : A → B is a predicate:
```
f : A × B → [0, 1]
f(a, b) = credence that f(a) = b
```

A **crisp function** has f(a, b) ∈ {0, 1} and exactly one b with f(a, b) = 1 for each a.

A **graded function** (or relation) allows intermediate values.

## Sets vs Predicates

Classical math: Sets are primitive, defined by membership.

Cred math: Predicates are primitive. "Sets" are crisp predicates.

```
S : X → [0, 1]   -- predicate

S is a "set" iff ∀x: S(x) ∈ {0, 1}   -- crisp
```

## Theorems

A theorem is a proposition with credence 1:
```
cred(Pythagorean theorem) = 1
cred(Fermat's Last Theorem) = 1  (since Wiles' proof)
```

A conjecture is a proposition with high but not certain credence:
```
cred(Riemann Hypothesis) ≈ 0.99  (strong evidence, no proof)
cred(P ≠ NP) ≈ 0.9
```

## Proofs as Credence Certificates

A proof of P is evidence that cred(P) = 1.

```
Proof of P:
  1. Start from axioms (cred = 1)
  2. Apply valid inference rules
  3. Reach P with cred = 1
```

The proof is a certificate that can be checked.

## Axioms

Axioms are propositions we ASSIGN credence 1:
```
cred(Axiom of extensionality) := 1  (by fiat)
cred(Axiom of choice) := ???        (controversial)
```

In Cred, we can be honest about axiom confidence:
```
cred(ZFC is consistent) ≈ 0.999  (no proof, strong evidence)
```

## Definitions

Definitions introduce new predicates:
```
Define Even(n) := (n mod 2 = 0)
```

Definitions don't change credences; they introduce names.

## Structures

Algebraic structures (groups, rings, etc.) are predicates on tuples:
```
Group : (G, *, e, inv) → [0, 1]

Group(G, *, e, inv) =
  cred(* is associative) *
  cred(e is identity) *
  cred(inv gives inverses)
```

A crisp group has Group(...) ∈ {0, 1}.
An approximate group might have Group(...) ≈ 0.9.

## Continuity and Limits

Continuity in Cred:
```
Continuous(f, x) = cred(∀ε>0. ∃δ>0. |y-x|<δ → |f(y)-f(x)|<ε)
```

For well-defined functions, this is crisp.
For approximate or uncertain functions, it can be graded.

## The Graded Continuum

Real numbers ℝ exist with credence 1 (we define them).

But properties of reals can be graded:
```
cred(π is normal) ≈ 0.99    -- believed but unproven
cred(CH is true) = ???       -- independent of ZFC
```

## Independence Results

Gödel/Cohen: CH is independent of ZFC.

In Cred:
```
cred(CH | ZFC) = undefined/unconstrained
```

There's no fact of the matter within ZFC. The credence is genuinely indeterminate.

This is different from "unknown" (cred ≈ 0.5). It's "not determined by the axioms."

## Summary: What Changes?

| Classical | Cred |
|-----------|------|
| Statements are true/false | Statements have credence [0,1] |
| Proofs establish truth | Proofs establish cred = 1 |
| Conjectures are unknown | Conjectures have cred ∈ (0,1) |
| Independent = unprovable | Independent = cred unconstrained |
| One mathematics | Parameterized by credence assignments |

The core mathematics (arithmetic, algebra, analysis) remains the same at credence 1. The difference is in how we handle uncertainty, conjectures, and independence.
