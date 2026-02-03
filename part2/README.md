# Part 2: Graded Mathematics (Primary)

**This is where we live.** Building mathematics directly in [0,1] credences.

## The Vision

We work in graded credences as the PRIMARY setting:
- Graded propositions (not binary truth)
- Graded predicates (not crisp sets)
- Graded inference (not binary derivation)
- Graded proofs (credence approaching 1)

**Binary/crisp is NOT the foundation. It's a degenerate special case.**

## Files

- `01-graded-propositions.md` — Propositions AS credences
- `02-graded-predicates.md` — Non-crisp sets
- `03-graded-inference.md` — Reasoning with credences
- `04-graded-quantifiers.md` — Forall and exists in graded setting
- `05-graded-proofs.md` — What "proof" means when truth is graded
- `06-mathematics.md` — Building math on graded foundation

## Why Graded is Better

| Binary Logic | Cred |
|--------------|------|
| Paradoxes break the system | Paradoxes (liar) → fixed points (cred 0.5) |
| Self-reference problematic | Self-negating reference works naturally |
| Ex falso: nonsense follows | No ex falso (unconstrained, not trivial) |
| Conditioning undefined at 0 | Conditioning unconstrained at 0 |

## The Key Insight

Self-negating sentences like the liar ("This sentence is false") have cred = 0.5.
This is a meaningful fixed point, not a paradox.

**Important:** Godel sentences are NOT self-negating. "This is unprovable" is not the same as "This is false." Cred handles the liar; Godel's incompleteness applies to any system strong enough to encode arithmetic, including Cred if extended.
