# Part 2: Credence Foundation Without Crisp Sets

Working directly in graded credences without collapsing to Boolean.

## The Goal

Build mathematics **staying in [0,1]** as long as possible:
- Graded propositions
- Graded predicates (not crisp sets)
- Graded inference
- Graded proofs

Boolean/crisp structures are limiting cases we can recover, but not where we live.

## Files

- `01-graded-propositions.md` - Propositions AS credences
- `02-graded-predicates.md` - Fuzzy sets / credence predicates
- `03-graded-inference.md` - Reasoning with credences
- `04-graded-quantifiers.md` - Forall and exists in graded setting
- `05-graded-proofs.md` - What "proof" means when truth is graded
- `06-mathematics.md` - Building math on graded foundation

## The Key Shift

| Classical | Cred |
|-----------|------|
| Proposition is true or false | Proposition has credence in [0,1] |
| Set membership is yes/no | Membership has degree in [0,1] |
| Proof establishes truth | Proof approaches credence 1 |
| Undecidable = neither provable nor refutable | Undecidable = credence stays at ½ |

## Why Stay Graded?

1. **More information**: [0,1] has more distinctions than {0,1}
2. **Undecidability visible**: Gödel sentences have credence ½
3. **Paradoxes dissolve**: Liar sentence has credence ½ (fixed point)
4. **Probability-native**: Chain rule works directly
5. **Robust**: Partial contradictions don't explode
