# Annotated Bibliography: Prior Art for the Cred Project

Reference list for the product De Morgan triplet, chain-rule conditioning, and
the no-explosion reading. Grouped by tradition. Each entry states what the work
contributes and how Cred relates to it. Citation keys point to
`singlepaper/refs.bib`. Cred's own commitments, for contrast: conjunction is the
product t-norm `c1 (x) c2 = c1 c2` with De Morgan dual disjunction; `(x)` is an
algebraic operation, not a rule for `cred(A and B)`; conditioning is primitive
via the chain rule `cred(A|B) (x) cred(B) = cred(A and B)`, never a ratio; at
`cred(B) = 0` the chain rule constrains nothing, so there is no explosion.

## Fuzzy and t-norm logic

- `hajek1998` Hajek, *Metamathematics of Fuzzy Logic* (1998). BL, the logic of
  all continuous t-norms and their residua. Cred keeps the product t-norm for
  `(x)` but bars it from defining `cred(A and B)` and replaces residuated
  implication with a primitive conditional.
- `esteva2001` Esteva and Godo, MTL (2001). The logic of left-continuous
  t-norms, weakest common ground below BL. Cred settles the "which t-norm"
  question (product) and answers implication outside truth-functional logic.
- `klement2000` Klement, Mesiar, Pap, *Triangular Norms* (2000). The reference
  monograph on t-norms as operations on `[0,1]`. Cred uses one member (product,
  strict Archimedean) and its De Morgan dual, and adds the conditioning layer
  the monograph does not treat.
- `cintula2011` Cintula, Hajek, Noguera, *Handbook of Mathematical Fuzzy Logic*
  (2011). Survey of the t-norm logics below BL and their extensions. Locates
  Cred's algebra inside the t-norm family.
- `lukasiewicz1920` Lukasiewicz (1920), `godel1932` Godel (1932). The two
  rejected collapse targets. Cred proves no Godel collapse and no Lukasiewicz
  collapse compatible with its congruence (`no_godel_collapse`,
  `no_luk_collapse`), selecting product.
- `zadeh1965` Zadeh, *Fuzzy sets* (1965); `goguen1969` Goguen, *The logic of
  inexact concepts* (1969). Graded membership and degree-valued connectives, the
  origin of `[0,1]` truth. Cred reads `[0,1]` as credence, not membership.

## Paraconsistent, Kleene, LP, K3, RM3

- `kleene1952` Kleene, *Introduction to Metamathematics* (1952). Strong Kleene
  K3 on `{0, 1/2, 1}`, third value "undefined", designates only 1, no
  tautologies. Cred's collapse sends `[0,1]` onto the Kleene three-element
  quotient (`kleeneCongruence`, unique by `three_element_quotient_unique`) and
  recovers K3 as the certainty reading (`k3_formula_bridge`, `k3_no_tautology`).
- `priest1979` Priest, *The Logic of Paradox* (1979); `asenjo1966` Asenjo
  (1966). LP: same tables as K3, but 1/2 is designated, so explosion fails. Cred
  recovers LP as the positivity reading (`lp_formula_bridge`, `lp_no_explosion`)
  and blocks explosion through unconstrained conditioning at zero evidence
  (`cred_no_ex_falso`), not a designated glut value.
- `avron1991` Avron, *Natural 3-valued logics* (1991). RM3 and the natural
  three-valued matrices; RM3's internal arrow has an explosion row. Cred records
  this (`rm3_ex_falso`) and contrasts it with external conditioning that never
  explodes.
- `belnap1977` Belnap, *A useful four-valued logic* (1977); `priest2008` Priest,
  *Introduction to Non-Classical Logic* (2008); `anderson1975` Anderson and
  Belnap, *Entailment* (1975). The four-valued and relevance routes to
  rejecting `A and not-A |- B`. Cred reaches no-explosion through the
  conditioning primitive instead (`labelled_no_ex_falso`,
  `Kernel.no_ex_falso_certificate`).

## Cox, Jaynes, and the conservative reading

- `cox1946` Cox (1946); `cox1961` Cox, *The Algebra of Probable Inference*
  (1961); `jaynes2003` Jaynes, *Probability Theory: The Logic of Science*
  (2003). Plausibility derived from desiderata; the product rule
  `p(AB|C) = p(A|BC) p(B|C)` is the chain rule, Cred's closest classical
  relative. Cred adopts the product rule as primitive, writes it as
  `cred(A|B) (x) cred(B) = cred(A and B)`, and drops the division step, so
  `cred(B) = 0` is unconstrained rather than ill-posed.
- `halpern1999` Halpern, *A Counterexample to Theorems of Cox and Fine* (1999).
  A finite plausibility model satisfies Cox's functional equations without being
  isomorphic to probability; the proof needs a dense domain and smoothness. Cred
  takes the conservative reading as a design license: it adopts the chain rule
  without the universality and smoothness axioms Halpern shows are load-bearing,
  and treats the resulting freedom as a feature.

## de Finetti and primitive conditional probability

- `definetti1936` de Finetti (1936); `definetti1937` de Finetti (1937).
  Conditional event `A|H` as a three-valued object, void when `H` fails; the
  void bet leaves `P(A|H)` unconstrained by coherence. Cred's
  `conditioning_zero_any` is the algebraic chain-rule analogue of the void bet,
  a theorem of the `(x)` equation rather than a betting stipulation.
- `renyi1955` Renyi (1955); `popper1959` Popper (1959); `krauss1968` Krauss
  (1968); `dubins1975` Dubins (1975). Primitive conditional probability:
  `p(A|B)` axiomatized directly, well behaved at `p(B) = 0`. Cred shares the
  "conditional first" stance on `[0,1]` credences with a product chain rule, and
  leaves `cred(A|B)` fully free at zero rather than fixing it by a Popper-function
  axiom.
- `coletti2002` Coletti and Scozzafava, *Probabilistic Logic in a Coherent
  Setting* (2002). Probabilistic logic with conditioning as primitive in the
  coherence sense. Cred's admissible-set conditioning is a precise analogue
  without the full coherence apparatus.
- `gilio2013` Gilio and Sanfilippo (2013); `gilio2014` Gilio and Sanfilippo
  (2014); `gilio2021` Gilio and Sanfilippo, *Compound Conditionals,
  Frechet-Hoeffding Bounds and Frank t-Norms* (2021). Conjunction of conditional
  events as a conditional random quantity, bounded by Frechet-Hoeffding, with
  Frank t-norms interpolating between the bounds. Cred's admissible set gives the
  same Frechet trichotomy (`Cond`, `cond_singleton_of_pos`, `cond_nonempty_iff`)
  but fixes the product t-norm rather than ranging over Frank t-norms.
- `flaminio2020conditionals` Flaminio, Godo, Hosni (2020). Boolean algebras of
  conditionals linking probability and logic. Algebraic neighbor to Cred's
  conditional layer.

## Imprecise and credal probability

- `walley1991` Walley, *Statistical Reasoning with Imprecise Probabilities*
  (1991). Lower and upper previsions, coherent lower prevision as the envelope of
  a credal set; conditioning on lower-probability-zero events via regular
  extension can return the vacuous `[0,1]`. Cred's admissible set `{c | c (x) e = j}`
  is a precise analogue: singleton at positive evidence, full interval at zero
  (`cond_zero_zero_univ`), with imprecision only at the conditional.
- `troffaes2014` Troffaes and de Cooman, *Lower Previsions* (2014); `augustin2014`
  Augustin, Coolen, de Cooman, Troffaes, *Introduction to Imprecise
  Probabilities* (2014). Field references: desirable gambles, lower previsions,
  credal sets shown equivalent. Cred carries no set of measures, so the
  equivalence has no Cred analogue.
- `debock2015` De Bock and de Cooman (2015); `wheeler2021` Wheeler and Cozman
  (2021). Conditioning and updating at lower probability zero; imprecision of
  full conditional probabilities. The imprecise-probability statement of the
  zero-evidence problem Cred solves algebraically.

## Copulas and Frechet-Hoeffding bounds

- `sklar1959` Sklar (1959). Every joint `H(x,y) = C(F(x), G(y))` for a copula
  `C`; the copula carries all dependence. Cred fixes `(x)` to the
  independence copula and supplies the joint explicitly when dependence matters.
- `nelsen2006` Nelsen, *An Introduction to Copulas* (2006). Frechet-Hoeffding
  bounds `W <= C <= M`, independence copula `Pi(u,v) = uv`. Cred uses `W` and `M`
  as the admissible range for the conditional; `min_copula_unique` and
  `copula_idempotent_unique` pin the relevant uniqueness, with min (`M`) the
  unique idempotent copula and product the generic interior case.
- `dhaene2002` Dhaene et al. (2002). Comonotonicity, the upper Frechet bound `M`
  in actuarial use. Application context for the boundary copula.

## Practical probabilistic and soft-logic systems

These are deployed inference and learning engines. Cred does not subsume or
replace them; it answers a different question (no-explosion conditioning over
credences). The mapping locates Cred's design choices against theirs.

- `bach2017` Bach, Broecheler, Huang, Getoor, *Hinge-Loss MRFs and Probabilistic
  Soft Logic* (2017); `kimmig2012` Kimmig et al. (2012). PSL: per-atom soft truth
  degrees in `[0,1]` plus a hinge-loss MRF density; conjunction is the
  Lukasiewicz t-norm `max(0, a+b-1)`, convex MAP inference. Cred's conjunction is
  the product t-norm with De Morgan dual, treats dependence by an explicit joint,
  and has primitive chain-rule conditioning PSL does not model; PSL has a
  probability layer Cred does not aim to provide.
- `richardson2006` Richardson and Domingos, *Markov Logic Networks* (2006). MLN:
  per-formula real weights plus query marginals, a log-linear distribution over
  crisp worlds; conditioning is Bayesian and breaks at probability-zero evidence.
  Cred's chain-rule conditioning leaves `cred(A|B)` unconstrained at `cred(B) = 0`
  instead.
- `sato1995` Sato, distribution semantics and PRISM (1995); `deraedt2007` De
  Raedt, Kimmig, Toivonen, *ProbLog* (2007); `fierens2015` Fierens et al. (2015);
  `deraedt2015` De Raedt and Kimmig, *Probabilistic (Logic) Programming Concepts*
  (2015). ProbLog: per-fact probabilities, independence of base facts assumed,
  joint over facts a literal product of marginals, dependence only via rules;
  conditioning is Bayesian (0/0 at impossible evidence). Cred makes no global
  independence assumption and lets the modeller supply the joint; its product is
  algebraic, not an independence claim.
- `pearl1988` Pearl, *Probabilistic Reasoning in Intelligent Systems* (1988).
  Bayesian networks: DAG chain-rule factorization with Markov independences,
  single joint, Bayesian conditioning undefined at zero-probability evidence.
  Cred shares the chain-rule shape but keeps it primitive and unconstrained at
  zero.
- `cozman2000` Cozman, *Credal Networks* (2000); `maua2020` Maua and Cozman
  (2020); `marinescu2021` Marinescu et al., *Logical Credal Networks* (2021).
  Credal networks: local credal sets, lower and upper bounds via optimization,
  more graceful zero-evidence handling but still probability-bound machinery. The
  closest neighbor in spirit; Cred's interval-valued admissible sets are
  comparable, but Cred is an algebra with primitive conditioning, not a credal
  network.

## Prior-art coverage matrix

| Tradition | Key reference(s) | Cred reuse | Cred difference | Paper location |
|---|---|---|---|---|
| Fuzzy / t-norm | `hajek1998`, `esteva2001`, `klement2000`, `cintula2011` | product t-norm for `(x)`, De Morgan dual | `(x)` is algebraic, not a rule for `cred(A and B)`; no residuated implication | Setup; Propositional Bridge |
| Product / Godel / Luk | `lukasiewicz1920`, `godel1932` | product as collapse target | proves no Godel/Lukasiewicz collapse (`no_godel_collapse`, `no_luk_collapse`) | Kleene Collapse and Congruence |
| Paraconsistent / Kleene-LP-K3 | `kleene1952`, `priest1979`, `asenjo1966`, `avron1991`, `belnap1977`, `priest2008` | Kleene quotient, K3/LP readings | no-explosion via zero-evidence conditioning, not a glut value (`cred_no_ex_falso`) | Propositional Bridge; Kleene Collapse |
| Cox / Jaynes | `cox1946`, `cox1961`, `jaynes2003`, `halpern1999` | chain-rule product rule as primitive | no division; drops universality/smoothness axioms; free at `cred(B)=0` | Chain-Rule Conditioning |
| de Finetti / primitive conditional | `definetti1936`, `definetti1937`, `renyi1955`, `popper1959`, `krauss1968`, `dubins1975`, `coletti2002` | conditional-first stance, void-at-zero | algebraic chain rule on `[0,1]`; `cred(A|B)` fully free at zero (`conditioning_zero_any`) | Chain-Rule Conditioning; Conditional Bridge |
| Compound conditionals / Frank | `gilio2013`, `gilio2014`, `gilio2021` | Frechet trichotomy for the conditional | fixes product t-norm, not a Frank family; explicit supplied joint | Conditional Bridge |
| Imprecise / credal | `walley1991`, `troffaes2014`, `augustin2014`, `debock2015`, `wheeler2021` | admissible set as precise interval analogue | no carried set of measures; imprecision only at the conditional, only from zero | Conditional Bridge; Update |
| Copulas | `sklar1959`, `nelsen2006`, `dhaene2002` | independence copula for `(x)`, `W`/`M` as bounds | min the unique idempotent copula (`min_copula_unique`); explicit joint for dependence | Chain-Rule Conditioning |
| PSL / HL-MRF | `bach2017`, `kimmig2012` | none (contrast only) | product not Lukasiewicz conjunction; primitive conditioning; no MRF density layer | Related Systems |
| MLN | `richardson2006` | none (contrast only) | chain-rule conditioning vs Bayesian; unconstrained at zero vs 0/0 | Related Systems |
| ProbLog / distribution semantics | `sato1995`, `deraedt2007`, `fierens2015`, `deraedt2015` | none (contrast only) | no global independence; explicit joint; algebraic product not independence claim | Related Systems |
| Bayesian networks | `pearl1988` | chain-rule factorization shape | conditioning primitive and unconstrained at zero | Related Systems |
| Credal networks | `cozman2000`, `maua2020`, `marinescu2021` | interval-valued admissible sets as comparison | an algebra with primitive conditioning, not a credal network | Related Systems |
