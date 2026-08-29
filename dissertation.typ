// AMS template
#import "custom-ams.typ": ams-article, proof

#import "@preview/ctheorems:1.1.3": *
#show: thmrules.with(qed-symbol: $square$)
#let mythmbox = thmbox.with(
  breakable: true,
)
#let theoremthmbox = mythmbox.with(
  fill: rgb("#ffefff"),
  breakable: false,
)
#let examplethmbox = mythmbox.with(
  fill: rgb("#f3f3ff"),
  breakable: true,
)
#let definitionthmbox = mythmbox.with(
  fill: rgb("#eeffee"),
)
#let notethmbox = mythmbox.with(
  inset: 0pt,
)
#let remarkthmbox = mythmbox.with(
  inset: 0pt,
)
#let theorem = theoremthmbox("common", "Theorem")
#let proposition = theoremthmbox("common", "Proposition")
#let lemma = theoremthmbox("common", "Lemma")
#let corollary = theoremthmbox("common", "Corollary", base: "common")
#let definition = definitionthmbox("common", "Definition")
#let example = examplethmbox("common", "Example")
#let remark = remarkthmbox("common", "Remark")
#let note = notethmbox("common", "Note")
#let axiom = notethmbox("common", "Axiom")
#let proof = thmproof(
  "proof",
  "Proof",
  stroke: (left: 0.2pt + black),
  radius: 0pt,
  inset: (left: 10pt),
)


// Proof trees
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set

// Diagrams
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

// Helper functions
#let linkref(target, supplement: none) = {
  link(target, ref(target, supplement: supplement))
}
#let scr(it) = text(
  features: ("ss01",),
  box($cal(it)$),
)
#let pair(..args) = {
  sym.chevron.l
  args.pos().join([,#h(0.16em)])
  sym.chevron.r
}

// Formatting
#show selector(link).or(cite): it => {
  set text(navy)
  underline(it)
}
#set text(12pt)
#set par(
  leading: 0.85em,
  spacing: 0.85em,
)
#set page(margin: (
  left: 77pt,
  right: 77pt,
  top: 80pt,
  bottom: 60pt,
))
#show math.equation.where(block: false): box

// Citations
// #let citation-style = "harvard-cite-them-right"
// #let citation-style = "./american-mathematical-society-label.csl"
// #let citation-style = "./american-mathematical-society-numeric.csl"
#let citation-style = "ieee"
#set cite(style: citation-style)

// Template parameters
#show: ams-article.with(
  title: [
    A title],
  authors: (
    (
      name: "Jo MacMahon",
      department: [Department of Mathematics],
      organization: [University of Manchester],
      paper-size: "a4",
      location: [Oxford Rd, Manchester M13 9PL, United Kingdom],
      email: "jo.macmahon@postgrad.manchester.ac.uk",
      // url: "https://personalpages.manchester.ac.uk/postgrad/jo.macmahon",
    ),
  ),
  abstract: [
    An abstract
  ],
  bibliography: bibliography(
    "dissertation.bib",
    style: citation-style,
  ),
)

// #set text(font: "Libertinus Serif")

// Numbering
#show ref: it => {
  let eq = math.equation
  let el = it.element
  if el != none and el.func() == eq and el.numbering != none {
    // Override equation references.
    numbering(
      el.numbering,
      ..counter(eq).at(el.location()),
    )
  } else {
    // Other references as usual.
    it
  }
}

#show: body => {
  for elem in body.children {
    if elem.func() == math.equation and elem.block {
      let numbering = if "label" in elem.fields().keys() { "(1)" } else { none }
      set math.equation(numbering: numbering)
      elem
    } else {
      elem
    }
  }
}

#pagebreak()

// Body

#let sd = $thin . thin$
#let UU = $cal(U)$
#let peq = $equiv$
#let equiv = $tilde.eq$
#let rec = $sans("rec")$
#let ind = $sans("ind")$
#let one = $bold(1)$
#let zero = $bold(0)$
#let ctx = $sans("ctx")$
#let Fin = $"Fin"$
#let inl = $sans("inl")$
#let inr = $sans("inr")$
#let succ = $sans("succ")$
#let refl = $sans("refl")$
#let qinv = $sans("qinv")$
#let isequiv = $sans("isequiv")$
#let ap = $sans("ap")$
#let apd = $sans("apd")$
#let transport = $sans("transport")$
#let code = $sans("code")$
#let encode = $sans("encode")$
#let decode = $sans("decode")$
#let happly = $sans("happly")$
#let funext = $sans("funext")$
#let isSet = $sans("isSet")$
#let is1Type = $sans("is1Type")$
#let bigrule = (..args) => {
  let judgments = args.pos()
  let kwargs = args.named()
  rule(
    ..judgments.map(j => block(
      inset: (left: 0em, right: 0em, top: 0em, bottom: 0.27em),
      j,
    )),
    ..kwargs,
  )
}
#let pt(label: none, ..args) = {
  if label != none {
    [#math.equation(
        block: true,
        numbering: "(1)",
        ..args,
      )
      #std.label(label)
    ]
  } else {
    math.equation(
      block: true,
      ..args,
    )
  }
  v(0.5em)
}

= Type theory

Type theory is a logical system, encoding *types* and *terms*, which is used as a foundation
of mathematics. Loosely, a type may be considered as an object which contains elements,
similar to a set in set theory. However, type theory is distinct from set theory in that
every object in type theory has a type. In mathematics, we might make statements such as
_"Let $n$ be a natural number. Then $n$ has a successor."_ What is meant by this in a
set-theoretic context is something like "let $n$ denote something", and then "if $n in NN$,
then $n$ has a successor". In type theory this is not allowed: every object we consider must
be constrained by its type. Supposing we have defined a type $NN$ of natural numbers (which
we will do later), we would write $n : NN$ to indicate that $n$ is a natural number. We may
then proceed with the claim about its successor.

== Terms

As type theory is a syntactic system, we define the construction of its terms. In our
presentation the basic terms may be _variables_, _primitive constants_ or _defined
constants_. Terms are formed according to the rule

$
  t ::= x | lambda (x : t) sd t | t(t') | c | f.
$

Here, $x$ stands for any variable, $t$ is any term, $c$ is any primitive constant and $f$ is
any defined constant.

The distinction between primitive and defined constants is that primitive constants are used
to encode new syntax, and will not be able to be reduced by some definition, while defined
constants are taken to be equivalent to some term (by a judgmental equality, which we will
introduce in the next subsection) and thus able to be eliminated or reduced.

The third term-forming rule, $t(t')$, represents function application, and we take the
convention that it associates to the left, i.e. $t_1(t_2)(t_3)$ means $(t_1(t_2))(t_3)$. We
will also write repeated application as $t_1(t_2, t_3)$, for reasons which will become clear
soon.

Note that we do not distinguish between the language of types and the language of terms.
Since we will be presenting a dependent type theory, types may depend on terms and vice
versa, so they are part of the same language.

== Judgments

We introduce three kinds of judgments in our presentation of type theory, namely *context
judgments*, *typing judgments* and *judgmental equalities*.

We will present context judgments in the next subsection, but for now suffice to say they
have the form
$
  Gamma ctx.
$

Typing judgments are of the form
$
  t : A
$
which is to be read as "the term $t$ is of the type $A$". Typing judgments are useful for
demonstrating the existence of a term of a particular type.

The final kind of judgment is the judgmental equality, which takes the form
$
  t peq t' : A.
$
Sometimes the type annotation "$: A$" will be omitted when it is clear from context. This
judgment is a metatheoretic equality, which is to be contrasted with "internal" equality
which we will introduce later. This is the reason we use the symbol $peq$ in place of the
more standard $=$, which we reserve for use in identity types later. This judgment says that
whenever we see the term $t$, we may rewrite it as $t'$ and vice versa.

We write deductive rules in the "proof tree" style, where antecedents are written above a
line and consequents below it:
#pt(prooftree(rule($cal(J)_1$, $cal(J)_2$, $cal(J)_3$)))
This deduction says that from the judgments $cal(J)_1$ and $cal(J)_2$ we may conclude
$cal(J)_3$.

== Universes and contexts<sec:universes-and-contexts>

In order to avoid a situation similar to Russell's paradox #cite(<coquand1992paradox>), we
define a hierarchy of *universes*, denoted

$ UU_0 quad UU_1 quad UU_2 quad ... quad UU_i quad ... $

/* TODO state that these are indexed by (metatheoretic) natural numbers, not all ordinals */

Each $UU_i$ is an element of $UU_(i + 1)$, and furthermore every universe contains all the
types contained in previous universes. I.e. if $x : UU_i$ then $x : UU_j$ for all $j >= i$.
This is known as the *cumulative* property. When we say $A$ is a type, what we mean is that
$A : UU_i$ for some universe $UU_i$. When working with (a finite number of) types in
different universes, the cumulative property guarantees that we can always find a universe
in which all our types are present.

A *context* is a (possibly empty) ordered list of distinct variables and their types, for
example $x_1 : A_1, x_2 : A_2$. Since types are terms, each type may use variables occurring
before it in the list, hence the order being important. Contexts are denoted by an uppercase
Greek letter, usually $Gamma$ or $Delta$. The judgment that $Gamma$ is a well-formed context
is denoted $Gamma ctx$, and the empty context is denoted $dot$.

Contexts appear on the left-hand side of a $tack$ symbol, with a judgment on the right, as
in
$
  Gamma tack cal(J).
$
This is to be read as "in the context $Gamma$, $cal(J)$ holds", and means that the judgment
$cal(J)$ contains variables and types declared in the context $Gamma$.

We have the following rules for universes and contexts.

#pt(rule-set(
  prooftree(rule($dot ctx$)),
  prooftree(rule(
    $x_1 : A_1, ..., x_(n-1) : A_(n-1) tack A_n : UU_i$,
    $(x_1 : A_1, ..., x_n : A_n) ctx$,
  )),
  prooftree(rule($Gamma ctx$, $Gamma tack UU_i : UU_(i+1)$)),
  prooftree(rule($Gamma tack A : UU_i$, $Gamma tack A : UU_(i+1)$)),
))

When working with formal constructions of type theory, there are (at least) two schools of
thought regarding contexts. One formulation #cite(<hottbook>, supplement: [Appendix A.2])
makes heavy use of explicit contexts and variable substitution, which change frequently from
deduction to deduction; the other formulation #cite(<hottbook>, supplement: [Appendix A.1])
keeps contexts fixed at the beginning of the proof, prefering the mechanics of function
application instead of variable substitution.

We proceed with the latter, since it is more familiar to dependently-typed programming
language theory. As a result, we will often leave contexts fairly implicit, using language
such as "for types $A : UU_i$ and elements $x : A$" to discursively define a context. Where
explicit manipulation of a context is required (for example in introducing a function by
capturing a variable in a $lambda$ expression), we will of course make a note of the change.
Moreover, in our proof trees, we will write the context explicitly as part of the judgment,
even if we will not do much manipulation of it.

== Structural rules

To begin with, we state some essential rules for working in type theory. These rules allow
us to manipulate terms and make judgments in a way which is natural for mathematicians.

The first rule says that the judgment $x : A$ may be derived from any context which contains
a variable $x$ of type $A$:
#pt(prooftree(rule(
  $(x_1 : A_1, ..., x_n : A_n) ctx$,
  $(x_1 : A_1, ..., x_n : A_n) tack x_i : A_i$,
  name: [Vble],
)))

We declare the following rules, *substitution* and *weakening* for typing judgments. The
first says that we may substitute terms for variables freely, and the second says that we
may introduce new variables while not affecting previous typing judgments.

#pt(rule-set(
  prooftree(
    rule(
      $Gamma tack t : A$,
      $Gamma, x : A, Delta tack s : B$,
      $Gamma, Delta[t slash x] tack s[t slash x] : B[t slash x]$,
      name: $"Subst"_1$,
    ),
  ),
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma, Delta tack t : B$,
    $Gamma, x : A, Delta tack t : B$,
    name: $"Wkg"_1$,
  )),
))

#note[In the rule $"Wkg"_1$, it may first seem as though there is a danger that the variable
  $x$ aliases with a variable present in $t$ or $B$, which may affect its truth. However,
  this is not a problem, since we require variables in contexts to be unique, meaning that
  $x : A$ cannot occur in $Gamma$ or $Delta$, and therefore not in $t$ or $B$.
]

The substitution and weakening rules have counterparts for judgmental equalities:

#pt(rule-set(
  prooftree(rule(
    $Gamma tack t : A$,
    $Gamma, x : A, Delta tack u peq v : B$,
    $Gamma, Delta[t slash x] tack u[t slash x] peq v[t slash x] : B[t slash x]$,
    name: $"Subst"_2$,
  )),
  prooftree(rule(
    $Gamma tack t peq s : A$,
    $Gamma, x : A, Delta tack u : B$,
    $Gamma, Delta tack u[t slash x] peq u[s slash x] : B[t slash x]$,
    name: $"Subst"_3$,
  )),
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma, Delta tack t peq s : B$,
    $Gamma, x : A, Delta tack t peq s : B$,
    name: $"Wkg"_2$,
  )),
))

The rule $"Subst"_2$ says that we may make substitutions on the "outside" of equalities, for
example we can go from $f(x) peq g(x)$ to $f(t) peq g(t)$; the rule $"Subst"_3$ says that we
may make substitutions on the "inside" of equalities, for example we can go from $x peq y$
to $f(x) peq f(y)$. The weakening rule is analogous to the weakening rule for typing
judgments.

We also assume that judgmental equality is an equivalence relation,
#pt(
  rule-set(
    prooftree(rule($Gamma tack t : A$, $Gamma tack t peq t : A$)),
    prooftree(rule(
      $Gamma tack t peq s : A$,
      $Gamma tack s peq t : A$,
    )),
    prooftree(rule(
      $Gamma tack t peq s : A$,
      $Gamma tack s peq u : A$,
      $Gamma tack t peq u : A$,
    )),
  ),
)
and that judgmental equality of types allows us to replace equal types for each other in
typing judgments and in judgmental equalities
#pt(
  rule-set(
    prooftree(rule($Gamma tack t : A$, $Gamma tack A peq B : UU_i$, $Gamma tack t : B$)),
    prooftree(rule(
      $Gamma tack t peq s : A$,
      $Gamma tack A peq B : UU_i$,
      $Gamma tack t peq s : B$,
    )),
  ),
)

Although these rules must be stated at least once, the process of reading (and writing)
proofs using them explicitly is rather tedious, and therefore we will use them implicitly
going forward. A demonstration of a proof using the structural rules for simply-typed lambda
calculus may be found in #cite(
  <mainproject>,
  // form: "prose",
  supplement: [Proposition 3.4.2],
).

== Data for types

The first part of this chapter will deal with introducing some useful types, which we will
use for the remainder of the thesis. These definitions follow a similar pattern. For each
new type we introduce, we give the following data:

#pad(left: 15pt)[
  / Formation rules: which specify how to make the type out of existing types.
  / Introduction rules: which specify how to construct terms of the new type.
  / Elimination rules: which specify how to reduce terms of the new type to terms of a
    simpler type.
  / Computation rules: which specify how elimination interacts with construction.
  / Uniqueness principle: (optional) which may impose constraints on the elements of a type
    by declaring certain elements to be equivalent under given conditions.
]

== Function types<sec:function-types>

The first type we will introduce is the (non-dependent) *function type*. We introduce a
primitive constant $c_(->)$, and we will write $c_(->)(A, B)$ using the syntactic sugar
$A -> B$.

Conceptually, functions take a value and return a value, so a term of type $A -> B$ takes a
value of type $A$ and returns a value of type $B$. Functions of multiple variables are
represented in *curried* form (after Haskell Curry), meaning that they are of type
$A -> (B -> C)$. That is, they are represented as a function which takes an $A$ and returns
another function of type $B -> C$. We will use the convention that $->$ associates to the
right, so the above type may be written as simply $A -> B -> C$.

Function terms are written using $lambda$ syntax, so $lambda (x : A) sd t$ is conceptually a
function which binds its input to the variable $x$, and returns the term $t$ with its free
occurrences of $x$ replaced with the input.

The data for function types and terms are given by the following rules:

#pt(rule-set(
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : UU_i$,
    $Gamma tack A -> B : UU_i$,
    name: [$->$-Form],
  )),
  prooftree(rule(
    $Gamma, x : A tack t : B$,
    $Gamma tack lambda(x : A) sd t : A -> B$,
    name: [$->$-Intr],
  )),
  prooftree(rule(
    $Gamma tack f : A -> B$,
    $Gamma tack t : A$,
    $Gamma tack f(t) : B$,
    name: [$->$-Elim],
  )),
  prooftree(rule(
    $Gamma tack B : UU_i$,
    $Gamma, x : A tack t : B$,
    $Gamma tack s : A$,
    $Gamma tack (lambda (x : A) sd t)(s) peq t[s slash x] : B$,
    name: [$->$-Comp ($beta$)],
  )),
  prooftree(rule(
    $Gamma tack f : A -> B$,
    $Gamma tack f peq lambda(x : A) sd f(x) : A->B$,
    name: [$->$-Uniq ($eta$)],
  )),
))

The $->$-Comp and $->$-Uniq rules are respectively also known as the $beta$ and $eta$ rules
in $lambda$-calculus.

== Type families<sec:type-families>

A *type family* is an element of a function type $A -> UU_i$, i.e. it is a function which
takes some parameter (of type $A$) and returns a type. In this way, we can construct types
which depend on values, which is central to dependent type theory. An example (which we will
return to later) is the type family of finite sets, $Fin : NN -> UU_i$. We have not yet
introduced the type $NN$ of natural numbers, but (we hope) readers will nevertheless be
familiar with the natural numbers and may therefore have some intuition about this type. The
type $Fin(0)$ has 0 elements, the type $Fin(1)$ has exactly 1 element, and so on. We will
precisely define $Fin$ in a later section, after defining the natural numbers.

Another example of a type family is a family $UU_i -> UU_i$, which takes a _type_ as a
parameter. This is familiar to programmers of common non-dependently-typed programming
languages such as Rust or Haskell as a _generic type parameter_. For instance, the type
family defined by
$ lambda (T : UU_i) sd (T -> T) : UU_i -> UU_i $
represents generically the type of an automorphism on $T$.



== Dependent function types

Now we have introduced function types and type families, we introduce *_dependent_ function
types*. A dependent function is one in which the output type may depend on the input
_value_. The notation for a dependent function type is $product_(x : A) B(x)$, where
$B : A -> UU_i$ is a type family. This represents the type of a function which takes a
parameter $x$ of type $A$ and returns a value of type $B(x)$. Continuing the example of
finite sets from @sec:type-families, we might define a function
$sans("max") : product_(n : NN) Fin(n)$ which returns the highest number available in
$Fin(n)$; that is, $max(1) peq 0_(Fin(1))$, $max(2) peq 1_(Fin(2))$ etc., where we use a
subscript on the numeral to emphasize that the elements of each type $Fin(n)$ are distinct.

Using primitive constants to represent syntax, we introduce a primitive constant $c_Pi$, and
write $c_Pi (A, lambda (x : A) sd B(x))$ as $product_(x : A) B(x)$. The rules for dependent
function types correspond closely with their counterparts for non-dependent functions:

#pt(rule-set(
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : A -> UU_i$,
    $Gamma tack product_(x : A) B(x) : UU_i$,
    name: [$Pi$-Form],
  )),
  prooftree(bigrule(
    $Gamma, x : A tack b : B(x)$,
    $Gamma tack lambda (x : A) sd b : product_(x : A) B(x)$,
    name: [$Pi$-Intr],
  )),
  prooftree(bigrule(
    $Gamma tack f : product_(x: A) B(x)$,
    $Gamma tack a : A$,
    $Gamma tack f(a) : B(a)$,
    name: [$Pi$-Elim],
  )),
  prooftree(rule(
    $Gamma, x : A tack b : B(x)$,
    $Gamma tack a : A$,
    $Gamma tack (lambda (x : A) sd b)(a) peq b[a slash x] : B(a)$,
    name: [$Pi$-Comp],
  )),
  prooftree(bigrule(
    $Gamma tack f : product_(x : A) B(x)$,
    $Gamma tack f peq lambda (x : A) sd f(x) : product_(x : A) B(x)$,
    name: [$Pi$-Uniq],
  )),
))

#note[
  As mentioned in @sec:universes-and-contexts, there is an alternative presentation of type
  theory which relies more heavily on contexts. That presentation does not use type families
  such as $Gamma tack B : A -> UU_i$, instead relying on judgments like
  $Gamma, x : A tack B' : UU_i$, which means that $B'$ is a type which may reference a
  variable $x$.

  There, the rules $Pi$-Intr and $Pi$-Elim, for example, would be expressed as
  #pt(
    rule-set(
      prooftree(bigrule(
        $Gamma, x : A tack b : B$,
        $Gamma tack lambda (x : A) sd b : product_(x : A) B$,
        name: [$Pi$-Intr\*],
      )),
      prooftree(bigrule(
        $Gamma tack f : product_(x : A) B$,
        $Gamma tack a : A$,
        $Gamma tack f(a) : B[a slash x]$,
        name: [$Pi$-Elim\*],
      )),
    ),
  )
  In $Pi$-Intr\*, we see that $B$ is not a function which yields a type, but rather a type
  with (potentially) a free variable $x$; similarly in $Pi$-Elim\*, the resulting type of
  $f(a)$ is computed by variable substitution, $B[a slash x]$, rather than the function
  application $B(a)$.

]


=== Functions in "open form" vs "closed form"<sec:open-form-funs>

When we wish to introduce a constant which will be defined to be equal to some function, our
syntax so far allows us to write expressions such as
$
  f :peq lambda (x : A) sd t.
$
For simple functions such as this one, this form is straightforward, however when
considering functiosn of multiple arguments, the syntax quickly becomes unwieldy. Consider
the definition
$
  g :peq lambda (C : A -> UU_i) sd lambda (x : A) sd lambda (y : C(x)) sd t.
$
If $t$ itself is a complicated expression, one can see how this syntax becomes difficult to
read.

To this end, we will sometimes adopt a definition in "open form", which is presentationally
more similar to the standard mathematical style of function definition. Supposing the term
$t$ has type $B$, we first declare the type of $g$:
$ g : product_(C : A -> UU_i) product_(x : A) C(x) -> B $
and then define it for all arguments
$ g(C, x, y) :peq t. $

We hope the reader agrees that this "open form" is clearer and easier to read.

=== Discarded parameters

Furthermore, we may use the symbol $\_$ as the name of a parameter to indicate that it will
not occur freely in the definition of the function. This is to indicate "constant"
functions, which because of their type must take a parameter, but immediately discard it. A
common usage will be a type family that does not in fact use its parameter and always
returns the same type. For example, when we later work with the type of natural numbers, we
may use the type family
$
  & C : NN -> UU_i \
  & C(\_) :peq A
$
or alternatively in closed form
$
  C :peq lambda (\_: NN) sd A.
$
This indicates a type family $C$ which may theoretically depend on a natural number, but in
fact evaluates to the type $A$ at every number.

This is useful when we wish to apply our induction terms (which are expressed in full
generality using type families and dependent functions) in a way which happens to be
non-dependent.

=== Equivalence of non-dependent $Pi$-types with function types<sec:dep-fun-equiv>

If we suppose, in the rules for $Pi$-types, that we have
$B peq lambda (x : A) sd B' : UU_i$, and that $x$ does not occur freely in $B'$, then we
derive (via the $->$-Comp rule) that
$ Gamma, x : A tack B(x) peq B'. $
In that case, the $Pi$-Intr rule becomes

#pt(
  prooftree(bigrule(
    $Gamma, x : A tack b : B'$,
    $Gamma tack lambda (x : A) sd b : product_(x : A) B'$,
    name: [$Pi$-Intr],
  )),
)

Comparing with the $->$-Intr rule,
#pt(
  prooftree(rule(
    $Gamma, x : A tack t : B$,
    $Gamma tack lambda(x : A) sd t : A -> B$,
    name: [$->$-Intr],
  )),
)
we see that this is just a rewriting of $product_(x : A) B'$ as $A -> B$. The application to
the other rules is similar, and in this way we see that a $Pi$-type over $x : A$ which has
no free occurences of $x$ is equivalent to a plain function type. By this equivalence, we
refer to the function types from @sec:function-types as *non-dependent* function types. This
is also the reason that there is no ambiguity in using the $lambda$-syntax for function
notation for both dependent functions.

One advantage of the context-driven approach mentioned in @sec:universes-and-contexts is
that it would allow us to define dependent functions first, and then consider non-dependent
functions as a special case. However, since we choose the more functional approach for its
other merits, we must state this equivalence explicitly.

=== Reordering of arguments

Supposing that we have a function $f : A -> B -> C$, we may wish to transform it into a
function $f' : B -> A -> C$, with its arguments swapped. Fortunately, this is easy to do for
non-dependent functions:

#pt(
  prooftree(rule(
    $Gamma tack a : A$,
    $Gamma tack b : B$,
    $Gamma tack f : A -> B -> C$,
    $Gamma tack f' peq lambda (y : B) sd lambda (x : A) sd f(x, y)$,
    $Gamma tack f'(b, a) peq f(a, b)$,
  )),
)

For the case of dependent functions, we may do almost the same thing, but we must be careful
that the type of the latter parameter does not depend on the value of the former:

#pt(
  prooftree(rule(
    $Gamma tack a : A$,
    $Gamma tack b : B$,
    $Gamma tack f : product_(x : A) product_(y : B) C(x, y)$,
    $Gamma tack f' peq lambda (y : B) sd lambda (x : A) sd f(x, y)$,
    $Gamma tack f'(b, a) peq f(a, b)$,
  )),
)

Note the specific signature of $f$. If we allowed $y$ to have type $B(x)$ rather than $B$,
as in $f : product_(x : A) product_(y : B(x)) C(x, y)$, then we could not construct $f'$
using the given $lambda$ syntax, since in the term
$lambda (y : B(x)) sd lambda (x : A) sd f(x, y)$ we have a free occurrence of $x$.

#note[In #cite(<hottbook>, form: "prose"), the authors frequently make use this equivalence
  of parameter ordering, using syntax such as
  $
    product_(x : A, y : B) C(x, y),
  $
  however we prefer to avoid it, making explicit reorderings where necessary.]

== Dependent pair types

We now introduce *pair types*. In its non-dependent variety, a pair type is written
$A times B$ and its elements are pairs $(a, b)$ of elements of $A$ and $B$ respectively.
This should be reasonably familiar to the reader from set theory or computer science. In
fact, we will not take it as an axiom that all elements of $A times B$ are such pairs, but
rather we will prove it using the uniqueness principle for functions. Generalizing this
concept to a dependent form, we may consider pair types where the second type $B$ depends on
the value of the first element of the pair. We write this as
$
  sum_(x : A) B(x)
$
where $A$ is a type and $B$ is a type family of type $A -> UU_i$.

Our formal presentation defines dependent pair types first, and considers non-dependent pair
types as a special case. Again using primitive constants to represent syntax, we introduce
primitive constants $c_Sigma$ and $c_"pair"$, and we write
$c_Sigma (A, lambda (x : A) sd B(x))$ as $sum_(x : A) B(x)$ and $c_"pair" (a, b)$ as
$(a, b)$.

These are the rules for formation and introduction of dependent pair types:
#pt(rule-set(
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : A -> UU_i$,
    $Gamma tack sum_(x : A) B(x) : UU_i$,
    name: [$Sigma$-Form],
  )),
  prooftree(rule(
    $Gamma tack B : A -> UU_i$,
    $Gamma tack a : A$,
    $Gamma tack b : B(a)$,
    $Gamma tack (a, b) : sum_(x : A) B(x)$,
    name: [$Sigma$-Intr],
  )),
))

For the special case of non-dependent pairs, where $x$ is not free in $B$, we write
$sum_(x: A) B(x)$ as $A times B$.

For the elimination and computation rules, we introduce, for each dependent pair type, a
defined constant $ind_(sum_(x : A) B(x))$ (standing for "inductor"). The point of the
inductor is to convert dependent functions of two variables into functions on dependent
pairs. Our rules say that in order to define a (dependent) function out of a pair type, it
is sufficient to provide a (dependent) function in two variables, which is applied to the
first element of the pair and then the second. For the non-dependent case, this corresponds
to the equivalence between functions $A times B -> C$ and functions $A -> B -> C$.

The name "inductor" in this context is somewhat confusing, since no induction is being
performed. However, it is a concept which will be generalized to the other types we will
introduce, and in the case of the natural numbers its name will be more appropriate. It is
generally useful to have a common pattern for the computation and elimination rules of a
type, and the purpose of the inductor is to represent this pattern. In general, the inductor
provides a way to construct functions out of a type by providing simpler functions.

The action of transforming binary functions into functions on pair types is captured by the
following type of $ind_(sum_(x : A) B(x))$.

$
  ind_(sum_(x: A) B(x)) : product_(C : (sum_(x: A) B(x)) -> UU_i) ((product_(x: A) product_(y:B(x))
      C((x, y))) -> product_(p : sum_(x: A) B(x)) C(p))
$

The formal elimination and computation rules are as follows:
#pt(rule-set(
  prooftree(bigrule(
    $Gamma tack C : (sum_(x : A) B(x)) -> UU_i$,
    $Gamma tack g : product_(x : A) product_(y : B(x)) C((x, y))$,
    $Gamma tack ind_(sum_(x : A) B(x)) (C, g) : product_(p : sum_(x : A) B(x)) C(p)$,
    name: [$Sigma$-Elim],
  )),
  prooftree(bigrule(
    $Gamma tack C : (sum_(x : A) B(x)) -> UU_i$,
    $Gamma tack g : product_(x : A) product_(y : B(x)) C((x, y))$,
    $Gamma tack a : A$,
    $Gamma tack b : B(a)$,
    $Gamma tack ind_(sum_(x : A) B(x)) (C, g, (a, b)) peq g(a, b)$,
    name: [$Sigma$-Comp],
  )),
))

=== Projections

It will be useful later to work with the *projection functions* on a pair type. These will
be functions $pi_0$ and $pi_1$, which intuitively will pick the left and right elements
(respectively) out of the pair elements of the pair type. In the case of a non-dependent
pair, we desire these functions to have signatures
$
  pi_0 & : A times B -> A \
  pi_1 & : A times B -> B.
$

In the case of a dependent pair type, the desired signature of $pi_0$ translates by an
equivalence of notation to
$ pi_0 : (sum_(x : A) B(x)) -> A, $
however the case of $pi_1$ on a dependent pair type is not so easy. Recall that the type of
the right element of the pair depends on the value of the left element, so we require a
dependent function, whose type contains a reference to $pi_0$:
$
  pi_1 : product_(p : sum_(x : A) B(x)) B(pi_0(p)).
$

To construct these functions, we use the inductor on the following multi-parameter "helper"
functions:

$
  & pi'_0 : product_(x : A) B(x) -> A \
  & pi'_0 (x, y) :peq x \
  & pi'_1 : product_(x : A) product_(y : B(x)) B(x) \
  & pi'_1 (x, y) :peq y
$
and then define the projections as
$
  pi_0 & :peq ind_(sum_(x : A) B(x)) (lambda (\_ : sum_(x : A) B(x)) sd A, pi'_0) \
  pi_1 & :peq ind_(sum_(x : A) B(x)) (lambda (p : sum_(x : A) B(x)) sd B(pi_0(p)), pi'_1).
$

#proposition[
  The functions $pi_0$ and $pi_1$ have the desired types
  $
    pi_0 & : (sum_(x : A) B(x)) -> A \
    pi_1 & : product_(p : sum_(x : A) B(x)) B(pi_0(p))
  $
]
#proof[
  We apply the "$Sigma$-Elim" rule in both cases to derive the types. Let $A : UU_i$ be a
  type and $B : A -> UU_i$ be a type family. Recall that this means that we will work in the
  context $A : UU_i, B : A -> UU_i$.

  By the rule "$Sigma$-Form", we have $sum_(x : A) B(x) : UU_i$, and we put $C(\_) :peq A$
  in open form, or equivalently in closed form
  $
    C :peq lambda(\_ : sum_(x : A) B(x)) sd A
  $
  and therefore by $->$-Intr we have $C : (sum_(x : A) B(x)) -> UU_i$. Then, we can rewrite
  the type of $pi'_0$ -- using the $beta$-rule on the expression $C((x, y))$ -- as
  $
    pi'_0 : product_(x : A) product_(y : B(x)) C((x, y)).
  $
  We have all the antecedents for the $Sigma$-Elim rule, so we may conclude
  $
    ind_(sum_(x : A) B(x)) (C, pi'_0) : product_(p : sum_(x : A) B(x)) C(p)
  $
  i.e.
  $
    pi_0 : (sum_(x : A) B(x)) -> A.
  $

  By a similar process for $pi_1$, we put
  $
    C(p) :peq B(pi_0 (p))
  $
  so that
  $
    ind_(sum_(x : A) B(x))(C, pi'_1) : product_(p : sum_(x : A) B(x)) C(p)
  $
  i.e.
  $ pi_1 : product_(p : sum_(x : A) B(x)) B(pi_0(p)) $
  as required.
]

#remark[This is the first proof we present, and we hope that it demonstrates our choice of
  style going forward. While every proof we give will be directly translatable to a formal
  proof-tree deduction/*TODO mention Agda?*/, we will go through the steps discursively.

  In this case, we were relatively explicit in showing the necessary antecedents for the
  $Sigma$-Elim rule, and in pointing out an elided use of the $beta$-rule, but we will not
  always be so. As we progress through the text and become more comfortable with the rules,
  we will naturally begin to use them implicitly in some cases. We hope that this achieves a
  balance of clarity and brevity.]

We have proved a statement about the types of the projection functions $pi_0$ and $pi_1$
using the $Sigma$-Elim rule. What can we achieve with the $Sigma$-Comp rule? The following
proposition will be useful later, as part of the proof that all elements of pair types are
indeed pairs.

#proposition[For a type $A : UU_i$ and a type family $B : A -> UU_i$ and elements $x : A$,
  $y : B(x)$, we have
  $ pi_0((x, y)) peq x $
  and
  $
    pi_1((x, y)) peq y.
  $
]<prop:projection_equality>
#proof[
  We will use the "$Sigma$-Comp" rule, the "$Pi$-Comp" rule and our structural rules of
  judgmental equality. Recalling our convention that $f(a,b,c)$ means $f(a)(b)(c)$, by the
  definition of $pi_0$, we have
  $
    pi_0((x, y)) peq ind_(sum_(x : A) B(x)) (lambda (\_ : sum_(x : A) B(x)) sd A, pi'_0, (x, y)).
  $

  We apply the "$Sigma$-Comp" rule and use the rules of equalities implicitly to get
  $
    pi_0((x, y)) peq pi'_0(x, y).
  $

  Then applying the definition of $pi'_0$ in closed form we get
  $
    pi_0((x, y)) peq (lambda (x : A) sd lambda (y : B(x)) sd x)(x, y)
  $

  Applying the "$Pi$-Comp" rule ($beta$-reduction) we get
  $
    pi_0((x, y)) peq pi_0((x, y)) peq x
  $
  as required. The proof for $pi_1$ is similar.
]

== Coproduct types

The next type we introduce is the coproduct. These correspond to disjoint unions from set
theory, or to discriminated unions from computer science. Conceptually, it represents a type
whose elements can be either elements of a type $A$ or elements of a type $B$. In the
functional programming language Haskell, for example, this type is called `Either`.

We introduce three more primitive constants, $c_+$, $inl$ and $inr$, writing $c_+ (A, B)$ as
$A + B$. Elements of $A + B$ can be constructed by terms $inl(a)$, where $a : A$, and
$inr(b)$, where $b : B$. The formal rules for formation and construction of the coproduct
are:

#pt(rule-set(
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : UU_i$,
    $Gamma tack A + B : UU_i$,
    name: [$+$-Form],
  )),
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : UU_i$,
    $Gamma tack a : A$,
    $Gamma tack inl(a) : A + B$,
    name: [$+$-Intr-L],
  )),
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : UU_i$,
    $Gamma tack b : B$,
    $Gamma tack inr(b) : A + B$,
    name: [$+$-Intr-R],
  )),
))

In order to define a function out of a coproduct type, we need to provide two functions: one
which operates on elements of type $A$ and one which operates on elements of type $B$. We
then choose which function to use depending on whether the particular element is constructed
by $inl$ or $inr$. We use a defined constant $ind_(A+B)$ to perform this, using the pattern
of the inductor established previously. This situation is captured by the following type of
$ind_(A+B)$:

$
  ind_(A+B) : product_(C:A + B -> UU_i) ((product_(x : A) C(inl(x))) -> (product_(x: B) C(inr(x))) -> product_(x : A+B) C(x))
$

The following are the elimination and computation rules for the coproduct, using the
inductor:

#pt(
  rule-set(
    prooftree(bigrule(
      $Gamma tack C : A + B -> UU_i$,
      $Gamma tack f : product_(x : A) C(inl(x))$,
      $Gamma tack g : product_(x : B) C(inr(x))$,
      $Gamma tack ind_(A+B) (C, f, g) : product_(x:A) C(x)$,
      name: [$+$-Elim],
    )),
    prooftree(bigrule(
      $Gamma tack C : A + B -> UU_i$,
      $Gamma tack f : product_(x : A) C(inl(x))$,
      $Gamma tack g : product_(x : B) C(inr(x))$,
      $Gamma tack a : A$,
      $Gamma tack ind_(A+B) (C, f, g, inl(a)) peq f(a)$,
      name: [$+$-Comp-L],
    )),
    prooftree(bigrule(
      $Gamma tack C : A + B -> UU_i$,
      $Gamma tack f : product_(x : A) C(inl(x))$,
      $Gamma tack g : product_(x : B) C(inr(x))$,
      $Gamma tack b : B$,
      $Gamma tack ind_(A+B) (C, f, g, inr(b)) peq g(b)$,
      name: [$+$-Comp-R],
    )),
  ),
)

== Pattern matching<sec:pattern-matching-1>

When we are working with the $ind$ functions for our various types, we have so far specified
the antecedent functions and invoked the inductor explicitly. This can become quite verbose,
so we introduce the concept of *pattern matching*.

Using pattern matching, we may define functions using syntax like
$
  & f : product_(x : A + B) C(x) \
  & f(inl(a)) :peq t \
  & f(inr(b)) :peq s,
$
where the term $t$ is of type $C(inl(a))$ and $s$ is of type $C(inr(b))$. The terms $t$ and
$s$ may contain free variables $a : A$ and $b : B$ respectively. What we are doing here is
_implicitly_ invoking the inductor for the coproduct type. Indeed, we can translate this
directly into
$
  & f :peq ind_(A + B) (C, lambda (a : A) sd t, lambda (b : B) sd s)
$
but the pattern matched version is often clearer.

For pair types, pattern matching looks like
$
  & f : product_(x : A times B) C(x) \
  & f((a, b)) :peq t
$
where $t$ is of type $C((a, b))$ and may contain free variables $a : A$ and $b : B$.

These examples of pattern matching may raise an important question: how do we know that by
defining functions in this way, we have really defined a total function? In other words, how
do we know that the patterns $inl(a)$ and $inr(b)$ "cover" all possible elements of $A + B$;
similarly how do we know that the pattern $(a, b)$ "covers" all possible elements of
$A times B$? The answer lies in the fact that these can be translated into the forms using
the inductor: for pair types, it is precisely the "$Sigma$-Elim" rule that says in order to
define a function out of $A times B$, it is enough to define a function on $a : A$ and
$b : B$.

Later, we will see that indeed all elements of $A times B$ are such pairs $(a, b)$, and a
similar proof will show that all elements of $A + B$ are $inl$ or $inr$.

== The singleton and empty types

Having given a number of ways of forming types from existing types, we now move on to
defining some "basic" types, which exist without prerequisites. We begin with two types
related to pairs and coproducts.

=== The singleton type $one$

When considering non-dependent pair types, we note that we can recursively construct $n$-ary
tuple types by considering a $times$-chain such as $(A_1 times A_2) times A_3$ and so on.
This gives rise to the question of what we might mean by a "nullary" pair type, i.e. the
type of an empty $times$-chain. The nullary type for pairs is the *singleton type*, denoted
$one$. Unlike in set theory, where the singleton set is defined as a set with exactly one
element, we will define $one$ in our usual way with introduction and computation rules, and
_prove_ that it contains only one element.

In functional programming, this type is often known as the "unit type". In Haskell and Rust,
it is written `()`.

The formation and introduction rules for $one$ are:

#pt(
  rule-set(
    prooftree(rule($one : UU_i$, name: [$one$-Form])),
    prooftree(rule($star : one$, name: [$one$-Intr])),
  ),
)


When defining the elimination and computation rules for $one$, using the inductor, we cannot
assume that $one$ has exactly one element. Indeed, the introduction rule states only that
there is at least one element of type $one$, making no restrictions on the possibility of
other elements. As a consequence of this, the inductor must be generic over a type family
$C : one -> UU_i$, rather than a particular type $C' : UU_i$, even though we know
intuitively that each such family $C$ can only identify one type in $UU_i$.

The type of the inductor is therefore
$
  ind_one : product_(C : one -> UU_i) (C(star) -> product_(a : one) C(a)).
$

The elimination and computation rules for $one$ are as follows:

#pt(rule-set(
  prooftree(rule(
    $Gamma tack C : one -> UU_i$,
    $Gamma tack c : C(star)$,
    $Gamma tack ind_one (C, c) : product_(a : one) C(a)$,
    name: [$one$-Elim],
  )),
  prooftree(rule(
    $Gamma tack C : one -> UU_i$,
    $Gamma tack c : C(star)$,
    $Gamma tack ind_one (C, c, star) peq c$,
    name: [$one$-Comp],
  )),
))

=== The empty type $zero$

Analogously to considering the nullary type of the pair type $times$, we may consider the
nullary type of the coproduct $+$. We call this type the *empty type*, denoted $zero$. Since
we intend this type to have no elements, it has no introduction or computation rules: the
only thing we can say about it is that it is a type (its formation rule) and that functions
out of it can be constructed (its elimination rule). The lack of a computation rule
corresponds to the idea that functions out of it cannot be evaluated, since it is impossible
to construct an element.

In functional programming, this type is often known as the "bottom type". In Haskell it is
written $bot$, and in Rust it is written `!`. It is used as the return type of functions
which diverge (i.e. either do not terminate or crash the program).

#pt(
  rule-set(
    prooftree(rule($zero : UU_i$, name: [$zero$-Form])),
    prooftree(rule(
      $Gamma tack C : zero -> UU_i$,
      $Gamma tack ind_zero (C) : product_(a : zero) C(a)$,
      name: [$zero$-Elim],
    )),
  ),
)

== Natural numbers

We are now ready to introduce the type of natural numbers, $NN$. We first declare that there
is a natural number 0, and from there say that every natural number has a successor.

#pt(rule-set(
  prooftree(rule($Gamma tack NN : UU_i$, name: [$NN$-Form])),
  prooftree(rule(
    $Gamma tack 0 : NN$,
    name: [$NN$-Intro-0],
  )),
  prooftree(rule(
    $Gamma tack n : NN$,
    $Gamma tack succ(n) : NN$,
    name: [$NN$-Intro-$succ$],
  )),
))

The process of defining functions out of the natural numbers is by *primitive recursion*.
That is to say, we provide the value that our desired function takes at 0, and we provide a
"successor" function which computes the value of the function at the successor of a natural
number $n$, given $n$ itself and the value at $n$.

#pt(rule-set(
  prooftree(bigrule(
    $Gamma tack C : NN -> UU_i$,
    $Gamma tack c_0 : C(0)$,
    $Gamma tack c_s : product_(n : NN) (C(n) -> C(succ(n)))$,
    $Gamma tack ind_NN (C, c_0, c_s) : product_(n : NN) C(n)$,
    name: [$NN$-Elim],
  )),
  prooftree(bigrule(
    $Gamma tack C : NN -> UU_i$,
    $Gamma tack c_0 : C(0)$,
    $Gamma tack c_s : product_(n : NN) (C(n) -> C(succ(n)))$,
    $Gamma tack ind_NN (C, c_0, c_s, 0) peq c_0$,
    name: [$NN$-Comp-0],
  )),
  prooftree(bigrule(
    $Gamma tack C : NN -> UU_i$,
    $Gamma tack c_0 : C(0)$,
    $Gamma tack c_s : product_(n : NN) (C(n) -> C(succ(n)))$,
    $Gamma tack n : NN$,
    $Gamma tack ind_NN (C, c_0, c_s, succ(n)) peq c_s (n, ind_NN (C, c_0, c_s, n))$,
    name: [$NN$-Comp-$succ$],
  )),
))

#remark[It may seem counterintuitive that in order to construct functions out of the natural
  numbers, we must provide a successor function $c_s$ which is itself a function out of the
  natural numbers. However, there is no circular logic here, since we may always define
  constant functions which simply throw away their argument. These kinds of successor
  functions, which ignore the first argument (the value of $n$) and consume only the second
  argument (the value of our target function at the predecessor value) are useful for
  defining "accumulator" functions such as sum and product. More complex functions which
  require knowledge of $n$ itself, such as the factorial, may then be constructed out of
  these more basic functions.]

#let add = $sans("add")$
#example(add)[
  $ add : NN -> NN -> NN $
  We introduce a defined constant $add$, and define it using the inductor, where
  - $C(\_) :peq NN$, i.e. $C$ is a constant type family always returning $NN$;
  - $c_0 :peq a$, where $a$ will be the first parameter to $add$; and
  - $c_s (\_, p) :peq succ(p)$, i.e. at every step, $c_s$ returns the successor of the value
    at the previous step.

  These amount to the following definition rule (taking $C$ and $c_s$ in their closed-form
  equivalents):
  #pt(rule-set(prooftree(rule(
    $Gamma tack a : NN$,
    $Gamma tack add(a) peq ind_NN (lambda (\_ : NN) sd NN, a, lambda (\_: NN) sd lambda (p : NN)) sd succ(p))$,
  ))))

  Using the conventional notation of $1$ for $succ(0)$, $2$ for $succ(1)$, etc., let us
  compute the value of $add(1, 1)$. In this computation we will use $C$ and $c_s$ to refer
  to the terms defined above.

  Since we have $0 : NN$, we have $1 : NN$ by rule "$NN$-Intro-$succ$", so the antecedent
  $a : NN$ is satisfied. Then using the definition rule for $add$, we have the following
  judgment for $add(1, 1)$:
  $
    add(1, 1) peq ind_NN (C, 1, c_s, 1).
  $
  Unwrapping the second occurrence of $1$ as $succ(0)$, we then use the rule
  "$NN$-Comp-$succ$". (We omit the verification that our $C$ and $c_s$ terms satisfy the
  necessary antecedents.) We obtain
  $
    add(1, 1) peq c_s (0, ind_NN (C, 1, c_s, 0)).
  $
  We use the rule "$NN$-Comp-0" on the inner $ind_NN$ term to get
  $
    add(1, 1) peq c_s (0, 1),
  $
  i.e.
  $
    add(1, 1) peq (lambda (\_ : NN) sd lambda (p : NN) sd succ(p)) (0, 1).
  $

  Using the rule "$->$-Comp" (the $beta$ rule) twice to perform the function application, we
  get
  $
    add(1, 1) peq succ(1) peq 2.
  $
]<example:add>

#let prod = $sans("prod")$
#example(prod)[
  $ prod : NN -> NN -> NN $
  Similarly to $add$, we introduce a defined constant $prod$ and define it using the
  inductor, where
  - $C(\_) :peq NN$
  - $c_0 :peq 0$
  - $c_s (\_, p) :peq add(a, p)$, where $a$ will be the first parameter to $prod$.

  These amount to the following definition rule:
  #pt(prooftree(rule(
    $Gamma tack a : NN$,
    $prod(a) peq ind_NN (lambda (\_ : NN) sd NN, 0, lambda (\_ : NN) sd lambda (p: NN) sd add(p, a))$,
  )))

  Let us again compute an example product, $prod(3, 2)$, following the convention of
  @example:add.

  We apply the definition rule to obtain
  $
    prod(3, 2) peq ind_NN (C, 0, c_s, 3, 2).
  $

  Then, unwrapping $2$ as $succ(1)$, we apply $NN$-Comp-$succ$ to obtain
  $
    prod(3, 2) peq c_s (1, ind_NN (C, 0, c_s, 1)).
  $

  Using the $beta$-rule to apply $c_s$, we get
  $
    prod(3, 2) peq add(3, ind_NN (C, 0, c_s, 1)).
  $

  By another application of $NN$-Comp-$succ$ and the $beta$-rule on the inner $ind$ term, we
  obtain
  $
    prod(3, 2) peq add(3, add(3, ind_NN (C, 0, c_s, 0))).
  $

  Now, by applying $NN$-Comp-0 to the inner $ind$ term, we obtain
  $
    prod(3, 2) peq add(3, add(3, 0)).
  $

  Finally, by computing the resulting expression using the process in @example:add, we
  arrive at
  $
    prod(3, 2) peq 6.
  $
]<example:prod>

#let fact = $sans("fact")$
#example(fact)[
  Both @example:add and @example:prod used a step function $c_s$ which ignored its first
  parameter, i.e. the recursion counter. We now demonstrate a function, namely the factorial
  function, which uses this value.

  $ fact : NN -> NN $

  We introduce a defined constant $fact$ and define it using the inductor, where
  - $C(n) :peq NN$
  - $c_0 :peq 1$
  - $c_s (s, p) :peq prod(succ(s), p)$

  These amount to the following definition rule:
  #pt(prooftree(rule(
    $fact peq ind_NN (lambda (\_ : NN) sd NN, 1, lambda (s : NN) sd lambda (p : NN) sd prod(s, p))$,
  )))

  For a demonstration, we compute $fact(3)$. We apply the definition rule to obtain
  $
    fact(3) peq ind_NN (C, 1, c_s, 3),
  $
  to which we then apply the $NN$-Comp-$succ$ rule to obtain
  $
    fact(3) peq c_s (2, ind_NN (C, 1, c_s, 2)).
  $
  Repeated applications of the $beta$-rule and $NN$-Comp-$succ$ gets us
  $
    fact(3) & peq prod(3, c_s (1, ind_NN (C, 1, c_s, 1))) \
            & peq prod(3, prod(2, c_s (0, ind_NN (C, 1, c_s, 0)))) \
            & peq prod(3, prod(2, prod(1, ind_NN (C, 1, c_s, 0)))).
  $
  Then, we apply $NN$-Comp-0 to the remaining $ind$ term to get
  $
    fact(3) peq prod(3, prod(2, prod(1, 1)))
  $
  and applying the process in @example:prod we arrive at
  $
    fact(3) peq 6.
  $
]<example:fact>

== Recursive pattern matching

We return to the concept of pattern matching discussed in @sec:pattern-matching-1. We want
to apply this concept to defining functions out of $NN$, using $ind_NN$, as we did for
functions out of pair and coproduct types. This raises some issues, however.

Computer scientists are familiar with the concept of recursion as "a function which calls
itself". An example of a recursive function from computer science might be
$
  & fact : && NN -> NN \
$$
  & fact(0)       && :peq 1 \
  & fact(succ(n)) && :peq succ(n) times fact(n) \
$
(where $times$ here denotes multiplication). Here we see that in the third line, the term
$fact(n)$ appears both on the left- and the right-hand side of the definition. This is
dangerous! It might allow us to write such "functions" as
#let never = $sans("never")$
$
  never : NN -> NN \
  never(n) :peq never(n).
$
If given to a computer, the function $never$ will continuously evaluate itself and never
yield a value. This is unacceptable to mathematicians, who require all our functions to be
well-defined.

The solution to this problem, in depedent type theory, is to assert that the recursive call
on the right-hand side of the definition _must_ reduce the value of $n$. In fact, this is
precisely the point of primitive recursion: in order to define a function out of the natural
numbers, we must provide an initial value $c_0$, and a step function $c_s$, which is
evaluated each time (in the $NN$-Comp rule) at decreasing values. When we define functions
out of $NN$ by pattern matching, therefore, we use syntax like that of $fact$ above:
$
  & f : && NN -> A \
$$
  & f(0)       && :peq t \
  & f(succ(n)) && :peq s
$
where $t :A$ is a term and $s : A$ is a term with a free variable $n : NN$, but may only
recursively call $f$ in the form $f(n)$. In dependent type theory, the recursive function
$fact$ given above is therefore valid, while $never$ is not. The recursive form of $fact$
translates directly by pattern matching to the explicit version using the inductor in
@example:fact.

TODO: talk about double recursion, use Giacomo's notes.

== Finite types

Now that we have the singleton type $one$, the empty type $zero$ and the coproduct
type-former $+$, we can construct the previously-mentioned example of finite sets, from
@sec:type-families. This is presented as an exercise in #cite(
  <hottbook>,
  // form: "prose",
  supplement: [Chapter 1],
).

We define the type family $Fin$ by recursive pattern matching:
$
  Fin : NN -> UU_i
$
$
  & Fin(0)       && :peq zero \
  & Fin(succ(n)) && :peq one + Fin(n).
$

For the sake of being explicit, this translates into the form
$
  &&         c_0 & :peq zero \
  && c_s (\_, T) & :peq one + T \
  &&         Fin & :peq ind_NN (lambda (\_ : NN) sd UU_i, c_0, c_s).
$

By applying the $NN$-Comp rules, we see for example that
$Fin(3) peq one + (one + (one + zero))$. We are not able to prove (yet) that $Fin(n)$ has
exactly $n$ elements (TODO we may even take it as axiomatic? or we may prove it later).

== Propositions as types

An interesting property of type theory is that it corresponds with the principles of
(constructive) logic. This is known as the Curry-Howard correspondence. We may translate
propositional logic into types as follows #cite(<hottbook>, supplement: [Section 1.11]):

#align(center, table(
  columns: (auto, auto),
  stroke: none,
  table.header([*Logical statement*], [*Type*]),
  table.hline(),
  [True], $one$,
  [False], $zero$,
  [$A$ and $B$], $A times B$,
  [$A$ or $B$], $A + B$,
  [$A$ implies $B$], $A -> B$,
  [Not $A$], $A -> zero$,
))


We consider a proposition to be true if its corresponding type has an element, and we call
this element a *witness* to the truth of the proposition. A worked example in #cite(
  <hottbook>,
  // form: "prose",
  supplement: [Section 1.11],
) gives a proof of one of de Morgan's laws,
$ "if not A and not B, then not (A or B)". $
The type translation of this is
$ (A -> zero) times (B -> zero) -> (A + B) -> zero. $
In order to prove this, we must exhibit an element of this type. Such an element is given as
$
  f((x, y), inl(z)) & :peq x(z) \
  f((x, y), inr(z)) & :peq y(z).
$
In our formal definitions this translates to
$
  C_1 &:peq lambda (\_: (A -> zero) times (B -> zero)) sd zero \
  C_2 &:peq lambda (\_: A + B) sd zero \
  g &:peq ind_(A + B) (C_2, lambda (z : A) sd x(z), lambda (z : B) sd y(z)) \
  f &:peq ind_((A -> zero) times (B -> zero)) (C_1, lambda (x : A -> zero) sd lambda (y : B -> zero) sd g).
$

#example[
  It is left as an exercise in #cite(<hottbook>) to show the converse, i.e.
  #align(center)[
    if not ($A$ or $B$) then (not $A$) and (not $B$)
  ]

  That is to say, we want to exhibit an element
  $ t : ((A + B) -> zero) -> ((A -> zero) times (B -> zero)). $

  In a nod to the logical style of this statement, we will write this example formally using
  proof trees.

  Let $Gamma$ be the context $A : UU_i, b : UU_i, z : (A + B) -> zero$. Then we have

  #pt(prooftree(
    rule(
      rule(
        rule($Gamma, a : A tack inl(a) : A + B$, name: [$+$-Intr-L]),
        $Gamma, a : A tack f(inl(a)) : zero$,
        name: [$->$-Elim],
      ),
      $Gamma tack lambda (a : A) sd f(inl(a)) : A -> zero$,
      name: [$->$-Intr],
    ),
  ))

  By a similar deduction we get
  #pt(prooftree(rule(
    $Gamma tack lambda (b : B) sd f(inr(b)) : B -> zero$,
  )))

  Writing these as a pair, we get
  #pt(prooftree(rule(
    rule(
      $Gamma tack lambda (a : A) sd f(inl(a)) : A -> zero$,
    ),
    rule(
      $Gamma tack lambda (b : B) sd f(inr(b)) : B -> zero$,
    ),
    $Gamma tack (lambda (a : A) sd f(inl(a)), lambda (b : B) sd f (inr(b))) : (A -> zero) times (B -> zero)$,
    name: [$Sigma$-Intr],
  )))

  Then applying $->$-Intr (removing $f$ from the context) we obtain a term
  $
    lambda (f : (A + B) -> zero) sd (lambda (a : A) sd f(inl(a)), lambda (b : B) sd f(inr(b))),
  $
  which has type
  $ ((A + B) -> zero) -> ((A -> zero) times (B -> zero)) $
  as required.
]

=== Predicate logic

We may use the fact that we are working in dependent type theory to move from propositional
to predicate logic by considering a type family $P : A -> UU_i$ as a predicate and
translating
- "for all $x$, $P(x)$" to $product_(x : A) P(x)$, and
- "there exists an $x$ such that $P(x)$" to $sum_(x : A) P(x)$.

We explore this correspondence with some further examples.

#example[The statement
  #block(inset: (left: 2em, right: 2em))[#align(center)[if for all $x : A$, $P(x)$ and
    $Q(x)$, then for all $x : A$, $P(x)$ and for all $x : A$, $Q(x)$]]
  translates to the type
  $
    (product_(x : A) P(x) times Q(x)) -> (product_(x : A) P(x)) times (product_(x : A) Q(x))
  $
  which has an element
  $
    lambda (f : product_(x : A) P(x) times Q(x)) sd (lambda (x : A) sd pi_0(f(x)), lambda (x : A) sd pi_1(f(x))).
  $
]

#let leq = $sans("leq")$
#example[We define inequality on the natural numbers as a type family
  $leq : NN -> NN -> UU_i$. For ease of notation, we express $leq(n, m)$ and $add(a, b)$
  (from @example:add) using infix notation: $n <= m$ and $a + b$ respectively.

  We define $leq$ as
  $
    n <= m :peq sum_(p : NN) n + p =_NN m
  $
  or in closed form
  $
    leq :peq lambda (n : NN) sd lambda (m : NN) sd sum_(p : NN) n + p =_N m.
  $

  We are jumping the gun here by using the identity type $=_NN$, which will be introduced in
  the next section. For now, it suffices to know that for any type $A$ and element $a : A$,
  there is a type $a =_A a$ and an element $refl_a : a =_A a$.

  Considering the statement $1 <= 2$, we translate this to the dependent pair
  $ sum_(p : NN) 1 + p =_NN 2. $
  To show this is inhabited, consider the element $refl_2 : 2 =_NN 2$. Since we have shown
  that $1 + 1 peq 2$, we may rewrite the 2 on the left hand side of $refl_2$ to get
  $refl_2 : 1 + 1 =_NN 2$. Then applying the rules for dependent pair types, we have

  #pt(prooftree(rule(
    bigrule($Gamma tack lambda (p : NN) sd 1 + p =_NN 2 : NN -> UU_i$),
    bigrule($Gamma tack 1 : NN$),
    bigrule($Gamma tack refl_2 : 1 + 1 =_NN 2$),
    $Gamma tack (1, refl_2) : sum_(p : NN) (1 + p =_NN 2)$,
    name: [$Sigma$-Intr],
  )))

  so the type $1 <= 2$ is inhabited by the pair $(1, refl_2)$.
]


== Identity types

We now arrive at one of the more powerful mechanics of dependent type theory, the concept of
the *identity type*. The identity type is a way of proving an equality _within_ type theory,
as opposed to the judgmental (metatheoretic) equality we have been using up to now. The idea
is that, since types may depend on values, we can construct a type $a =_A b$ for $a$ and $b$
terms of type $A$, and an element of this type is a witness to the equality of $a$ and $b$.

The introduction rule consists of an element $refl_a$ of type $a =_A a$, i.e. it is an axiom
that there is a witness to the equality of $a$ with itself. The formal statements of the
formation and introduction rules are:

#pt(rule-set(
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack a : A$,
    $Gamma tack b : B$,
    $Gamma tack a =_A b : UU_i$,
    name: [=-Form],
  )),
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack a : A$,
    $Gamma tack refl_a : a =_A a$,
    name: [=-Intr],
  )),
))

The elimination and computation rules represent the *path induction principle*, which is
"one of the most subtle parts of type theory". We will state the formal definitions of the
rules first, and then examine their meaning using examples.

#pt(rule-set(
  prooftree(bigrule(
    $Gamma tack A : UU_i$,
    $Gamma tack C : product_(x : A) product_(y : A) (x =_A y) -> UU_i$,
    $Gamma tack c : product_(z : A) C(z, z, refl_z)$,
    $Gamma tack ind_=_A (C, c) : product_(a : A) product_(b : A) product_(p : a =_A b) C(a, b, p)$,

    name: [=-Elim],
  )),
  prooftree(bigrule(
    $Gamma tack A : UU_i$,
    $Gamma tack C : product_(x : A) product_(y : A) (x =_A y) -> UU_i$,
    $Gamma tack c : product_(z : A) C(z, z, refl_z)$,
    $Gamma tack a : A$,
    $Gamma tack ind_=_A (C, c, a, a, refl_a) peq c(a)$,
    name: [=-Comp],
  )),
))

A useful first point of understanding these rules is to compute a consequence of them, the
*indiscernibility of identicals*. In terms of types and elements, it gives us a way of
"transporting" an element of a type $C(x)$ "across" an equality $x = y$ to obtain an element
of a type $C(y)$. Translated to the language of type families as predicates, it means that
predicates which are satisfied by some element remain satisfied by any equal element, i.e.
that equal terms may be substituted for each other.

#theorem([Indiscernibility of identicals])[Let $A : UU_i$ be a type and $D : A -> UU_i$ a
  type family. For every pair of elements $x : A$, $y : A$, there is a function
  $
    transport^D : (x =_A y) -> D(x) -> D(y)
  $
  such that when $x peq y$, we have
  $
    transport^D (refl_x) peq id_D(x).
  $
]<thm:indiscernibility-of-identicals>

#proof[
  Fix a type family $D : A -> UU_i$ and variables $x : A$, $y : A$. Define $C$, as in the
  computation and elimination rules, as
  $
    C : product_(x : A) product_(y : A) (x =_A y) -> UU_i \
    C(x, y, \_) :peq D(x) -> D(y).
  $

  For a variable $z : A$, we have $C(z, z, refl_z) peq D(z) -> D(z)$, so we require a
  function
  $
    c : product_(z : A) D(z) -> D(z),
  $
  for which we put the identity:
  $
    c(z) :peq id_(D(z))
  $

  We then apply the "=-Elim" rule to derive the type of $ind_=(C, c)$:
  $
    ind_=_A (C, c) : product_(x : A) product_(y : A) product_(p : x =_A y) D(x) -> D(y).
  $
  Recalling the equivalence between non-dependent function types and dependent function
  types which do not use their parameter in their return type (@sec:dep-fun-equiv), we may
  write
  $
    ind_=_A (C, c) : product_(x : A) product_(y : B) (x =_A y) -> D(x) -> D(y).
  $

  We define $transport^D$ as
  $
    transport^D :peq ind_(=_A) (C, c, x, y)
  $
  so that it has the desired type:
  $
    transport^D : (x = y) -> D(x) -> D(y).
  $

  Moreover, by the rule "=-Comp" we have
  $
    transport^D (refl_x) peq id_(D(x))
  $
  as required.
]

#remark[The function $transport$ is very useful, since it allows to talk about elements of
  $D(x)$ as if they were elements of $D(y)$. For example, given elements $w : D(x)$ and
  $z : D(y)$, we cannot form a type $w = z$, since $w$ and $z$ live in different types.
  Using $transport$, however, we can suppose a witness $p : x = y$ and form the type
  $transport^D (p, w) = z$. We will make frequent use of $transport$ throughout the rest of
  the text.
]

Moving to the general form of the elimination rule, we allow $C$ to depend not only on
$x : A$ and $y : A$ (which must be equal) but also on the specific witness $p$ to their
equality. The rule supposes that we have such a family $C$, and for each $z : A$, an element
$c(z) : C(z, z, refl_z)$. We then get an element of $C(a, b, p)$ for all $a : A$, $b : A$
such that $a$ and $b$ are (propositionally) equal. In other words, if we want to construct
an element of the family $C(a, b, p)$, it is sufficient to show an element of
$C(z, z, refl_z)$. This allows us to move from statements about judgmental equality to
statements about propositional equality: the rule "opens up" propositional equality by
saying that if we assume a judgmental equality and conclude something, we can conclude the
same thing on the basis of a propositional equality;

This is precisely analogous to the principle of induction on natural numbers -- if we want
to construct a function $f : NN -> T$, it is sufficient to provide a value $c_0 : T$ and a
step function $c_s : NN -> NN -> T$. The induction principle "opens up" functions out of the
natural numbers by saying we only need to provide the data $c_0$ and $c_s$.

In the language of propositions and predicates, the induction principle says that if
$C(z, z, refl_z)$ is true -- i.e. $C$ is a reflexive predicate -- then $C(a, b, p)$ is true
whenever $p$ proves that $a$ and $b$ are equal. Moreover, the general form of the
computation rule gives us a judgmental equality in the case where $a$ and $b$ are
judgmentally equal.


== Proofs about our types

Now that we have defined identity types, we can make some statements about identities within
our previously-defined types.

#proposition[The type $one$ has only one element.]<prop:one-is-a-singleton>
#proof[
  We have defined, in the $one$-Intr rule, how to specify a particular element of $one$,
  namely $star : one$. The method we will use to prove this proposition is to show that
  given an element $a : one$, there is a witness to the equality $a =_one star$. That is,
  that there is a function $f : product_(a : one) a =_one star$.

  The $one$-Elim rule says that in order to construct such a function out of $one$, it is
  sufficient to give its value at $star$. (To most mathematicians, this statement alone
  should give us the necessary intuition that $one$ only has one element.) Working formally,
  we define a type family $C$ as
  $
    C : one -> UU_i \
    C(a) :peq a =_one star.
  $
  Recall that the $one$-Elim rule says that we must provide an element $c : C(star)$, i.e.
  $c : star =_one star$. Of course, $refl_star$ is such an element, so we then conclude
  $
    ind_one (C, refl_star) : product_(a : one) a =_one star
  $
  as required.
]

#proposition[Every element of a pair type $A times B$ is equal to $(x, y)$, for some
  $x : A$, $y : B$.]<prop:pair-types-consist-of-pairs>
#proof[
  This proof uses exactly the same principle as @prop:one-is-a-singleton: the rule
  $Sigma$-Elim tells us that in order to define a function out of a pair type $A times B$,
  it is sufficient to give a multi-parameter function on $A$ and $B$. We define the type
  family $C$ as
  $
    C : A times B -> UU_i \
    C(p) :peq (pi_0(p), pi_1(p)) =_(A times B) p.
  $
  That is to say, $C(p)$ represents the proposition that an element $p : A times B$ is equal
  to the pair of its projections, and in particular that $p$ is a pair. Our aim, then, is to
  show that $C(p)$ is inhabited for all $p : A times B$, i.e. to construct a function of
  type $product_(p : A times B) C(p)$.

  Applying the $Sigma$-Elim rule with our $C$, we see that we need to show a function
  $g : product_(x : A) product_(y : B) C((x, y))$, i.e.
  $ g : product_(x : A) product_(y : B) (pi_0((x, y)), pi_1((x, y))) =_(A times B) (x, y). $

  This function can be defined using $refl_((x, y))$ as follows. Recall
  @prop:projection_equality: for all $x : A$ and $y : B$, we have
  $ pi_0((x, y)) peq x wide "and" wide pi_1((x, y)) peq y. $
  We can therefore rewrite the type of $refl_((x, y))$ as
  $ refl_((x, y)) : (pi_0((x, y)), pi_1((x, y))) =_(A times B) (x, y). $

  Therefore for our function $g : product_(x : A) product_(y : B) C((x, y))$, we put
  $
    g(x, y) :peq refl_((x, y)).
  $
  Applying the inductor, we get
  $
    ind_(A times B) (C, g) : product_(p : A times B) C(p)
  $
  as required.
]

=== Identity as an equivalence relation

In order for us to believe that the type $x =_A y$ really "means" that $x : A$ and $y : A$
are in some sense equal, we must at least know that identity forms an equivalence relation.
That is, it obeys the laws of reflexivity, symmetry and transitivity. This section proves
these laws for identity types.

#lemma[For a type $A : UU_i$ and elements $x : A$, $y : A$, there is a function
  $ (-)^(-1) : (x =_A y) -> (y =_A x). $
  That is to say, any element $p : x =_A y$ can be transformed into an element
  $p^(-1) : y =_A x$, so the identity type is symmetric.

  Furthermore, for all $x : A$, $refl_x^(-1) peq refl_x$.
]<lemma:identity-symmetry>
#proof[
  We use the computation and elimination rules for identity types. For
  $C : product_(x : A) product_(y : A) (x =_A y) -> UU_i$, we put
  $
    C(x, y, \_) :peq y =_A x.
  $
  For a variable $z : A$, we have $C(z, z, refl_z) peq z =_A z$, so the natural fit for $c$
  is
  $
    c : product_(z : A) C(z, z, refl_z) \
    c(z) :peq refl_z
  $

  Fixing variables $x : A$ and $y : A$ as in the statement of the lemma, we define
  $
    (-)^(-1) :peq ind_=_A (C, c, x, y)
  $
  and use the "=-Elim" rule to verify that it has the desired type
  $
    (-)^(-1) : (x =_A y) -> (y =_A x)
  $

  To prove the "furthermore" case, we use the "=-Comp" rule. For a variable $x : A$, we have
  $
    refl_x^(-1) peq ind_=_A (C, c, x, x, refl_x) peq c(x) peq refl_x
  $
  as required.
]

#lemma[For a type $A : UU_i$ and elements $x : A$, $y : A$, $z : A$, there is a function
  $
    (- bullet -) : (x =_A y) -> (y =_A z) -> (x =_A z).
  $
  That is to say, given elements $p : x =_A y$ and $q : y =_A z$, we may construct an
  element $p bullet q : x =_A z$, so the identity type is transitive.

  Furthermore, for all $x : A$, $refl_x bullet refl_x peq refl_x.$
]<lemma:identity-transitivity>
#proof[
  Fix variables $x : A$, $y : A$ and $z : A$ as in the statement of the lemma, and for the
  $C$ as in the elimination and computation rules for identity, put
  $
    C(x, y, \_) :peq (y =_A z) -> (x =_A z).
  $

  For a variable $w : A$ (renamed from $z$ in the statements of the rules), we compute
  $C(w, w, refl_w) peq (w =_A z) -> (w =_A z)$, so we write
  $
    c(w) :peq id_(w =_A z).
  $
  Using the elimination rule, we get
  $
    ind(C, c) : product_(x : A) product_(y : A) (x =_A y) -> (y =_A z) -> (x =_A z).
  $
  We define
  $
    (- bullet -) :peq ind(C, c, x, y)
  $
  so that the type is the desired one:
  $
    (- bullet -) : (x = y) -> (y = z) -> (x = z).
  $

  Applying the computation rule, we see
  $
    (refl_x bullet -) peq ind(C, c, x, x, refl_x) peq id_(x = x)
  $
  so
  $
    refl_x bullet refl_x peq refl_x
  $
  as required.
]

#proposition[The identity type over a type $A : UU_i$ forms an equivalence relation, in the
  sense that:
  - (Reflexivity) For all $x : A$, there is an element of (i.e. a witness to) the type
    $x = x$;
  - (Symmetry) For all $x : A$, $y : A$, there is an element of $x = y$ if and only if there
    is an element of $y = x$;
  - (Transitivity) For all $x : A$, $y : A$, $z : A$, if there are elements $p : x = y$ and
    $q : y = z$, then there is an element of $x = z$.
]<prop:identity-equiv>
#proof[We have reflexivity axiomatically by the "$=$-Intr" rule. We have symmetry by
  @lemma:identity-symmetry and transitivity is by @lemma:identity-transitivity.]

= Homotopy

In this section we will... TODO

== Classical homotopy theory

We begin with a brief discursive exposition of classical homotopy theory, from the point of
view of a set-theoretic foundation of topological spaces.

In a space $X$, consisting of points equipped with a topology, a *path* from a point $x$ to
a point $y$ is a continuous map $f : [0, 1] -> X$ such that $f(0) = x$ and $f(1) = y$. We
can construct the inverse of a path, such as $f^(-1)$ which walks from $y$ back to $x$, and
also composition of paths: supposing $g : [0, 1] -> X$ is a path such that $g(0) = y$ and
$g(1) = z$, the composition $f bullet g$ is a path which walks from $x$ to $z$ via $y$.
(Note that our definition of the "inverse path" $f^(-1)$ is _not_ the inverse function of
$f$ -- in general such an inverse function need not even exist -- and our definition of path
composition is similarly unrelated to function composition, and notated in the opposite
order.)

Given spaces $X_1$, $X_2$ and two continuous maps $f, g : X_1 -> X_2$, we may consider a
continuous map $H : [0, 1] times X_1 -> X_2$ such that $H(0, -) = f$ and $H(1, -) = g$.
(Note that such a map $H$ does not in general always exist.) Such maps between maps are
called *homotopies*. We may think of a homotopy as continuously deforming the map $f$ into
$g$. If we additionally require that $H(t, 0) = x$ and $H(t, 1) = y$ for all $t in [0, 1]$,
we say that $H$ is *endpoint preserving*. By setting $X_1$ to the singleton set, we can
consider paths themselves to be homotopies between points, and furthermore the notion of
inverses and composition generalize to the case of homotopies.

By considering the space of functions $[0, 1] -> X$ itself as a topological space (FEEDBACK:
verify we can do this), denoted $X'$, we get a notion of homotopies between homotopies. This
concept can be iterated up to infinity, so we have a tower of homotopies at different
"levels".

Moreover, homotopies form an equivalence relation on the paths or homotopies they transform.
For paths (or homotopies) $f$ and $g$, we say $f ~ g$ if there exists an endpoint-preserving
homotopy $H$ between them. The rules of equivalence relations then follow from the above
construction of inverses and composition. For example, if we have a path $p$ from a point
$x$ to a point $y$, the composition $p bullet p^(-1)$, which walks from $x$ to $y$ and then
back again, can be deformed continuously to the constant path $q$, which does not move from
$x$. Therefore we have $p bullet p^(-1) ~ q$.

== $infinity$-groupoids

This structure of paths which can be inverted and composed, with an equivalence relation
that works up to the next "level", is structurally represented by the concept of an
$infinity$-groupoid. In category theory, a groupoid is a category where all morphisms are
invertible. An $infinity$-groupoid is a categorical object (precisely, a quasi-category),
characterized by a base level of objects and morphisms, and morphisms at level $n$ form the
objects at level $n + 1$. Furthermore, morphisms at level $n$ follow the usual categorical
notions of identity and composition, as well as having an inverse, up to transformation by
morphisms at level $n + 1$.

That is to say, every object at every level has an identity morphism, denoted $1_X$ for an
object $X$, and for a morphism
$X -->^f Y$
at level $n$, there is a morphism
$Y -->^(f^(-1)) X$
at level $n$ and a morphism
$ f bullet f^(-1) -->^H 1_X $
at level $n + 1$, so that we have an equivalence
$ f bullet f^(-1) ~ 1_X. $
Furthermore, if we have morphisms
$ W -->^f X -->^g Y -->^h Z $
at level $n$, then we have associativity expressed as
$ (f bullet g) bullet h ~ f bullet (g bullet h) : W --> Z, $
i.e. there is a (by definition, invertible) morphism
$(f bullet g) bullet h -->^H f bullet (g bullet h)$ at level $n + 1$.

Since witnesses for our identity types from the previous chapter can be composed and
inverted (forming an equivalence relation by @prop:identity-equiv), we will show that their
structure can be represented by an $infinity$-groupoid. It is in this sense which identity
types and homotopies are related.

We may consider the type $x =_A y$ as representing the collection of paths (or morphisms)
from $x$ to $y$. Given some witness (or path) $p : x =_A y$, we may wish to know if it is
equal to some other witness $q : x =_A y$, which would be represented by the type
$ p =_((x =_A y)) q. $
The type $p = q$ exists at the next level up from the type $x = y$, so this fits naturally
into the $infinity$-groupoid structure.

We need, however, to show that the laws of inverses and associativity hold when we consider
witnesses to equalities as paths.

#lemma([HoTT 2.1.4])[
  For a type $A : UU_i$, elements $x, y, z, w : A$ and witnesses $p : x =_A y$,
  $q : y =_A z$ and $r : z =_A w$, the following statements hold:

  + $p = p bullet refl_y$ and $p = refl_x bullet p$
  + $p bullet p^(-1) = refl_x$ and $p^(-1) bullet p = refl_y$
  + $(p^(-1))^(-1) = p$
  + $p bullet (q bullet r) = (p bullet q) bullet r$

  where these identities are second-level identities.
]<lem:paths-inv-assoc>
#proof[
  All proofs use the induction principle (the $=$-Elim rule), and we work in an ambient
  context containing $x, y, z, w, p, q, r$ as in the statement of the lemma.

  + We consider the first case and put
    $
      C : product_(x : A) product_(y : A) (x = y) -> UU_i \
      C(x, y, p) :peq (p = p bullet refl_y)
    $

    We want to construct a function
    $ c : product_(z : A) C(z, z, refl_z) $
    and we compute $C(z, z, refl_z) peq (refl_z = refl_z bullet refl_z)$. By
    @lemma:identity-symmetry, we know $refl_z bullet refl_z peq refl_z$, so we have
    $C(z, z, refl_z) peq (refl_z = refl_z)$. Thus, we can put
    $
      c(z) :peq refl_(refl_z)
    $
    and by induction we get
    $
      ind_=(C, c, x, y, p) : p = p bullet refl_y
    $
    as required. The proof for the second case is similar.

  + We again consider only the first case, with the second case being completely analogous.
    This time, we put
    $
      C(x, y, p) :peq (p bullet p^(-1) = refl_x)
    $
    and compute, for a variable $z : A$,
    $
      C(z, z, refl_z) &peq (refl_z bullet refl_z^(-1) = refl_z) \
      & peq (refl_z = refl_z) wide "by" #ref(<lemma:identity-symmetry>) "and" #ref(<lemma:identity-transitivity>).
    $
    Then, we again may put $c(z) :peq refl_refl_z$ to obtain
    $
      ind_=(C, c, x, y, p) : (p bullet p^(-1) = refl_x).
    $
  + For this case, we put $C(\_, \_, p) :peq (p^(-1))^(-1) = p$, and compute
    $
      C(z, z, refl_z) & peq (refl_z^(-1))^(-1) = refl_z \
                      & peq refl_z = refl_z wide "by" #ref(<lemma:identity-symmetry>)
    $
    By again putting $c(z) :peq refl_refl_z$ we obtain
    $
      ind_=(C, c, x, y, p) : (p^(-1))^(-1) = p.
    $
  + For this case, we have two things to consider. Firstly, our usual variable name $z$ in
    the $=$-Elim rule conflicts with the $z$ that we have in the context, and secondly we
    are going to need use induction three times. We are running out of letters in the
    alphabet! We therefore replace the $z$ in the $=$-Elim rule with $v_1, v_2, v_3$ for
    each induction.

    For the first induction, put
    $
      C_1 (x, y, p) :peq product_(z : A) product_(q : y = z) product_(w : A) product_(r : z = w) p bullet (q bullet r) = (p bullet q) bullet r
    $
    so that, for $v_1 : A$, we have
    $
      C_1(v_1, v_1, refl_v_1) peq product_(z : A) product_(w : A) product_(q : v_1 = z) product_(r : z = w) refl_v_1 bullet (q bullet r) = (refl_v_1 bullet q) bullet r.
    $
    We want to construct an element of $C_1(v_1, v_1, refl_v_1)$, which leads us into the
    second induction. Put
    $
      C_2 (x, z, q) :peq product_(w : A) product_(r : z = w) refl_x bullet (q bullet r) = (refl_x bullet q) bullet r \
    $
    so that for $v_2 : A$, we have
    $
      C_2(v_2, v_2, refl_v_2) peq product_(w : A) product_(r : v_2 = w) refl_v_2 bullet (refl_v_2 bullet r) = (refl_v_2 bullet refl_v_2) bullet r.
    $
    We want to construct an element of $C_2(v_2, v_2, refl_v_2)$, which leads us into the
    third induction. Put
    $
      C_3 (x, w, r) :peq refl_x bullet (refl_x bullet r) = (refl_x bullet refl_x) bullet r
    $
    so that for $v_3 : A$, we have
    $
      C_3(v_3, v_3, refl_v_3) peq refl_v_3 bullet (refl_v_3 bullet refl_v_3) = (refl_v_3 bullet refl_v_3) bullet refl_v_3.
    $
    Applying @lemma:identity-transitivity, this reduces to
    $
      C_3(v_3, v_3, refl_v_3) peq refl_v_3 = refl_v_3
    $
    which is inhabited by
    $
      c_3(v_3) :peq refl_refl_v_3.
    $
    Going back up the chain of inductions, we put $c_2 (v_2) :peq ind_=(C_3, c_3, v_2)$ to
    get
    $
      c_2(v_2) : product_(w : A) product_(r : v_2 = w) refl_v_2 bullet (refl_v_2 bullet r) = (refl_v_2 bullet refl_v_2) bullet r
    $
    and we put $c_1(v_1) :peq ind_=(C_2, c_2, v_1)$ to get
    $
      c_1(v_1) : product_(z : A) product_(q : v_1 = z) product_(w : A) product_(r : z = w) refl_v_1 bullet (q bullet r) = (refl_v_1 bullet q) bullet r.
    $
    Finally, we find
    $
      ind_=(C_1, c_1, x, y, p, z, q, w, r) : p bullet (q bullet r) = (p bullet q) bullet r
    $
    as required.#footnote([Phew!])
]

#remark[
  The proofs in @lem:paths-inv-assoc were very explicit, noting each application of the
  $=$-Elim rule with its associated named terms. In #cite(<hottbook>, form: "prose"), the
  authors adopt the convention of writing such proofs much more tersely, using the
  formulation "by induction it is sufficient to assume $p peq refl_x$," and then computing
  the desired result. We, however, will adopt the more explicit form in all our proofs, for
  the sake of clarity and demonstration of understanding. In any case, we will not require
  such complex proofs involving multiple levels of induction for the remainder of this work.
  /*TODO talk about Agda? */
]

#remark[
  The proof of @lem:paths-inv-assoc establishes witnesses to the necessary laws (identity,
  associativity) for the first level of a higher groupoid. To truly show that a type forms
  an $infinity$-groupoid, it would be necessary to prove these laws at every level "up to
  infinity". In #cite(<hottbook>, form: "prose"), the authors note that this can be achieved
  "using the notion of a globular operad". However, for the remainder of this work, we only
  require these coherence laws up to a finite level. By considering the type $A$ in
  @lem:paths-inv-assoc itself as an identity type (and then as an identity between
  identities, etc.), we can rely on these laws up to any finite level we desire.
]

By this equivalence between witnesses to identities and paths in a homotopy space, we will
use the terms "path" and "witness" interchangably from now on.

== Functions and functors

#lemma([HoTT book Lemma 2.2.1])[For $f : A -> B$ a (non-dependent) function and $x : A$,
  $y : A$ elements, there is a function
  $
    ap_f : (x =_A y) -> (f(x) =_B f(y)).
  $

  Moreover, we have
  $ ap_f (refl_z) peq refl_f(z) $
  for all $z : A$.
]
#proof[
  Put
  $
    C : product_(x : A) product_(y : A) (x =_A y) -> UU_i \
    C(x, y, \_) :peq f(x) =_B f(y)
  $
  and
  $
                   & c : product_(z : A) C(z, z, refl_z) \
    \( "i.e." quad & c : product_(z : A) f(z) =_B f(z) \) \
                   & c(z) :peq refl_f(z).
  $
  Then, applying the rule "$=$-Elim" we have
  $
    ap_f :peq ind_(=_A) (C, c, x, y)
  $
  which has the required type.

  Furthermore, by assuming a variable $z : A$ and applying the rule "$=$-Comp", we get
  $
    ap_f (refl_z) peq refl_f(z)
  $
  as required.
]


#lemma([HoTT Book 2.2.2])[TODO: Functoriality of $ap$

  FEEDBACK: not sure we need this but would be good to include for
  completeness]<lemma:ap-functoriality>

#lemma([HoTT Book 2.3.4])[
  For a type family $B : A -> UU_i$, a dependent function $f : product_(x : A) -> B(x)$ and
  elements $a, b : A$, there is a function
  $
    apd_f : product_(p : a = b) transport^B (p, f(a)) =_(B(b)) f(b)
  $
]
#proof[
  We proceed by path induction on $p$. We put
  $
    C : product_(x : A) product_(y : A) (x = y) -> UU_i \
    C(x, y, p) :peq transport^B (p, f(x)) =_B(y) f(y).
  $
  We need to exhibit for all $z : A$ an element
  $
                & c(z) : C(z, z, refl_z) \
    "i.e." wide & c(z) : transport^B (refl_z, f(z)) =_B(z) f(z).
  $
  Recalling that $transport^B (refl_z) peq id_B(z)$, we have
  $ transport^B (refl_z, f(z)) peq f(z) $
  so we put
  $ c(z) :peq refl_f(z). $

  Then, by induction, we get
  $
    ind_= (C, c) : product_(x : A) product_(y : A) product_(p : x = y) C(x, y, p).
  $

  We then define $apd_f :peq ind_= (C, c, a, b)$ as required.
]

- By the existence of $ap_f$ and $apd_f$, we say that all functions in type theory are
  "continuous" -- they preserve paths.

The following lemma describes a useful interaction between $ap$ and $transport$.

#lemma([HoTT 2.3.10])[For types $A$ and $B$, a type family $D: B -> UU_i$, a function
  $f : A -> B$, elements $x, y : A$ and a witness $p : x = y$, we have
  $
    transport^D (ap_f (p)) = transport^(D compose f) (p).
  $
]<lem:transport-ap>
#proof[
  We proceed by path induction on $p$. We put
  $
    C : product_(x : A) product_(y : A) (x = y) -> UU_i \
    C(x, y, p) :peq transport^D (ap_f (p)) = transport^(D compose f) (p).
  $
  For a variable $z : A$, we compute
  $
    C(z, z, refl_z) & peq transport^D (ap_f (refl_z)) = transport^(D compose f) (refl_z) \
                    & peq transport^D (refl_f(z)) = transport^(D compose f) (refl_z) \
                    & peq id_(D(f(z))) = id_(D(f(z)))
  $
  so we put
  $
    c : product_(z : A) C(z, z, refl_z) \
    c(z) :peq refl_id_(D(f(z))).
  $

  By path induction, we have
  $
    ind_=(C, c, x, y, p) : transport^D (ap_f (p)) = transport^(D compose f) (p)
  $
  as required.
]

== Homotopies and equivalences

- We move from identity of elements of types to identity of functions and of types
- We use the term homotopy here to refer to such an identity, in a way which is at face
  value different from our earlier use of homotopy. We will see they become the same (with
  univalence?)

#definition[For a type family $P : A -> UU_i$ and dependent functions
  $f, g : product_(x : A) P(x)$, a *homotopy* from $f$ to $g$ is a dependent function of
  type $f ~ g : UU_i$, where we define
  $
    f ~ g & :peq product_(x : A) f(x) =_(P(x)) g(x)
  $
]

- Proofs which are left to the reader in HoTT:

#lemma([HoTT book 2.4.2])[For a type family $P : A -> UU_i$, homotopy is an equivalence
  relation on each dependent function type $product_(x : A) P(x)$.

  We state this formally using the shorthand $F :peq product_(x : A) P(x)$. We claim the
  following functions exist:
  $
    r & : product_(f : F) f ~ f \
    s & : product_(f : F) product_(g : F) (f ~ g) -> (g ~ f) \
    t & : product_(f : F) product_(g : F) product_(h : F) (f ~ g) -> (g ~ h) -> (f ~ h).
  $
]<lemma:homotopy-equivalence>
#proof[
  Using the notation in @lemma:identity-symmetry and @lemma:identity-transitivity, we define
  $
             r(f) & :peq refl_f(x) \
       s(f, g, p) & :peq p^(-1) \
    t(f, g, p, q) & :peq p bullet q.
  $
]


#lemma[For (non-dependent) functions $e : A -> B$, $f, g : B -> C$ and $h : C -> D$, such
  that there is a homotopy $alpha : f ~ g$, there is a homotopy
  $
    beta : (h compose f compose e) ~ (h compose g compose e).
  $

  That is to say, homotopies are preserved under function
  composition.]<lemma:homotopy-function-composition>
#proof[Let $x : A$ be a variable in the context. Then we have $e(x) : B$ and hence
  $
    alpha(e(x)) : (f compose e)(x) =_C (g compose e)(x).
  $
  Applying $h$ to this path using $ap_h$, we get
  $
    ap_h (alpha(e(x)) : (h compose f compose e)(x) =_D (h compose g compose e)(x).
  $
  Abstracting over $x$ using the "$Pi$-Intr" rule, we get a function
  $
    &beta : product_(x : A) (h compose f compose e)(x) =_D (h compose g compose e)(x) \
    "i.e." wide &beta : (h compose f compose e) ~ (h compose g compose e)
  $
  as required.
]

// - TODO include Lemma 2.4.3? Possibly requires talking about fibrations

#definition[For a function $f : A -> B$, a *quasi-inverse* of $f$ is a triple
  $(g, alpha, beta)$, where
  $
    g : B -> A
  $
  is a function and $alpha$, $beta$ are homotopies such that
  $
    alpha : (f compose g) ~ id_B
  $
  and
  $
    beta : (g compose f) ~ id_A.
  $

  We denote the type of quasi-inverses of $f$ as $qinv(f)$:
  $
       qinv & : (A -> B) -> UU_i \
    qinv(f) & :peq sum_(g : B -> A) (f compose g ~ id_B) times (g compose f ~ id_A).
  $
]

- TODO some examples? Perhaps 2.4.8

- Equivalence of types: use $isequiv : (A -> B) -> UU_i$
- If $isequiv(f)$ is inhabited, $A$ and $B$ are equivalent, written $A tilde.eq B$.

- Define
  $
    isequiv &: (A -> B) ->UU_i \
    isequiv(f) &:peq (sum_(g : B -> A) (f compose g ~ id_B)) times (sum_(h : B -> A) h compose f ~ id_A)
  $

#proposition[For each $f : A -> B$,
  + there is a function of type $qinv(f) -> isequiv(f)$; and
  + there is a function of type $isequiv(f) -> qinv(f)$.

]<prop:qinv-is-equiv>
#proof[
  Statement (1) is satisfied by the function $(g, alpha, beta) |-> (g, alpha, g, beta)$.
  (TODO express in terms of projections? or note that you can...)

  For statement (2), we use the fact that homotopies are equivalence relations
  (@lemma:homotopy-equivalence) and the fact that they are well-behaved under composition
  (@lemma:homotopy-function-composition). Suppose we are given an equivalence
  $(g, alpha, h, beta)$, i.e. functions $g : B -> A$, $h : B -> A$ and homotopies
  $alpha : f compose g ~ id_B$, $beta : h compose f ~ id_A$.

  To give a quasi-inverse, we will construct a homotopy $beta' : g compose f ~ id_A$, so
  that our quasi-inverse will be given by $(g, alpha, beta')$.

  First, we consider the homotopy $beta$ inverted and pre-composed with $g$ to get a
  homotopy
  $
    g ~ h compose f compose g.
  $
  Similarly, consider the homotopy $alpha$ post-composed with $h$ to get
  $
    h compose f compose h ~ h.
  $

  We therefore have a homotopy
  $ gamma : g ~ h. $

  Pre-composing $f$ with $gamma$, we get
  $ gamma' : g compose f ~ h compose f $
  and since we have $beta : h compose f ~ id_A$, we have a homotopy
  $
    beta' : g compose f ~ id_A.
  $

]

@prop:qinv-is-equiv tells us that the concepts of equivalence and having a quasi-inverse are
equivalent. We will use to show an interesting property of the singleton type $one$: not
only does it have a single element, but indeed there is only a single witness to any
equality between its elements.

#theorem([HoTT 2.8.1])[For any $x, y : one$, we have $x = y equiv one$.]<thm:one-is-a-set>
#proof[
  We construct a function $f : (x =_one y) -> one$ by setting $f(\_) :peq star$ and we aim
  to show that it has a quasi-inverse. We need a function $g : one -> (x =_one y)$. By the
  rule "$one$-Elim", it is sufficient to provide a value of $x =_one y$ to construct $g$.
  However we know that we have $refl_star : x =_one star$ and $refl_star : y =_one star$ by
  (TODO uniqueness of elements of $one$), so we can invert and compose as necessary to
  obtain $refl_star : x =_one y$. Formally, we put
  $
    g :peq ind_one (lambda (\_ : ) sd (x =_one y), refl_star)
  $
  so that $g$ has the type
  $
    g : one -> (x =_one y).
  $

  We then wish to show that there are homotopies
  $ alpha : f compose g ~ id_one wide "and" wide beta : g compose f ~ id_(x =_one y), $
  i.e. we wish to construct functions
  $
    alpha : product_(a : one) f(g(a)) =_one a wide "and" wide beta : product_(p : x =_one y) g(f(p)) =_(x =_one y) p.
  $

  For $alpha$, we fix a variable $a : one$ and compute $f(g(a))$. Since $f$ sends every
  argument to $star$, we have $f(g(a)) peq star$. Again by (TODO uniqueness of elements of
  $one$) we have $refl_star : a =_one star$, so we have $refl_star : f(g(a)) =_one a$.
  Abstracting over the variable $a$ (removing it from the context), we use the rule
  "$Pi$-Intr" to construct
  $
    & alpha : f compose g ~ id_one \
    & alpha(a) :peq refl_star.
  $

  For $beta$, we use the path induction principle (rules "$=$-Intr" and "$=$-Comp"). We set
  $
    & C : product_(x : one) product_(y : one) (x =_one y) -> UU_i \
    & C(x, y, p) :peq g(f(p)) =_(x =_one y) p \
  $
  so that we need to provide a function
  $
                & c : product_(z : one) C(z, z, refl_z) \
    "i.e." wide & c : product_(z : one) g(f(refl_z)) =_(z =_one z) refl_z.
  $

  For a variable $z : one$, we compute $g(f(refl_z))$. We have $f(refl_z) peq star$, and by
  the rule "$one$-Comp" we have $g(star) peq refl_star$. We therefore wish to exhibit an
  element
  $
    r : refl_star =_(z =_one z) refl_z.
  $
  Since we know $z =_one star$ is inhabited, we have
  $refl_(refl_star) : refl_z =_(z =_one z) refl_star$ (FEEDBACK is this correct?), so we put
  $
    c(z) :peq refl_refl_star.
  $
  Then we derive
  $
           & beta :peq ind(C, c, x, y) : product_(p : x =_one y) g(f(p)) =_(x =_one y) p \
    "i.e." & beta : g compose f ~ id_(x =_one y).
  $

  Therefore we have exhibited a quasi-inverse to $f$ as required.

  - TODO make a note somewhere about this proof being significantly more in-depth than in
    HoTT book
]

// #example([Finite sets TODO])[
//   We show that $Fin(n)$ has exactly $n$ elements. We do this by recalling our definition of
//   $<=$ from (TODO earlier):
//   $
//     n <= m :peq sum_(p : NN) n + p = m
//   $

//   We define a type family $B : NN -> UU_i$ as
//   $
//     B(n) :peq sum_(k : NN) (succ(k) <= n).
//   $
//   That is, $B(n)$ consists of pairs of natural numbers $k$ and witnesses to the type
//   $succ(k) <= n$, so the left projections of its elements consist precisely of natural
//   numbers strictly less than $n$. (Note that $n <= m$ is itself defined as a pair type, so
//   elements of $B(n)$ will have the form $(k, (p, q))$ where $k : NN$, $p : NN$ and
//   $q : succ(k) + p = n$.)

//   We therefore want to show a sequence of equivalences
//   $
//     product_(n : NN) Fin(n) equiv B(n).
//   $
//   Because we are working with a sequence of equivalences over $NN$, we will make our
//   quasi-inverses functions of $NN$ also.

//   We want functions
//   $
//     f : product_(n : NN) Fin(n) -> B(n), quad g : product_(n : NN) B(n) -> Fin(n)
//   $
//   and sequences of homotopies
//   $
//     alpha : product_(n : NN) f(n) compose g(n) ~ id_B(n), quad beta : product_(n : NN) g(n) compose f(n) ~ id_Fin(n).
//   $

//   We define $f$ by pattern matching:
//   $
//     & f(0) : Fin(0) -> B(0) \
//     & f(0, z) :peq ind_zero (lambda (\_ : zero) sd B(0), z)
//   $
//   that is, when $n peq 0$, $Fin(0) peq zero$, so we can use $ind_zero$ to give us an element
//   of whatever type we like. The case for a successor itself uses pattern matching for
//   coproduct and pair types:
//   $
//     & f(succ(n)) : Fin(succ(n)) -> B(succ(n)) \
//     & f(succ(n), inl(star)) :peq (0, (n, refl_succ(n))) \
//     & f(succ(n), inr(y)) :peq (succ(k), (p, ap_succ (q))) \
//     & wide "where" (k, (p, q)) peq f(n, y).
//   $

//   We define $g$ also by pattern matching. Considering $g(0)$, we want a function
//   $
//     g(0) : B(0) -> Fin(0),
//   $
//   but recalling that $Fin(0) peq zero$, this means we must construct an element of $zero$
//   given $k : NN$, $p : NN$ and $q : succ(k) + p = 0$. To do this, we introduce a type family
//   $code : NN -> UU_i$ defined by
//   $
//     & code(0) :peq zero \
//     & code(succ(\_)) :peq one
//   $
//   and transport $code(succ(k) + p))$ across the equality $q$. From the definition of $add$,
//   we know that $succ(k) + p$ is a successor, so $code(succ(k) + p) peq one$. Therefore we
//   have
//   $
//     transport^code (q, star) : code(0)
//   $
//   i.e. an element of $zero$. So we put
//   $
//     g(0, (k, (p, q))) :peq transport^code (q, star) : Fin(0).
//   $
//   We then put
//   $
//     & g(succ(n), (0,       && (p, q))) :peq inl(star) \
//     & g(succ(n), (succ(m), && (p, q))) :peq inr(g(n, (m, (p, q)))).
//   $

//   It remains to construct the sequences of homotopies $alpha$ and $beta$. Let us consider
//   $alpha$ first.

//   Fix $n : NN$. We want to construct
//   $
//     alpha(n) : product_(x : B(n)) f(n, g(n, x)) = x
//   $
//   which we do by pattern matching. If $n$ is zero, we have $g(n, x) : zero$ for all
//   $x : B(0)$, so we may construct $f(n, g(n, x)) = x$ freely:
//   $
//     alpha(0, x) :peq ind_zero (lambda (z : zero) sd f(n, g(n, x)) = x, g(n, x)).
//   $
//   If $n$ is a successor, i.e. $n peq succ(n')$, and $x$ is $(0, (p, q))$, then we have
//   $ g(succ(n'), (0, (p, q))) peq inl(star), $
//   and
//   $ f(succ(n'), inl(star))) peq (0, (n', refl_succ(n'))) $
//   so we need to show that $p = n'$ and $q = refl_succ(n')$. We have
//   $
//     q : succ(0) + p = succ(n'),
//   $
//   and by the uniqueness of paths in $NN$ (TODO move to after that theorem), we must have $q : refl_succ(n')$ and hence $p = n'$.

//   So we put
//   $
//   alpha(0, (succ(n'), (p, q))) :peq
//   $
//   TODO: I don't know if this is worth it
// ]

== Transport and coding

One of the uses of the $transport$ function is when it is combined with a method of proof
called "coding". When we use coding, we define a type family $code : A -> UU_i$, which turns
an element of $A$ into some type which we find useful. Given an equality $p : x =_A y$, we
transport a value of $code(x)$ into a value of $code(y)$, which we then use to make some
statement about $x$ and $y$ when they are equal. This is best illustrated with an example.

#example[
  We consider the coproduct type $A + B$ for types $A$ and $B$ and show that for all $a : A$
  and $b : B$, it is not the case that $inl(a) =_(A + B) inr(b)$.

  Fixing types $A$, $B$ and variables $a : A$, $b : B$, we translate this logical statement
  into type theory. We wish to construct a function
  $
    f : (inl(a) = inr(b)) -> zero.
  $

  To do this, we use the coding method. We define, by pattern matching,
  $
    code : A + B -> UU_i
  $$
    & code(inl(\_)) :peq one \
    & code(inr(\_)) :peq zero.
  $
  The transport function $transport^code$ has type
  $
    transport^code : (inl(a) = inr(b)) -> code(inl(a)) -> code(inr(b)).
  $
  By computing using judgmental equalities, we have $code(inl(a)) peq one$ and
  $code(inr(b)) peq zero$, so we have a function
  $
    transport^code : (inl(a) = inr(b)) -> one -> zero.
  $
  By partially applying just the second parameter, we get the desired function:
  $
    f(p) :peq transport^code (p, star).
  $
]

Now that we are familiar with the coding method, we can use it in the following proof about
natural numbers. We wish to show a property similar to @thm:one-is-a-set, but for the
natural numbers, i.e. that for natural numbers $n : NN$ and $m : NN$, we have
$n = m equiv one$ if $n = m$ is inhabited, and $n = m equiv zero$ otherwise. We use the
coding method, and introduce the type family $code : NN -> NN -> UU_i$, defined by
doubly-recursive pattern matching:

$
              code(0, 0) & :peq one \
        code(0, succ(n)) & :peq zero \
        code(succ(m), 0) & :peq zero \
  code(succ(m), succ(n)) & :peq code(m, n)
$

#theorem([HoTT 2.13.1])[For all $m, n : NN$, we have
  $ (m = n) equiv code(m, n). $

  That is to say, there is at most one witness to $m = n$.
]<thm:n-is-set>
#proof[
  We define
  $
    encode : product_(m : NN) product_(n : NN) (m = n) -> code(m, n)
  $
  by using the transport function with the type $code(m, -)$:
  $
    encode(m, n, p) :peq transport^(code(m, -)) (p, star).
  $
  Let us briefly type-check this, to be comfortable with what is happening here. We
  temporarily assume we have variables $m, n : NN$ and $p : m = n$ in context, and we
  compute $code^((m, -))$. We have
  $
    transport^code(m, -) : (m = n) -> code(m, m) -> code(m, n).
  $
  We can deduce that $code(m, m) peq one$ from the definition#footnote([although such a
    deduction requires a proof of length $O(m)$]), so the term on the right-hand side of the
  definition of $encode$ indeed has the correct type:
  $
    transport^code(m, -) (p, star) : code(m, n).
  $

  We then define
  $
    decode : product_(m : NN) product_(n : NN) code(m, n) -> (m = n)
  $
  using doubly-recursive pattern matching. For clarity, we annotate each partial definition
  with its computed type.
  $
    decode(0, 0) & :peq lambda (\_ : one) sd refl_0 && : one -> (0 = 0)\
    decode(0, succ(n)) & :peq ind_zero (lambda (\_ : zero) sd (0 = succ(n))) && : zero -> (0 = succ(n)) \
    decode(succ(m), 0) & :peq ind_zero (lambda (\_ : zero) sd (succ(m) = 0)) && : zero -> (succ(m) = 0)\
  $
  and the final partial definition (which is presented separately for typographical
  reasons):
  $
    decode & (succ(m), succ(n)) :peq \
           & lambda (c : code(succ(m), succ(n))) sd ap_succ (decode(m, n, c)) \
           & : code(succ(m), succ(n)) -> (succ(m) = succ(n)) \
  $

  Fix $m, n : NN$ in context. We aim to show, for all $m, n : NN$, that $encode(m, n)$ and
  $decode(m, n)$ are quasi-inverses, i.e. to exhibit homotopies
  $
    alpha & : encode(m, n) compose decode(m, n) ~ id_(code(m, n)) \
     beta & : decode(m, n) compose encode(m, n) ~ id_(m = n).
  $

  For $beta$, we wish to construct
  $
    beta : product_(p : m = n) decode(m, n, encode(m, n, p)) =_(n = m) p,
  $
  which we do by path induction on $m = n$. Put
  $ C(m, n, p) :peq decode(m, n, encode(m, n, p)) =_(n = m) p. $
  We wish to define $c : product_(n : NN) C(n, n, refl_n)$. Recalling from the definition of
  $transport$ that
  $ transport^code(n, -) (refl_n, star) peq star : one, $
  we compute
  $
    C(n, n, refl_n) & peq decode(n, n, encode(n, n, refl_n)) =_(n = n) refl_n \
                    & peq decode(n, n, star) =_(n = n) refl_n.
  $
  We define $c$ by recursive pattern matching: when the argument to $c$ is zero, we have
  $decode(0, 0, star) peq refl_0$, so $C(0, 0, refl_0) peq refl_0 = refl_0$. We therefore
  put
  $
    c(0) :peq refl_refl_0 : C(0, 0, refl_0).
  $
  When the argument to $c$ is $succ(n)$, we first compute
  $
    decode(succ(n), succ(n), star) peq ap_succ (decode(n, n, star))
  $
  so we need to construct a value of
  $ ap_succ (decode(n, n, star)) = refl_succ(n). $
  But we may recursively use $c(n)$, which has the type
  $
    c(n) : decode(n, n, star) = refl_n.
  $
  Recalling that $ap_succ (refl_n) peq refl_succ(n)$, we put
  $
    c(succ(n)) :peq ap_ap_succ (c(n)).
  $
  We have now constructed $c : product_(n : NN) C(n, n, refl_n)$, so we may put
  $ beta :peq ind_=_N (C, c, m, n) $
  and derive by path induction
  $
    beta : product_(p : m = n) decode(m, n, encode(m, n, p)) =_(n = m) p
  $
  as required.

  For $alpha$, we wish to construct
  $
    alpha : product_(a : code(m, n)) encode(m, n, decode(m, n, a)) =_code(m, n) a
  $
  We do this by defining
  $
    alpha' : product_(m : NN) product_(n : NN) product_(a : code(m, n)) encode(m, n, decode(m, n, a)) =_code(m, n) a
  $
  and then writing $alpha :peq alpha'(m, n)$ for the $m$ and $n$ in our context. We proceed
  in defining $alpha'$ by doubly-recursive pattern matching. If the arguments are both zero,
  we have $code(0, 0) peq one$, $decode(0, 0, \_) peq refl_0$, and
  $encode(0, 0, refl_0) peq transport^code(m, -) (refl_0, star) peq star$, so we need to
  provide a witness to $star = a$. By @prop:one-is-a-singleton, $refl_star$ is such a
  witness, so we put
  $
    alpha'(0, 0) :peq lambda (a : one) sd refl_star.
  $

  If the arguments are zero and a successor, we have $code(0, succ(n)) peq zero$, so we may
  use the $zero$-Elim rule to get our desired type:
  $
    alpha'(0, succ(n)) :peq ind_zero (lambda (a : zero) sd encode(0, succ(n), decode(0, succ(n), a) = a))
  $
  similarly for a successor and zero we put,
  $
    alpha'(succ(m), 0) :peq ind_zero (lambda (a : zero) sd encode(succ(m), 0, decode(succ(m), 0, a) = a)).
  $
  For the case of defining $alpha'(succ(m), succ(n))$, we fix $a : code(succ(m), succ(n))$
  and compute:
  $
    encode & (succ(m), succ(n), decode(succ(m), succ(n), a)) \
           & peq encode(succ(m), succ(n), ap_succ (decode(m, n, a))) \
           & peq transport^code(succ(m), -) (ap_succ (decode(m, n, a)), star)
  $
  by definitions of $encode$ and $decode$. Then by @lem:transport-ap, we have a witness $q$
  to the following equality:
  $
    q : & transport^code(succ(m), -) (ap_succ (decode(m, n, a)), star) \
        & = transport^code(succ(m), succ(-)) (decode(m, n, a), star).
  $
  Recalling from the definition of $code$ that $code(succ(m), succ(n)) peq code(m, n)$, we
  have
  $
    transport^code(succ(m), succ(-)) & (decode(m, n, a), star) \
                                     & peq transport^code(m, -) (decode(m, n, a), star) \
                                     & peq encode(m, n, decode(m, n, a)).
  $
  So our witness $q$ has the computed type
  $
    q : & encode(succ(m), succ(n), decode(succ(m), succ(n), a)) \
        & = encode(m, n, decode(m, n, a)).
  $

  Recall that by recursive pattern matching, we may suppose in the definition of
  $alpha'(succ(m), succ(n), a)$ that
  $ alpha'(m, n, a) : encode(m, n, decode(m, n, a)) = a. $
  we put
  $
    alpha'(succ(m), succ(n), a) :peq q bullet alpha'(m, n, a)
  $
  and $alpha'$ is finally fully-defined by recursive pattern matching. To recap, we have
  $
    alpha' : product_(m : NN) product_(n : NN) product_(a : code(m, n)) encode(m, n, decode(m, n, a)) = a
  $
  so we put $alpha :peq alpha'(m, n)$. Therefore we have homotopies
  $
    & alpha : encode(m, n) compose decode(m, n) && ~ id_code(m, n) \
    & beta : decode(m, n) compose encode(m, n)  && ~ id_(m = n)
  $
  and hence an equivalence
  $
    (m = n) equiv code(m, n)
  $
  as required.
]

== Function extensionality and univalence

- Want to consider identity of functions. We have the $eta$ rule to say that functions are
  judgmentally equal if they are pointwise judgmentally equal, but we would like to extend
  this to propositional equality.
- I.e. we would like a witness to
  $
    product_(f : product_(x : A) B(x)) product_(g : product_(x : A) B(x)) (product_(x : A) f(x) =_B(x) g(x)) -> f =_(product_(x : A) B(x)) g
  $
- We can certainly go the other way, by an application of path induction:

#lemma[For a type $A$, a type family $B : A -> UU_i$ and functions
  $f, g : product_(x : A) B(x)$, there is a function
  $
    happly : (f = g) -> product_(x : A) f(x) = g(x).
  $
  That is to say that if two functions are (propositionally) equal, then they are
  (propositionally) equal pointwise.
]
#proof[
  Fix $A, B, f, g$ as in the statement of the lemma. For brevity, we write the type
  $product_(x : A) B(x)$ as $F$. Put
  $
    C : product_(f : F) product_(g: F) f = g -> UU_i \
    C(f, g, \_) :peq product_(x : A) f(x) = g(x).
  $
  For a variable $z : F$ we compute $C(z, z, refl_z) peq product_(x : A) z(x) = z(x)$, so we
  put
  $
    c : product_(z : F) C(z, z, refl_z) \
    c(z) :peq lambda (x : A) sd refl_(z(x)).
  $
  We then define $happly :peq ind_=(C, c, f, g)$ to get
  $
    happly : (f = g) -> product_(x : A) f(x) = g(x)
  $
  as required.
]

- We have no way to go back the other way, so we must take it as an axiom:

#axiom([Function extensionality])[
  For a type $A$, a type family $B : A -> UU_i$ and functions $f, g: product_(x : A) B(x)$,
  the function
  $
    happly : (f = g) -> product_(x : A) f(x) = g(x)
  $
  is an equivalence. That is to say, there is a function of type
  $
    funext : (product_(x : A) f(x) = g(x)) -> f = g.
  $
]

- We now consider the transport function in the case of identities between functions
- We want to transport a function $f : A(x_1) -> B(x_1)$ along an equality $x_1 = x_2$ to
  get a function $g : A(x_2) -> B(x_2)$.
- We can express this already with our $transport$ function, setting the type family to be
  transported over to be $x |-> A(x) -> B(x)$, but we show that this is equivalent to
  something else:

#lemma[
  For a type $X$, elements $x_1, x_2 : X$, type families $A, B : X -> UU_i$ and a function
  $f : A(x_1) -> B(x_1)$, we have
  $
    transport^(lambda (x : X) sd A(x) -> B(x)) (p, f) = \
    (lambda (x : A(x_2)) sd transport^B (p, f(transport^A (p^(-1), x)))).
  $

  That is to say, if we want to compute the transport of a function $f : A(x_1) -> B(x_1)$
  across an equality $x_1 = x_2$, we can apply the following process: first transport its
  parameter across $p^(-1) : x_2 = x_1$ to get an element of $A(x_1)$, then apply $f$ to get
  an element of $B(x_1)$, then transport back across $p : x_1 = x_2$ to get an element of
  $B(x_2)$.

  This corresponds to the following commutative diagram of functions and types:
  #align(center)[
    #diagram({
      let ax1 = (0, 1)
      let ax2 = (0, 0)
      let bx1 = (1, 1)
      let bx2 = (1, 0)
      node(ax2, $A(x_2)$)
      node(bx2, $B(x_2)$)
      node(ax1, $A(x_1)$)
      node(bx1, $B(x_1)$)
      edge(ax2, bx2, "->", $transport^(lambda (x : X) sd A(x) -> B(x))(p, f)$)
      edge(ax2, ax1, "->", $transport^A (p^(-1))$)
      edge(ax1, bx1, "->", $f$)
      edge(bx1, bx2, "->", $transport^B (p)$)
    })

  ]
]
#proof[
  We proceed by path induction. Fix $X, A, B$ as in the lemma and let
  $ f' : product_(x_1 : X) A(x_1) -> B(x_1). $
  We put
  $
    // & C &   & : product_(x_1 : X) product_(x_2 : X) (x_1 = x_2) -> UU_i \
    C & (x_1, x_2, p) :peq \
      & transport^(lambda (x : X) sd A(x) -> B(x)) (p, f'(x_1)) = \
      & (lambda (x : A(x_2)) sd transport^B (p, f'(x_1, transport^A (p^(-1), x))))
  $
  and compute $C(z, z, refl_z)$ for $z : X$. For $x : A(z)$, we have
  $
    transport^A (refl_z^(-1), x) peq x
  $
  and
  $
    transport^B (refl_z, f'(z, x)) peq f'(z, x),
  $
  so we have a judgmental equality (using the $eta$-rule) for the right-hand side of
  $C(z, z, refl_z)$:
  $ lambda (x : A(z)) sd transport^B (refl_z, f'(z, x)) peq f'(z). $
  Considering the left-hand side, we have
  $
    transport^(lambda (x : X) sd A(x) -> B(x)) (refl_z, f'(z)) peq f'(z)
  $
  so we may put
  $
    c(z) :peq refl_(f'(z)).
  $
  Therefore, fixing $x_1, x_2 : A$ and writing $f :peq f'(x_1)$, we have
  $
    ind_= & (C, c, x_1, x_2, p) : \
          & transport^(lambda (x : X) sd A(x) -> B(x)) (p, f) = \
          & lambda (x : A(x_2)) sd transport^B (p, f(transport^A (p^(-1), x)))
  $
  as required.
]

== Sets

- Sets are types where witnesses are unique

#definition[We say that a type $A$ is a *set* if for all $x, y : A$ and all paths
  $p, q : x =_A y$, we have a path $r : p =_(x =_A y) q$.

  Formally, we define a type family $isSet$ by
  $
    isSet : A -> UU_i \
    isSet(A) :peq product_(x : A) product_(y : A) product_(p : x = y) product_(q : x = y) p = q.
  $
]

- These correspond to groupoids where homotopies between paths consist only of identity
  - (TODO/FEEDBACK: we can show that higher paths being identities $=>$ witnesses are
    unique, but can we show converse?)
- We saw that $one$ and $NN$ are sets
- $zero$ is a set because we can construct
  $product_(x : zero) product_(y : zero) product_(p : x = y) product_(q : x = y) p = q$
  freely by the $zero$-Intr rule
- If witnesses in a type form a set, call that set a 1-type. Similarly if witnesses to
  witnesses form a set, that's a 2-type, and so on.
- All sets are 1-types, all 1-types are 2-types, etc. They are upward-closed
#definition[
  TODO words
  $
    is1Type : A -> UU_i \
    // is1Type(A) :peq product_(x : A) product_(y : A) product_(p : x = y) product_(q : x = y) product_(r : p = q) product_(s : p = q) r = s\
    is1Type(A) :peq product_(x : A) product_(y : A) isSet(x =_A y)
  $
]
- Proof of upward-closedness requires a lemma about transport

#lemma[For $A : UU_i$, $a, x, y : A$ and $p : x =_A y$, we have
  $
    &transport^(x |-> a = x) (p, q) &&=_(a = y) q bullet p quad &&"for" q : a = x \
    &transport^(x |-> x = a) (p, q) &&=_(y = a) p^(-1) bullet q quad &&"for" q : x = a \
    &transport^(x |-> x = x) (p, q) &&=_(y = y) p^(-1) bullet q bullet p quad &&"for" q : x = x
  $
]<lem:transport-path-composition>
#proof[
  /* TODO write more words */
  For the first claim, we consider the case of $q : a =_A x$. We put
  $
    C(x, y, p) :peq product_(q : a = x) transport^(x |-> a = x) (p, q) = q bullet p \
  $
  We wish to exhibit, for all $z : A$, an element of type
  $ product_(q : a = z) transport^(x |-> a = x) (refl_z, q) = q bullet refl_z $
  but we have
  $ transport^(x |-> a = x)(refl_z, q) peq q $
  by @thm:indiscernibility-of-identicals, and we have a path $r : q = q bullet refl_z$ by
  @lem:paths-inv-assoc, so we put
  $
    c(z) :peq refl_q bullet r : C(z, z, refl_z).
  $
  By induction we get
  $
    ind(C, c) : product_(x : A) product_(y : A) product_(p : x = y) product_(q : a = x) transport^(x |-> a = x)(p, q) =_(a = x_2) q bullet p
  $

  The second and third claims are analogous, by altering the type of $q$.
]

#lemma[If $A$ is a set, then $A$ is a 1-type, i.e. there is a function
  $ g : isSet(A) -> is1Type(A). $
]
#proof[
  #figure(
    diagram({
      let A = (0, 0)
      let gm = (0, 1)
      let dlt = (0, 2)
      let gmp = (-1, 3)
      let dltp = (1, 3)
      node(A, $A : UU_i$)
      node(gm, $Gamma$)
      node(dlt, $Delta$)
      node(dltp, $Delta'$)
      node(gmp, $Gamma'$)
      edge(gm, A, "->")
      edge(dlt, gm, "->")
      edge(gmp, dlt, "->")
      edge(dltp, dlt, "->")

      edge(dlt, dltp, "->", stroke: blue, bend: -30deg, label: text(blue)[$1$])
      edge(dltp, dlt, "->", stroke: blue, bend: -30deg, label: text(blue)[$2^*$])
      edge(dlt, gmp, "->", stroke: blue, bend: 30deg, label: text(blue)[$3$])
      edge(gmp, gm, "->", stroke: blue, bend: 30deg, label: text(blue)[$4^*$])
      edge(gm, A, "->", stroke: blue, bend: 30deg, label: text(blue)[$5^*$])
    }),
    caption: [A visualization of contexts used in this proof. Black arrows represent context
      inclusion (e.g. $Delta$ includes $Gamma$) and blue arrows denote the movement as we go
      through the proof. Blue arrows marked with an asterisk denote that the move involves a
      $beta$-reduction.],
  )
  Let the context $Gamma$ consist of $A : UU_i, f : isSet(A)$. We aim to exhibit an element
  $g' : is1Type(A)$, and hence by $beta$-reduction an element $g$ such that
  $ A : UU_i tack g : isSet(A) -> is1Type(A). $

  In the context $Delta :peq (Gamma, x : A, y : A, p : x = y)$, we define a function $g$ by
  $
    g : product_(q : x = y) p = q \
    g :peq f(x, y, p).
  $

  Then, in the context
  $ Delta' :peq Delta, q : x = y, q' : x = y, r : q = q', $
  we compute $apd_g (r)$. Recall that ... TODO facts about $apd$ ..., so we have
  $
    transport^(x |-> p = x) (r, g(q)) : p = q'.
  $
  and
  $
    apd_g (r) : transport^(x |-> p = x) (r, g(q)) = g(q').
  $
  By @lem:transport-path-composition, we have a path
  $
    t : transport^(x |-> p = x) (r, g(q)) = g(q) bullet r
  $
  so by path composition we get
  $
    t^(-1) bullet apd_g(r) : g(q) bullet r = g(q').
  $
  Applying $beta$-reduction over the variables introduced in context $Delta'$, we get a
  function $h$ in context $Delta$ such that
  $
    Delta tack h : product_(q : x=y) product_(q' : x = y) product_(r : q = q') g(q) bullet r = g(q').
  $

  Now, in the context
  $
    Gamma' :peq Delta, q : x = y, r : p = q, s : p = q,
  $
  we apply $h(p, q, r)$ and $h(p, q, s)$ to get
  $
    h(p, q, r) : g(p) bullet r = g(q) quad "and" quad h(p, q, s) : g(p) bullet s = g(q)
  $
  hence
  $
    && h(p, q, r) bullet h(p, q, s)^(-1) &: g(p) bullet r = g(p) bullet s \
    => quad && ap_(g(p)^(-1) bullet -)(h(p, q, r) bullet h(p, q, s)^(-1) ) &: r = s.
  $

  Then applying $beta$-reduction over the variables in $Gamma'$, we get a function in
  $Gamma$,
  $
    &Gamma tack g' : product_(x : A) product_(y : A) product_(p : x = y) product_(q : x = y) product_(r : p = q) product_(s : p = q) r = s \
    "i.e." quad &Gamma tack g' : is1Type(A).
  $
  Finally, applying a further $beta$-reduction over $f : isSet(A)$ in $Gamma$, we get
  $
    A : UU_i tack g : isSet(A) -> is1Type(A)
  $
  as required.
  - TODO remark about contexts not being explicit in HoTT book
]
