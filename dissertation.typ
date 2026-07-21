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
#let rec = $sans("rec")$
#let ind = $sans("ind")$
#let one = $bold(1)$
#let ctx = $sans("ctx")$
#let Fin = $"Fin"$
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

As type theory is syntactic system, we define the construction of its terms. In our
presentation the basic terms may be _variables_, _primitive constants_ or _defined
constants_. Terms are formed according to the rule

$
  t ::= x | lambda x sd t | t(t') | c | f.
$
TODO: or
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

// == Variables

// The concept of a variable is familiar to logicians. They are denoted by a single lowercase
// letter, usually taken from $x, y, z$, with an optional subscript. To indicate $n$ variables
// we will use $x_1, x_2, ..., x_n$. In type theory, all variables are of a particular type,
// which is written $x : A$.

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
which we will introduce later. It says that whenever we see the term $t$, we may rewrite it
as $t'$ and vice versa. (TODO: does $t$ need to have no free variables?)

We write deductive rules in the "proof tree" style, where antecedents are written above a
line and consequents below it:
#pt(prooftree(rule($cal(J)_1$, $cal(J)_2$, $cal(J)_3$)))
This deduction says that from the judgments $cal(J)_1$ and $cal(J)_2$ we may conclude
$cal(J)_3$.

== Universes and contexts

In order to avoid a situation similar to Russell's paradox (TODO cite and/or clarify), we
define a hierarchy of *universes*, denoted

$ UU_0 quad UU_1 quad UU_2 quad ... quad UU_i quad ... $

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
$cal(J)$ contains variables (TODO and types?) declared in the context $Gamma$.

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

== Structural rules

TODO: which of these do we need?

== Data for types

For each new type we introduce, we give the following data

- *Formation rules* which specify how to make the type out of existing types.
- *Introduction rules* which specify how to construct terms of the new type.
- *Elimination rules* which specify how to reduce terms of the new type to terms of a
  simpler type.
- *Computation rules* which specify how elimination interacts with construction.
- *Uniqueness principle* (optional) which ???

== Function types

The first type we will introduce is the (non-dependent) function type. We introduce a
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
    $Gamma tack B : UU_i$,
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

== Type families

A type family is an element of a function type $A -> UU_i$, i.e. it is a function which
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

- TODO check universes
- TODO check this presentation is valid with contexts

#pt(rule-set(
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : A -> UU_i$,
    $Gamma tack product_(x : A) B(x) : UU_i$,
    name: [$Pi$-Form],
  )),
  prooftree(rule(
    $Gamma, x : A tack b : B(x)$,
    $Gamma tack lambda (x : A) sd b : product_(x : A) B(x)$,
    name: [$Pi$-Intr],
  )),
  prooftree(rule(
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
  prooftree(rule(
    $Gamma tack f : product_(x : A)B$,
    $Gamma tack f peq lambda (x : A) sd f x : product_(x : A) B$,
    name: [$Pi$-Uniq],
  )),
))

== Product types

- Introduce primitive constants $c_Sigma$ and $c_"pair"$, writing
  $c_Sigma (A, lambda (x : A) sd B)$ as $sum_(x : A) B(x)$ and $c_"pair" (a, b)$ as
  $(a, b)$.
- Write $sum_(x : A) B(x)$ as $A times B$ if $x$ not free in $B$.

Formation and introduction:
#pt(rule-set(
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : A -> UU_i$,
    $Gamma tack sum_(x : A) B(x) : UU_i$,
    name: [$Sigma$-Form],
  )),
  prooftree(rule(
    $Gamma tack a : A$,
    $Gamma, x : A tack b : B(x)$,
    $Gamma tack (a, b) : sum_(x : A) B(x)$,
    name: [$Sigma$-Intr],
  )),
  prooftree(rule(
    $Gamma, x : A tack B(x) : UU_i$,
    $Gamma tack a : A$,
    $Gamma tack b : B(a)$,
    $Gamma tack (a, b) : sum_(x : A) B(x)$,
    name: [$Sigma$-Intr\*],
  )),
))

TODO: is $Sigma$-Intr correct? differs from appendix slightly.

Elimination and computation:

#pt(rule-set(
  prooftree(rule(
    $Gamma tack C : sum_(x : A) B(x) -> UU_i$,
    $Gamma tack g : product_(x : A) product_(y : B) C((x, y))$,
    $Gamma tack p : sum_(x : A) B(x)$,
    $Gamma tack ind_(sum_(x : A) B(x)) (C, g, p) : C(p)$,
    name: [$Sigma$-Elim],
  )),
  prooftree(rule(
    $Gamma tack C : sum_(x : A) B(x) -> UU_i$,
    $Gamma tack g : product_(x : A) product_(y : B) C((x, y))$,
    $Gamma tack a : A$,
    $Gamma, x : A tack b : B(x)$,
    $Gamma tack ind_(sum_(x : A) B(x)) (C, g, (a, b)) peq g(a, b)$,
    name: [$Sigma$-Comp],
  )),
  prooftree(rule(
    $Gamma tack C : sum_(x : A) B(x) -> UU_i$,
    $Gamma tack g : product_(x : A) product_(y : B) C((x, y))$,
    $Gamma tack a : A$,
    $Gamma tack b : B(a)$,
    $Gamma tack ind_(sum_(x : A) B(x)) (C, g, (a, b)) peq g(a, b)$,
    name: [$Sigma$-Comp\*],
  )),
))

// #definition[If $A$ and $B$ are types, there is a *product type* $A times B$. There is also a
//   nullary product type $one$.]

// An element of a product type may be introduced as a *pair* using bracketing notation. If
// $s : A$ and $t : B$ are terms, then $(s, t) : A times B$ is a term.

// We assume that a function out of $A times B$ is completely determined by is action on pairs,
// and a function out of $one$ is completely determined by is action on a (unique?) element
// $star : one$. Using this, we will prove (TODO) that the elements of $A times B$ are
// precisely the pairs, and $one$ has a unique element $star$.


#block[
  #set text(luma(130))
  == ... Fragments ...



  ---

  with the following rules: supposing $A$ and $B$ are types,
  - There is a *function type* $A -> B$.
  - There is a *product type* $A times B$.
  - There is a *coproduct type* $A + B$.


  ---

  - Judgemental equality vs propositional equality: $peq$ vs $=$
  - Function types
    - Definition in closed form or open form

  == Dependent functions

  Functions whose output type depends on the input (type or value). Given a type $A$ and a
  family $B : A -> UU$, write
  $ f : product_(x : A) B(x) $
  to mean a function which takes a parameter $x$ of type $A$ and returns a value of type
  $B(x)$.

  == Product types

  === "Recursor"

  - Generic way to construct functions taking product parameters, using simple functions

  $
    & rec_(A times B) : product_(C: UU) (A -> B -> C) -> A times B -> C \
    & rec_(A times B) (C, g, (a, b)) :peq g(a)(b)
  $

  Projections:
  $
    pi_1 & :peq rec_(A times B)(A, lambda a sd lambda b sd a) \
    pi_2 & :peq rec_(A times B)(B, lambda a sd lambda b sd b)
  $
]
