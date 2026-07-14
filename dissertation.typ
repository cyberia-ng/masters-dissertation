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
#let rec = $"rec"$
#let one = $bold(1)$

= Type theory

The basic objects of study in type theory are types, which are denoted by uppercase letters:
$A$, $B$, etc. Unlike in set theory, every object in type theory has a type. In
set-theoretic mathematics, we might make statements such as _"Let $n$ be a natural number.
Then $n$ has a successor."_ What is meant by this is something like "let $n$ denote
something", and then "if $n in NN$, then $n$ has a successor". In type theory this is not
allowed: every object we consider must be constrained by its type. Supposing we have defined
a type $NN$ of natural numbers (which we will do later), we would write $n : NN$ to indicate
that $n$ is a natural number. We may then proceed with the claim about its successor.
// TODO tidy this example
// TODO mention lambda calculus

In this way, we can view types as "containing" elements. Notationally, we write
$
  x : A
$
to mean that $x$ is an element of type $A$.

Types are either *basic types*, which we assume to exist axiomatically, or *compound types*,
which are constructed recursively out of other types. The basic types we choose will be
natural "units" for the various recursive type constructors, for example we will take a
basic type $one$ corresponding to a product type constructor $- times -$.

== Terms

In order to speak about elements of types, we use *terms*. Terms are syntactic strings which
can be rewritten according to certain deductive rules. The idea is to be able to introduce
terms and eliminate them.

== Universes

Before we define our basic and compound types, we first introduce the important notion of
type universes.


In order to avoid a situation similar to Russell's paradox (TODO cite and/or clarify), we
define a hierarchy of *universes*, denoted

$ UU_0 : UU_1 : ... $

Each $UU_i$ is an element of $UU_(i + 1)$, and furthermore every universe contains all the
types contained in previous universes. I.e. if $x : UU_i$ then $x : UU_j$ for all $j >= i$.
This is known as the *cumulative* property. When we say $A$ is a type, what we mean is that
$A : UU_i$ for some universe $UU_i$. When working with (a finite number of) types in
different universes, the cumulative property guarantees that we can always find a universe
in which all our types are present.

== Function types

== Product types

#definition[If $A$ and $B$ are types, there is a *product type* $A times B$. There is also a
  nullary product type $one$.]

An element of a product type may be introduced as a *pair* using bracketing notation. If
$s : A$ and $t : B$ are terms, then $(s, t) : A times B$ is a term.

We assume that a function out of $A times B$ is completely determined by is action on pairs,
and a function out of $one$ is completely determined by is action on a (unique?) element
$star : one$. Using this, we will prove (TODO) that the elements of $A times B$ are
precisely the pairs, and $one$ has a unique element $star$.


== ...



---

with the following rules: supposing $A$ and $B$ are types,
- There is a *function type* $A -> B$.
- There is a *product type* $A times B$.
- There is a *coproduct type* $A + B$.


---

- Judgemental equality vs propositional equality: $peq$ vs $=$
- Function types
  - Definition in closed form or open form

== Type families

Functions of type $B : A -> UU$, i.e. for $x : A$, we have $B(x)$ a type.

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
