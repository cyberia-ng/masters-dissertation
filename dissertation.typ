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
#let one = $bold(1)$
#let ctx = $sans("ctx")$
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

Type theory is an instance of a *typed $lambda$-calculus*, and in our presentation the basic
terms may be _variables_, _primitive constants_ or _defined constants_. Terms are formed
according to the rule

$
  t ::= x | lambda x sd t | t(t') | c | f.
$

Here, $x$ stands for any variable, $t$ is any term, $c$ is any primitive constant and $f$ is
any defined constant.

The distinction between primitive and defined constants is that primitive constants are used
to encode new syntax, and will not be able to be reduced by some definition, while defined
constants are taken to be equivalent to some term (by a judgmental equality, which we will
introduce in the next subsection) and thus able to be eliminated or reduced.

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

We discuss context judgments in more depth in the next subsection, but for now suffice to
say they have the form
$
  Gamma ctx.
$

Typing judgments are of the form
$
  t : A
$
which is to be read as "the term $t$ is of the type $A$". Typing judgments are useful for
demonstrating the existence of a term of a particular type.

The final kind of judgment is the judmental equality, which takes the form
$
  t peq t' : A.
$
Sometimes the type annotation "$: A$" will be omitted when it is clear from context. This
judgment is a metatheoretic equality, which is to be contrasted with "internal" equality
which we will introduce later. It says that whenever we see the term $t$, we may rewrite it
as $t'$. (TODO: does $t$ need to be in closed form?)

== Universes and contexts

In order to avoid a situation similar to Russell's paradox (TODO cite and/or clarify), we
define a hierarchy of *universes*, denoted

$ UU_0 : UU_1 : ... $

Each $UU_i$ is an element of $UU_(i + 1)$, and furthermore every universe contains all the
types contained in previous universes. I.e. if $x : UU_i$ then $x : UU_j$ for all $j >= i$.
This is known as the *cumulative* property. When we say $A$ is a type, what we mean is that
$A : UU_i$ for some universe $UU_i$. When working with (a finite number of) types in
different universes, the cumulative property guarantees that we can always find a universe
in which all our types are present.

A *context* is a (possibly empty) collection of distinct variables and their types, for
example $x_1 : A_1, x_2 : A_2$. Contexts are denoted by an uppercase Greek letter, usually
$Gamma$ or $Delta$. The judgment that $Gamma$ is a well-formed context is denoted
$Gamma ctx$, and the empty context is denoted $dot$.

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

== Terms

In order to speak about elements of types, we use *terms*. Terms are syntactic strings which
can be rewritten according to certain deductive rules.

TODO structural rules

== Data for types

For each new type we introduce, we give the following data

- *Formation rules* which specify how to make the type out of existing types.
- *Introduction rules* which specify how to construct terms of the new type.
- *Elimination rules* which specify how to reduce terms of the new type to terms of a
  simpler type.
- *Computation rules* which specify how elimination interacts with construction.
- *Uniqueness principle* (optional) which ???

== Function types

TODO: make discursive, set up for formal defn of dependent function types

#definition([Function types])[
  - *Formation*: If $A$ and $B$ are types, then $A -> B$ is a type.
  - *Introduction*: if $t : B$ is a term, then $lambda x : A sd t : A -> B$ is a term.
  - *Elimination*: if $t : A -> B$ is a term and $s : A$ is a term, then $t s : B$ is a
    term, representing the function $t$ applied at a parameter $s$.
  - *Computation*: if $lambda x : A sd t : A -> B$ is a term and $s : A$ is a term, then
    $(lambda x : A sd t) s peq t[s slash x]$. The notation $t[s slash x]$ means the term $t$
    with all free occurrences of $x$ replaced with $s$.
  - *Uniqueness*: if $f : A -> B$ is a term, then $f peq lambda x : A sd f x$.
]

== Dependent function types

TODO check universes

#pt(rule-set(
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma, x : A tack B : UU_i$,
    $Gamma tack product_(x : A) B : UU_i$,
    name: [$Pi$-Form],
  )),
  prooftree(rule(
    $Gamma, x : A tack b : B$,
    $Gamma tack lambda (x : A) sd b : product_(x : A) B$,
    name: [$Pi$-Intr],
  )),
  prooftree(rule(
    $Gamma tack f : product_(x: A) B$,
    $Gamma tack a : A$,
    $Gamma tack f a : B[a slash x]$,
    name: [$Pi$-Elim],
  )),
  prooftree(rule(
    $Gamma, x : A tack b : B$,
    $Gamma tack a : A$,
    $Gamma tack (lambda (x : A) sd b)(a) peq b[a slash x] : B[a slash x]$,
    name: [$Pi$-Comp],
  )),
  prooftree(rule(
    $Gamma tack f : product_(x : A)B$,
    $Gamma tack f peq lambda (x : A) sd f x : product_(x : A) B$,
    name: [$Pi$-Uniq],
  )),
))

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
