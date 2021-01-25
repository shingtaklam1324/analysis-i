# Lean Formalisation of IA Analysis I

This is my Lean formalisation of the First Year Real Analysis Course at the
University of Cambridge.

Note that the statements of lemmas are written in terms of filters. Often I will
write a statement using filters, but the prove them using standard epsilon-N or
epsilon-delta arguments. The reason for stating them in terms of filters is to
be able to use the lemmas already within the library.

As a result of this, instead of definitions, often I will prove the equivalence
of the filter definition with the common mathematical definition. This allows us
to both use lemmas in mathlib, as well as prove them manually.
