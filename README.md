This is the formalization accompanying the paper:

- Cezary Kaliszyk and Karol Pąk
  "Semantics of Mizar as an Isabelle Object Logic"
  [doi:10.1007/s10817-018-9479-z](https://dx.doi.org/10.1007/s10817-018-9479-z)

I assume they have the copyright to the code, I do not know. But this is
my attempt to make it work with Isabelle-2023 (since it was written to
work with Isabelle-2017).

A list of encountered problems may be found in the
[changes](./changes.md) file.

## Attribute semantics

The more complicated semantics as discussed in:

- Cezary Kaliszyk and Karol Pąk
  "Presentation and Manipulation of Mizar Properties in an Isabelle Object Logic"
  https://alioth.uwb.edu.pl/~pakkarol/articles/CKKP-CICMMKM17.pdf

is in the `mizar-cicm2017` subdirectory. It has more realistic attribute
semantics. This was last modified 30-Mar-2017 07:00 and was compatible with
Isabelle 2016-1.

## Structure semantics

There is also the [code](./macis2017/) accompanying the paper:

- Cezary Kaliszyk and Karol Pąk
  "Isabelle Formalization of Set Theoretic Structures and Set Comprehensions"
  http://cl-informatik.uibk.ac.at/cek/docs/17/ckkp-macis17.pdf

was last modified 25-Aug-2017 03:20, works for Isabelle 2016-1.

I have managed to patch it for Isabelle-2023.

# Bugs

There were some minor bugs with defining functors by equality
(`func foo -> type equals bar`), which I have fixed. So now everything
works for Isabelle 2023.

# Annotated Table of Contents

Just some notes to myself where things are located, because sometimes
it's not at all clear.

- mizar
  - [`mizar_defs.thy`](./mizar/mizar_defs.th) formalizes syntax of
    Isabelle-ized definitions
  - [`mizar_reserve.thy`](./mizar/mizar_reserve.th) formalizes the
    parsing of Isabelle-ized definitions, as well as reservations
  - [`mizar_ty.thy`](./mizar/mizar_ty.th) encodes Mizar type data using
    Isabelle `Generic_Data`, as well as type inference