This is the formalization accompanying the paper:

  Cezary Kaliszyk and Karol Pąk
  "Semantics of Mizar as an Isabelle Object Logic"
  [doi:10.1007/s10817-018-9479-z](https://dx.doi.org/10.1007/s10817-018-9479-z)

I assume they have the copyright to the code, I do not know. But this is
my attempt to make it work with Isabelle-2023 (since it was written to
work with Isabelle-2017).

A list of encountered problems may be found in the
[changes](./changes.md) file.

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