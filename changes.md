# Change log

Bugs encountered due to upgrading Isabelle.

- [ML antiquotations for object-logic](https://isabelle.systems/zulip-archive/stream/247542-Mirror:-Isabelle-Development-Mailing-List/topic/.5Bisabelle-dev.5D.20NEWS.3A.20ML.20antiquotations.20for.20object-logic.20j.2E.2E.2E.html)
  since 2021, `\<^make_judgment>` replaced `mk_Trueprop`,
  and `\<^dest_judgment>` replaced `dest_Trueprop`
- Old-style verbatim `{* ... *}` have been discontinued in Isabelle
  2022, cartouche `\<open> ... \<close>` have been recommended
- In Isabelle2017, `src/Pure/more_thm.ML` had 
  `Thm.full_rules = Item_Net.init eq_thm_prop (single o Thm.full_prop_of);`
  This was removed by Isabelle2023, specifically in commit
  `cd4cdfa81fe1860bfd62a5374e5b3fc50ca13f37` (apparently replaced by
  `Thm.item_net`)
  - **BUT** I have seen `Thm.full_rules` appear in 
    `Generic_Data(...; val empty = Thm.full_rules; ...)`
    I have also seen `Symtab.empty` used, and `Thm.item_net`, and I am
    uncertain which to use.
- `Parse.text` was removed by Isabelle2021, specifically in commit
  `b92cb7ae8c71385b1c7bb9524533e1f3c3846e2b` (apparently replaced by
  `Parse.embedded`)
- `Thm.instantiate` changed (in commit
  `5df2c0c275bfdd2a251822e4d20c55215253a5f2`)
  to use tables instead of lists
- Apparently there was a time when you could use `--"this is a comment"`
  for single-line comments. But those days are long gone now
  (evidently).
  You instead need to use `\<comment>\<open>this is a comment\<close>`,
  which I've done in the formalization of Tarski, but I bet you need to
  fix a lot more places.
- Isabelle 2016 allowed `(* ... *)` comments in the inner syntax, but
  that changed since then: they are no longer allowed and must be removed.

# TODO List

- Apparently, `Local_Theory.declaration` required a `pos` field, and I
  have no clue what to give it in the local function `afterqed` (for
  `mdecl` in [`mizar_reserve.thy`](./mizar/mizar_reserve.th)). I assume 
  `\<^here>` is fine, but maybe it isn't?