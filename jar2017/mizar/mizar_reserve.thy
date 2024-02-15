\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory mizar_reserve
  imports mizar_ty mizar_defs
keywords "reserve" :: thy_decl
     and "mtheorem" :: thy_goal and "mlemma" :: thy_goal
     and "mdefinition" :: thy_goal and "mlet"
     and "func" :: thy_goal and "attr" :: thy_decl
begin

ML \<open>
fun dest_be (Const (@{const_name ty_membership}, _) $ l $ r) = (l, r)
  | dest_be x = raise TERM ("dest_be", [x])
\<close>

ML \<open>
structure Miz_Reserve_Data = Theory_Data
(
  type T = term Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge _ = Symtab.empty;
);
fun do_var (v as (n, _)) lthy =
  if Variable.is_fixed lthy n then ([], lthy) else
  case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of lthy)) n of
    NONE => raise Fail ("Non-reserved free set variable: " ^ n ^ " in goal!")
  | SOME D =>
    let
      val fs = Term.add_frees D [];
      val (assms, lthy1) = fold_map do_var fs lthy;
      val (_, lthy2) = Variable.add_fixes [n] lthy1;
      val cp = Thm.cterm_of lthy (mk_Trueprop ((@{term ty_membership} $ (Free v)) $ D))
      val (assm, lthy3) = yield_singleton (Assumption.add_assms Assumption.presume_export) cp lthy2
    in
      ((assm :: flat assms), Context.proof_map (ty_add_thm assm) lthy3)
    end
\<close>

ML \<open>
fun reserve_cmd (vs, tm) lthy =
  let
    val tm = (Syntax.read_term lthy tm)
    val gl = mk_Trueprop (@{term inhabited} $ tm)
    val fs = Term.add_frees tm [];
    val (_, lthy') = fold_map do_var fs lthy;
(*    val lthy'' = mty_tms ty_add_thm (map Thm.prop_of (flat assms)) lthy'*)
    val _ = Goal.prove lthy' [] [] gl (fn {context = ctxt, ...} => HEADGOAL (simp_tac ctxt))
    val _ = if fastype_of tm <> @{typ "Ty"} then
      raise Fail "not a correctly typed constraint" else ();
    fun reserve thy =
      fold (fn v => fn thy => Miz_Reserve_Data.map (Symtab.update (v, tm)) thy)
        vs thy;
  in Local_Theory.background_theory reserve lthy end;

val () =
  Outer_Syntax.local_theory @{command_keyword reserve}
    "reserve variable names with types"
    ((Parse.list1 Parse.embedded -- (Parse.$$$ "for" |-- Parse.term)) >> reserve_cmd);
\<close>

ML \<open>
fun do_lt tm lthya =
   case dest_Trueprop tm of
     (Const (@{const_name ty_membership}, _) $ Free (n, _) $ _) =>
       let
         val (_, lthya2) = Variable.add_fixes [n] lthya;
         val ct = Thm.cterm_of lthya tm;
         val (assm, lthya3) = yield_singleton (Assumption.add_assms Assumption.presume_export) ct lthya2
       in
         (assm, Context.proof_map (ty_add_thm assm) lthya3)
       end
   | _ =>
       let
         val ct = Thm.cterm_of lthya tm;
         val (assm, lthya2) = yield_singleton (Assumption.add_assms Assumption.presume_export) ct lthya
       in
         (assm, lthya2 addsimps [assm])
(*         (assm, lthya2)*)
       end;
\<close>

ML \<open>
fun normalize_thm ctxt th =
  let
    val th2 = Object_Logic.rulify ctxt th
(*    val _ = tracing ("<" ^ Thm.string_of_thm ctxt th2)*)
    val th3 = Simplifier.asm_full_simplify (put_simpset main_ss ctxt addsimps @{thms object_root ty_intersection} addsimprocs [@{simproc ex_simp}]) th2
    fun do_prem (Const (@{const_name Trueprop}, _) $ (Const (@{const_name Ball}, _) $ _ $ _)) = @{thm ballI}
      | do_prem _ = asm_rl
    val th4 = th3 OF (map (do_prem o Logic.strip_assums_concl) (Thm.prems_of th3))
    val th5 = @{thm bspec} OF [th4] handle THM _ => th4
(*    val _ = tracing (">" ^ Thm.string_of_thm ctxt th5)*)
  in
    if Thm.prop_of th = Thm.prop_of th5 then th else normalize_thm ctxt th5
  end
\<close>

ML \<open>
fun setup_proof (((name, attr), lt), str) lthy =
  let
    val prop = Syntax.read_prop lthy str;
    val lt2 = map (Syntax.read_prop lthy) (flat (the_list lt))
    val attr = map (Attrib.check_src lthy) attr;
    val as_fs = map (dest_Free o fst o dest_be o dest_Trueprop) lt2
    val c_fs = Term.add_frees prop []
    val fs = subtract (op =) as_fs c_fs
    val _ = if filter_out (fn (_, ty) => ty = @{typ Set}) fs <> [] then
      warning "Warning: Free variables! Is it a scheme?" else ()
    val setfs = filter (fn (_, ty) => ty = @{typ Set}) fs
    val (assms1, lthy1) = fold_map do_var setfs lthy
    val (assms2, lthy2) = fold_map do_lt lt2 lthy1
    val lthy4 = mty_tms ty_add_thm (prop :: map Thm.prop_of (flat assms1 @ assms2)) lthy2
    fun after_qed thms lthy' =
      let
        val a = [((name, attr), [(map (normalize_thm lthy') (flat thms), [])])];
        val a = Attrib.partial_evaluation lthy' a;
      in
        Local_Theory.notes a lthy' |> snd
      end;
  in
    Proof.theorem NONE after_qed [[(prop, [])]] lthy4
  end;
\<close>

ML \<open>
Outer_Syntax.local_theory_to_proof @{command_keyword mtheorem} "Mizar theorem"
  ((Parse_Spec.opt_thm_name ":" -- (Scan.option ((@{keyword "mlet"} || @{keyword "assumes"}) |-- Parse.list1 Parse.prop))
   -- Parse.prop) >> setup_proof);
Outer_Syntax.local_theory_to_proof @{command_keyword mlemma} "Mizar lemma"
  ((Parse_Spec.opt_thm_name ":" -- (Scan.option ((@{keyword "mlet"} || @{keyword "assumes"}) |-- Parse.list1 Parse.prop))
   -- Parse.prop) >> setup_proof);
\<close>

ML \<open>
fun mdecl decl lt defn getth afterqed lthy =
  let
   val lt2 = map (Syntax.read_prop lthy) (flat (the_list lt))
   val ((tm, (_, th)), lthy2) = Specification.definition_cmd decl [] [] (Binding.empty_atts, defn) false lthy
   val vs = Term.add_vars (Thm.prop_of th) [];
   val fs = map (fn (v as ((n, _), t)) => (v, Thm.cterm_of lthy2 (Free (n, t)))) vs;
   val th2 = Thm.instantiate (TVars.empty, Vars.make fs) th
   val (fname, _) = dest_Free tm
   (* where getth is used *)
   val thr2 = (getth (Thm.prop_of th2)) OF [th2]

   val as_fs = map_filter (fn th => SOME ((dest_Free o fst o dest_be o dest_Trueprop) th) handle TERM _ => NONE) lt2
   val c_fs = Term.add_frees (Thm.prop_of thr2) []
   val fs = subtract (op =) as_fs c_fs
   val setfs = filter (fn (_, ty) => ty = @{typ Set}) fs
   fun do_var_nofail v lthy = do_var v lthy handle Fail _ => ([], lthy)
   val (assms1, lthy2a) = fold_map do_var_nofail setfs lthy2
   val (assms2, lthy3) = fold_map do_lt lt2 lthy2a
   val lthy4 = mty_tms ty_add_thm (Thm.prop_of thr2 :: map Thm.prop_of (flat assms1 @ assms2)) lthy3
   fun after_qed thms lthy' = afterqed fname (flat thms) (Thm.prop_of th2) lthy'
  in
    lthy4 |>
    Proof.theorem NONE after_qed [[(Thm.concl_of thr2, [])]]
 |> Proof.refine_singleton (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (resolve_tac ctxt [thr2] 1)))
  end;
\<close>

ML \<open>
fun mdefinition ((decl, lt), (defn, thref)) lthy =
  let
    fun afterqed fname thms _ lthy' =
     let
       val bind = (Binding.make (fname, Position.none), [])
       val ths = [(map (normalize_thm lthy') (conj_elims (the_single thms)), [])]
       val a = Attrib.partial_evaluation lthy' [(bind, ths)];
     in
       Local_Theory.notes a lthy' |> snd
     end;
  in
    mdecl decl lt defn (fn _ => singleton (Attrib.eval_thms lthy) thref) afterqed lthy
  end;
val parser = (Scan.option Parse_Spec.constdecl --
    (Scan.option ((@{keyword "mlet"} || @{keyword "assumes"}) |-- Parse.list1 Parse.prop)) --
    (Parse.prop -- (@{keyword ":"} |-- Parse.thm))) >> mdefinition;
Outer_Syntax.local_theory_to_proof @{command_keyword mdefinition} "Mizar constant" parser
\<close>

ML \<open>
fun yxml_insert i s =
  case YXML.parse s of
    XML.Elem (a, [XML.Text c]) =>
      let
        val _ = warning (@{make_string} a)
        val s1 = String.substring (c, 0, 1);
        val s2 = String.substring (c, 1, (String.size c - 1));
      in
        YXML.string_of (XML.Elem (a, [XML.Text (s1 ^ i ^ s2)]))
      end
  | _ => raise ERROR "yxml_insert"
 \<close>
thm assume_equals_property
thm assume_means_property
thm equals_property
thm means_property
(* Alex annotation: I believe this code related to defining functors, as discussed on page 573
(section 6.2). It turns out that @{term eq} corresponds to @{IFOL.eq}, and I'm not sure
if there's an idiomatic way to have polymorphic matching --- that is to say, could
we have `val eq = @{term "IFOL.eq"}` and have it match a constant term 
`@{term "(IFOL.eq :: Set \<Rightarrow> Set \<Rightarrow> o)"}`. Right now I am "overfitting" and  using
the coincidence that we're always using equality on Sets. *)
ML \<open>
val eq = @{term "(IFOL.eq :: Set \<Rightarrow> Set \<Rightarrow> o)"}; 
(* Alex annotation: @{term is_as_eq} refers to "is assume_equals", meaning the functor
is defined with an assumption AND set equal to some term. *)

tracing (@{make_string} eq);

fun is_as_eq (_ $ (_ $ _ $ (_ $ (_ $ _ $ C $ D)))) =
  (tracing ("C = "^(@{make_string} C));
  tracing ("D = "^(@{make_string} D));
  let
    val assum =
      case C of
        Abs (_, _, (Const (@{const_name True}, _))) => false
      | _ => true;
    val eq =
      case D of
        Abs (_, _, (c1 $ Bound 0 $ _)) => (tracing ("c1 = "^(@{make_string} c1));
              if c1 = eq then true else false)
      | _ => false
  in
  (tracing ("assum = "^(Bool.toString assum)^", eq = "^(Bool.toString eq)));
 (assum, eq) end)
  | is_as_eq _ = raise Fail "invalid func definition";

fun note_suffix fname sffx thm lthy =
  let
    val bind = ((Binding.map_name (suffix sffx) (Binding.make (fname, Position.none))), [])
    val a = Attrib.partial_evaluation lthy [(bind, [([normalize_thm lthy thm], [])])]
  in
    Local_Theory.notes a lthy |> snd
  end;

fun functr ((decl, lt), defn) lthy =
  let
    fun getth prop =
      let
        val (aas, eq) = is_as_eq prop
(*        val _ = if aas then warning "permissive" else ()
        val _ = if eq then warning "eq" else ()*)
      in
        case (aas, eq) of
        (true, true) => @{thm assume_equals_property}
      | (true, false) => @{thm assume_means_property}
      | (false, true) => @{thm equals_property}
      | (false, false) => @{thm means_property}
      end
    fun afterqed fname thms prop lthy' =
     let
       val thm = the_single thms
       val thm_ty = @{thm conjunct1} OF [thm]
      (* XXX: I have no clue what to give for "pos", so \<^here> it is... *)
       val lthy'' = Local_Theory.declaration {syntax = false, pervasive = false, pos = \<^here>}
          (fn phi => ty_func_add_thm (Morphism.thm phi thm_ty)) lthy'
       val lthy''' = note_suffix fname "_ty" thm_ty lthy''
       val thm = @{thm conjunct2} OF [thm];
     in
       if snd (is_as_eq prop) then note_suffix fname "" thm lthy'''
       else lthy'''
         |> note_suffix fname "" (@{thm conjunct1} OF [thm])
         |> note_suffix fname "_uniq" (@{thm conjunct2} OF [thm])
     end;
  in
    mdecl decl lt defn getth afterqed lthy
  end;

val parser = (Scan.option Parse_Spec.constdecl --
    (Scan.option ((@{keyword "mlet"} || @{keyword "assumes"}) |-- Parse.list1 Parse.prop)) --
    Parse.prop) >> functr;
Outer_Syntax.local_theory_to_proof @{command_keyword func} "Mizar constant" parser
\<close>

ML \<open>
fun attr ((bind, mixf), str) int lthy =
  let
    val bind2 = Binding.map_name (suffix "_orig") bind
    val ((_, (_, th)), lthy) =
      Specification.definition_cmd (SOME (bind, NONE, mixf)) [] [] ((bind2, []), str) int lthy
    val _ = tracing (@{make_string} th);
    val thE = normalize_thm lthy (@{thm attr_property(3)} OF [th])
    val thI = normalize_thm lthy (@{thm attr_property(2)} OF [th])
    val th = normalize_thm lthy (@{thm attr_property(1)} OF [th])
    val lthy2 = snd (Local_Theory.note ((bind, []), [th]) lthy)
    val lthy3 = snd (Local_Theory.note ((Binding.map_name (suffix "E") bind, []), [thE]) lthy2)
    val lthy4 = snd (Local_Theory.note ((Binding.map_name (suffix "I") bind, @{attributes [intro?]}), [thI]) lthy3)
  in lthy4 end
val _ =
  Outer_Syntax.local_theory' @{command_keyword attr} "attr definition"
    (((Parse.binding -- Parse.opt_mixfix') -- Parse.prop) >> attr);
\<close>

parse_translation \<open> [(@{syntax_const "_BallML2"},
  let fun tr ctxt [((Const (@{syntax_const "_vs"}, _)) $ (v as (_ $ (vv as Free (n, _)) $ _)) $ vs), P] =
          (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of ctxt)) n of
            NONE => raise Fail ("BallML2a: Variable " ^ n ^ " \<not> reserved and 'being' \<not> given!")
          | SOME D => Syntax.const @{const_syntax Ball} $ D $ (Syntax_Trans.abs_tr [v, tr ctxt [vs, P]]))
        | tr ctxt [(v as (_ $ (vv as Free (n, _)) $ _)), P] =
          (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of ctxt)) n of
            NONE => raise Fail ("BallML2b: Variable " ^ n ^ " \<not> reserved and 'being' \<not> given!")
          | SOME D => Syntax.const @{const_syntax Ball} $ D $ (Syntax_Trans.abs_tr [v, P]))
  in tr end)] \<close>

parse_translation \<open> [(@{syntax_const "_BexML2"},
  let fun tr ctxt [((Const (@{syntax_const "_vs"}, _)) $ (v as (_ $ (vv as Free (n, _)) $ _)) $ vs), P] =
          (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of ctxt)) n of
            NONE => raise Fail ("BexML2a: Variable " ^ n ^ " \<not> reserved and 'being' \<not> given!")
          | SOME D => Syntax.const @{const_syntax Bex} $ D $ (Syntax_Trans.abs_tr [v, tr ctxt [vs, P]]))
        | tr ctxt [(v as (_ $ (vv as Free (n, _)) $ _)), P] =
          (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of ctxt)) n of
            NONE => raise Fail ("BexML2b: Variable " ^ n ^ " \<not> reserved and 'being' \<not> given!")
          | SOME D => Syntax.const @{const_syntax Bex} $ D $ (Syntax_Trans.abs_tr [v, P]))
  in tr end)] \<close>

end