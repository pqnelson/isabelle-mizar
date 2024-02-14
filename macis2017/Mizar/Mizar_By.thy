\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Mizar_By
  imports Mizar FOL
begin

ML \<open>
structure Miz_Ty_Data = Generic_Data
( type T = thm Item_Net.T;
  val empty = Thm.item_net;
  val extend = I;
  val merge = Item_Net.merge);
\<close>
ML \<open>
fun add_thm thm ctxt = Miz_Ty_Data.map (Item_Net.update thm) ctxt;
fun del_thm thm ctxt = Miz_Ty_Data.map (Item_Net.remove thm) ctxt;
fun add_or_del aod_fn = Thm.declaration_attribute (fn thm => fn ctxt => aod_fn thm ctxt);
val attrib = Attrib.add_del (add_or_del add_thm) (add_or_del del_thm)
\<close>
setup \<open> Attrib.setup @{binding "type_infer"} attrib "Declare as Mizar type inference rule" \<close>
setup \<open> Global_Theory.add_thms_dynamic (@{binding "type_infers"}, (Item_Net.content o Miz_Ty_Data.get)) \<close>

end