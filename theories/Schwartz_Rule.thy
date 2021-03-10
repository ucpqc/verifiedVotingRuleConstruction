(*  File:       Schwartz_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Schwartz Rule\<close>

theory Schwartz_Rule
  imports Borda_Module Defer_One_Loop_Composition
begin

text
\<open>This is the Schwartz voting rule. Confusingly, it is sometimes also referred as
Nanson's rule. The Schwartz rule proceeds as in the classic Nanson's rule, but
excludes alternatives with a Borda score that is strictly less than the
average Borda score.\<close>

subsection \<open>Definition\<close>

fun schwartz_rule :: "'a Electoral_Module" where
  "schwartz_rule A p =
    iter (less_average_eliminator borda_score) A p"

fun schwartz_rule_code :: "'a Electoral_Module" where
  "schwartz_rule_code A p =
    iter (less_average_eliminator borda_score_code) A p"

end
