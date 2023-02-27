section \<open>Split Cycle Rule\<close>

theory Split_Cycle_Rule
  imports "Compositional_Structures/Basic_Modules/Split_Cycle_Module"
begin

text \<open>
  This is the Split Cycle Rule.
\<close>

subsection \<open>Definition\<close>

fun split_cycle_rule :: "'a Electoral_Module" where
  "split_cycle_rule A p = split_cycle A p"

end
