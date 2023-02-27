(*  File:       Reject_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Reject Module\<close>

theory Reject_Module
  imports "Component_Types/Electoral_Module"
begin

text \<open>
  The reject module is not concerned about the voter's ballots, and
  just rejects all alternatives. It is primarily used in sequence after
  an electoral module that only defers alternatives to finalize the decision,
  thereby inducing a proper voting rule in the social choice sense.
\<close>

subsection \<open>Definition\<close>

fun reject_module :: "'a Electoral_Module" where
  "reject_module A p = ({}, A, {})"

subsection \<open>Soundness\<close>

theorem reject_mod_sound[simp]: "electoral_module reject_module"
  unfolding electoral_module_def
  by simp

subsection \<open>Rejecting\<close>

theorem reject_mod_rejecting[simp]: "rejecting reject_module"
  unfolding rejecting_def
  by simp 


end
