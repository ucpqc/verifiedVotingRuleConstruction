(*  File:       Electoral_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Component Types\<close>

section \<open>Electoral Module\<close>

theory Electoral_Module
  imports "Social_Choice_Types/Profile"
          "Social_Choice_Types/Result"
begin

text \<open>
  Electoral modules are the principal component type of the composable modules
  voting framework, as they are a generalization of voting rules in the sense
  of social choice functions.
  These are only the types used for electoral modules. Further restrictions are
  encompassed by the electoral-module predicate.

  An electoral module does not need to make final decisions for all
  alternatives, but can instead defer the decision for some or all of them to
  other modules. Hence, electoral modules partition the received (possibly
  empty) set of alternatives into elected, rejected and deferred alternatives.
  In particular, any of those sets, e.g., the set of winning (elected)
  alternatives, may also be left empty, as long as they collectively still hold
  all the received alternatives. Just like a voting rule, an electoral module
  also receives a profile which holds the voters’ preferences, which, unlike a
  voting rule, consider only the (sub-)set of alternatives that the module
  receives.
\<close>

subsection \<open>Definition\<close>

text \<open>
  An electoral module maps a set of alternatives and a profile to a result.
\<close>

type_synonym 'a Electoral_Module = "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result"

subsection \<open>Auxiliary Definitions\<close>

text \<open>
  Electoral modules partition a given set of alternatives A into a set of
  elected alternatives e, a set of rejected alternatives r, and a set of
  deferred alternatives d, using a profile.
  e, r, and d partition A.
  Electoral modules can be used as voting rules. They can also be composed
  in multiple structures to create more complex electoral modules.
\<close>

definition electoral_module :: " 'a Electoral_Module \<Rightarrow> bool" where
  "electoral_module m \<equiv> \<forall> A p. finite_profile A p \<longrightarrow> well_formed A (m A p)"

lemma electoral_modI:
  "((\<And> A p. \<lbrakk> finite_profile A p \<rbrakk> \<Longrightarrow> well_formed A (m A p)) \<Longrightarrow>
       electoral_module m)"
  unfolding electoral_module_def
  by auto

text \<open>
  The next three functions take an electoral module and turn it into a
  function only outputting the elect, reject, or defer set respectively.
\<close>

abbreviation elect ::
  "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "elect m A p \<equiv> elect_r (m A p)"

abbreviation reject ::
  "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "reject m A p \<equiv> reject_r (m A p)"

abbreviation "defer" ::
  "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "defer m A p \<equiv> defer_r (m A p)"

text \<open>
  "defers n" is true for all electoral modules that defer exactly
  n alternatives, whenever there are n or more alternatives.
\<close>

definition defers :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "defers n m \<equiv>
    electoral_module m \<and>
      (\<forall> A p. (card A \<ge> n \<and> finite_profile A p) \<longrightarrow>
          card (defer m A p) = n)"

text \<open>
  "rejects n" is true for all electoral modules that reject exactly
  n alternatives, whenever there are n or more alternatives.
\<close>

definition rejects :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "rejects n m \<equiv>
    electoral_module m \<and>
      (\<forall> A p. (card A \<ge> n \<and> finite_profile A p) \<longrightarrow> card (reject m A p) = n)"

text \<open>
  As opposed to "rejects", "eliminates" allows to stop rejecting if no
  alternatives were to remain.
\<close>

definition eliminates :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "eliminates n m \<equiv>
    electoral_module m \<and>
      (\<forall> A p. (card A > n \<and> finite_profile A p) \<longrightarrow> card (reject m A p) = n)"

text \<open>
  "elects n" is true for all electoral modules that
  elect exactly n alternatives, whenever there are n or more alternatives.
\<close>

definition elects :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "elects n m \<equiv>
    electoral_module m \<and>
      (\<forall> A p. (card A \<ge> n \<and> finite_profile A p) \<longrightarrow> card (elect m A p) = n)"

text \<open>
  An electoral module is independent of an alternative a iff
  a's ranking does not influence the outcome.
\<close>

definition indep_of_alt :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "indep_of_alt m A a \<equiv>
    electoral_module m \<and> (\<forall> p q. equiv_prof_except_a A p q a \<longrightarrow> m A p = m A q)"

definition unique_winner_if_profile_non_empty :: "'a Electoral_Module \<Rightarrow> bool" where
  "unique_winner_if_profile_non_empty m \<equiv>
    electoral_module m \<and>
    (\<forall> A p. (A \<noteq> {} \<and> p \<noteq> [] \<and> finite_profile A p) \<longrightarrow>
              (\<exists> a \<in> A. m A p = ({a}, A - {a}, {})))"

subsection \<open>Equivalence Definitions\<close>

definition prof_contains_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                                       'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_contains_result m A p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect m A q) \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<in> defer m A q)"

definition prof_leq_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                                  'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_leq_result m A p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<notin> elect m A q)"

definition prof_geq_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                                  'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_geq_result m A p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<notin> reject m A q)"

definition mod_contains_result :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
                                      'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "mod_contains_result m n A p a \<equiv>
    electoral_module m \<and> electoral_module n \<and> finite_profile A p \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect n A p) \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject n A p) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<in> defer n A p)"

subsection \<open>Auxiliary Lemmata\<close>

lemma combine_ele_rej_def:
  assumes
    ele: "elect m A p = e" and
    rej: "reject m A p = r" and
    def: "defer m A p = d"
  shows "m A p = (e, r, d)"
  using def ele rej
  by auto

lemma par_comp_result_sound:
  assumes
    mod_m: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "well_formed A (m A p)"
  using mod_m f_prof
  unfolding electoral_module_def
  by simp

lemma result_presv_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
proof (safe)
  fix x :: "'a"
  assume elec_x: "x \<in> elect m A p"
  have partit:
    "\<forall> A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists> A' elec rej def. A = A' \<and> p = (elec, rej, def) \<and> elec \<union> rej \<union> def = A')"
    by simp
  from e_mod f_prof have set_partit:
    "set_equals_partition A (m A p)"
    unfolding electoral_module_def
    by simp
  thus "x \<in> A"
    using UnI1 elec_x fstI set_partit partit
    by (metis (no_types))
next
  fix x :: "'a"
  assume rej_x: "x \<in> reject m A p"
  have partit:
    "\<forall> A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists> A' elec rej def. A = A' \<and> p = (elec, rej, def) \<and> elec \<union> rej \<union> def = A')"
    by simp
  from e_mod f_prof have set_partit:
    "set_equals_partition A (m A p)"
    unfolding electoral_module_def
    by simp
  thus "x \<in> A"
    using UnI1 rej_x fstI set_partit partit
          sndI subsetD sup_ge2
    by metis
next
  fix x :: "'a"
  assume def_x: "x \<in> defer m A p"
  have partit:
    "\<forall> A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists> A' elec rej def. A = A' \<and> p = (elec, rej, def) \<and> elec \<union> rej \<union> def = A')"
    by simp
  from e_mod f_prof have set_partit:
    "set_equals_partition A (m A p)"
    unfolding electoral_module_def
    by simp
  thus "x \<in> A"
    using def_x set_partit partit sndI subsetD sup_ge2
    by metis
next
  fix x :: "'a"
  assume
    x_in_A: "x \<in> A" and
    not_def_x: "x \<notin> defer m A p" and
    not_rej_x: "x \<notin> reject m A p"
  have partit:
    "\<forall> A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists> A' elec rej def. A = A' \<and> p = (elec, rej, def) \<and> elec \<union> rej \<union> def = A')"
    by simp
  from e_mod f_prof have set_partit:
    "set_equals_partition A (m A p)"
    unfolding electoral_module_def
    by simp
  show "x \<in> elect m A p"
    using x_in_A not_def_x not_rej_x fst_conv partit
          set_partit snd_conv Un_iff
    by metis
qed

lemma result_disj:
  assumes
    module: "electoral_module m" and
    profile: "finite_profile A p"
  shows
    "(elect m A p) \<inter> (reject m A p) = {} \<and>
        (elect m A p) \<inter> (defer m A p) = {} \<and>
        (reject m A p) \<inter> (defer m A p) = {}"
proof (safe, simp_all)
  fix x :: "'a"
  assume
    elect_x: "x \<in> elect m A p" and
    reject_x: "x \<in> reject m A p"
  have partit:
    "\<forall> A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists> B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from module profile have set_partit:
    "set_equals_partition A (m A p)"
    unfolding electoral_module_def
    by simp
  from profile have prof_p:
    "finite A \<and> profile A p"
    by simp
  from module prof_p have wf_A_m:
    "well_formed A (m A p)"
    unfolding electoral_module_def
    by metis
  show False
    using prod.exhaust_sel DiffE UnCI elect_x reject_x
          module profile result_imp_rej wf_A_m
          prof_p set_partit partit
    by (metis (no_types))
next
  fix x :: "'a"
  assume
    elect_x: "x \<in> elect m A p" and
    defer_x: "x \<in> defer m A p"
  have partit:
    "\<forall> A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists> B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  have disj:
    "\<forall> p. \<not> disjoint3 p \<or>
      (\<exists> B C D. p = (B::'a set, C, D) \<and>
        B \<inter> C = {} \<and> B \<inter> D = {} \<and> C \<inter> D = {})"
    by simp
  from profile have prof_p:
    "finite A \<and> profile A p"
    by simp
  from module prof_p have wf_A_m:
    "well_formed A (m A p)"
    unfolding electoral_module_def
    by metis
  hence wf_A_m_0:
    "disjoint3 (m A p) \<and> set_equals_partition A (m A p)"
    by simp
  hence disj3:
    "disjoint3 (m A p)"
    by simp
  have set_partit:
    "set_equals_partition A (m A p)"
    using wf_A_m_0
    by simp
  from disj3 obtain
    elec :: "'a Result \<Rightarrow> 'a set" and
    rej :: "'a Result \<Rightarrow> 'a set" and
    def :: "'a Result \<Rightarrow> 'a set"
    where
    "m A p =
      (elec (m A p), rej (m A p), def (m A p)) \<and>
        elec (m A p) \<inter> rej (m A p) = {} \<and>
        elec (m A p) \<inter> def (m A p) = {} \<and>
        rej (m A p) \<inter> def (m A p) = {}"
    using elect_x defer_x disj
    by metis
  hence "((elect m A p) \<inter> (reject m A p) = {}) \<and>
          ((elect m A p) \<inter> (defer m A p) = {}) \<and>
          ((reject m A p) \<inter> (defer m A p) = {})"
    using disj3 eq_snd_iff fstI
    by metis
  thus False
    using elect_x defer_x module profile wf_A_m prof_p
          set_partit partit disjoint_iff_not_equal
    by (metis (no_types))
next
  fix x :: "'a"
  assume
    reject_x: "x \<in> reject m A p" and
    defer_x: "x \<in> defer m A p"
  have partit:
    "\<forall> A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists> B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from module profile have set_partit:
    "set_equals_partition A (m A p)"
    unfolding electoral_module_def
    by simp
  from profile have prof_p:
    "finite A \<and> profile A p"
    by simp
  from module prof_p have wf_A_m:
    "well_formed A (m A p)"
    unfolding electoral_module_def
    by simp
  show False
    using prod.exhaust_sel DiffE UnCI reject_x defer_x
          module profile result_imp_rej wf_A_m
          prof_p set_partit partit
    by (metis (no_types))
qed

lemma elect_in_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "elect m A p \<subseteq> A"
  using le_supI1 e_mod f_prof result_presv_alts sup_ge1
  by metis

lemma reject_in_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "reject m A p \<subseteq> A"
  using le_supI1 e_mod f_prof result_presv_alts sup_ge2
  by fastforce

lemma defer_in_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "defer m A p \<subseteq> A"
  using e_mod f_prof result_presv_alts
  by auto

lemma def_presv_fin_prof:
  assumes
    module:  "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "let new_A = defer m A p in finite_profile new_A (limit_profile new_A p)"
  using defer_in_alts infinite_super limit_profile_sound module f_prof
  by metis

text \<open>
  An electoral module can never reject, defer or elect more than
  |A| alternatives.
\<close>

lemma upper_card_bounds_for_result:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows
    "card (elect m A p) \<le> card A \<and>
      card (reject m A p) \<le> card A \<and>
      card (defer m A p) \<le> card A "
  using e_mod f_prof
  by (simp add: card_mono defer_in_alts elect_in_alts reject_in_alts)

lemma reject_not_elec_or_def:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "reject m A p = A - (elect m A p) - (defer m A p)"
proof -
  from e_mod f_prof
  have 0: "well_formed A (m A p)"
    unfolding electoral_module_def
    by simp
  with e_mod f_prof
    have "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
      using result_presv_alts
      by simp
    moreover from 0
    have
      "(elect m A p) \<inter> (reject m A p) = {} \<and>
          (reject m A p) \<inter> (defer m A p) = {}"
    using e_mod f_prof result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma elec_and_def_not_rej:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "elect m A p \<union> defer m A p = A - (reject m A p)"
proof -
  from e_mod f_prof
  have 0: "well_formed A (m A p)"
    unfolding electoral_module_def
    by simp
  hence
    "disjoint3 (m A p) \<and> set_equals_partition A (m A p)"
    by simp
  with e_mod f_prof
  have "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
    using e_mod f_prof result_presv_alts
    by blast
  moreover from 0 have
    "(elect m A p) \<inter> (reject m A p) = {} \<and>
        (reject m A p) \<inter> (defer m A p) = {}"
    using e_mod f_prof result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma defer_not_elec_or_rej:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "defer m A p = A - (elect m A p) - (reject m A p)"
proof -
  from e_mod f_prof
  have 0: "well_formed A (m A p)"
    unfolding electoral_module_def
    by simp
  hence "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
    using e_mod f_prof result_presv_alts
    by simp
  moreover from 0 have
    "(elect m A p) \<inter> (defer m A p) = {} \<and>
        (reject m A p) \<inter> (defer m A p) = {}"
    using e_mod f_prof result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma electoral_mod_defer_elem:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    alternative: "x \<in> A" and
    not_elected: "x \<notin> elect m A p" and
    not_rejected: "x \<notin> reject m A p"
  shows "x \<in> defer m A p"
  using DiffI e_mod f_prof alternative
        not_elected not_rejected
        reject_not_elec_or_def
  by metis

lemma mod_contains_result_comm:
  assumes "mod_contains_result m n A p a"
  shows "mod_contains_result n m A p a"
proof (unfold mod_contains_result_def, safe)
  from assms
  show "electoral_module n"
    unfolding mod_contains_result_def
    by simp
next
  from assms
  show "electoral_module m"
    unfolding mod_contains_result_def
    by simp
next
  from assms
  show "finite A"
    unfolding mod_contains_result_def
    by simp
next
  from assms
  show "profile A p"
    unfolding mod_contains_result_def
    by simp
next
  from assms
  show "a \<in> A"
    unfolding mod_contains_result_def
    by simp
next
  assume "a \<in> elect n A p"
  thus "a \<in> elect m A p"
    using IntI assms electoral_mod_defer_elem empty_iff
          mod_contains_result_def result_disj
    by (metis (mono_tags, lifting))
next
  assume "a \<in> reject n A p"
  thus "a \<in> reject m A p"
    using IntI assms electoral_mod_defer_elem empty_iff
          mod_contains_result_def result_disj
    by (metis (mono_tags, lifting))
next
  assume "a \<in> defer n A p"
  thus "a \<in> defer m A p"
    using IntI assms electoral_mod_defer_elem empty_iff
          mod_contains_result_def result_disj
    by (metis (mono_tags, lifting))
qed

lemma not_rej_imp_elec_or_def:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    alternative: "x \<in> A" and
    not_rejected: "x \<notin> reject m A p"
  shows "x \<in> elect m A p \<or> x \<in> defer m A p"
  using alternative electoral_mod_defer_elem
        e_mod not_rejected f_prof
  by metis

lemma single_elim_imp_red_def_set:
  assumes
    eliminating: "eliminates 1 m" and
    leftover_alternatives: "card A > 1" and
    f_prof: "finite_profile A p"
  shows "defer m A p \<subset> A"
  using Diff_eq_empty_iff Diff_subset card_eq_0_iff defer_in_alts
        eliminates_def eliminating eq_iff leftover_alternatives
        not_one_le_zero f_prof psubsetI reject_not_elec_or_def
  by metis

lemma eq_alts_in_profs_imp_eq_results:
  assumes
    eq: "\<forall> a \<in> A. prof_contains_result m A p p' a" and
    input: "electoral_module m \<and> finite_profile A p \<and> finite_profile A p'"
  shows "m A p = m A p'"
proof -
  have "\<forall> a \<in> elect m A p. a \<in> elect m A p'"
    using elect_in_alts eq prof_contains_result_def input in_mono
    by metis
  moreover have "\<forall> a \<in> elect m A p'. a \<in> elect m A p"
  proof -
    fix a :: 'a
    have "\<forall> A A'. (A'::'a set) \<inter> A = {} \<or> A' \<noteq> {}"
      by blast
    moreover have elect_diff: "elect m A p' - A = {}"
      using Diff_eq_empty_iff elect_in_alts input
      by metis
    moreover have def_elec_disj: "defer m A p' \<inter> elect m A p' = {}"
      using disjoint_iff_not_equal input result_disj
      by (metis (no_types))
    moreover have rej_elec_disj: "reject m A p' \<inter> elect m A p' = {}"
      using disjoint_iff_not_equal input result_disj
      by (metis (no_types))
    ultimately have
      "(\<exists> A'. A' \<inter> elect m A p' = {} \<and> a \<in> A') \<or>
          a \<notin> elect m A p' \<or> a \<in> elect m A p"
      using DiffI electoral_mod_defer_elem eq
      unfolding prof_contains_result_def
      by (metis (no_types))
    from elect_diff def_elec_disj rej_elec_disj
    show ?thesis
      using Diff_iff Int_iff empty_iff eq not_rej_imp_elec_or_def
      unfolding prof_contains_result_def
      by metis
  qed
  moreover have
    "\<forall> a \<in> reject m A p. a \<in> reject m A p'"
    using reject_in_alts eq prof_contains_result_def input in_mono
    by fastforce
  moreover have
    "\<forall> a \<in> reject m A p'. a \<in> reject m A p"
  proof -
    {
      fix a' :: 'a
      have rej_set:
        "\<forall> f. electoral_module f \<longrightarrow> reject f A p' \<subseteq> A"
        using input reject_in_alts
        by metis
      have rej_def_disj:
        "\<forall> f. electoral_module f \<longrightarrow> reject f A p' \<inter> defer f A p' = {}"
        using input result_disj
        by metis
      have "electoral_module m \<and> profile A p \<and> finite_profile A p'"
        using input
        by blast
      hence
        "elect m A p' \<inter> reject m A p' = {} \<and> elect m A p' \<inter> defer m A p' = {} \<and>
          reject m A p' \<inter> defer m A p' = {}"
        by (simp add: result_disj)
      hence
        "a' \<in> elect m A p' \<longrightarrow> a' \<notin> reject m A p' \<or> a' \<in> reject m A p"
        using disjoint_iff_not_equal
        by metis
      hence "a' \<notin> reject m A p' \<or> a' \<in> reject m A p"
        using rej_def_disj rej_set electoral_mod_defer_elem eq input
        unfolding prof_contains_result_def
        by fastforce
    }
    thus ?thesis
      by metis
  qed
  moreover have "\<forall> a \<in> defer m A p. a \<in> defer m A p'"
    using defer_in_alts eq prof_contains_result_def input in_mono
    by fastforce
  moreover have "\<forall> a \<in> defer m A p'. a \<in> defer m A p"
    using calculation defer_not_elec_or_rej
          input subsetI subset_antisym
    by metis
  ultimately show ?thesis
    using prod.collapse subsetI subset_antisym
    by metis
qed

lemma eq_def_and_elect_imp_eq:
  assumes
    mod_m: "electoral_module m" and
    mod_n: "electoral_module n" and
    fin_p: "finite_profile A p" and
    fin_q: "finite_profile A q" and
    elec_eq: "elect m A p = elect n A q" and
    def_eq: "defer m A p = defer n A q"
  shows "m A p = n A q"
proof -
  have disj_m:
    "disjoint3 (m A p)"
    using mod_m fin_p
    unfolding electoral_module_def
    by auto
  have disj_n:
    "disjoint3 (n A q)"
    using mod_n fin_q
    unfolding electoral_module_def
    by auto
  have set_partit_m:
    "set_equals_partition A ((elect m A p), (reject m A p), (defer m A p))"
    using mod_m fin_p
    unfolding electoral_module_def
    by auto
  moreover have
    "disjoint3 ((elect m A p),(reject m A p),(defer m A p))"
    using disj_m prod.collapse
    by metis
  have set_partit_n:
    "set_equals_partition A ((elect n A q), (reject n A q), (defer n A q))"
    using mod_n fin_q
    unfolding electoral_module_def
    by auto
  moreover have
    "disjoint3 ((elect n A q),(reject n A q),(defer n A q))"
    using disj_n prod.collapse
    by metis
  have reject_p:
    "reject m A p = A - ((elect m A p) \<union> (defer m A p))"
    using mod_m fin_p combine_ele_rej_def result_imp_rej
    unfolding electoral_module_def
    by metis
  have reject_q:
    "reject n A q = A - ((elect n A q) \<union> (defer n A q))"
    using mod_n fin_q combine_ele_rej_def result_imp_rej
    unfolding electoral_module_def
    by metis
  from reject_p reject_q
  show ?thesis
    using elec_eq def_eq prod_eqI
    by metis
qed

subsection \<open>Non-Blocking\<close>

text \<open>
  An electoral module is non-blocking iff
  this module never rejects all alternatives.
\<close>

definition non_blocking :: "'a Electoral_Module \<Rightarrow> bool" where
  "non_blocking m \<equiv>
    electoral_module m \<and>
      (\<forall> A p.
          ((A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> reject m A p \<noteq> A))"

subsection \<open>Electing\<close>

text \<open>
  An electoral module is electing iff
  it always elects at least one alternative.
\<close>

definition electing :: "'a Electoral_Module \<Rightarrow> bool" where
  "electing m \<equiv>
    electoral_module m \<and>
      (\<forall> A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> elect m A p \<noteq> {})"

lemma electing_for_only_alt:
  assumes
    one_alt: "card A = 1" and
    electing: "electing m" and
    f_prof: "finite_profile A p"
  shows "elect m A p = A"
proof (safe)
  fix x :: "'a"
  assume electX: "x \<in> elect m A p"
  have
    "\<not> electoral_module m \<or> elect m A p \<subseteq> A"
    using elect_in_alts f_prof
    by (simp add: elect_in_alts)
  with electing have "elect m A p \<subseteq> A"
    unfolding electing_def
    by metis
  with electX show "x \<in> A"
    by auto
next
  fix x :: "'a"
  assume "x \<in> A"
  with electing f_prof one_alt
  show "x \<in> elect m A p"
    unfolding electing_def
    using One_nat_def Suc_leI card_seteq
          card_gt_0_iff elect_in_alts
          infinite_super
    by metis
qed

theorem electing_imp_non_blocking:
  assumes "electing m"
  shows "non_blocking m"
proof (unfold non_blocking_def, safe)
  from assms
  show "electoral_module m"
    unfolding electing_def
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    x :: "'a"
  assume
    finA: "finite A" and
    profA: "profile A p" and
    rejA: "reject m A p = A" and
    xInA: "x \<in> A"
  from assms have
    "electoral_module m \<and>
      (\<forall> A rs. A = {} \<or> infinite A \<or>
        \<not> profile A rs \<or> elect m A rs \<noteq> {})"
    unfolding electing_def
    by metis
  hence f1: "A = {}"
    using Diff_cancel Un_empty
          elec_and_def_not_rej
          finA profA rejA
    by (metis (no_types))
  from  xInA
  have "x \<in> A"
    by metis
  with f1 show "x \<in> {}"
    by metis
qed

subsection \<open>Rejecting\<close>

definition rejecting :: "'a Electoral_Module \<Rightarrow> bool" where
  "rejecting m \<equiv>
    electoral_module m \<and>
      (\<forall> A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> reject m A p \<noteq> {})"


subsection \<open>Properties\<close>

text \<open>
  An electoral module is non-electing iff
  it never elects an alternative.
\<close>

definition non_electing :: "'a Electoral_Module \<Rightarrow> bool" where
  "non_electing m \<equiv>
    electoral_module m \<and> (\<forall> A p. finite_profile A p \<longrightarrow> elect m A p = {})"

lemma single_elim_decr_def_card:
  assumes
    rejecting: "rejects 1 m" and
    not_empty: "A \<noteq> {}" and
    non_electing: "non_electing m" and
    f_prof: "finite_profile A p"
  shows "card (defer m A p) = card A - 1"
proof -
  have "rejects 1 m"
    using One_nat_def rejecting
    by metis
  moreover have
    "electoral_module m \<and>
      (\<forall> A rs. infinite A \<or> \<not> profile A rs \<or> elect m A rs = {})"
    using non_electing
    unfolding non_electing_def
    by metis
  moreover from this have
    "reject m A p \<subseteq> A"
    using f_prof reject_in_alts
    by metis
  ultimately show ?thesis
    using f_prof not_empty
    by (simp add: Suc_leI card_Diff_subset card_gt_0_iff
                  defer_not_elec_or_rej finite_subset
                  rejects_def)
qed

lemma single_elim_decr_def_card2:
  assumes
    eliminating: "eliminates 1 m" and
    not_empty: "card A > 1" and
    non_electing: "non_electing m" and
    f_prof: "finite_profile A p"
  shows "card (defer m A p) = card A - 1"
proof -
  have
    "\<forall> f. (non_electing f \<or>
            (\<exists> A rs. ({}::'a set) \<noteq> elect f A rs \<and> profile A rs \<and> finite A) \<or>
            \<not> electoral_module f) \<and>
          ((\<forall> A rs. {} = elect f A rs \<or> \<not> profile A rs \<or> infinite A) \<and>
            electoral_module f \<or> \<not> non_electing f)"
    using non_electing_def
    by metis
  moreover from this have
    "electoral_module m \<and>
      (\<forall> A rs. infinite A \<or> \<not> profile A rs \<or> elect m A rs = {})"
    using non_electing
    by (metis (no_types))
  moreover from this have
    "reject m A p \<subseteq> A"
    using f_prof reject_in_alts
    by metis
  moreover have "1 < card A"
    using not_empty
    by presburger
  moreover have "eliminates 1 m"
    using One_nat_def eliminating
    by presburger
  moreover have "eliminates 1 m"
    using eliminating
    by force
  ultimately show ?thesis
    using f_prof
    by (simp add: card_Diff_subset defer_not_elec_or_rej
                  eliminates_def finite_subset)
qed

text \<open>
  An electoral module is defer-deciding iff
  this module chooses exactly 1 alternative to defer and
  rejects any other alternative.
  Note that `rejects n-1 m` can be omitted due to the
  well-formedness property.
\<close>

definition defer_deciding :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_deciding m \<equiv>
    electoral_module m \<and> non_electing m \<and> defers 1 m"

text \<open>
  An electoral module decrements iff
  this module rejects at least one alternative whenever possible (|A| > 1).
\<close>

definition decrementing :: "'a Electoral_Module \<Rightarrow> bool" where
  "decrementing m \<equiv>
    electoral_module m \<and> (
      \<forall> A p . finite_profile A p \<longrightarrow>
          (card A > 1 \<longrightarrow> card (reject m A p) \<ge> 1))"

definition defer_condorcet_consistency :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_condorcet_consistency m \<equiv>
    electoral_module m \<and>
    (\<forall> A p w. condorcet_winner A p w \<and> finite A \<longrightarrow>
      (m A p =
        ({},
        A - (defer m A p),
        {d \<in> A. condorcet_winner A p d})))"

definition condorcet_compatibility :: "'a Electoral_Module \<Rightarrow> bool" where
  "condorcet_compatibility m \<equiv>
    electoral_module m \<and>
    (\<forall> A p w. condorcet_winner A p w \<and> finite A \<longrightarrow>
      (w \<notin> reject m A p \<and>
        (\<forall> l. \<not>condorcet_winner A p l \<longrightarrow> l \<notin> elect m A p) \<and>
          (w \<in> elect m A p \<longrightarrow>
            (\<forall> l. \<not>condorcet_winner A p l \<longrightarrow> l \<in> reject m A p))))"

text \<open>
  An electoral module is defer-monotone iff,
  when a deferred alternative is lifted, this alternative remains deferred.
\<close>

definition defer_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_monotonicity m \<equiv>
    electoral_module m \<and>
      (\<forall> A p q w.
          (finite A \<and> w \<in> defer m A p \<and> lifted A p q w) \<longrightarrow> w \<in> defer m A q)"

text \<open>
  An electoral module is defer-lift-invariant iff
  lifting a deferred alternative does not affect the outcome.
\<close>

definition defer_lift_invariance :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_lift_invariance m \<equiv>
    electoral_module m \<and>
      (\<forall> A p q a.
          (a \<in> (defer m A p) \<and> lifted A p q a) \<longrightarrow> m A p = m A q)"

text \<open>
  Two electoral modules are disjoint-compatible if they only make decisions
  over disjoint sets of alternatives. Electoral modules reject alternatives
  for which they make no decision.
\<close>

definition disjoint_compatibility :: "'a Electoral_Module \<Rightarrow>
                                         'a Electoral_Module \<Rightarrow> bool" where
  "disjoint_compatibility m n \<equiv>
    electoral_module m \<and> electoral_module n \<and>
        (\<forall> S. finite S \<longrightarrow>
          (\<exists> A \<subseteq> S.
            (\<forall> a \<in> A. indep_of_alt m S a \<and>
              (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject m S p)) \<and>
            (\<forall> a \<in> S - A. indep_of_alt n S a \<and>
              (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject n S p))))"

text \<open>
  Lifting an elected alternative a from an invariant-monotone
  electoral module either does not change the elect set, or
  makes a the only elected alternative.
\<close>

definition invariant_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "invariant_monotonicity m \<equiv>
    electoral_module m \<and>
        (\<forall> A p q a. (a \<in> elect m A p \<and> lifted A p q a) \<longrightarrow>
          (elect m A q = elect m A p \<or> elect m A q = {a}))"

text \<open>
  Lifting a deferred alternative a from a defer-invariant-monotone
  electoral module either does not change the defer set, or
  makes a the only deferred alternative.
\<close>

definition defer_invariant_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_invariant_monotonicity m \<equiv>
    electoral_module m \<and> non_electing m \<and>
        (\<forall> A p q a. (a \<in> defer m A p \<and> lifted A p q a) \<longrightarrow>
          (defer m A q = defer m A p \<or> defer m A q = {a}))"

subsection \<open>Inference Rules\<close>

lemma ccomp_and_dd_imp_def_only_winner:
  assumes ccomp: "condorcet_compatibility m" and
          dd: "defer_deciding m" and
          winner: "condorcet_winner A p w"
  shows "defer m A p = {w}"
proof (rule ccontr)
  assume not_w: "defer m A p \<noteq> {w}"
  from dd have def_1:
    "defers 1 m"
    unfolding defer_deciding_def
    by metis
  hence c_win:
    "finite_profile A p \<and>  w \<in> A \<and> (\<forall>x \<in> A - {w} . wins w p x)"
    using winner
    by simp
  hence "card (defer m A p) = 1"
    using Suc_leI card_gt_0_iff def_1 equals0D
    unfolding One_nat_def defers_def
    by metis
  hence 0: "\<exists> x \<in> A . defer m A p = {x}"
    using card_1_singletonE dd defer_in_alts insert_subset c_win
    unfolding defer_deciding_def
    by metis
  with not_w have "\<exists> l \<in> A . l \<noteq> w \<and> defer m A p = {l}"
    by metis
  hence not_in_defer: "w \<notin> defer m A p"
    by auto
  have "non_electing m"
    using dd
    unfolding defer_deciding_def
    by simp
  hence not_in_elect: "w \<notin> elect m A p"
    using c_win equals0D
    unfolding non_electing_def
    by simp
  from not_in_defer not_in_elect
  have one_side:
    "w \<in> reject m A p"
    using ccomp c_win electoral_mod_defer_elem
    unfolding condorcet_compatibility_def
    by metis
  from ccomp
  have other_side: "w \<notin> reject m A p"
    using c_win winner
    unfolding condorcet_compatibility_def
    by simp
  thus False
    by (simp add: one_side)
qed

theorem ccomp_and_dd_imp_dcc[simp]:
  assumes
    ccomp: "condorcet_compatibility m" and
    dd: "defer_deciding m"
  shows "defer_condorcet_consistency m"
proof (unfold defer_condorcet_consistency_def, auto)
  from dd
  show "electoral_module m"
    unfolding defer_deciding_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assume
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    finiteness: "finite A" and
    assm: "\<forall> x \<in> A - {w}.
          card {i. i < length p \<and> (w, x) \<in> (p!i)} <
            card {i. i < length p \<and> (x, w) \<in> (p!i)}"
  have winner: "condorcet_winner A p w"
    using assm finiteness prof_A w_in_A
    by simp
  hence
    "m A p =
      ({},
        A - defer m A p,
        {d \<in> A. condorcet_winner A p d})"
  proof -
    from dd have 0: "elect m A p = {}"
      using winner
      unfolding defer_deciding_def non_electing_def
      by simp
    from dd ccomp have 1: "defer m A p = {w}"
      using ccomp_and_dd_imp_def_only_winner winner
      by simp
    from 0 1 have 2: "reject m A p = A - defer m A p"
      using Diff_empty dd reject_not_elec_or_def winner
      unfolding defer_deciding_def
      by fastforce
    from 0 1 2 have 3: "m A p = ({}, A - defer m A p, {w})"
      using combine_ele_rej_def
      by metis
    have "{w} = {d \<in> A. condorcet_winner A p d}"
      using cond_winner_unique3 winner
      by metis
    thus ?thesis
      using 3
      by auto
  qed
  hence
    "m A p =
      ({},
        A - defer m A p,
        {d \<in> A. \<forall> x \<in> A - {d}. wins d p x})"
    using finiteness prof_A winner Collect_cong
    by auto
  hence
    "m A p =
        ({},
          A - defer m A p,
          {d \<in> A. \<forall> x \<in> A - {d}.
            prefer_count p x d < prefer_count p d x})"
    by simp
  hence
    "m A p =
        ({},
          A - defer m A p,
          {d \<in> A. \<forall> x \<in> A - {d}.
            card {i. i < length p \<and> (let r = (p!i) in (d \<preceq>\<^sub>r x))} <
                card {i. i < length p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r d))}})"
    by simp
  thus
    "m A p =
        ({},
          A - defer m A p,
          {d \<in> A. \<forall> x \<in> A - {d}.
            card {i. i < length p \<and> (d, x) \<in> (p!i)} <
              card {i. i < length p \<and> (x, d) \<in> (p!i)}})"
    by simp
qed

text \<open>
  If m and n are disjoint compatible, so are n and m.
\<close>

theorem disj_compat_comm[simp]:
  assumes "disjoint_compatibility m n"
  shows "disjoint_compatibility n m"
proof (unfold disjoint_compatibility_def, safe)
  show "electoral_module m"
    using assms
    unfolding disjoint_compatibility_def
    by simp
next
  show "electoral_module n"
    using assms
    unfolding disjoint_compatibility_def
    by simp
next
  fix S :: "'a set"
  assume fin_S: "finite S"
  obtain A where
    old_A:
      "(A \<subseteq> S \<and>
        (\<forall> a \<in> A. indep_of_alt m S a \<and>
          (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject m S p)) \<and>
        (\<forall> a \<in> S - A. indep_of_alt n S a \<and>
          (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject n S p)))"
    using assms fin_S
    unfolding disjoint_compatibility_def
    by metis
  hence
    "(\<exists> A \<subseteq> S.
      (\<forall> a \<in> S - A. indep_of_alt n S a \<and>
        (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
      (\<forall> a \<in> A. indep_of_alt m S a \<and>
        (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
    by auto
  hence
    "(\<exists> A \<subseteq> S.
      (\<forall> a \<in> S - A. indep_of_alt n S a \<and>
        (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
      (\<forall> a \<in> S - (S - A). indep_of_alt m S a \<and>
        (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
    using double_diff order_refl
    by metis
  thus
    "(\<exists> A \<subseteq> S.
        (\<forall> a \<in> A. indep_of_alt n S a \<and>
          (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
        (\<forall> a \<in> S - A. indep_of_alt m S a \<and>
          (\<forall> p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
    by fastforce
qed

text \<open>
  Every electoral module which is defer-lift-invariant is
  also defer-monotone.
\<close>

theorem dl_inv_imp_def_mono[simp]:
  assumes "defer_lift_invariance m"
  shows "defer_monotonicity m"
  using assms
  unfolding defer_monotonicity_def defer_lift_invariance_def
  by metis

subsection \<open>Social Choice Properties\<close>

subsubsection \<open>Condorcet Consistency\<close>

definition condorcet_consistency :: "'a Electoral_Module \<Rightarrow> bool" where
  "condorcet_consistency m \<equiv>
    electoral_module m \<and>
    (\<forall> A p w. condorcet_winner A p w \<longrightarrow>
      (m A p =
        ({e \<in> A. condorcet_winner A p e},
          A - (elect m A p),
          {})))"

lemma condorcet_consistency2:
  "condorcet_consistency m \<longleftrightarrow>
      electoral_module m \<and>
        (\<forall> A p w. condorcet_winner A p w \<longrightarrow>
            (m A p =
              ({w}, A - (elect m A p), {})))"
proof (safe)
  assume "condorcet_consistency m"
  thus "electoral_module m"
    unfolding condorcet_consistency_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assume
    cc: "condorcet_consistency m" and
    cwin: "condorcet_winner A p w"
  show
    "m A p = ({w}, A - elect m A p, {})"
    using cond_winner_unique3 cc cwin
    unfolding condorcet_consistency_def
    by (metis (mono_tags, lifting))
next
  assume
    e_mod: "electoral_module m" and
    cwin:
    "\<forall> A p w. condorcet_winner A p w \<longrightarrow>
      m A p = ({w}, A - elect m A p, {})"
  have
    "\<forall> f. condorcet_consistency f =
      (electoral_module f \<and>
        (\<forall> A rs a. \<not> condorcet_winner A rs (a::'a) \<or>
          f A rs = ({a \<in> A. condorcet_winner A rs a},
                    A - elect f A rs, {})))"
    unfolding condorcet_consistency_def
    by blast
  moreover have
    "\<forall> A rs a. \<not> condorcet_winner A rs (a::'a) \<or>
        {a \<in> A. condorcet_winner A rs a} = {a}"
    using cond_winner_unique3
    by (metis (full_types))
  ultimately show "condorcet_consistency m"
    unfolding condorcet_consistency_def
    using cond_winner_unique3 e_mod cwin
    by presburger
qed

subsubsection \<open>(Weak) Monotonicity\<close>

text \<open>
  An electoral module is monotone iff
  when an elected alternative is lifted, this alternative remains elected.
\<close>

definition monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "monotonicity m \<equiv>
    electoral_module m \<and>
      (\<forall> A p q w.
          (finite A \<and> w \<in> elect m A p \<and> lifted A p q w) \<longrightarrow> w \<in> elect m A q)"

subsubsection \<open>Homogeneity\<close>

fun times :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "times n l = concat (replicate n l)"

definition homogeneity :: "'a Electoral_Module \<Rightarrow> bool" where
  "homogeneity m \<equiv>
    electoral_module m \<and>
      (\<forall> A p n.
        (finite_profile A p \<and> n > 0 \<longrightarrow>
          (m A p = m A (times n p))))"

end
