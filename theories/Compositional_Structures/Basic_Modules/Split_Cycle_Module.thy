section \<open>Split Cycle Module\<close>

theory Split_Cycle_Module
  imports "Component_Types/Electoral_Module"
          "Component_Types/Margin_Graph_Creator"
          "Component_Types/Graph_Winner_Finder"
          "Component_Types/Cycle_Resolver"
          Reject_Module
begin

text\<open>
  The Split Cycle Module uses several other modules to perform the split cycle voting rule.
  It's made up of three Electoral Modules used sequentially.
\<close>

fun mg_weight::"'a Weight_Function" where
"mg_weight cand P arc = (prefer_count P (fst arc) (snd arc)) 
- (prefer_count P (snd arc) (fst arc))"

fun split_cycle::"'a Electoral_Module" where
"split_cycle A p = evaluate_graph( resolve_all_cycles 
(create_margin_graph A p mg_weight) mg_weight p)"

lemma split_cycle_sound:"electoral_module split_cycle"
  unfolding electoral_module_def
  using validResult candidates_are_vertices resolve_cycle_preserves_verts split_cycle.simps
  by metis

subsection \<open>Condorcet Consistency\<close>

lemma condorcet_winner_in_graph: "condorcet_winner A p c \<longrightarrow> c \<in> A"
  by simp

lemma condorcet_weight:
  assumes "condorcet_winner A p c"
  shows "\<forall>x\<in>(A - {c}). mg_weight A p (x,c) = 0"
proof 
  have "\<forall>x\<in>(A-{c}). wins c p x"
    using assms 
    by simp
  then have preferred:"\<forall>x\<in>(A-{c}).prefer_count p c x > prefer_count p x c "
    by simp
  then have "\<forall>x\<in>(A-{c}).prefer_count p x c - prefer_count p c x = 0 "
  proof -
    show ?thesis
      using preferred diff_is_0_eq order_less_imp_le
      by metis
  qed
  then show "\<And>x. x \<in> A - {c} \<Longrightarrow> mg_weight A p (x, c) = 0"
    by simp
qed

lemma condorcet_winner_no_in_arcs:
  assumes "condorcet_winner A p c"
  shows "in_arcs (create_margin_graph A p mg_weight) c = {}"
proof -
  have first:"\<forall>x\<in>(A - {c}). mg_weight A p (x,c) = 0 \<and> c\<in>A"
    using assms condorcet_weight condorcet_winner_in_graph
    by simp
  then show ?thesis
    using condorcet_degree
    by metis
qed

lemma condorcet_winner_is_winner:
  assumes "condorcet_winner A p c"
  shows "c \<in> elect (split_cycle) A p"
proof -
  have "in_arcs (create_margin_graph A p mg_weight) c = {}"
    using condorcet_winner_no_in_arcs assms
    by metis
  then have no_in_arcs: "in_arcs (resolve_all_cycles 
    (create_margin_graph A p mg_weight) mg_weight p) c = {}"
    using resolving_in_arcs_empty
    by metis
  moreover have "c\<in>verts(create_margin_graph A p mg_weight)"
    using assms
    by simp
  then have "c\<in>verts(resolve_all_cycles 
    (create_margin_graph A p mg_weight) mg_weight p)"
    using resolve_cycle_preserves_verts
    by metis
  then have "c\<in>get_winners (resolve_all_cycles 
    (create_margin_graph A p mg_weight) mg_weight p)"
    using winners_def no_in_arcs in_arcs_def
    by simp
  then show ?thesis
    by simp
qed
    
lemma non_condorcet_weight:
  assumes "condorcet_winner A p c"
  shows "\<forall>x\<in>(A - {c}). mg_weight A p (c,x) > 0"
proof 
  have "\<forall>x\<in>(A-{c}). wins c p x"
    using assms 
    by simp
  then have unpreferred:"\<forall>x\<in>(A-{c}).prefer_count p c x > prefer_count p x c "
    by simp
  then have "\<forall>x\<in>(A-{c}).prefer_count p c x - prefer_count p x c > 0 "
  proof -
    show ?thesis
      using unpreferred zero_less_diff by blast 
  qed
  then show "\<And>x. x \<in> A - {c} \<Longrightarrow> mg_weight A p (c, x) > 0"
    by simp
qed    

lemma non_condorcet_is_loser: 
  assumes "condorcet_winner A p c"
  shows "(A-{c}) \<subseteq> reject (split_cycle) A p"
proof -
  have "(\<forall>x\<in>(A - {c}). mg_weight A p (c,x) > 0) \<and> c\<in>A"
    using non_condorcet_weight condorcet_winner_in_graph assms
    by metis
  then have unresolved:"\<forall>x\<in>(A - {c}). \<exists>y. y\<in>in_arcs (create_margin_graph A p mg_weight) x 
    \<and> y \<in>out_arcs (create_margin_graph A p mg_weight) c"
    using non_condorcet_degree
    by metis
  then have "\<forall>x\<in>(A - {c}). \<exists>y. (y\<in>in_arcs (
    resolve_all_cycles (create_margin_graph A p mg_weight) mg_weight p) x)"
  proof (cases "cycle_exists (create_margin_graph A p mg_weight)")
    case True
    have "in_arcs (create_margin_graph A p mg_weight) c = {}"
      using condorcet_winner_no_in_arcs assms
      by metis
    then have "(out_arcs (create_margin_graph A p mg_weight) c)
      \<inter> (all_arcs_in_cycles (create_margin_graph A p mg_weight)) = {}"
      using condorcet_not_in_cycle True Int_commute
      by metis
    then have "\<forall>x\<in>(A - {c}). \<exists>y. (y\<in>in_arcs
     (create_margin_graph A p mg_weight) x) 
    \<and> (y\<notin>all_arcs_in_cycles(create_margin_graph A p mg_weight))"
      using unresolved disjoint_iff_not_equal
      by meson
    then have "\<forall>x\<in>(A - {c}). \<exists>y. (y\<in>in_arcs
     (create_margin_graph A p mg_weight) x) 
    \<and> (y\<in>arcs(resolve_all_cycles(create_margin_graph A p mg_weight) mg_weight p))"
      using resolve_all_cycles_preserves_non_cycle_arcs True arcs_subset Diff_iff in_arcs_in_arcs in_mono
      by (smt (verit, ccfv_threshold) )
    then show ?thesis 
      using  True unresolved in_arcs_def resolve_all_cycles_preserves_head 
      by (metis (no_types, lifting) in_in_arcs_conv)
  next
    case False
    then have "arcs (resolve_all_cycles (create_margin_graph A p mg_weight) mg_weight p)
      = arcs (create_margin_graph A p mg_weight)"
      using no_cycle_no_min_arcs resolve_all_cycles.simps Diff_empty select_convs(2)
      by metis
      
    then show ?thesis 
      using unresolved in_in_arcs_conv resolve_all_cycles_preserves_head 
      by (metis (no_types, lifting) )      
  qed
  then have in_arcs_exist:"\<forall>x\<in>A-{c}. in_arcs (resolve_all_cycles 
    (create_margin_graph A p mg_weight) mg_weight p) x \<noteq> {}"
    using empty_iff
    by metis
  have "\<forall>x\<in>A-{c}. x\<in>verts (resolve_all_cycles 
    (create_margin_graph A p mg_weight) mg_weight p)"
    using candidates_are_vertices resolve_cycle_preserves_verts DiffD1
    by metis   
  then have "\<forall>x\<in>A-{c}. x\<in>get_losers (resolve_all_cycles 
    (create_margin_graph A p mg_weight) mg_weight p)"
    using winners_def in_arcs_exist
    by simp  
  then show ?thesis
    using evaluate_graph.simps fst_eqD snd_eqD split_cycle.simps subsetI
    by metis    
qed

lemma condorcet_winner_sole_winner:
  assumes "condorcet_winner A p c"
  shows "split_cycle A p = ({c},A-{c},{})"
proof -
  have partition: "set_equals_partition A (split_cycle A p)"
    using candidates_are_vertices resolve_cycle_preserves_verts split_cycle.elims validResult well_formed.elims(2)
    by metis 
  have disjoint:"disjoint3 (split_cycle A p)"
    using validResult split_cycle.simps well_formed.elims(2)
    by metis
  have winner:"c\<in>elect split_cycle A p"
    using assms condorcet_winner_is_winner
    by metis
  have loser:"A-{c}\<subseteq> reject split_cycle A p"
    using assms non_condorcet_is_loser
    by metis
  then have elected:"elect split_cycle A p={c}"
    using winner disjoint partition Diff_empty Int_absorb2 Int_insert_right_if1 disjoint3.simps elect_subset insert_Diff insert_Diff_single prod.collapse reject_subset subset_Diff_insert subset_antisym well_formed.elims(3)
    by (smt (verit)) 
  then have rejected:"reject split_cycle A p=A-{c}"
    using partition disjoint winner loser
       Diff_empty Int_iff disjoint3.simps empty_iff prod.collapse reject_subset subset_Diff_insert subset_antisym well_formed.elims(3)
    by metis
  have deferred:"defer split_cycle A p = {}"
    using evaluate_graph.simps split_cycle.simps snd_conv
    by metis
  show ?thesis
    using elected rejected deferred
    by simp
qed


lemma split_cycle_condorcet_consistent:"condorcet_consistency split_cycle"
  using condorcet_winner_sole_winner split_cycle_sound condorcet_consistency2 fst_eqD
  by (smt (verit, ccfv_threshold))

subsection \<open>Monotonicity\<close>

lemma lift_starter:
  assumes "lifted A p q a"
  shows "\<forall> x \<in> A - {a}. card {i::nat. 
    i < length p \<and> (let r = (p!i) in (a \<preceq>\<^sub>r x))} \<ge>
    card {i::nat. i < length q \<and> (let r = (q!i) in (a \<preceq>\<^sub>r x))}"
proof -
  have finite:"finite_profile A p \<and> finite_profile A q"
    using assms lifted_def
    by metis
  have 1:"(\<forall> i::nat.
        (i < length p \<and> \<not>Preference_Relation.lifted A (p!i) (q!i) a) \<longrightarrow>
          (p!i) = (q!i)) \<and>
      (\<exists> i::nat. i < length p \<and> Preference_Relation.lifted A (p!i) (q!i) a)"
    using assms lifted_def
    by metis
  then have "\<forall>i < length p.(p!i) = (q!i) \<or> (let r = p!i in let s = q!i in 
    (\<forall> x \<in> A - {a}. \<not>(x \<preceq>\<^sub>r a \<and> a \<preceq>\<^sub>s x)))"
    using assms lifted_mono 
    by (metis (full_types))
  then have "\<forall>i < length p.(p!i) = (q!i) \<or> (let r = p!i in let s = q!i in 
    (\<forall> x \<in> A - {a}. (a \<preceq>\<^sub>s x \<longrightarrow> a \<preceq>\<^sub>r x)))"
    using 1 lifted_above pref_imp_in_above subsetD
    by (meson )
  then have "\<forall>i < length p.(let r = p!i in let s = q!i in 
    (\<forall> x \<in> A - {a}. (a \<preceq>\<^sub>s x \<longrightarrow> a \<preceq>\<^sub>r x)))"
    by metis
  then have "\<forall> x \<in> A - {a}. {i::nat. 
    i < length p \<and> (let r = (p!i) in (a \<preceq>\<^sub>r x))} \<supseteq>
     {i::nat. i < length p \<and> (let r = (q!i) in (a \<preceq>\<^sub>r x))}"
    by (simp add: Collect_mono_iff)
  then have "\<forall> x \<in> A - {a}. card {i::nat. 
    i < length p \<and> (let r = (p!i) in (a \<preceq>\<^sub>r x))} \<ge>
     card {i::nat. i < length p \<and> (let r = (q!i) in (a \<preceq>\<^sub>r x))}"
    using finite
  proof -
    { fix aa :: 'a
      { assume "{n. n < length p \<and> a \<preceq>\<^sub>(q ! n) aa} \<subseteq> {n. n < length p \<and> a \<preceq>\<^sub>(p ! n) aa} \<and> finite {n. n < length p \<and> a \<preceq>\<^sub>(p ! n) aa}"
        then have "aa \<notin> A - {a} \<or> card {n. n < length p \<and> a \<preceq>\<^sub>(q ! n) aa} \<le> card {n. n < length p \<and> a \<preceq>\<^sub>(p ! n) aa}"
          using card_mono by blast }
      then have "aa \<notin> A - {a} \<or> card {n. n < length p \<and> a \<preceq>\<^sub>(q ! n) aa} \<le> card {n. n < length p \<and> a \<preceq>\<^sub>(p ! n) aa}"
        by (metis (lifting) \<open>\<forall>x\<in>A - {a}. {i. i < length p \<and> (let r = q ! i in a \<preceq>\<^sub>r x)} \<subseteq> {i. i < length p \<and> (let r = p ! i in a \<preceq>\<^sub>r x)}\<close> bounded_nat_set_is_finite mem_Collect_eq) }
    then show ?thesis
      by meson
  qed
  moreover have "length p = length q"
    using assms lifted_def
    by metis
  ultimately show "\<forall> x \<in> A - {a}. card {i::nat. 
    i < length p \<and> (let r = (p!i) in (a \<preceq>\<^sub>r x))} \<ge>
    card {i::nat. i < length q \<and> (let r = (q!i) in (a \<preceq>\<^sub>r x))}"
    by simp 
qed

lemma lift_decreases_in_arc_weight:
  assumes "lifted A p q a"
  shows "\<forall>x\<in>A-{a}. mg_weight A q (x,a) \<le> mg_weight A p (x,a)"
proof -
  have "\<forall> x \<in> A - {a}. card {i::nat. 
    i < length p \<and> (let r = (p!i) in (a \<preceq>\<^sub>r x))} \<ge>
    card {i::nat. i < length q \<and> (let r = (q!i) in (a \<preceq>\<^sub>r x))}"
    using lift_starter assms
    by simp
  then have "\<forall> x \<in> A - {a}. prefer_count p x a \<ge> prefer_count q x a"
    using prefer_count.simps
    by simp
  moreover have "\<forall> x \<in> A - {a}. prefer_count p a x \<le> prefer_count q a x"
    using DiffE Profile.lifted_def assms calculation diff_le_mono2 pref_count singleton_iff
    by (metis (no_types, lifting))    
  ultimately have "\<forall> x \<in> A - {a}. prefer_count q x a - prefer_count q a x
    \<le> prefer_count p x a - prefer_count p a x"
    using diff_commute diff_diff_cancel diff_le_mono2 diff_le_self le_trans
    by (metis (full_types))
  then show ?thesis
    by simp    
qed

lemma lift_increases_out_arc_weight:
  assumes "lifted A p q w"
  shows "\<forall>x\<in>A-{w}. mg_weight A q (w,x) \<ge> mg_weight A p (w,x)"
proof -
  have "\<forall> x \<in> A - {w}. card {i::nat. 
    i < length p \<and> (let r = (p!i) in (w \<preceq>\<^sub>r x))} \<ge>
    card {i::nat. i < length q \<and> (let r = (q!i) in (w \<preceq>\<^sub>r x))}"
    using lift_starter assms
    by simp
  then have "\<forall> x \<in> A - {w}. prefer_count p x w \<ge> prefer_count q x w"
    using prefer_count.simps
    by simp
  moreover have "\<forall> x \<in> A - {w}. prefer_count p w x \<le> prefer_count q w x"
    using DiffE Profile.lifted_def assms calculation diff_le_mono2 pref_count singleton_iff
    by (metis (no_types, lifting))    
  ultimately have "\<forall> x \<in> A - {w}. prefer_count q w x - prefer_count q x w
    \<ge> prefer_count p w x - prefer_count p x w"
    using diff_commute diff_diff_cancel diff_le_mono2 diff_le_self le_trans
    by (metis (full_types))
  then show ?thesis
    by simp    
qed

lemma lift_keeps_other_weights:
  assumes "lifted A p q w"
  shows "\<forall>x\<in>A-{w}. \<forall>y\<in>A-{w}. mg_weight A q (x,y) = mg_weight A p (x,y)"
proof -
  have start:"finite_profile A p \<and> finite_profile A q \<and> length q = length p"
    using assms lifted_def
    by metis
  have 1:"(\<forall> i::nat.
        (i < length p \<and> \<not>Preference_Relation.lifted A (p!i) (q!i) w) \<longrightarrow>
          (p!i) = (q!i)) \<and>
      (\<exists> i::nat. i < length p \<and> Preference_Relation.lifted A (p!i) (q!i) w)"
    using assms lifted_def
    by metis
  then have either:"\<forall>i < length p. (p!i) = (q!i) \<or> equiv_rel_except_a A (p!i) (q!i) w"
    using lifted_imp_equiv_rel_except_a
    by meson
  then have "\<forall>i < length p. \<forall>x\<in>A-{w}. \<forall>y\<in>A-{w}. 
    (let r = p!i in let s = q!i in y \<preceq>\<^sub>s x \<longleftrightarrow> y \<preceq>\<^sub>r x)"
    using equiv_rel_except_a_def
  proof -
    { fix nn :: nat and aa :: 'a and aaa :: 'a
      have "\<not> nn < length p \<or> aa \<notin> A - {w} \<or> aaa \<notin> A - {w} \<or> \<not> aa \<preceq>\<^sub>(p ! nn) aaa \<and> \<not> aa \<preceq>\<^sub>(q ! nn) aaa \<or> aa \<preceq>\<^sub>(p ! nn) aaa \<and> aa \<preceq>\<^sub>(q ! nn) aaa"
        using either equiv_rel_except_a_def
        by (metis (no_types) ) }
    then show ?thesis
      by meson
  qed
  then have "\<forall>x\<in>A-{w}. \<forall>y\<in>A-{w}. prefer_count p x y = prefer_count q x y" 
    using start Collect_cong prefer_count.simps
    by (metis (mono_tags, lifting))
  then show ?thesis
    using mg_weight.simps
    by simp
qed

lemma lift_in_arcs_subset:
  assumes "lifted A p q w"
  shows "in_arcs (create_margin_graph A q mg_weight) w
    \<subseteq> in_arcs (create_margin_graph A p mg_weight) w"
proof (rule subsetI)
  fix x
  assume x_def:"x \<in> in_arcs (create_margin_graph A q mg_weight) w"
  then have 1:"snd x = w"
    using in_arcs_def
    by simp
  have 2:"fst x \<in> A"
    using x_def by auto
  then have 3:"x \<in> arcs (delete_empty_edges (create_full_graph A) A q mg_weight)"
    using x_def by simp
  then have 4:"x \<in> arcs (create_full_graph A)"
    by auto
  have weight:"mg_weight A q x > 0"
    using 3 by auto
  have "mg_weight A q (w,w) = 0"
    by simp
  then have "fst x \<in> A - {w}"
    using 1 2 weight
    by auto 
  then have "mg_weight A p x > 0"
    using lift_decreases_in_arc_weight assms x_def weight 1 2 gr0I linorder_not_less prod.exhaust_sel
    by metis
  then have "x \<in> arcs (delete_empty_edges (create_full_graph A) A p mg_weight)"
    using 4
    by auto
  then show "x \<in> in_arcs (create_margin_graph A p mg_weight) w"
    using 1 by simp
qed

lemma other_arcs_stay:
  assumes "lifted A p q w"
  assumes "x\<in>arcs(create_margin_graph A p mg_weight)"
  assumes "snd x \<noteq> w"
  shows "x\<in>arcs(create_margin_graph A q mg_weight)"
proof -
  have 1:"x \<in> arcs (delete_empty_edges (create_full_graph A) A p mg_weight)"
    using assms(2) by simp
  then have in_G:"x \<in> arcs (create_full_graph A)"
    by auto
  then have x_def:"fst x\<in> A \<and> snd x\<in>A - {w}"
    using assms(3)
    by auto
  have weight:"mg_weight A p x > 0"
    using 1 by auto
  then have "mg_weight A q x > 0"
    using x_def assms(1) lift_keeps_other_weights lift_increases_out_arc_weight
    Diff_empty Diff_insert0 gr0I insertE insert_Diff leD prod.collapse
    by (smt (verit))
  then have "x \<in> arcs (delete_empty_edges (create_full_graph A) A q mg_weight)"
    using in_G by auto
  then show ?thesis
    by simp
qed

    

lemma lift_winner_still_winner:
  assumes "(finite A \<and> w \<in> elect split_cycle A p \<and> lifted A p q w)"
  shows "w \<in> elect split_cycle A q"
proof -
  have final:"in_arcs (resolve_all_cycles 
    (create_margin_graph A p mg_weight) mg_weight p) w = {}"
    using assms
    by simp
  show ?thesis
  proof (cases "in_arcs (create_margin_graph A p mg_weight) w = {}")
    case True
    then have "in_arcs (delete_empty_edges (create_full_graph A) 
      A p mg_weight) w = {}"
      by simp
    moreover have "w \<in> A" 
      using assms by simp
    ultimately have "\<forall>x\<in>A-{w}. mg_weight A p (x,w) = 0"
      using no_in_arcs_no_weights
      by auto
    then have "\<forall>x\<in>A-{w}. mg_weight A q (x,w) = 0"
      using assms lift_decreases_in_arc_weight bot.extremum_unique bot_nat_def
      by metis
    then have "in_arcs (create_margin_graph A q mg_weight) w = {}"
      using condorcet_degree assms
      by auto
    then have no_in_arcs: "in_arcs (resolve_all_cycles 
      (create_margin_graph A q mg_weight) mg_weight q) w = {}"
      using resolving_in_arcs_empty
      by metis
    moreover have "w\<in>verts(create_margin_graph A q mg_weight)"
      using assms
      by simp
    then have "w\<in>verts(resolve_all_cycles 
      (create_margin_graph A q mg_weight) mg_weight q)"
      using resolve_cycle_preserves_verts
      by metis
    then have "w\<in>get_winners (resolve_all_cycles 
      (create_margin_graph A q mg_weight) mg_weight q)"
      using winners_def no_in_arcs in_arcs_def
      by simp
    then show ?thesis
      by simp
  next
    case False
    obtain G where G_def:"G = (create_margin_graph A p mg_weight)"
      by simp
    then have hd_def:"head G = snd \<and> tail G = fst"
      by simp
    then have snd_w:"\<forall>x\<in>in_arcs G w. snd x = w"
      using in_arcs_def
      by simp
    have "in_arcs G w \<subseteq> (min_arcs G mg_weight A p)"
      using G_def final resolve_all_cycles.simps candidates_are_vertices in_in_arcs_conv
      DiffI insert_absorb insert_not_empty resolve_all_cycles_preserves_head select_convs(2) subsetI
      by (smt (verit, del_insts))
    then have "\<forall>x\<in>in_arcs G w. \<exists>cyc\<in>all_simple_cycles G. 
      x\<in>(min_elems mg_weight A p cyc)"
      using min_arcs_def
      by fastforce
    then have "\<forall>x\<in>in_arcs G w. \<exists>cyc\<in>all_simple_cycles G. 
      x\<in>(set cyc) \<and> set (cyc)-{x}\<inter>in_arcs G w = {}"
      using in_arcs_def snd_w all_simple_cycles_def trim_cyc_distinct_unfinished min_elems_in_set
      

    then show ?thesis sorry
  qed
qed

lemma split_cycle_monotone:
  "monotonicity split_cycle"
proof-
  have "
      (\<forall> A p q w.
          (finite A \<and> w \<in> elect split_cycle A p \<and> lifted A p q w) \<longrightarrow> w \<in> elect split_cycle A q)"
    using lift_winner_still_winner
    by metis
  then show ?thesis
    using split_cycle_sound monotonicity_def
    by (smt (verit, best))    
qed

subsection \<open>Other\<close>

lemma "profile {} [{}] = True"
 unfolding profile_def all_set_conv_all_nth
  by simp


lemma "profile {0} [{(0,0)}] = True"
  unfolding profile_def all_set_conv_all_nth
  by simp


lemma help11[simp]: "card {i. i = c \<and> x \<in> (s ! c)} = (if x\<in>(s ! c) then 1 else 0)"
  by auto

lemma help12[simp]: "{i. i = c \<and> x \<in> (s ! i)} = (if x\<in>(s ! c) then {c} else {})"
  by auto


  

end