section \<open>Split Cycle Module\<close>

theory Split_Cycle_Module
  imports "Component_Types/Electoral_Module"
          "Component_Types/Margin_Graph_Creator"
          "Component_Types/Graph_Winner_Finder"
          "Component_Types/Cycle_Resolver"
begin

text\<open>
  The Split Cycle Module uses several other modules to perform the split cycle voting rule.
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
  assumes "lifted A p q w"
  shows "\<forall> x \<in> A - {w}. card {i::nat. 
    i < length p \<and> (let r = (p!i) in (w \<preceq>\<^sub>r x))} \<ge>
    card {i::nat. i < length q \<and> (let r = (q!i) in (w \<preceq>\<^sub>r x))}"
proof -
  have finite:"finite_profile A p \<and> finite_profile A q"
    using assms lifted_def
    by metis
  have 1:"(\<forall> i::nat.
        (i < length p \<and> \<not>Preference_Relation.lifted A (p!i) (q!i) w) \<longrightarrow>
          (p!i) = (q!i)) \<and>
      (\<exists> i::nat. i < length p \<and> Preference_Relation.lifted A (p!i) (q!i) w)"
    using assms lifted_def
    by metis
  then have "\<forall>i < length p.(p!i) = (q!i) \<or> (let r = p!i in let s = q!i in 
    (\<forall> x \<in> A - {w}. \<not>(x \<preceq>\<^sub>r w \<and> w \<preceq>\<^sub>s x)))"
    using assms lifted_mono 
    by (metis (full_types))
  then have "\<forall>i < length p.(p!i) = (q!i) \<or> (let r = p!i in let s = q!i in 
    (\<forall> x \<in> A - {w}. (w \<preceq>\<^sub>s x \<longrightarrow> w \<preceq>\<^sub>r x)))"
    using 1 lifted_above pref_imp_in_above subsetD
    by (meson )
  then have "\<forall>i < length p.(let r = p!i in let s = q!i in 
    (\<forall> x \<in> A - {w}. (w \<preceq>\<^sub>s x \<longrightarrow> w \<preceq>\<^sub>r x)))"
    by metis
  then have "\<forall> x \<in> A - {w}. {i::nat. 
    i < length p \<and> (let r = (p!i) in (w \<preceq>\<^sub>r x))} \<supseteq>
     {i::nat. i < length p \<and> (let r = (q!i) in (w \<preceq>\<^sub>r x))}"
    by (simp add: Collect_mono_iff)
  then have "\<forall> x \<in> A - {w}. card {i::nat. 
    i < length p \<and> (let r = (p!i) in (w \<preceq>\<^sub>r x))} \<ge>
     card {i::nat. i < length p \<and> (let r = (q!i) in (w \<preceq>\<^sub>r x))}"
    using finite
  proof -
    { fix aa :: 'a
      { assume "{n. n < length p \<and> w \<preceq>\<^sub>(q ! n) aa} \<subseteq> {n. n < length p \<and> w \<preceq>\<^sub>(p ! n) aa} \<and> finite {n. n < length p \<and> w \<preceq>\<^sub>(p ! n) aa}"
        then have "aa \<notin> A - {w} \<or> card {n. n < length p \<and> w \<preceq>\<^sub>(q ! n) aa} \<le> card {n. n < length p \<and> w \<preceq>\<^sub>(p ! n) aa}"
          using card_mono by blast }
      then have "aa \<notin> A - {w} \<or> card {n. n < length p \<and> w \<preceq>\<^sub>(q ! n) aa} \<le> card {n. n < length p \<and> w \<preceq>\<^sub>(p ! n) aa}"
        by (metis (lifting) \<open>\<forall>x\<in>A - {w}. {i. i < length p \<and> (let r = q ! i in w \<preceq>\<^sub>r x)} \<subseteq> {i. i < length p \<and> (let r = p ! i in w \<preceq>\<^sub>r x)}\<close> bounded_nat_set_is_finite mem_Collect_eq) }
    then show ?thesis
      by meson
  qed
  moreover have "length p = length q"
    using assms lifted_def
    by metis
  ultimately show "\<forall> x \<in> A - {w}. card {i::nat. 
    i < length p \<and> (let r = (p!i) in (w \<preceq>\<^sub>r x))} \<ge>
    card {i::nat. i < length q \<and> (let r = (q!i) in (w \<preceq>\<^sub>r x))}"
    by simp 
qed

lemma lift_decreases_in_arc_weight:
  assumes "lifted A p q w"
  shows "\<forall>x\<in>A-{w}. mg_weight A q (x,w) \<le> mg_weight A p (x,w)"
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
  ultimately have "\<forall> x \<in> A - {w}. prefer_count q x w - prefer_count q w x
    \<le> prefer_count p x w - prefer_count p w x"
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


lemma lifted_in_arcs_min_arcs:
  assumes "(finite A \<and> w \<in> elect split_cycle A p \<and> lifted A p q w)"
  shows "in_arcs (create_margin_graph A q mg_weight) w 
    \<subseteq> min_arcs (create_margin_graph A q mg_weight) mg_weight A q"
proof (rule subsetI)
  fix x
  assume x_def:"x\<in>in_arcs (create_margin_graph A q mg_weight) w"
  obtain G where G_def:"G = (create_margin_graph A p mg_weight)"
    by simp
  obtain G' where G'_def:"G' = (create_margin_graph A q mg_weight)"
    by simp
  have x_snd:"snd x = w"
    using x_def in_arcs_def 
    by simp
  have "mg_weight A q (w,w) = 0"
    by simp
  then have x_fst:"fst x \<in> A-{w}" 
    using x_def by auto
  have "x\<in>in_arcs G w"
    using x_def lift_in_arcs_subset assms subset_iff G_def
    by metis 
  moreover have "in_arcs (resolve_all_cycles G mg_weight p) w = {}"
    using assms G_def by simp
  ultimately have "x\<in>min_arcs G mg_weight A p"
    using G_def resolve_all_cycles_preserves_head select_convs(2) empty_iff 
    DiffI candidates_are_vertices  resolve_all_cycles.simps in_in_arcs_conv
    by metis
  then obtain simpcyc where sc_def:"simpcyc \<in> all_simple_cycles G 
    \<and> x\<in>min_elems mg_weight A p simpcyc"
    using Union_iff min_arcs_def by fastforce
  then have x_in_sc: "x\<in>set simpcyc"
    using min_elems_in_set subset_iff by metis
  then have "\<exists>i. i<length simpcyc \<and> simpcyc!i = x"
    using sc_def
    by (simp add: in_set_conv_nth)    
  then obtain i where i_def:"i<length simpcyc \<and> simpcyc!i = x"
    by auto
  moreover have "distinct_snd simpcyc"
    using simple_cycle_distinct sc_def by metis
  ultimately have notw:"\<forall>j<length simpcyc.  j \<noteq> i\<longrightarrow> snd (simpcyc!j)\<noteq>w"
    using x_snd distinct_Ex1 distinct_snd.elims(2) length_map nth_map nth_mem
    by metis 
  moreover have subset_sc:"set simpcyc \<subseteq> arcs G"
    using sc_def cyc_arc_still_arc all_arcs_in_cycles_def
    by blast
  ultimately have "\<forall>j<length simpcyc.  j \<noteq> i\<longrightarrow>(simpcyc!j)\<in>arcs G'"
    using assms G'_def G_def other_arcs_stay subset_iff nth_mem length_map nth_map
  proof -
    have f1: "veriT_sk0 < length simpcyc \<longrightarrow> simpcyc ! veriT_sk0 \<in> set simpcyc"
      by auto
    have f2: "Profile.lifted A p q w \<and> simpcyc ! veriT_sk0 \<in> arcs (create_margin_graph A p mg_weight) \<and> w \<noteq> snd (simpcyc ! veriT_sk0) \<longrightarrow> simpcyc ! veriT_sk0 \<in> arcs (create_margin_graph A q mg_weight)"
      by (metis other_arcs_stay)
    have f3: "\<forall>p. p \<in> set simpcyc \<longrightarrow> p \<in> arcs G"
      using \<open>set simpcyc \<subseteq> arcs G\<close> by force
    obtain nn :: nat where
      "(\<exists>veriT_vr1. (veriT_vr1 < length simpcyc \<and> i \<noteq> veriT_vr1) \<and> simpcyc ! veriT_vr1 \<notin> arcs G') \<longrightarrow> (nn < length simpcyc \<and> i \<noteq> nn) \<and> simpcyc ! nn \<notin> arcs G'"
      by moura
    then show ?thesis
      using f3 f2 f1 G'_def G_def \<open>\<forall>j<length simpcyc. j \<noteq> i \<longrightarrow> snd (simpcyc ! j) \<noteq> w\<close> assms by blast
  qed
  then have sc_def2:"simpcyc \<in> all_simple_cycles G'"
    sorry
  have 1:"\<forall>y\<in>set simpcyc. mg_weight A p x \<le> mg_weight A p y"
    using sc_def min_elems_give_min by metis
  have 2:"mg_weight A q x \<le> mg_weight A p x"
    using x_snd x_fst assms lift_decreases_in_arc_weight prod.collapse
    by metis
  have "\<forall>j<length simpcyc. fst (simpcyc!j) \<in> A"
    using subset_sc G_def arcs_lead_to_verts(1) Diff_iff G'_def candidates_are_vertices
    \<open>\<forall>j<length simpcyc. j \<noteq> i \<longrightarrow> simpcyc ! j \<in> arcs G'\<close>  i_def x_fst
    by metis
  moreover have "\<forall>j<length simpcyc. j\<noteq>i \<longrightarrow> snd (simpcyc!j) \<in> A-{w}"
    using subset_sc G_def arcs_lead_to_verts(2) Diff_iff G'_def candidates_are_vertices
    \<open>\<forall>j<length simpcyc. j \<noteq> i \<longrightarrow> simpcyc ! j \<in> arcs G'\<close>  i_def x_fst notw empty_iff insert_iff
    by metis
  ultimately have 3:"\<forall>j<length simpcyc. j\<noteq>i \<longrightarrow>
    mg_weight A q (simpcyc!j) \<ge> mg_weight A p (simpcyc!j)"
    using assms lift_keeps_other_weights lift_increases_out_arc_weight insertE
     Diff_empty Diff_insert0  insert_Diff order_class.order_eq_iff prod.collapse
    by (smt (verit, del_insts))
  have "\<forall>y\<in>set simpcyc. mg_weight A q x \<le> mg_weight A q y"
    using 1 2 3 i_def order_less_le_trans in_set_conv_nth
    Orderings.order_eq_iff order_le_imp_less_or_eq order_less_imp_le 
    by (smt (verit, ccfv_threshold) )
  then have "x\<in>min_elems mg_weight A q simpcyc"
    using x_in_sc min_in_min_elems
    by metis
  then show "x\<in>min_arcs (create_margin_graph A q mg_weight) mg_weight A q"
    using sc_def2 min_arcs_def G'_def
    by blast    
qed

lemma lift_winner_still_winner:
  assumes "(finite A \<and> w \<in> elect split_cycle A p \<and> lifted A p q w)"
  shows "w \<in> elect split_cycle A q"
proof -
  have "in_arcs (create_margin_graph A q mg_weight) w 
    \<subseteq> min_arcs (create_margin_graph A q mg_weight) mg_weight A q"
    using assms lifted_in_arcs_min_arcs
    by metis
  then have no_in_arcs: "in_arcs (resolve_all_cycles 
      (create_margin_graph A q mg_weight) mg_weight q) w = {}"
    using resolve_all_cycles.simps in_arcs_def
    by fastforce
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


end