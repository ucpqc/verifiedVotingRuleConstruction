(* Title:  Cycle_Helper.thy
   
*)
section \<open>Cycle Helper\<close>

theory Cycle_Helper
  imports "Graph_Theory.Digraph"
          "Graph_Theory.Arc_Walk"
          "../Social_Choice_Types/Profile"
begin                                  

text \<open>Additional theorems for Graphs\<close>

type_synonym 'a Weight_Function = "'a set \<Rightarrow> 'a Profile \<Rightarrow> ('a*'a) \<Rightarrow> nat"

type_synonym 'a Margin_Graph = "('a, ('a\<times>'a)) pre_digraph"

subsection \<open>Finding Cycles\<close>

text\<open>
  The following two functions serve to find cycles in a graph
\<close>

fun path ::"'a Margin_Graph \<Rightarrow> ('a\<times>'a) awalk \<Rightarrow> bool" where
"path G [] = True" |
"path G [e] = (e\<in>(arcs G) \<and> head G e \<noteq> tail G e)" |
"path G (e # (f # es))= (e\<in>(arcs G) \<and> head G e \<noteq> tail G e \<and> (head G e) =
 (tail G f)\<and> path G (f#es))"

fun get_cyclical_walks::"'a Margin_Graph \<Rightarrow> ('a\<times>'a) awalk set" where
"get_cyclical_walks G = {walk.(path G walk)\<and>
 (length walk \<le> card(verts G) + 1) \<and> \<not>(distinct walk)}"

fun cycle_exists::"'a Margin_Graph \<Rightarrow> bool" where
"cycle_exists G = (get_cyclical_walks G  \<noteq> {})"

lemma first_in_arc:"path G (e # es) \<longrightarrow> e\<in>arcs G"
  using path.elims(2) by blast
 
lemma head_of_path_is_path: 
  assumes "path G (Cons a b)"
  shows "path G [a]"
proof -
  show ?thesis
    using assms
  proof -
    obtain bb :: "('a\<times>'a) list \<Rightarrow> ('a\<times>'a)" and bbs :: "('a\<times>'a) list \<Rightarrow> ('a\<times>'a) list" where
      "\<forall>bs. bs = bb bs # bbs bs \<or> bs = []"
      using list.exhaust
      by metis
    then show ?thesis
      using assms path.simps(2) path.simps(3)
      by metis
  qed    
qed

lemma tail_of_path_is_path:
  assumes "path G (e # es)"
  shows "path G es"
proof -
  show ?thesis
    using assms
  proof (cases "es = []")
    case True
    then have is_empty:"es = []" by metis
    have empty_good:"path G []"
      by simp
    thus "path G es" 
      using is_empty empty_good by metis
next
  case False
  then have "path G (e # es)" using assms by simp
  then show "path G es" 
    using path.simps(3) False path.elims(1)
    by auto
  qed
qed


lemma path_in_graph: 
  shows "path G walk \<longrightarrow> set walk \<subseteq> arcs G"
proof (induction walk)
  case Nil
  then show ?case by simp
next
  case (Cons a walk)
  assume IH1:"path G walk \<longrightarrow> set walk \<subseteq> arcs G"
  then show "path G (a#walk) \<longrightarrow> set (a#walk) \<subseteq> arcs G"
  proof -
    have "set walk \<subseteq> arcs G \<or> \<not> path G walk"
      using IH1
      by metis
    then show ?thesis
      using first_in_arc insert_subsetI list.simps(15) tail_of_path_is_path
      by (metis (full_types) )
  qed
qed

lemma path_prior_arc_exists:
  assumes "path G (e#es)"
  shows "\<forall>x \<in>set es. \<exists>y\<in>set(e#es). tail G x = head G y"
  using assms
proof (induction es arbitrary:e)
  case Nil
  then show ?case by simp
next
  case (Cons a es)  
  then have is_path:"path G (a#es)"   
    by simp
  then have "tail G a = head G e" 
    using Cons.prems path.elims(3)
    by simp
  then have IS:"\<exists>y \<in> set (e#a#es). tail G a = head G y" 
    by simp
  then have "\<forall>x\<in>set es. \<exists>y\<in>set (a # es). tail G x = head G y"
    using is_path Cons.IH
    by metis
  then have "\<forall>x\<in>set (a#es). \<exists>y\<in>set (e#a#es). tail G x = head G y"
    using IS
    by simp
  then show ?case by auto
qed
  
lemma no_in_arcs_only_head_of_path:
  assumes "in_arcs G c = {}"
  assumes "path G (e#es)"
  shows "(set (es) \<inter> out_arcs G c) = {}"
proof -
  have subset_es:"set es \<subseteq> set (e#es)"
    by auto
  have first_step:"set (e#es) \<inter> in_arcs G c = {}"
    using assms(1)
    by simp
  then have "\<nexists>a. a\<in>(set (e#es)) \<and> head G a = c"
    using assms(2) path_in_graph by fastforce
  then show ?thesis
    using assms(2) path_prior_arc_exists disjoint_iff_not_equal in_out_arcs_conv
    by metis
qed
    


lemma getCyclicalWalks_in_arcs:
 shows "\<forall> walk \<in> get_cyclical_walks G. set walk \<subseteq> arcs G"
proof (intro ballI)
fix walk
assume "walk \<in> get_cyclical_walks G"
  from this have "path G walk"
    by auto
  then show "set walk \<subseteq> arcs G" 
    using path_in_graph
    by metis
qed

lemma empty_graph_has_no_cycle:
  assumes "arcs G = {}"
  shows "cycle_exists G = False"
proof -
  have "get_cyclical_walks G = {}"
    proof (rule ccontr)
      assume "get_cyclical_walks G \<noteq> {}"
      then obtain w where w_cyclical:"w \<in> get_cyclical_walks G"
        by auto
      then have "path G w"
        by auto
      then have w_in_arcs: "set w \<subseteq> arcs G"
        using path_in_graph
        by metis
      have "distinct w = False"
        using w_cyclical
        by simp
      then have w_not_empty:"w \<noteq> []"
        by auto
      then show False 
        using assms w_in_arcs w_not_empty
        by simp
    qed
    then show ?thesis
      by simp
  qed

lemma less_arcs_less_paths:
  assumes "arcs H\<subseteq>arcs G""verts H=verts G""head H=head G""tail H=tail G""path H w"
  shows "path G w"
  using assms
proof (induction rule:path.induct)
  case (1 G)
  then show ?case by simp
next
  case (2 G e)
  then show ?case using path.simps(2) by auto
next
  case (3 G e f es)
  then show ?case using path.simps(3) by auto
qed

lemma less_arcs_less_cycles:
  assumes "arcs H\<subseteq>arcs G""verts H=verts G""head H=head G""tail H=tail G"
  shows "get_cyclical_walks H \<subseteq> get_cyclical_walks G"
proof (rule subsetI)
  fix x
  assume "x\<in>get_cyclical_walks H"
  then have x_def:"path H x \<and> (length x \<le> card(verts H) + 1) \<and> \<not>(distinct x)"
    by simp
  then have less_paths:" path G x" 
    using less_arcs_less_paths assms
    by metis
  have "card (verts H) = card (verts G)"
    using assms(2)
    by metis
  then have "(length x \<le> card(verts G) + 1)" using x_def by simp
  then have "path G x \<and> (length x \<le> card(verts G) + 1) \<and> \<not>(distinct x)"
    using less_paths x_def by simp
  then show "x\<in>get_cyclical_walks G" using get_cyclical_walks.simps by simp
qed

subsection \<open>Turning Cycles into simple cycles\<close>

text\<open>
  The following three functions serve to turn any cycle into a simple cycle
\<close>

fun distinct_fst::"('a\<times>'a) awalk \<Rightarrow> bool" where
"distinct_fst walk = distinct (map fst walk)"

fun distinct_snd::"('a\<times>'a) awalk \<Rightarrow> bool" where
"distinct_snd walk = distinct (map snd walk)"

fun trim::"('a\<times>'a) awalk \<Rightarrow> ('a\<times>'a) awalk" where
"trim [] = []" |
"trim (e # es) = (if (distinct_fst (es)) \<and> (distinct_snd (es))
  then (e#es) else trim es)"

fun trim_rev::"('a\<times>'a) awalk \<Rightarrow> ('a\<times>'a) awalk" where
"trim_rev [] = []" |
"trim_rev (e # es) = (if (distinct_fst (butlast (e#es))) \<and> (distinct_snd (butlast (e#es)))
  then (e#es) else trim_rev (butlast (e#es)))"

fun butfirst::"'a list \<Rightarrow> 'a list" where
"butfirst [] = []" |
"butfirst (e#es) = es"

fun trim_cyclical_path::"('a\<times>'a) awalk \<Rightarrow> ('a\<times>'a) awalk" where
"trim_cyclical_path [] = []" |
"trim_cyclical_path (e # es) = (if \<not>(distinct_fst(trim_rev(trim (e#es)))) 
then butlast (trim_rev(trim (e#es))) else butfirst(trim_rev(trim (e#es))))" 


lemma trim_subset: "set (trim (e#es)) \<subseteq> set (e#es)"
proof (cases "(distinct_fst (es)) \<and> (distinct_snd (es))")
  case True
  then show ?thesis by simp                                   
next
  case False
  then show ?thesis
  proof (induction rule:trim.induct)
    case 1
    then show ?case by simp
  next
    case (2 e es)
    then show ?case using False
      by auto
  qed
qed

lemma trim_rev_subset: "set (trim_rev (e#es)) \<subseteq> set (e#es)"
proof (cases "(distinct_fst (butlast (e#es))) \<and> (distinct_snd (butlast (e#es)))")
  case True
  then show ?thesis by simp  
next
  case False
  then show ?thesis
  proof (induction rule:rev_induct)
    case Nil
    then show ?case by simp
  next
    case (snoc e es)
    then have "trim_rev (es@ [e]) = trim_rev es"
      using snoc_eq_iff_butlast trim_rev.elims
      by (metis (no_types, opaque_lifting))   
    then show ?case using False snoc
      using set_append subset_trans sup.cobounded1 trim_rev.elims
      by (smt (verit, del_insts))    
  qed
qed

lemma distinct_arc_distinct_vert:
  assumes "distinct (e#es) = False"
  shows "distinct_fst ((e#es)) = False"
proof -
  have "distinct (map fst (e#es)) = False"
    using assms distinct_zipI1 zip_map_fst_snd 
    by metis
  then show ?thesis by simp
qed

lemma distinct_fst_sublist:
  assumes "distinct_fst (a@b@c)"
  shows "distinct_fst b"
proof -
  have "distinct (map fst (a@b@c))"
    using assms by simp
  have "distinct (map fst b)"
  proof (rule ccontr)
    assume assm:"\<not>(distinct (map fst b))"
    then have "\<exists>i j. i < length b \<and> j < length b \<and> fst(b!i) = fst (b!j) \<and> i \<noteq> j"
      using distinct_conv_nth by fastforce  
    then obtain i j where ij_def:"i < length b \<and> j < length b \<and> fst(b!i) = fst (b!j) \<and> i \<noteq> j"
      by metis
    then have "\<exists>k. ((a@b@c)!k) = b!i"
      using nth_append nth_append_length_plus
      by metis
    moreover have "\<exists>k. ((a@b@c)!k) = b!j"
      using nth_append nth_append_length_plus ij_def
      by metis
    ultimately have "\<exists>k1 k2. k1 < length (a@b@c) \<and> k2 < length (a@b@c) \<and>
      fst((a@b@c)!k1) = fst ((a@b@c)!k2) \<and> k1 \<noteq> k2"
      using ij_def append_eq_conv_conj nth_append_length_plus nth_take
      using \<open>distinct (map fst (a @ b @ c))\<close> assm 
      by fastforce      
    then have "\<not>(distinct_fst (a@b@c))"
      using distinct_fst.simps length_map nth_eq_iff_index_eq nth_map
      by (metis (mono_tags, lifting) ) 
    then show False using assms by simp
  qed
  then show ?thesis by simp
qed

lemma distinct_snd_sublist:
  assumes "distinct_snd (a@b@c)"
  shows "distinct_snd (a@c)"
proof -
  have "distinct (map snd (a@b@c))"
    using assms by simp
  have "distinct (map snd (a@c))"
  proof (rule ccontr)
    assume assm:"\<not>(distinct (map snd (a@c)))"
    then have "\<exists>i j. i < length (a@c) \<and> j < length (a@c) \<and> 
      snd((a@c)!i) = snd ((a@c)!j) \<and> i \<noteq> j"
      using distinct_conv_nth length_map nth_map
      by (metis (mono_tags, lifting) )
    then obtain i j where ij_def:"i < length (a@c) \<and> j < length (a@c) \<and> 
      snd((a@c)!i) = snd ((a@c)!j) \<and> i \<noteq> j"
      by metis
    then have "(if i < length a then (a@b@c)!i = (a@c)!i 
      else (a@c)!i = (a@b@c)!(i + length b))" 
      using add_diff_cancel_right add_less_cancel_right append.assoc length_append nth_append
      by (metis (no_types, lifting) )
    then obtain k1 where k1_define:"(if i < length a then k1 = i 
      else k1 = (i + length b)) \<and> (a@b@c)!k1 = (a@c)!i"
      by presburger
    then have "(if j < length a then (a@b@c)!j = (a@c)!j 
      else (a@c)!j = (a@b@c)!(j + length b))" 
      using add_diff_cancel_right add_less_cancel_right append.assoc 
        length_append nth_append
      by (metis (no_types, lifting) )
    then obtain k2 where k2_def:"(if j < length a then k2 = j 
      else k2 = (j + length b)) \<and> (a@b@c)!k2 = (a@c)!j"
      by presburger
    then have "k1 \<noteq> k2"
      using k1_define ij_def
      by (metis add_lessD1 add_right_cancel)
    moreover have "snd((a@b@c)!k2) = snd ((a@b@c)!k1)"
      using k1_define k2_def ij_def
      by simp
    moreover have "k1 < length (a@b@c) \<and> k2 < length (a@b@c)"
      using k1_define k2_def ij_def add.commute add.left_commute 
        length_append nat_add_left_cancel_less trans_less_add1
      by (smt (verit) )
    ultimately have "\<exists>k1 k2. k1\<noteq>k2 \<and> snd((a@b@c)!k2) = snd ((a@b@c)!k1)
      \<and> k1 < length (a@b@c) \<and> k2 < length (a@b@c)"
      by auto
    then have "\<not>(distinct_snd (a@b@c))"
      using distinct_snd.simps length_map nth_eq_iff_index_eq nth_map
      by (metis (full_types))       
    then show False using assms by simp
  qed
  then show ?thesis by simp
qed
      
      

lemma trim_nonempty: "p \<noteq> []\<Longrightarrow> trim p \<noteq> []"
proof (induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then show ?case
  proof (cases "(distinct_fst p) \<and> (distinct_snd p)")
    case True
    then show ?thesis by simp
  next
    case False
    then have "trim p \<noteq> []"
      using Cons.IH by fastforce
    then show ?thesis by simp
  qed
qed

lemma trim_rev_nonempty: "p \<noteq> []\<Longrightarrow> trim_rev p \<noteq> []"
proof (induction p rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc a p)
  then show ?case
  proof (cases "(distinct_fst (p)) \<and> (distinct_snd (p))")
    case True
    then have "trim_rev (p@[a]) = (p@[a])"
      using trim_rev.simps(2) butlast.simps  butlast_snoc trim_rev.elims
      by (smt (verit, ccfv_threshold))         
    then show ?thesis by simp
  next
    case False
    then have "trim_rev p \<noteq> []"
      using snoc.IH by fastforce
    moreover have "trim_rev (p@[a]) = trim_rev(p)"
      using False butlast_snoc trim_rev.elims snoc.prems
      by (smt (verit, best) )
    ultimately show ?thesis by simp
  qed
qed

lemma trim_preserves_last:
  "last x = last (trim x)"
proof (induction x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case 
  proof (cases "(distinct_fst x) \<and> (distinct_snd x)")
    case True
    then have "trim (a#x) = (a#x)"
      using trim.cases
      by simp
    then show ?thesis by simp
  next
    case False
    then have "trim (a#x) = trim x"
      using trim.cases
      by force
    then have "last (trim (a#x)) = last x"
      using Cons
      by simp
    then show ?thesis 
      using last_def
      by auto
  qed
qed

lemma trim_path_path:
  "path G x \<longrightarrow> path G (trim x)"
proof (induction x rule:trim.induct)
  case 1
  then show ?case by simp
next
  case (2 e es)
  then show ?case
  proof (cases "distinct_fst es \<and> distinct_snd es")
    case True
    then have "trim (e#es) = e#es"
      by simp
    then show ?thesis by simp
  next
    case False
    then have "trim (e#es) = trim es"
      by auto
    moreover have "path G (e#es) \<longrightarrow> path G es"
      using tail_of_path_is_path
      by metis
    ultimately show ?thesis using 2 False by simp
  qed 
qed

lemma trim_nearly_distinct:
  "(e#es) = trim x \<longrightarrow> (distinct_fst es) \<and>  (distinct_snd es)"
proof (induction x arbitrary:e es)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  then show ?case by simp
qed

lemma trim_rev_nearly_distinct:
  "(e#es) = trim_rev x \<longrightarrow> (distinct_fst (butlast (e#es))) 
    \<and>  (distinct_snd (butlast (e#es)))"
proof (induction x arbitrary:e es rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc e es)
  then show ?case
    using append_Nil2 butlast.simps(2) butlast_append list.distinct(1) trim_rev.elims
    by (smt (verit) )
qed

lemma trim_not_distinct:
  assumes "\<not>((distinct_fst z) \<and>  (distinct_snd z))"
  shows "\<not>((distinct_fst (trim z)) \<and> (distinct_snd (trim z)))"
  using assms
proof (induction z)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  show ?case
  proof (cases "(distinct_fst es) \<and> (distinct_snd es)" )
    case True
    then have "trim (e # es) = e # es" by simp
    moreover have "\<not>((distinct_fst (e#es)) \<and> (distinct_snd (e#es)))"
      using Cons.prems True by simp
    ultimately show ?thesis by simp
  next
    case False     
    then have "\<not>((distinct_fst (es)) \<and> (distinct_snd (es)))" 
      using False 
      by simp 
    then have "\<not>(distinct_fst (es)) \<or>
      \<not>(distinct_snd (es))"
      by metis
    then show ?thesis 
      using Cons
      by auto
  qed
qed

lemma trim_rev_not_distinct:
  assumes "\<not>((distinct_fst z) \<and>  (distinct_snd z))"
  shows "\<not>((distinct_fst (trim_rev z)) \<and> (distinct_snd (trim_rev z)))"
  using assms
proof (induction z rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc e es)
  show ?case
  proof (cases "(distinct_fst es) \<and> (distinct_snd es)" )
    case True
    then have "trim (e # es) = e # es" by simp
    moreover have "\<not>((distinct_fst (e#es)) \<and> (distinct_snd (e#es)))"
      using snoc.prems True by simp
    ultimately show ?thesis
      using True snoc.prems snoc_eq_iff_butlast trim_rev.elims
      by (metis (no_types, lifting) ) 
  next
    case False     
    then have "\<not>((distinct_fst (es)) \<and> (distinct_snd (es)))" 
      using False 
      by simp 
    then have "\<not>(distinct_fst (es)) \<or>
      \<not>(distinct_snd (es))"
      by metis
    then show ?thesis 
      using snoc butlast_snoc trim_rev.elims
      by (smt (verit, best))      
  qed
qed

lemma trim_rev_trim_near_distinct:
  assumes "\<not>((distinct_fst (z)) \<and>  (distinct_snd (z)))"
  assumes "(distinct_fst (butfirst(z))) \<and>  (distinct_snd (butfirst(z)))"
  shows "(distinct_fst (butfirst (trim_rev (z)))) 
    \<and> (distinct_snd (butfirst (trim_rev (z))))"
  using assms
proof (induction z rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc e es)
  then show ?case
  proof (cases "(distinct_fst es) \<and> (distinct_snd es)" )
    case True
    then have "\<not>((distinct_fst (e#es)) \<and> (distinct_snd (e#es)))"
      using snoc.prems True by simp
    then show ?thesis
      using True snoc.prems snoc_eq_iff_butlast trim_rev.elims
      by (metis (no_types, lifting) ) 
  next
    case False     
    then have "\<not>((distinct_fst (es)) \<and> (distinct_snd (es)))" 
      using False 
      by simp 
    then have "trim_rev (es@[e]) = trim_rev es"
      using snoc_eq_iff_butlast trim_rev.elims
      by (metis (mono_tags, lifting))
    then show ?thesis 
      using snoc False append_Nil append_Nil2 butfirst.simps(2) 
        distinct_fst_sublist distinct_snd_sublist hd_Cons_tl tl_append2
      by metis           
  qed
qed

lemma trim_cyc_subset: 
  assumes "\<not>(distinct_fst p \<and> distinct_snd p)"
  shows "set (trim_cyclical_path p) \<subseteq> set p"
proof -
  have initial:"set (trim_rev(trim p)) \<subseteq> set p"
    using trim_subset trim_rev_subset dual_order.trans subsetI
      trim.simps(1) trim_cyclical_path.cases trim_rev.simps(1)
    by (metis (no_types, opaque_lifting))    
  have p_not_empty: "p\<noteq>[]"
    using distinct_fst.simps distinct_snd.simps assms
    by auto
  then obtain e es where ees_def:"(e#es) = trim p"
    using trim_cyclical_path.cases trim_nonempty
    by metis
  then obtain f fs where ffs_def:"(f#fs) = trim_rev (trim p)"
    using trim_cyclical_path.cases  trim_rev_nonempty 
    by metis
  have "\<not>(distinct_fst (e#es) \<and> distinct_snd (e#es))"
    using trim_not_distinct assms ees_def 
    by metis
  then have near_distinct:"\<not>(distinct_fst (f#fs) \<and> distinct_snd (f#fs))"
    using ees_def ffs_def trim_rev_not_distinct
    by metis
  then show ?thesis 
  proof (cases "\<not>(distinct_fst (f#fs))")
    case True
    then have "trim_cyclical_path p = butlast (f#fs)"
      using trim_cyclical_path.elims ffs_def p_not_empty
      by metis    
    then show ?thesis 
      using initial ffs_def butlast.simps in_set_butlastD
      by fastforce
  next
    case False
    then have "\<not>(distinct_snd (f#fs))"
      using near_distinct
      by simp
    then have "trim_cyclical_path p = butfirst (f#fs)"
      using trim_cyclical_path.elims ffs_def p_not_empty False
      by metis       
    then show ?thesis 
      using initial ffs_def dual_order.trans set_subset_Cons butfirst.simps(2)
      by metis
  qed
qed 


    
lemma trim_cyc_distinct:
  assumes "distinct x = False"
  shows "distinct_fst (trim_cyclical_path x) \<and> 
    distinct_snd (trim_cyclical_path x)"
proof -
  obtain a ay where aay_def:"x = a#ay"
    using assms distinct.simps(1) list.exhaust
    by metis
  then obtain c cy where ccy_def:"c#cy = (trim (a#ay))"
    using trim_nonempty butfirst.elims
    by metis
  then obtain e ey where eey_def:"e#ey = trim_rev (c#cy)"
    using trim_rev_nonempty butfirst.elims
    by metis
  then show ?thesis
  proof (cases "distinct_fst(e#ey)")
    case True
    have "distinct_fst (butfirst (c#cy)) \<and> distinct_snd (butfirst (c#cy))"
      using aay_def ccy_def trim_nearly_distinct butfirst.simps(2)
      by metis
    moreover have "\<not>(distinct_fst (c#cy) \<and> distinct_snd (c#cy))"
      using ccy_def aay_def trim_not_distinct assms distinct_arc_distinct_vert
      by metis
    ultimately have "distinct_fst (butfirst (e#ey)) \<and> distinct_snd ((butfirst (e#ey)))"
      using eey_def ccy_def trim_rev_trim_near_distinct
      by metis
    moreover have "(trim_cyclical_path x) = butfirst (e#ey)"
      using trim_cyclical_path.simps eey_def ccy_def aay_def True
      by simp
    ultimately show ?thesis 
      by simp
  next
    case False
    then have "distinct_fst (butlast (e#ey)) \<and> distinct_snd ((butlast (e#ey)))"
      using eey_def trim_rev_nearly_distinct
      by metis
    moreover have "(trim_cyclical_path x) = butlast (e#ey)"
      using trim_cyclical_path.simps eey_def ccy_def aay_def False
      by simp
    ultimately show ?thesis 
      by simp
  qed
qed  

lemma trim_head_away:
  assumes "distinct (e#es) = False"
  assumes "A \<inter> set (es) = {}"
  assumes "e\<in>A"
  shows "A \<inter> set(trim_cyclical_path(e#es)) = {}"
proof -
  have "e\<notin>set es"
    using assms(2) assms(3)
    by auto
  then have "distinct es = False"
    using assms(1)
    by simp
  then have 1:"distinct_fst es = False"
    using distinct_arc_distinct_vert distinct.simps(1) trim.elims
    by metis   
  then have "trim (e#es) = trim (es)"
    by simp
  then have "set(trim(e#es))\<subseteq>set(es)"
    using trim_subset trim.elims trim_nonempty
    by (metis (full_types))
  then have subset: "set(trim_rev(trim(e#es)))\<subseteq>set es"
    using trim_rev_subset dual_order.trans trim_rev.elims
    by (metis (no_types, lifting))
  have "\<not>(distinct_fst(trim(e#es))\<and>distinct_snd(trim(e#es)))"
    using trim_not_distinct 1
    by auto
  then have "trim_cyclical_path(e#es) = butfirst (trim_rev(trim(e#es))) \<or>
    trim_cyclical_path(e#es) = butlast (trim_rev(trim(e#es)))"
    using trim_cyclical_path.simps(2)
    by metis
  moreover have notempty:"(trim(rev(trim(e#es)))) \<noteq> []"
    using Nil_is_rev_conv assms(1) distinct.simps(1) trim_nonempty
    by metis
  ultimately show ?thesis
    using Int_mono \<open>e \<notin> set es\<close> assms(1) assms(2) bot.extremum_uniqueI butfirst.elims distinct_arc_distinct_vert dual_order.eq_iff in_mono in_set_butlastD list.set_intros(2) list.simps(15) subset subset_insert_iff trim_cyc_subset
    by (smt (verit, ccfv_SIG))
qed

lemma no_in_arcs_no_head:
  assumes "in_arcs G c = {}"
  assumes "(e#es) \<in> get_cyclical_walks G"
  shows "out_arcs G c \<inter> set (trim_cyclical_path(e#es)) = {}"
proof -
  have non_distinct:"distinct (e#es) = False"
    using assms(2)
    by simp
  have "path G (e#es)"
    using assms(2)
    by simp
  then have tail_not_inter:" out_arcs G c \<inter> set (es) = {}"
    using no_in_arcs_only_head_of_path assms inf_commute
    by metis
  then show ?thesis 
  proof (cases "e\<in>out_arcs G c")
    case True
    then show ?thesis
      using trim_head_away assms(2) tail_not_inter non_distinct
      by metis
  next
    case False
    then have total_not_inter:"out_arcs G c \<inter> set (e#es) = {}"
      using tail_not_inter 
      by auto
    then show ?thesis 
    proof -
      have "set (trim_cyclical_path (e # es)) \<subseteq> set (e # es)"
        using trim_cyc_subset distinct_arc_distinct_vert non_distinct
        by blast
      then show ?thesis
        using total_not_inter
        by blast
    qed
  qed
qed  

subsection \<open>All Simple Cycles\<close>

definition all_simple_cycles::"('a, ('a\<times>'a)) pre_digraph \<Rightarrow> ('a\<times>'a) awalk set" where
"all_simple_cycles G =  trim_cyclical_path ` (get_cyclical_walks G)"

definition all_arcs_in_cycles::"('a, ('a\<times>'a)) pre_digraph \<Rightarrow> ('a\<times>'a) set" where
"all_arcs_in_cycles G = \<Union> (set ` (all_simple_cycles G))"

lemma cyc_arc_still_arc: "all_arcs_in_cycles G \<subseteq> arcs G"
proof -
  have "\<forall>x\<in>get_cyclical_walks G. \<not>distinct x"
    using get_cyclical_walks.simps
    by simp
  then have "\<forall>x\<in>get_cyclical_walks G. \<not>(distinct_fst x \<and> distinct_snd x)"
    using distinct.simps(1) distinct_arc_distinct_vert list.exhaust
    by metis 
  then have 1:"\<forall>x\<in>all_simple_cycles G. \<exists>y\<in>get_cyclical_walks G. set x \<subseteq> set y"
    using trim_cyc_subset all_simple_cycles_def image_iff
    by (metis (mono_tags, opaque_lifting))
  have 2:"\<forall>y\<in>get_cyclical_walks G. set y \<subseteq> arcs G"
    using getCyclicalWalks_in_arcs
    by metis
  then show ?thesis 
    using 1 all_arcs_in_cycles_def Union_least dual_order.trans image_iff
    by (smt (verit))
qed

lemma less_paths_less_cycles:
  assumes "get_cyclical_walks H \<subseteq> get_cyclical_walks G"
  shows "all_arcs_in_cycles H \<subseteq> all_arcs_in_cycles G"
  using all_arcs_in_cycles_def all_simple_cycles_def assms Union_mono image_mono
  by metis

lemma simple_cycle_distinct:
  assumes "x\<in>all_simple_cycles G"
  shows "distinct_fst x \<and> distinct_snd x"
proof -
  obtain w where w_def:"w\<in>get_cyclical_walks G \<and> trim_cyclical_path w = x"
    using assms all_simple_cycles_def image_iff
    by metis 
  then have "\<not>(distinct w)"
    by simp
  then show ?thesis
    using trim_cyc_distinct w_def assms
    by metis
qed


                                
text \<open>
  These currently don't get used in the implementation. 
  WARNING: Only call getsinglecycle if you know cycleexists G is true 
  otherwise an error will be thrown.
\<close>

fun get_single_cycle::"('a,('a*'a)) pre_digraph \<Rightarrow> ('a*'a) awalk" where
"get_single_cycle G = (SOME x. x \<in> get_cyclical_walks G)"

fun get_simple_cycle::"('a,('a*'a)) pre_digraph \<Rightarrow> ('a*'a) awalk" where
"get_simple_cycle G = trim_cyclical_path (get_single_cycle G)"

lemma simple_cycle_other_def:
  assumes "cycle_exists G"
  shows "get_simple_cycle G \<in> all_simple_cycles G"
proof - 
  have single_cycle_def:"(get_single_cycle G) \<in> get_cyclical_walks G"
    using assms cycle_exists.simps get_single_cycle.simps some_in_eq
    by metis
  have "get_simple_cycle G = trim_cyclical_path (get_single_cycle G)"
    by simp
  then show ?thesis
    using all_simple_cycles_def single_cycle_def
    by auto
qed

lemma simple_cycle_subset:
  assumes "cycle_exists G"
  shows"set(get_simple_cycle G) \<subseteq> all_arcs_in_cycles G"
proof -
  have "get_simple_cycle G \<in> all_simple_cycles G"
    using assms simple_cycle_other_def
    by metis
  then show ?thesis
    using all_arcs_in_cycles_def Union_upper rev_image_eqI
    by metis
qed




lemma single_cycle_non_distinct:
  assumes "cycle_exists G"
  shows "distinct (get_single_cycle G) = False"
proof -
  have not_empty:"get_cyclical_walks G \<noteq> {}"
    using assms
    by simp
  then have single_cycle_in_cycles:"(get_single_cycle G)\<in>(get_cyclical_walks G)"
    using some_in_eq get_single_cycle.simps
    by metis
  have "\<forall>x\<in>(get_cyclical_walks G). distinct x = False"
    by simp
  then show "distinct (get_single_cycle G) = False"
    using single_cycle_in_cycles 
    by simp 
qed

lemma single_cycle_non_empty:
  assumes cycle:"cycle_exists G"
  shows "(get_single_cycle G) \<noteq> []"
proof -
  have not_empty:"get_cyclical_walks G \<noteq> {}"
    using cycle
    by simp
  then have single_cycle_in_cycles:"(get_single_cycle G)\<in>(get_cyclical_walks G)"
    using some_in_eq get_single_cycle.simps
    by metis
  then have "distinct (get_single_cycle G) = False"
    by simp
  then show "(get_single_cycle G) \<noteq> []"
    by auto
qed


lemma single_cycle_in_arcs:
  assumes cycle:"cycle_exists G"
  shows "set (get_single_cycle G) \<subseteq> arcs G"
proof -
  have not_empty:"get_cyclical_walks G \<noteq> {}"
    using cycle
    by auto
  have single_cycle_in_cycles:"(get_single_cycle G)\<in>(get_cyclical_walks G)"
    using get_single_cycle.simps not_empty some_in_eq
    by metis
  then have "path G (get_single_cycle G)"
    by simp
  then show "set (get_single_cycle G) \<subseteq> arcs G"
    using path_in_graph
    by metis
qed


lemma get_simple_cycle_in_arcs:
assumes cycle:"cycle_exists G"
shows "set (get_simple_cycle G) \<subseteq> arcs G"
proof (rule subsetI)
  fix x
  assume x_in_cycle:"x \<in> set (get_simple_cycle G)"
  have "\<forall>x\<in>get_cyclical_walks G. \<not>distinct x"
    using get_cyclical_walks.simps
    by simp
  then have "\<forall>x\<in>get_cyclical_walks G. \<not>(distinct_fst x \<and>distinct_snd x)"
    using distinct_arc_distinct_vert distinct.simps(1) list.exhaust
    by metis
  have simple_in_single:"set (get_simple_cycle G) \<subseteq> set (get_single_cycle G)"
    using trim_cyc_subset cycle distinct_arc_distinct_vert get_simple_cycle.simps 
      single_cycle_non_distinct single_cycle_non_empty trim_cyclical_path.cases
    by metis     
  then have single_in_arcs:"set (get_single_cycle G) \<subseteq> arcs G"
    using single_cycle_in_arcs cycle
    by simp
  then have x_in_arcs: "x \<in> arcs G"
    using single_in_arcs x_in_cycle simple_in_single 
    by auto
  show "x \<in> arcs G"
    by (rule x_in_arcs)
qed


lemma condorcet_not_in_cycle:
  assumes "in_arcs G c = {}"
  assumes "cycle_exists G"
  shows "(all_arcs_in_cycles G) \<inter> out_arcs G c = {}"
proof -
  have "\<forall>x\<in>all_simple_cycles G. \<exists>y\<in>get_cyclical_walks G. x=trim_cyclical_path y"
    using  all_simple_cycles_def image_iff
    by metis
  then have "\<forall>x\<in>all_simple_cycles G. \<exists>y\<in>get_cyclical_walks G. 
    (x=trim_cyclical_path y) \<and> path G y"
    using get_cyclical_walks.simps
    by simp
  then have "\<forall>x\<in>all_simple_cycles G. set x \<inter> out_arcs G c = {}"
    using  no_in_arcs_no_head assms empty_set inf_bot_right subset_empty
    inf_commute path.elims(2) trim_cyc_subset trim_cyclical_path.elims
    by (smt (verit))
  then show ?thesis
    using all_arcs_in_cycles_def Union_disjoint image_iff
    by (smt (verit, best))
qed





end