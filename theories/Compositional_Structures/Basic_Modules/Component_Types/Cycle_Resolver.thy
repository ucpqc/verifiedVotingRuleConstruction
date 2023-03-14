section \<open>Cycle_Resolver\<close>

theory Cycle_Resolver
  imports
          "Graph_Theory/Cycle_Helper"
begin

text\<open>
\<close>

type_synonym 'a Cycle_Resolver = 
"'a Margin_Graph \<Rightarrow> 'a Weight_Function \<Rightarrow> 'a Profile \<Rightarrow>'a Margin_Graph"

subsection \<open>Finding the arc with the smallest weight in a cycle\<close>

text\<open>
  This function serves to find the elements in a list with minimum weight
\<close>
(*
function testmin :: "nat set \<Rightarrow> nat list \<Rightarrow> nat set" where
"testmin a [] = a" |
"testmin {} (x#xs) = testmin {x} xs" |
"testmin a (x#xs) = (if (x < (SOME y. y\<in> a)) then testmin {x} xs
   else (if (x = (SOME y. y\<in> a)) then testmin (a \<union> {x}) xs else testmin a xs))"
  apply (metis list_encode.cases old.prod.exhaust)
  apply simp
  apply simp
apply simp
apply simp
  apply simp
   *)


fun min_help :: "('a*'a) list \<Rightarrow>'a Weight_Function \<Rightarrow> 'a set 
  \<Rightarrow> 'a Profile  \<Rightarrow> ('a*'a) list \<Rightarrow> ('a*'a) set" where
"min_help list f c p [] = {}" |
"min_help list f c p (x#xs)= (if (\<forall> y \<in> set list. f c p x \<le> f c p y) then {x} 
else {}) \<union> min_help list f c p xs"

fun min_elems ::  "'a Weight_Function \<Rightarrow> 'a set 
  \<Rightarrow> 'a Profile  \<Rightarrow> ('a*'a) list \<Rightarrow> ('a*'a) set" where
"min_elems f c p l = min_help l f c p l"

lemma min_help_gives_min:
  shows "\<forall>y\<in>set list. x\<in>min_help list f c p (cyc) \<longrightarrow> f c p x \<le> f c p y"
proof (induction rule: min_help.induct)
  case (1 list f c p)
  then show ?case by simp
next
  case (2 list f c p a as)
  then show ?case 
  proof (cases "x=a")
    case True
    then have x_def:"x=a"
      by simp   
    then show ?thesis
    proof (cases "\<forall> y \<in> set list. f c p a \<le> f c p y")
      case True
      then have "min_help list f c p (a#as) = {a} \<union> min_help list f c p as"
        by simp
      then show ?thesis
        using True x_def
        by metis
    next
      case False
      then have "min_help list f c p (a#as) = min_help list f c p as"
        by auto
      moreover have "x \<notin> min_help list f c p as"
        using 2 x_def False
        by simp
      ultimately have "x \<notin> min_help list f c p (a#as)"
        by simp
      then show ?thesis
        by simp
    qed      
  next
    case False
    then have "min_help list f c p (as) \<subseteq> min_help list f c p (a#as)"
      by simp
    then show ?thesis
      using 2
      by simp
  qed
qed


lemma min_help_in_set:
 "(min_help list f c p cyc) \<subseteq> set cyc"
  proof (induction cyc )
    case Nil
    then show ?case by simp
  next
    case (Cons a as)
    then show ?case 
    proof (cases "\<forall> y \<in> set list. f c p a \<le> f c p y")
      case True
      then have "min_help list f c p (a#as) = {a} \<union> (min_help list f c p as)"
        by simp
      then show ?thesis
        using Cons
        by auto
    next
      case False
      then have "min_help list f c p (a#as) = (min_help list f c p as)"
        by auto
      then show ?thesis using Cons
        by auto
    qed
  qed
    
lemma min_elems_in_set:
  "(min_elems f c p cyc) \<subseteq> set cyc"
proof -
  have "min_elems f c p cyc = min_help cyc f c p cyc"
    by simp
  then show ?thesis
    using min_help_in_set
    by simp
qed

lemma min_elems_give_min:
  "\<forall>y\<in>set cyc. x\<in>min_elems f c p (cyc) \<longrightarrow> f c p x \<le> f c p y"
proof -
  have "min_elems f c p cyc = min_help cyc f c p cyc"
    by simp
  then show ?thesis
    using min_help_gives_min
    by simp
qed

lemma min_in_min_help:
  assumes "\<forall>y\<in>set list. f c p x \<le> f c p y"
  shows "x\<in>set cyc\<longrightarrow>x\<in>min_help list f c p cyc"
proof (induction cyc)
  case Nil
  then show ?case by simp
next
  case (Cons a cyc)
  assume IH:"x\<in>set cyc \<longrightarrow> x\<in>min_help list f c p cyc"
  have 1:"x\<in>set (a#cyc)\<longrightarrow>x\<in>min_help list f c p (a#cyc)"
  proof (cases "x\<in>set (a#cyc)")
    case True
    then have x_in_set:"x\<in>set (a#cyc)"
      by simp
    then show ?thesis 
    proof (cases "x=a")
      case True
      then have "min_help list f c p (a#cyc) = {a} \<union> min_help list f c p (cyc)"
        using assms
        by simp 
      then show ?thesis sorry
    next
      case False
      then show ?thesis 
        using x_in_set IH
        by simp
    qed
  next
    case False
    then show ?thesis by simp
  qed

  have 2:"x\<in>min_help list f c p cyc \<longrightarrow> x\<in>min_help list f c p (a#cyc)"
  proof (cases "\<forall> y \<in> set list. f c p a \<le> f c p y")
    case True
    then have "min_help list f c p (a#cyc) = {a} \<union> min_help list f c p cyc"
      by simp
    then show ?thesis
      by simp
  next
    case False
    then have "min_help list f c p (a#cyc) = min_help list f c p cyc"
      by auto
    then show ?thesis 
      by simp
  qed
  
  show " x\<in>set (a#cyc) \<longrightarrow> x\<in>min_help list f c p (a#cyc)"
  
  
qed

lemma smallest_arcs_in_graph:
  assumes "cycle_exists G"
  shows "min_elems f c p (get_simple_cycle G) \<subseteq> arcs G"
proof
  fix x
  assume "x \<in> min_elems f c p (get_simple_cycle G)"
  then have "x \<in> set (get_simple_cycle G)" using 
    min_elems_in_set by blast
  then show "x \<in> arcs G" using assms get_simple_cycle_in_arcs by blast
qed

definition min_arcs::"'a Margin_Graph \<Rightarrow> 'a Weight_Function \<Rightarrow> 'a set 
\<Rightarrow> 'a Profile \<Rightarrow> ('a*'a) set" where
"min_arcs G f c p = \<Union> (min_elems f c p ` (all_simple_cycles G))"

lemma min_arcs_in_cyc_arcs:"min_arcs G f c p \<subseteq> all_arcs_in_cycles G"
proof -
  show ?thesis
  using min_elems_in_set all_arcs_in_cycles_def Sup_mono image_iff min_arcs_def
  by (smt (verit))  
qed

lemma no_cycle_no_min_arcs:
  assumes "cycle_exists G = False"
  shows "min_arcs G f c p = {}"
proof -
  have "get_cyclical_walks G = {}"
    using assms
    by simp
  then have "all_simple_cycles G = {}"
    using all_simple_cycles_def
    by blast
  then show ?thesis
    using min_arcs_def
    by blast
qed
  
fun resolve_all_cycles::"'a Cycle_Resolver" where
"resolve_all_cycles G f p = \<lparr>verts = verts G, 
  arcs = arcs G - min_arcs G f (verts G) p,
  tail = tail G,  head = head G\<rparr>"


lemma resolve_cycle_preserves_verts:
  shows "verts (resolve_all_cycles G f p) = verts G"
  by simp

lemma arcs_subset:
shows "arcs (resolve_all_cycles G f p) \<subseteq> arcs G"
  by simp

lemma resolve_all_cycles_preserves_tail: 
"tail (resolve_all_cycles G f p) = tail G"
  by simp

lemma resolve_all_cycles_preserves_head: 
"head (resolve_all_cycles G f p) = head G"
  by simp

lemma resolve_all_cycles_preserves_non_cycle_arcs:
  "arcs G - arcs (resolve_all_cycles G f p) \<subseteq>  (all_arcs_in_cycles G)"
proof -
  show ?thesis
    using min_arcs_in_cyc_arcs resolve_all_cycles.simps 
    by fastforce 
qed


lemma resolving_in_arcs_empty: 
  assumes "in_arcs G x = {}"
  shows "in_arcs (resolve_all_cycles G f p) x = {}"
proof -
  have start:"{e \<in> arcs G. head G e = x} = {}"
    using assms in_arcs_def
    by metis
  have "arcs (resolve_all_cycles G f p) \<subseteq> arcs G"
    using arcs_subset
    by metis
  then have "{e \<in> arcs (resolve_all_cycles G f p). head (resolve_all_cycles G f p) e = x} = {}"
    using assms start resolve_all_cycles_preserves_head Collect_empty_eq subset_iff
 Collect_empty_eq \<open>arcs (resolve_all_cycles G f p) \<subseteq> arcs G\<close> resolve_all_cycles_preserves_head start subset_iff
    by (smt (verit))    
  then show ?thesis
    using in_arcs_def
    by (metis (no_types))
qed
    

end
