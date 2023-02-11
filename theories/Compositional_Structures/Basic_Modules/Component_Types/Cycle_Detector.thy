section \<open>Cycle_Detector\<close>

theory Cycle_Detector
  imports "Graph_Theory.Digraph" 
          "Graph_Theory.Arc_Walk" 
          "Social_Choice_Types/Profile"
begin

text\<open>
\<close>

type_synonym ('a, 'b) Cycle_Detector = "('a, 'b) pre_digraph \<Rightarrow> bool"


fun legitPath ::"('a, 'b) pre_digraph \<Rightarrow> 'b awalk \<Rightarrow> bool" where
"legitPath G [] = True" |
"legitPath G [e] = (e\<in>(arcs G) \<and> head G e \<noteq> tail G e)" |
"legitPath G (e # (f # es))= (e\<in>(arcs G) \<and> head G e \<noteq> tail G e \<and> (head G e) =
 (tail G f)\<and> legitPath G (f#es))"

fun getCyclicalWalks::"('a, 'b) pre_digraph \<Rightarrow> 'b awalk set" where
"getCyclicalWalks G = {walk.(legitPath G walk)\<and> (length walk \<le> card(verts G) + 1) \<and> \<not>(distinct walk)}"


fun cycleExists::"('a, 'b) Cycle_Detector" where
"cycleExists G = (getCyclicalWalks G  \<noteq> {})"


lemma first_in_arc:"legitPath G (e # es) \<longrightarrow> e\<in>arcs G"
  using legitPath.elims(2) by blast
 

lemma head_of_legit_path_legit: 
  assumes isLegit:"legitPath G (Cons a b)"
  shows "legitPath G [a]"
proof -
  show ?thesis
    using isLegit
  proof -
    obtain bb :: "'b list \<Rightarrow> 'b" and bbs :: "'b list \<Rightarrow> 'b list" where
      "\<forall>bs. bs = bb bs # bbs bs \<or> bs = []"
      using list.exhaust
      by metis
    then show ?thesis
      using isLegit legitPath.simps(2) legitPath.simps(3)
      by metis
  qed    
qed

lemma tail_of_legit_path_legit:
  assumes isLegit:"legitPath G (e # es)"
  shows "legitPath G es"
proof -
  show ?thesis
    using isLegit
  proof (cases "es = []")
    case True
    then have is_empty:"es = []" by metis
    have empty_good:"legitPath G []"
      by simp
    thus "legitPath G es" 
      using is_empty empty_good by metis
next
  case False
  then have isLegitTail: "legitPath G (e #  es)" using isLegit by simp
  then show "legitPath G es" 
    using legitPath.simps(3) False legitPath.elims(1)
    by auto
  qed
qed

lemma legitPathInGraph: 
  shows "legitPath G walk \<longrightarrow> set walk \<subseteq> arcs G"
proof (induction walk)
  case Nil
  then show ?case by simp
next
  case (Cons a walk)
  assume IH1:"legitPath G walk \<longrightarrow> set walk \<subseteq> arcs G"
  then show "legitPath G (a#walk) \<longrightarrow> set (a#walk) \<subseteq> arcs G"
  proof -
    have "set walk \<subseteq> arcs G \<or> \<not> legitPath G walk"
      using IH1
      by metis
    then show ?thesis
      by (metis (full_types) first_in_arc insert_subsetI list.simps(15) tail_of_legit_path_legit)
  qed
    
qed

lemma getCyclicalWalks_in_arcs:
 fixes  G :: "('a, 'b) pre_digraph"
 shows "\<forall> walk \<in> getCyclicalWalks G. set walk \<subseteq> arcs G"
proof (intro ballI)
fix walk
assume "walk \<in> getCyclicalWalks G"
  from this have legit:"legitPath G walk"
    by auto
  show "set walk \<subseteq> arcs G" 
    using legit legitPathInGraph
    by metis
qed


end


