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
"legitPath G [] = False" |
"legitPath G [e] = (e\<in>(arcs G) \<and> head G e \<noteq> tail G e)" |
"legitPath G (e # (f # es))= (e\<in>(arcs G) \<and> head G e \<noteq> tail G e \<and> (head G e) =
 (tail G f)\<and> legitPath G (f#es))"

fun getCyclicalWalks::"('a, 'b) pre_digraph \<Rightarrow> 'b awalk set" where
"getCyclicalWalks G = {walk.(legitPath G walk)\<and> (length walk \<le> card(verts G) + 1) \<and> \<not>(distinct walk)}"


fun cycleExists::"('a, 'b) Cycle_Detector" where
"cycleExists G = (getCyclicalWalks G  \<noteq> {})"

lemma "legitPath G [a] \<longrightarrow> a \<in> arcs G"
  by auto

lemma first_in_arc[simp]:"legitPath G (e # es) \<longrightarrow> e\<in>arcs G"
  using legitPath.elims(2) by blast
  

lemma head_of_legit_path_legit[simp]: 
  assumes isLegit:"legitPath G (Cons a b)"
  shows "legitPath G [a]"
proof -
  show ?thesis
    using isLegit
  proof -
    obtain bb :: "'b list \<Rightarrow> 'b" and bbs :: "'b list \<Rightarrow> 'b list" where
      "\<forall>bs. bs = bb bs # bbs bs \<or> bs = []"
      by (metis list.exhaust)
    then show ?thesis
      by (metis isLegit legitPath.simps(2) legitPath.simps(3))
  qed    
qed

lemma legitPathInGraph[simp]: 
  fixes walk::"'b awalk"
  assumes isLegit:"legitPath G walk"
  shows "set walk \<subseteq> arcs G"
proof (induction walk rule: legitPath.induct)
  case (1 G)
  then show ?case sorry
next
  case (2 G e)
  then show ?case sorry
next
  case (3 G e f es)
  then show ?case sorry
qed

lemma getCyclicalWalks_in_arcs[simp]:
 fixes  G :: "('a, 'b) pre_digraph"
 shows "\<forall> walk \<in> getCyclicalWalks G. set walk \<subseteq> arcs G"
proof (intro ballI)
fix walk
assume "walk \<in> getCyclicalWalks G"
  from this have legit:"legitPath G walk"
    by auto
  show "set walk \<subseteq> arcs G" 
    using legit 
    by simp
qed

lemma[simp]: "legitPath \<lparr>verts = v, arcs = {}, tail = t, head = h\<rparr> x = False"
  using legitPath.elims(1) by force

lemma no_arcs_no_cycle[simp]: "cycleExists \<lparr> verts = v, arcs = {},tail = t, head = h\<rparr> = False"
  by simp


end


