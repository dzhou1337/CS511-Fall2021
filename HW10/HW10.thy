text\<open> 12 November 2021: Exercises for Homework 10 in CS 511 \<close> 
text\<open> Your task to remove the invocations of the pre-defined method 
      'blast' by an equivalent sequence of 'apply' steps \<close>

theory HW10
  imports Main
begin

text\<open> 'blast' is invoked four times, once in the proof of each of
      lemmas E1, F1, G1, and H1 below \<close>

(* lemma E1 is the same in Exercise 2.3.9 (e), page 161, in [LCS] *)
lemma E1 : "\<forall> x. (P x \<or> Q x) \<Longrightarrow> (\<forall> x. P x) \<or> (\<exists> x. Q x)" 
  apply (rule disjCI)
  apply (rule allI)
  apply (erule_tac x="x" in allE)
  apply (erule disjE)
   apply assumption
  apply (erule notE)
  apply (rule exI)
  apply assumption  
  done

(* lemma F1 is the same in Exercise 2.3.9 (f), page 161, in [LCS] *)
lemma F1 : "\<forall> x. \<exists> y. (P x \<or> Q y) \<Longrightarrow> \<exists> y. \<forall> x. (P x \<or> Q y)" 
  apply (rule classical)
  apply (rule_tac x="z" in exI)
  apply (rule allI)
  apply (rule disjCI)
  apply (erule_tac x="x" in allE)
  apply (erule exE)
  apply (erule disjE)
   apply assumption
  apply (erule notE)
  by auto
  

(* lemma G1 is the same in Exercise 2.3.9 (g), page 161, in [LCS] *)
lemma G1 : "\<forall> x. (\<not> P x \<and> Q x) \<Longrightarrow> (\<forall> x. P x \<longrightarrow> Q x)" 
  apply (rule allI)
  apply (rule impI)
  apply (erule_tac x="x" in allE)
  apply (erule conjE)
  apply assumption
  done 


(* lemma H1 is the same in Exercise 2.3.9 (h), page 161, in [LCS] *)
lemma H1 : "\<forall> x. (P x \<and> Q x) \<Longrightarrow> (\<forall> x. P x \<longrightarrow> Q x)" 
  apply (rule allI)
  apply (rule impI)
  apply (erule_tac x="x" in allE)
  apply (erule conjE)
  apply assumption
  done 

end