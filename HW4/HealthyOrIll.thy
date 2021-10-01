theory HealthyOrIll
  imports Main
begin
  text\<open> Apply style \<close>
lemma l_1: "(healthy \<or> ill) \<and> (healthy \<longrightarrow> travel) \<and> \<not>ill \<longrightarrow> travel"
  apply (rule impI)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule conjE)
   apply (erule impE)
    apply assumption
   apply assumption
  apply (erule conjE)
  apply (erule notE)
  apply assumption
  done   
end