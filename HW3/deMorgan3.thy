theory deMorgan3
  imports Main
begin
  text\<open> Apply style \<close>
lemma lem_k_1 : " (\<not>p \<or> \<not>q)\<longrightarrow> \<not>(p \<and> q)"
    apply (rule impI)
  apply (erule disjE)
   apply (rule notI)
  apply (erule notE)
   apply (erule conjE)
   apply assumption
  apply (rule notI)
  apply (erule conjE)
  apply (erule notE)
  apply assumption
  done 
end