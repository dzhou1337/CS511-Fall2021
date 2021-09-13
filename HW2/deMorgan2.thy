theory deMorgan2
  imports Main
begin
  text\<open> Apply style \<close>
   lemma lem_k_1 : " (\<not>p \<and> \<not>q)\<longrightarrow> \<not>(p \<or> q)"
    apply (rule impI)
     apply (erule conjE)
     apply (rule notI)
     apply (erule notE)
     apply (erule disjE)
      apply assumption
     apply (erule notE)
     apply assumption
    done

end