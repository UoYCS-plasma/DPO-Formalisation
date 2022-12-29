theory Rule
  imports Morphism
begin

locale rule =
  k: inclusion_morphism K L +
  r: inclusion_morphism K R 
  for L K R
begin

lemma k_subset_l:
  \<open>V\<^bsub>K\<^esub> \<subseteq> V\<^bsub>L\<^esub>\<close> and \<open>E\<^bsub>K\<^esub> \<subseteq> E\<^bsub>L\<^esub>\<close>
  by (simp_all add: subset_iff)

lemma k_subset_r:
  \<open>V\<^bsub>K\<^esub> \<subseteq> V\<^bsub>R\<^esub>\<close> and \<open>E\<^bsub>K\<^esub> \<subseteq> E\<^bsub>R\<^esub>\<close>
  by auto  
end

notation rule ("_\<leftarrow>_\<rightarrow>_")

end