theory AuxLemmas
  imports Main
begin


lemma case_sum_ran_childs:
  assumes "ran f \<subseteq> A" and "ran g \<subseteq> A"
  shows "ran (case_sum f g) \<subseteq> A"
proof -
  have \<open>case_sum f g x = Some y \<longrightarrow> y \<in> A\<close> for x and y
    by (metis assms old.sum.simps(5) old.sum.simps(6) ranI subset_iff sumE)
  thus ?thesis
    unfolding ran_def
    by blast 
qed

lemma ex_eq:
  shows "\<exists>!x. P x \<Longrightarrow> P y \<Longrightarrow> P z \<Longrightarrow> y = z"
  by blast

lemma map_comp_assoc:
  shows "(a \<circ>\<^sub>m b) \<circ>\<^sub>m c = a \<circ>\<^sub>m (b \<circ>\<^sub>m c)"
  unfolding map_comp_def
  by (metis option.case_eq_if)

end