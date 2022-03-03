theory Deletion 
  imports Pushout Morphism
begin

section "Deletion"

text_raw \<open>
\begin{figure}[!htb]
  \centering
  \includegraphics{figs/fig-pushout-deletion.pdf}
  \caption{Deletion Pushout}
\end{figure}
\<close>

locale deletion =
  L: graph V\<^sub>L E\<^sub>L s\<^sub>L s'\<^sub>L t\<^sub>L t'\<^sub>L l\<^sub>L l'\<^sub>L m\<^sub>L m'\<^sub>L +
  K: graph V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K +
  G: graph V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G +

  i: inclusion_morphism 
    V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K
    V\<^sub>L E\<^sub>L s\<^sub>L s'\<^sub>L t\<^sub>L t'\<^sub>L l\<^sub>L l'\<^sub>L m\<^sub>L m'\<^sub>L 
    k\<^sub>V k'\<^sub>V k\<^sub>E k'\<^sub>E +

  m: injective_morphism
    V\<^sub>L E\<^sub>L s\<^sub>L s'\<^sub>L t\<^sub>L t'\<^sub>L l\<^sub>L l'\<^sub>L m\<^sub>L m'\<^sub>L 
    V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G
    f\<^sub>V f'\<^sub>V f\<^sub>E f'\<^sub>E
  for
    V\<^sub>L E\<^sub>L s\<^sub>L s'\<^sub>L t\<^sub>L t'\<^sub>L l\<^sub>L l'\<^sub>L m\<^sub>L m'\<^sub>L
    V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K  
    V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G
    k\<^sub>V k'\<^sub>V k\<^sub>E k'\<^sub>E
    f\<^sub>V f'\<^sub>V f\<^sub>E f'\<^sub>E +
  assumes
    dang: \<open>e \<in> E\<^sub>G - f'\<^sub>E ` E\<^sub>L \<Longrightarrow> s'\<^sub>G e \<notin> f'\<^sub>V ` (V\<^sub>L-V\<^sub>K) \<and> t'\<^sub>G e \<notin> f'\<^sub>V ` (V\<^sub>L-V\<^sub>K)\<close>
begin

abbreviation V where
"V \<equiv> V\<^sub>G - f'\<^sub>V ` (V\<^sub>L-V\<^sub>K)"

lemma k_subset_v:
  shows \<open>f'\<^sub>V ` V\<^sub>K \<subseteq> V\<close>
  by (smt (verit, del_insts) Diff_iff i.v_inclusion_alt image_iff inj_on_image_set_diff m.integrity_v' m.node_injectivity subsetI)

abbreviation E where
"E \<equiv> E\<^sub>G - f'\<^sub>E ` (E\<^sub>L-E\<^sub>K)"

lemma k_subset_e:
  shows \<open>f'\<^sub>E ` E\<^sub>K \<subseteq> E\<close>
  by (smt (verit, del_insts) Diff_iff Diff_subset i.e_inclusion_alt i.subset_edges image_subset_iff inj_on_image_set_diff m.edge_injectivity m.integrity_e' subset_refl)


abbreviation s where
"s \<equiv> s\<^sub>G |` E"

lemma dom_s:
  shows \<open>dom s = E\<close>
  using G.integrity_s by force

lemma ran_s:
  shows \<open>ran s \<subseteq> V\<close>
  by (smt (verit, ccfv_threshold) DiffD2 DiffI Diff_subset G.integrity_s_alt G.s_def K.integrity_s' dang i.s_equality_alt i.s_inclusion image_iff k_subset_v m.source_preserve_alt mem_Collect_eq option.sel option.simps(3) ran_def restrict_map_def subset_iff)

abbreviation t where
"t \<equiv> t\<^sub>G |` E"

lemma dom_t:
  shows \<open>dom t = E\<close>
  using G.integrity_t by force

lemma ran_t:
  shows \<open>ran t \<subseteq> V\<close>
  by (smt (verit, ccfv_threshold) DiffD2 DiffI Diff_subset G.integrity_t_alt G.t_def K.integrity_t' dang i.t_equality_alt i.t_inclusion image_iff k_subset_v m.target_preserve_alt mem_Collect_eq option.sel option.simps(3) ran_def restrict_map_def subset_eq)


abbreviation l where
"l \<equiv> l\<^sub>G |` V"

lemma dom_l:
  shows \<open>dom l = V\<close>
  using G.integrity_l by auto

abbreviation m where
"m \<equiv> m\<^sub>G |` E"

lemma dom_m:
  shows \<open>dom m = E\<close>
  using G.integrity_m by auto


interpretation object: graph V E s "totalize s" t "totalize t" l "totalize l" m "totalize m"
proof unfold_locales
  show \<open>finite V\<close>
    using G.finite_nodes by blast
next
  show \<open>finite E\<close>
    using G.finite_edges by blast
next
  show \<open>dom s = E \<and> ran s \<subseteq> V\<close>
  proof
    show \<open>dom s = E\<close>
      using G.integrity_s by auto
  next
    show \<open>ran s \<subseteq> V\<close>
      using ran_s by blast
  qed
next
  show \<open>dom t = E \<and> ran t \<subseteq> V\<close>
  proof
    show \<open>dom t = E\<close>
      using dom_t by blast
  next
    show \<open>ran t \<subseteq> V\<close>
      using ran_t by blast
  qed
next
  show \<open>dom l = V\<close>
    using dom_l by blast
next
  show \<open>dom m = E\<close>
    using dom_m by blast
qed simp_all


definition d\<^sub>V where
"d\<^sub>V \<equiv> f\<^sub>V |` V\<^sub>K"

lemma dom_d\<^sub>V:
  shows \<open>dom d\<^sub>V = V\<^sub>K\<close>
  unfolding d\<^sub>V_def
  using i.subset_nodes m.dom_gv by auto

lemma ran_d\<^sub>V:
  shows \<open>ran d\<^sub>V \<subseteq> V\<close>
  unfolding d\<^sub>V_def
  by (smt (verit, ccfv_SIG) i.subset_nodes imageE inj_on_def m.g\<^sub>V_def m.integrity_v_alt m.node_injectivity mem_Collect_eq option.sel option.simps(3) ran_def restrict_map_def set_diff_eq subset_iff)


definition d\<^sub>E where
"d\<^sub>E \<equiv> f\<^sub>E |` E\<^sub>K"

lemma dom_d\<^sub>E:
  shows \<open>dom d\<^sub>E = E\<^sub>K\<close>
  unfolding d\<^sub>E_def
  using i.subset_edges m.dom_ge by auto

lemma ran_d\<^sub>E:
  shows \<open>ran d\<^sub>E \<subseteq> E\<close>
  unfolding d\<^sub>E_def
  using k_subset_e ran_restrictD by fastforce


interpretation d: injective_morphism 
  V\<^sub>K E\<^sub>K s\<^sub>K "totalize s\<^sub>K" t\<^sub>K "totalize t\<^sub>K" l\<^sub>K "totalize l\<^sub>K" m\<^sub>K "totalize m\<^sub>K"
  V E s "totalize s" t "totalize t" l "totalize l" m "totalize m"
  d\<^sub>V "totalize d\<^sub>V"
  d\<^sub>E "totalize d\<^sub>E"
proof intro_locales
  show \<open>morphism_axioms V\<^sub>K E\<^sub>K s\<^sub>K t\<^sub>K l\<^sub>K m\<^sub>K V E s t l m d\<^sub>V d\<^sub>E\<close>
  proof
    show \<open>dom d\<^sub>V = V\<^sub>K \<and> ran d\<^sub>V \<subseteq> V\<close>
    proof
      show \<open>dom d\<^sub>V = V\<^sub>K\<close>
        using dom_d\<^sub>V by auto
    next
      show \<open>ran d\<^sub>V \<subseteq> V\<close>
        using ran_d\<^sub>V by blast
    qed
  next
    show \<open>dom d\<^sub>E = E\<^sub>K \<and> ran d\<^sub>E \<subseteq> E\<close>
    proof
      show \<open>dom d\<^sub>E = E\<^sub>K\<close>
        using dom_d\<^sub>E by auto
    next
      show \<open>ran d\<^sub>E \<subseteq> E\<close>
        using ran_d\<^sub>E by blast
    qed
  next
    show \<open>d\<^sub>V \<circ>\<^sub>m s\<^sub>K = s \<circ>\<^sub>m d\<^sub>E\<close> (is "?f = ?g")
    proof -
      have \<open>?f x = ?g x\<close> if \<open>x \<notin> E\<^sub>K\<close> for x
        unfolding d\<^sub>V_def d\<^sub>E_def
        using i.s_inclusion that by simp

      moreover have \<open>?f x \<noteq> None\<close> if \<open>x \<in> E\<^sub>K\<close> for x
        by (metis K.integrity_s K.integrity_s' K.s_def domIff dom_d\<^sub>V map_comp_None_iff option.sel that)

      moreover have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<^sub>K\<close> for x
        using that map_comp_def dang
        unfolding d\<^sub>V_def d\<^sub>E_def
        by (smt (verit, best) DiffD2 G.s_def K.integrity_s' K.s_def calculation(2) domIff i.e_inclusion_alt i.s_equality_alt i.s_inclusion i.v_inclusion_alt image_cong image_subset_iff k_subset_e m.e_morph_not_none m.g\<^sub>V_def m.g\<^sub>E_def m.integrity_e' m.source_preserve_alt m.v_morph_not_none map_comp_simps(1) object.integrity_s option.case_eq_if option.case_eq_if option.collapse restrict_map_def)

      ultimately show ?thesis
        by blast
    qed
  next
    show \<open>d\<^sub>V \<circ>\<^sub>m t\<^sub>K = t \<circ>\<^sub>m d\<^sub>E\<close> (is "?f = ?g")
    proof -
      have \<open>?f x = ?g x\<close> if \<open>x \<notin> E\<^sub>K\<close> for x
        unfolding d\<^sub>V_def d\<^sub>E_def
        using i.t_inclusion that by simp

      moreover have \<open>?f x \<noteq> None\<close> if \<open>x \<in> E\<^sub>K\<close> for x
        by (metis K.integrity_t K.integrity_t' K.t_def domIff dom_d\<^sub>V map_comp_None_iff option.sel that)

      moreover have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<^sub>K\<close> for x
        using that map_comp_def dang
        unfolding d\<^sub>V_def d\<^sub>E_def
        by (smt (verit, ccfv_SIG) K.integrity_t K.integrity_t' K.t_def d\<^sub>E_def domD dom_d\<^sub>E i.t_inclusion image_subset_iff k_subset_e m.g\<^sub>E_def m.target_preserve map_comp_simps(2) option.sel restrict_map_def)

      ultimately show ?thesis
        by blast
    qed
  next
    show \<open>l\<^sub>K = l \<circ>\<^sub>m d\<^sub>V\<close> (is "_ = ?g")
    proof -
      have \<open>l\<^sub>K x = ?g x\<close> if \<open>x \<notin> V\<^sub>K\<close> for x
        using that i.l_inclusion
        unfolding d\<^sub>V_def
        by auto
      moreover have \<open>l\<^sub>K x = ?g x\<close> if \<open>x \<in> V\<^sub>K\<close> for x
        unfolding map_comp_def d\<^sub>V_def
        by (smt (z3) i.l_inclusion image_subset_iff k_subset_v m.g\<^sub>V_def m.node_label_preserve map_comp_def option.case_eq_if restrict_map_def)

      ultimately show ?thesis
        by blast
    qed
  next
    show \<open>m\<^sub>K = m \<circ>\<^sub>m d\<^sub>E\<close> (is "_ = ?g")
    proof -
      have \<open>m\<^sub>K x = ?g x\<close> if \<open>x \<notin> E\<^sub>K\<close> for x
        using that i.m_inclusion
        unfolding d\<^sub>E_def
        by auto
      moreover have \<open>m\<^sub>K x = ?g x\<close> if \<open>x \<in> E\<^sub>K\<close> for x
        unfolding map_comp_def d\<^sub>E_def
        by (smt (z3) i.m_inclusion image_subset_iff k_subset_e m.edge_label_preserve m.g\<^sub>E_def map_comp_def option.case_eq_if restrict_map_def)


      ultimately show ?thesis
        by blast
    qed
  qed
next
  show \<open>injective_morphism_axioms V\<^sub>K E\<^sub>K d\<^sub>V d\<^sub>E\<close>
  proof
    show \<open>inj_on (totalize d\<^sub>V) V\<^sub>K\<close>
      unfolding d\<^sub>V_def
      by (smt (verit, best) d\<^sub>V_def domD domIff dom_d\<^sub>V inj_on_def m.dom_gv m.node_injectivity_alt option.sel restrict_in)
      

  next
    show \<open>inj_on (totalize d\<^sub>E) E\<^sub>K\<close>
      unfolding d\<^sub>E_def
      by (smt (verit, del_insts) i.subset_edges inj_onI inj_on_contraD m.edge_injectivity m.g\<^sub>E_def restrict_in subset_inj_on)
  qed
qed simp_all


definition g\<^sub>V where
"g\<^sub>V \<equiv> \<lambda>v. if v \<in> V then Some v else None"

definition g\<^sub>E where
"g\<^sub>E \<equiv> \<lambda>e. if e \<in> E then Some e else None"

interpretation g: injective_morphism 
  V E s "totalize s" t "totalize t" l "totalize l" m "totalize m"
  V\<^sub>G E\<^sub>G s\<^sub>G "totalize s\<^sub>G" t\<^sub>G "totalize t\<^sub>G" l\<^sub>G "totalize l\<^sub>G" m\<^sub>G "totalize m\<^sub>G"
  g\<^sub>V "totalize g\<^sub>V"
  g\<^sub>E "totalize g\<^sub>E"
proof intro_locales
  show \<open>morphism_axioms V E s t l m V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G g\<^sub>V g\<^sub>E\<close>
  proof
    show \<open>dom g\<^sub>V = V \<and> ran g\<^sub>V \<subseteq> V\<^sub>G\<close>
    proof
      show \<open>dom g\<^sub>V = V\<close>
        unfolding g\<^sub>V_def
        using subset_antisym by fastforce
    next 
      show \<open>ran g\<^sub>V \<subseteq> V\<^sub>G\<close>
        unfolding g\<^sub>V_def
        by (smt (verit) Diff_subset mem_Collect_eq option.sel option.simps(3) ran_def subset_iff)
    qed
  next
    show \<open>dom g\<^sub>E = E \<and> ran g\<^sub>E \<subseteq> E\<^sub>G\<close>
    proof
      show \<open>dom g\<^sub>E = E\<close>
        unfolding g\<^sub>E_def
        using subset_antisym by fastforce
    next 
      show \<open>ran g\<^sub>E \<subseteq> E\<^sub>G\<close>
        unfolding g\<^sub>E_def
        by (smt (verit) Diff_subset mem_Collect_eq option.sel option.simps(3) ran_def subset_iff)
    qed
  next
    show \<open>g\<^sub>V \<circ>\<^sub>m s = s\<^sub>G \<circ>\<^sub>m g\<^sub>E\<close> (is "?f = ?g")
    proof -
      have \<open>?f x = ?g x\<close> if \<open>x \<notin> E\<close> for x
        unfolding g\<^sub>E_def
        using that by auto

      moreover have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<close> for x
        unfolding g\<^sub>V_def g\<^sub>E_def
        by (smt (z3) domIff map_comp_simps(2) object.integrity_s object.integrity_s_alt option.collapse restrict_map_def that)

      ultimately show ?thesis
        by blast
    qed
  next
    show \<open>g\<^sub>V \<circ>\<^sub>m t = t\<^sub>G \<circ>\<^sub>m g\<^sub>E\<close> (is "?f = ?g")
    proof -
      have \<open>?f x = ?g x\<close> if \<open>x \<notin> E\<close> for x
        unfolding g\<^sub>V_def g\<^sub>E_def
        using that by force

      moreover have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<close> for x
        unfolding g\<^sub>V_def g\<^sub>E_def
        by (smt (verit, ccfv_threshold) map_comp_None_iff map_comp_simps(2) not_Some_eq object.integrity_t_alt restrict_map_def)

      ultimately show ?thesis
        by blast
    qed
  next
    show \<open>l = l\<^sub>G \<circ>\<^sub>m g\<^sub>V\<close> (is "_ = ?g")
    proof -
      have \<open>l x = ?g x\<close> if \<open>x \<notin> V\<close> for x
        unfolding g\<^sub>V_def
        using that by auto

      moreover have \<open>l x = ?g x\<close> if \<open>x \<in> V\<close> for x
        unfolding g\<^sub>V_def
        using that by auto

      ultimately show ?thesis
        by blast
    qed
  next
    show \<open>m = m\<^sub>G \<circ>\<^sub>m g\<^sub>E\<close>(is "_ = ?g")
    proof -
      have \<open>m x = ?g x\<close> if \<open>x \<notin> E\<close> for x
        unfolding g\<^sub>E_def
        using that by auto

      moreover have \<open>m x = ?g x\<close> if \<open>x \<in> E\<close> for x
        unfolding g\<^sub>E_def
        using that by auto

      ultimately show ?thesis
        by blast
    qed
  qed
next
  show \<open>injective_morphism_axioms V E g\<^sub>V g\<^sub>E\<close>
  proof
    show \<open>inj_on (totalize g\<^sub>V) V\<close>
      unfolding g\<^sub>V_def
      by (simp add: inj_on_def)
  next
    show \<open>inj_on (totalize g\<^sub>E) E\<close>
      unfolding g\<^sub>E_def
      by (simp add: inj_on_def)
  qed
qed simp_all


text \<open>Pushout\<close>
lemma 
  shows \<open>\<forall>v \<in> V\<^sub>G. v \<in> V \<or> v \<in> f'\<^sub>V ` (V\<^sub>L-V\<^sub>K)\<close>
  by blast

lemma univ_prop:
  assumes
  H: "graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H" and
  p: "morphism V\<^sub>L E\<^sub>L s\<^sub>L t\<^sub>L l\<^sub>L m\<^sub>L V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V p\<^sub>E" and
  q: "morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H t\<^sub>V t\<^sub>E" and
  commutativity_v: "p\<^sub>V \<circ>\<^sub>m k\<^sub>V = t\<^sub>V \<circ>\<^sub>m d\<^sub>V" and
  commutativity_e: "p\<^sub>E \<circ>\<^sub>m k\<^sub>E = t\<^sub>E \<circ>\<^sub>m d\<^sub>E"
shows \<open>\<exists>!(u\<^sub>V, u\<^sub>E).
     morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> 
      u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> 
      u\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close>
proof

  define u\<^sub>V where \<open>u\<^sub>V \<equiv> \<lambda>v. 
    (if v \<in> V then t\<^sub>V v else 
      if (\<exists>y \<in> V\<^sub>L-k'\<^sub>V ` V\<^sub>K. f\<^sub>V y = Some v) then p\<^sub>V (THE x. f\<^sub>V x = Some v) else None)\<close>

 define u\<^sub>E where \<open>u\<^sub>E \<equiv> \<lambda>e. 
    (if e \<in> E then t\<^sub>E e else 
      if (\<exists>y \<in> E\<^sub>L- k'\<^sub>E ` E\<^sub>K. f\<^sub>E y = Some e) then p\<^sub>E (THE x. f\<^sub>E x = Some e) else None)\<close>

  show \<open>case (u\<^sub>V,u\<^sub>E) of (u\<^sub>V, u\<^sub>E) \<Rightarrow> morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close>
  proof (simp, intro conjI)
    show \<open>morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E\<close>
    proof intro_locales
      show \<open>graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close>
        using assms
        by simp
      show \<open>morphism_axioms V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E\<close>
      proof
        show \<open>dom u\<^sub>V = V\<^sub>G \<and> ran u\<^sub>V \<subseteq> V\<^sub>H\<close>
        proof
          show \<open>dom u\<^sub>V = V\<^sub>G\<close>
          proof -
            have \<open>u\<^sub>V x \<noteq> None\<close> if \<open>x \<in> V\<^sub>G\<close> for x
            proof (cases \<open>x \<in> V\<close>)
              case True
              then show ?thesis 
                unfolding u\<^sub>V_def
                using q morphism.v_morph_not_none
                by fastforce
            next
              case False
              then show ?thesis 
                unfolding u\<^sub>V_def 
                by (smt (z3) DiffI Diff_subset assms(2) domIff i.inclusion_nodes image_iff k_subset_v m.node_injectivity_alt m.dom_gv m.g\<^sub>V_def morphism.v_morph_not_none option.collapse subset_iff that the_equality)
            qed
            moreover have \<open>u\<^sub>V x = None\<close> if \<open>x \<notin> V\<^sub>G\<close> for x
              using that
              unfolding u\<^sub>V_def
              using m.integrity_v_alt
              by auto
                
            ultimately show ?thesis
              by fastforce
          qed
        next
          show \<open>ran u\<^sub>V \<subseteq> V\<^sub>H\<close>
          proof -
            have \<open>ran t\<^sub>V \<subseteq> V\<^sub>H\<close>
              using q morphism.ran_gv
              by fast

            moreover have \<open>ran p\<^sub>V \<subseteq> V\<^sub>H\<close>
              using p morphism.ran_gv
              by fast

            ultimately show ?thesis
              unfolding ran_def u\<^sub>V_def
              by auto
          qed
        qed
      next
        show \<open>dom u\<^sub>E = E\<^sub>G \<and> ran u\<^sub>E \<subseteq> E\<^sub>H\<close>
        proof
          show \<open>dom u\<^sub>E = E\<^sub>G\<close>
          proof -
            have \<open>u\<^sub>E x \<noteq> None\<close> if \<open>x \<in> E\<^sub>G\<close> for x
            proof (cases \<open>x \<in> E\<close>)
              case True
              then show ?thesis 
                unfolding u\<^sub>E_def
                using q morphism.e_morph_not_none
                by fastforce
            next
              case False
              then show ?thesis 
                unfolding u\<^sub>E_def 
                by (smt (z3) DiffI Diff_subset assms(2) domIff i.inclusion_edges image_iff k_subset_e m.edge_injectivity_alt m.dom_ge m.g\<^sub>E_def morphism.e_morph_not_none option.collapse subset_iff that the_equality)            qed

            moreover have \<open>u\<^sub>E x = None\<close> if \<open>x \<notin> E\<^sub>G\<close> for x
              using that
              unfolding u\<^sub>E_def
              using m.integrity_e_alt
              by auto
                
            ultimately show ?thesis
              by fastforce
          qed
        next
          show \<open>ran u\<^sub>E \<subseteq> E\<^sub>H\<close>
          proof -
            have \<open>ran t\<^sub>E \<subseteq> E\<^sub>H\<close>
              using q morphism.ran_ge
              by fast

            moreover have \<open>ran p\<^sub>E \<subseteq> E\<^sub>H\<close>
              using p morphism.ran_ge
              by fast

            ultimately show ?thesis
              unfolding ran_def u\<^sub>E_def
              by auto
          qed
        qed
      next
        show \<open>u\<^sub>V \<circ>\<^sub>m s\<^sub>G = s\<^sub>H \<circ>\<^sub>m u\<^sub>E\<close> (is "?f = ?g")
        proof -
          have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<^sub>G\<close> for x
          proof -
            consider (a) \<open>\<exists>y \<in> E\<^sub>L- k'\<^sub>E ` E\<^sub>K. f\<^sub>E y = Some x\<close> | (b) \<open>x \<in> E\<close>
              using \<open>x \<in> E\<^sub>G\<close> i.inclusion_edges m.e_morph_not_none by fastforce
            thus ?thesis
            proof cases
              case a

              obtain y where \<open>y \<in> E\<^sub>L- k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close>
                using a by blast

              have \<open>?f x = (u\<^sub>V \<circ>\<^sub>m f\<^sub>V \<circ>\<^sub>m s\<^sub>L) y\<close>
              proof -
                obtain v' where \<open>s\<^sub>L y = Some v'\<close>
                  using L.integrity_s \<open>y \<in> E\<^sub>L - k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close> by blast

                have \<open>?f x = (u\<^sub>V \<circ>\<^sub>m f\<^sub>V) v'\<close>
                  unfolding map_comp_def u\<^sub>V_def
                  using dang
                  by (metis (no_types, lifting) DiffD1 G.s_def L.integrity_s_alt L.s_def \<open>s\<^sub>L y = Some v'\<close> \<open>y \<in> E\<^sub>L - k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close> domD g.H.integrity_s m.g\<^sub>E_def m.g\<^sub>V_def m.source_preserve_alt m.v_morph_not_none option.case_eq_if option.distinct(1) option.sel that)
                thus ?thesis
                  by (simp add: \<open>s\<^sub>L y = Some v'\<close>)
              qed

              also have \<open>... = (p\<^sub>V \<circ>\<^sub>m s\<^sub>L) y\<close>
              proof -
                obtain v' where \<open>s\<^sub>L y = Some v'\<close>
                  using L.integrity_s \<open>y \<in> E\<^sub>L - k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close> by blast

                obtain v'' where \<open>f\<^sub>V v' = Some v''\<close>
                  using L.integrity_s_alt \<open>s\<^sub>L y = Some v'\<close> m.dom_gv by blast

                have \<open>u\<^sub>V v'' = p\<^sub>V v'\<close>
                proof (cases \<open>v' \<in> V\<^sub>L-V\<^sub>K\<close>)
                  case True
                  then show ?thesis 
                    unfolding u\<^sub>V_def
                    by (smt (verit, ccfv_threshold) Diff_iff \<open>f\<^sub>V v' = Some v''\<close> domIff i.inclusion_nodes image_iff m.node_injectivity_alt m.dom_gv m.g\<^sub>V_def option.sel the_equality)
                next
                  case False

                  have \<open>u\<^sub>V v'' = p\<^sub>V v'\<close> if \<open>v' \<notin> V\<^sub>L\<close>
                    unfolding u\<^sub>V_def
                    using that
                    using L.integrity_s_alt \<open>s\<^sub>L y = Some v'\<close> by blast

                  moreover have \<open>u\<^sub>V v'' = p\<^sub>V v'\<close> if \<open>v'' \<in> V\<close>
                    unfolding u\<^sub>V_def
                    using that
                    by (metis (no_types, lifting) DiffI False \<open>f\<^sub>V v' = Some v''\<close> \<open>v' \<notin> V\<^sub>L \<Longrightarrow> u\<^sub>V v'' = p\<^sub>V v'\<close> assms(4) d\<^sub>V_def domD i.dom_gv i.inclusion_nodes_alt map_comp_simps(2) restrict_in u\<^sub>V_def)

                  ultimately show ?thesis
                    by (metis DiffI False \<open>f\<^sub>V v' = Some v''\<close> k_subset_v m.g\<^sub>V_def option.sel rev_image_eqI subset_eq)
                qed
                thus ?thesis
                  by (simp add: \<open>f\<^sub>V v' = Some v''\<close> \<open>s\<^sub>L y = Some v'\<close>)
              qed

              also have \<open>... = (s\<^sub>H \<circ>\<^sub>m p\<^sub>E) y\<close>
                by (metis morphism.source_preserve p)

              also have \<open>... = (s\<^sub>H \<circ>\<^sub>m u\<^sub>E) x\<close>
              proof -
                have  \<open>(s\<^sub>H \<circ>\<^sub>m p\<^sub>E) y = (s\<^sub>H \<circ>\<^sub>m u\<^sub>E) x\<close> if \<open>x \<in> E\<close>
                  unfolding map_comp_def u\<^sub>E_def
                  using that
                  by (smt (verit, ccfv_threshold) Diff_iff \<open>y \<in> E\<^sub>L - k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close> i.inclusion_edges image_iff m.g\<^sub>E_def option.sel)

                moreover have \<open>(s\<^sub>H \<circ>\<^sub>m p\<^sub>E) y = (s\<^sub>H \<circ>\<^sub>m u\<^sub>E) x\<close>
                  unfolding map_comp_def u\<^sub>E_def
                  using that
                  by (smt (verit, del_insts) DiffD2 DiffI \<open>y \<in> E\<^sub>L - k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close> domIff i.inclusion_edges image_eqI m.edge_injectivity_alt m.g\<^sub>E_def m.integrity_e option.distinct(1) option.sel the_equality)

                ultimately show ?thesis 
                  using a by blast
              qed
              finally show ?thesis .

            next
              case b
              then show ?thesis
                by (smt (verit, best) domIff g.H.integrity_s map_comp_def map_comp_simps(2) morphism.source_preserve object.integrity_s' option.collapse q restrict_in that u\<^sub>E_def u\<^sub>V_def)
            qed
          qed
          thus ?thesis
            unfolding map_comp_def
            by (metis DiffD1 domIff g.H.integrity_s m.g\<^sub>E_def m.integrity_e' option.case_eq_if option.sel u\<^sub>E_def)
        qed      
      next
        show \<open>u\<^sub>V \<circ>\<^sub>m t\<^sub>G = t\<^sub>H \<circ>\<^sub>m u\<^sub>E\<close> (is "?f = ?g")
        proof -
          have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<^sub>G\<close> for x
          proof -
            consider (a) \<open>\<exists>y \<in> E\<^sub>L- k'\<^sub>E ` E\<^sub>K. f\<^sub>E y = Some x\<close> | (b) \<open>x \<in> E\<close>
              using \<open>x \<in> E\<^sub>G\<close> i.inclusion_edges m.e_morph_not_none by fastforce
            thus ?thesis
            proof cases
              case a

              obtain y where \<open>y \<in> E\<^sub>L- k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close>
                using a by blast

              have \<open>?f x = (u\<^sub>V \<circ>\<^sub>m f\<^sub>V \<circ>\<^sub>m t\<^sub>L) y\<close>
              proof -
                obtain v' where \<open>t\<^sub>L y = Some v'\<close>
                  using L.integrity_t \<open>y \<in> E\<^sub>L - k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close> by blast

                have \<open>?f x = (u\<^sub>V \<circ>\<^sub>m f\<^sub>V) v'\<close>
                  unfolding map_comp_def u\<^sub>V_def
                  using dang
                  by (metis (no_types, lifting) DiffD1 G.t_def L.integrity_t_alt L.t_def \<open>t\<^sub>L y = Some v'\<close> \<open>y \<in> E\<^sub>L - k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close> domD g.H.integrity_t m.g\<^sub>E_def m.g\<^sub>V_def m.target_preserve_alt m.v_morph_not_none option.case_eq_if option.distinct(1) option.sel that)
                thus ?thesis
                  by (simp add: \<open>t\<^sub>L y = Some v'\<close>)
              qed

              also have \<open>... = (p\<^sub>V \<circ>\<^sub>m t\<^sub>L) y\<close>
              proof -
                obtain v' where \<open>t\<^sub>L y = Some v'\<close>
                  using L.integrity_t \<open>y \<in> E\<^sub>L - k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close> by blast

                obtain v'' where \<open>f\<^sub>V v' = Some v''\<close>
                  using L.integrity_t_alt \<open>t\<^sub>L y = Some v'\<close> m.dom_gv by blast

                have \<open>u\<^sub>V v'' = p\<^sub>V v'\<close>
                proof (cases \<open>v' \<in> V\<^sub>L-V\<^sub>K\<close>)
                  case True
                  then show ?thesis 
                    unfolding u\<^sub>V_def
                    by (smt (verit, ccfv_threshold) Diff_iff \<open>f\<^sub>V v' = Some v''\<close> domIff i.inclusion_nodes image_iff m.node_injectivity_alt m.dom_gv m.g\<^sub>V_def option.sel the_equality)
                next
                  case False

                  have \<open>u\<^sub>V v'' = p\<^sub>V v'\<close> if \<open>v' \<notin> V\<^sub>L\<close>
                    unfolding u\<^sub>V_def
                    using that
                    using L.integrity_t_alt \<open>t\<^sub>L y = Some v'\<close> by blast

                  moreover have \<open>u\<^sub>V v'' = p\<^sub>V v'\<close> if \<open>v'' \<in> V\<close>
                    unfolding u\<^sub>V_def
                    using that
                    by (metis (no_types, lifting) DiffI False \<open>f\<^sub>V v' = Some v''\<close> \<open>v' \<notin> V\<^sub>L \<Longrightarrow> u\<^sub>V v'' = p\<^sub>V v'\<close> assms(4) d\<^sub>V_def domD i.dom_gv i.inclusion_nodes_alt map_comp_simps(2) restrict_in u\<^sub>V_def)

                  ultimately show ?thesis
                    by (metis DiffI False \<open>f\<^sub>V v' = Some v''\<close> k_subset_v m.g\<^sub>V_def option.sel rev_image_eqI subset_eq)
                qed
                thus ?thesis
                  by (simp add: \<open>f\<^sub>V v' = Some v''\<close> \<open>t\<^sub>L y = Some v'\<close>)
              qed

              also have \<open>... = (t\<^sub>H \<circ>\<^sub>m p\<^sub>E) y\<close>
                by (metis morphism.target_preserve p)

              also have \<open>... = (t\<^sub>H \<circ>\<^sub>m u\<^sub>E) x\<close>
              proof -
                have  \<open>(t\<^sub>H \<circ>\<^sub>m p\<^sub>E) y = (t\<^sub>H \<circ>\<^sub>m u\<^sub>E) x\<close> if \<open>x \<in> E\<close>
                  unfolding map_comp_def u\<^sub>E_def
                  using that
                  by (smt (verit, ccfv_threshold) Diff_iff \<open>y \<in> E\<^sub>L - k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close> i.inclusion_edges image_iff m.g\<^sub>E_def option.sel)

                moreover have \<open>(t\<^sub>H \<circ>\<^sub>m p\<^sub>E) y = (t\<^sub>H \<circ>\<^sub>m u\<^sub>E) x\<close>
                  unfolding map_comp_def u\<^sub>E_def
                  using that
                  by (smt (verit, del_insts) DiffD2 DiffI \<open>y \<in> E\<^sub>L - k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close> domIff i.inclusion_edges image_eqI m.edge_injectivity_alt m.g\<^sub>E_def m.integrity_e option.distinct(1) option.sel the_equality)

                ultimately show ?thesis 
                  using a by blast
              qed
              finally show ?thesis .

            next
              case b
              then show ?thesis
                by (smt (verit, best) domIff g.H.integrity_t map_comp_def map_comp_simps(2) morphism.target_preserve object.integrity_t' option.collapse q restrict_in that u\<^sub>E_def u\<^sub>V_def)
            qed
          qed
          thus ?thesis
            unfolding map_comp_def
            by (metis DiffD1 domIff g.H.integrity_t m.g\<^sub>E_def m.integrity_e' option.case_eq_if option.sel u\<^sub>E_def)
        qed
      next
        show \<open>l\<^sub>G = l\<^sub>H \<circ>\<^sub>m u\<^sub>V\<close> (is "_ = ?f")
        proof -
          have \<open>l\<^sub>G x = ?f x\<close> if \<open>x \<in> V\<^sub>G\<close> for x
          proof -
            consider (a) \<open>\<exists>y \<in> V\<^sub>L-k'\<^sub>V ` V\<^sub>K. f\<^sub>V y = Some x\<close> | (b) \<open>x \<in> V\<close>
              using \<open>x \<in> V\<^sub>G\<close> i.inclusion_nodes m.v_morph_not_none by fastforce
            thus ?thesis
            proof cases
              case a
              then show ?thesis 
              proof -
                obtain y where ex:\<open>y \<in> V\<^sub>L- k'\<^sub>V ` V\<^sub>K \<and> f\<^sub>V y = Some x\<close>
                  using a by blast

                have \<open>l\<^sub>G x = (l\<^sub>H \<circ>\<^sub>m p\<^sub>V) y\<close>
                  using a that
                  by (metis \<open>y \<in> V\<^sub>L - k'\<^sub>V ` V\<^sub>K \<and> f\<^sub>V y = Some x\<close> m.node_label_preserve map_comp_simps(2) morphism.node_label_preserve p)


                thus ?thesis
                  using a  ex that
                  unfolding u\<^sub>V_def map_comp_def
                  apply auto
                   apply (metis (mono_tags, lifting) Diff_iff ex i.inclusion_nodes image_iff option.sel)
                  by (metis (mono_tags, lifting) domIff m.node_injectivity_alt m.dom_gv the_equality)
              qed
            next
              case b

              obtain y where ex:\<open>t\<^sub>V x = Some y\<close>
                by (meson b domD domIff morphism.v_morph_not_none q)

              have \<open>l\<^sub>G x = (l\<^sub>H \<circ>\<^sub>m t\<^sub>V) x\<close>
                unfolding map_comp_def
                by (metis b map_comp_def morphism.node_label_preserve q restrict_in)

              
              thus ?thesis 
                using b ex u\<^sub>V_def by auto

            qed
          qed
          moreover have \<open>l\<^sub>G x = ?f x\<close> if \<open>x \<notin> V\<^sub>G\<close> for x
            unfolding map_comp_def u\<^sub>V_def
            by (smt (z3) DiffE G.integrity_l domIff m.integrity_v_alt option.case_eq_if that)
          ultimately show ?thesis
            by blast
        qed
      next
        show \<open>m\<^sub>G = m\<^sub>H \<circ>\<^sub>m u\<^sub>E\<close> (is "_ = ?f")
        proof -
          have \<open>m\<^sub>G x = ?f x\<close> if \<open>x \<in> E\<^sub>G\<close> for x
          proof -
            consider (a) \<open>\<exists>y \<in> E\<^sub>L-k'\<^sub>E ` E\<^sub>K. f\<^sub>E y = Some x\<close> | (b) \<open>x \<in> E\<close>
              using \<open>x \<in> E\<^sub>G\<close> i.inclusion_edges m.e_morph_not_none by fastforce
            thus ?thesis
            proof cases
              case a
              then show ?thesis 
              proof -
                obtain y where ex:\<open>y \<in> E\<^sub>L- k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close>
                  using a by blast

                have \<open>m\<^sub>G x = (m\<^sub>H \<circ>\<^sub>m p\<^sub>E) y\<close>
                  using a that
                  by (metis \<open>y \<in> E\<^sub>L - k'\<^sub>E ` E\<^sub>K \<and> f\<^sub>E y = Some x\<close> m.edge_label_preserve map_comp_simps(2) morphism.edge_label_preserve p)


                thus ?thesis
                  using a  ex that
                  unfolding u\<^sub>E_def map_comp_def
                  apply auto
                   apply (metis (mono_tags, lifting) Diff_iff ex i.inclusion_edges image_iff option.sel)
                  by (metis (mono_tags, lifting) domIff m.edge_injectivity_alt m.dom_ge the_equality)
              qed
            next
              case b

              obtain y where ex:\<open>t\<^sub>E x = Some y\<close>
                by (meson b domD domIff morphism.e_morph_not_none q)

              have \<open>m\<^sub>G x = (m\<^sub>H \<circ>\<^sub>m t\<^sub>E) x\<close>
                unfolding map_comp_def
                by (metis b map_comp_def morphism.edge_label_preserve q restrict_in)
              
              thus ?thesis 
                using b ex u\<^sub>E_def by auto

            qed
          qed
          moreover have \<open>m\<^sub>G x = ?f x\<close> if \<open>x \<notin> E\<^sub>G\<close> for x
            unfolding map_comp_def u\<^sub>E_def
            by (smt (z3) DiffE G.integrity_m domIff m.integrity_e_alt option.case_eq_if that)
          ultimately show ?thesis
            by blast
        qed
      qed
    qed
  next
    \<comment> \<open>TODO: proof see gluing\<close>
    show \<open>u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V\<close> (is "?f = p\<^sub>V")
    proof -
      have \<open>?f x = p\<^sub>V x\<close> if \<open>x \<in> V\<^sub>L\<close> for x
      proof -
        consider
            (a) \<open>x \<in> V\<^sub>L - k'\<^sub>V ` V\<^sub>K\<close> 
          | (b) \<open>x \<in> k'\<^sub>V ` V\<^sub>K\<close>
          using \<open>x \<in> V\<^sub>L\<close> by blast

        then show ?thesis
        proof cases
          case a
          then show ?thesis 
            unfolding map_comp_def u\<^sub>V_def
            by (smt (verit, del_insts) Diff_iff domD domIff i.inclusion_nodes image_iff m.node_injectivity_alt m.dom_gv m.g\<^sub>V_def option.case_eq_if option.sel the_equality)
        next
          case b
          then show ?thesis 
            unfolding map_comp_def u\<^sub>V_def
            by (smt (verit, best) assms(4) d.integrity_v' d\<^sub>V_def domIff i.dom_gv i.inclusion_morphism_axioms i.inclusion_nodes i.v_inclusion_alt image_iff inclusion_morphism.inclusion_nodes m.dom_gv map_comp_simps(2) option.case_eq_if option.collapse restrict_in)
        qed
      qed
      moreover have \<open>?f x = p\<^sub>V x\<close> if \<open>x \<notin> V\<^sub>L\<close> for x
        using p that m.dom_gv domIff
        unfolding map_comp_def
        by (metis domIff m.dom_gv morphism.dom_gv option.case_eq_if)

      ultimately show ?thesis
        by blast
    qed
  next
    show \<open>u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E\<close> (is "?f = _")
    proof -
      have \<open>?f x = p\<^sub>E x\<close> if \<open>x \<in> E\<^sub>L\<close> for x
      proof -
        consider
            (a) \<open>x \<in> E\<^sub>L - k'\<^sub>E ` E\<^sub>K\<close> 
          | (b) \<open>x \<in> k'\<^sub>E ` E\<^sub>K\<close>
          using \<open>x \<in> E\<^sub>L\<close> by blast

        then show ?thesis
        proof cases
          case a
          then show ?thesis 
            unfolding map_comp_def u\<^sub>E_def
            by (smt (verit, del_insts) Diff_iff domD domIff i.inclusion_edges image_iff m.edge_injectivity_alt m.dom_ge m.g\<^sub>E_def option.case_eq_if option.sel the_equality)
        next
          case b
          then show ?thesis 
            unfolding map_comp_def u\<^sub>E_def
            by (smt (verit, best) assms(5) d.integrity_e' d\<^sub>E_def domIff i.dom_ge i.inclusion_morphism_axioms i.inclusion_edges i.e_inclusion_alt image_iff inclusion_morphism.inclusion_edges m.dom_ge map_comp_simps(2) option.case_eq_if option.collapse restrict_in)
        qed
      qed
      moreover have \<open>?f x = p\<^sub>E x\<close> if \<open>x \<notin> E\<^sub>L\<close> for x
        using p that m.dom_ge domIff
        unfolding map_comp_def
        by (metis domIff m.dom_ge morphism.dom_ge option.case_eq_if)

      ultimately show ?thesis
        by blast
    qed
  next
    show \<open>u\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V\<close> (is "?f = _")
    proof -
      have \<open>?f x = t\<^sub>V x\<close> for x
      proof (cases \<open>x \<in> V\<close>)
        case True
        then show ?thesis
          unfolding u\<^sub>V_def map_comp_def g\<^sub>V_def
          using True
          by auto
      next
        case False
        then show ?thesis 
          unfolding map_comp_def g\<^sub>V_def
          by (metis (full_types) domIff morphism.dom_gv option.simps(4) q)
      qed
      thus?thesis
        by blast
    qed
    next
    show \<open>u\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> (is "?f = _")
    proof -
      have \<open>?f x = t\<^sub>E x\<close> for x
      proof (cases \<open>x \<in> E\<close>)
        case True
        then show ?thesis
          unfolding u\<^sub>E_def map_comp_def g\<^sub>E_def
          using True
          by auto
      next
        case False
        then show ?thesis 
          unfolding map_comp_def g\<^sub>E_def
          by (metis (full_types) domIff morphism.dom_ge option.simps(4) q)
      qed
      thus?thesis
        by blast
    qed
  qed
next
  define u\<^sub>V where \<open>u\<^sub>V \<equiv> \<lambda>v. 
    (if v \<in> V then t\<^sub>V v else 
      if (\<exists>y \<in> V\<^sub>L-k'\<^sub>V ` V\<^sub>K. f\<^sub>V y = Some v) then p\<^sub>V (THE x. f\<^sub>V x = Some v) else None)\<close>

 define u\<^sub>E where \<open>u\<^sub>E \<equiv> \<lambda>e. 
    (if e \<in> E then t\<^sub>E e else 
      if (\<exists>y \<in> E\<^sub>L- k'\<^sub>E ` E\<^sub>K. f\<^sub>E y = Some e) then p\<^sub>E (THE x. f\<^sub>E x = Some e) else None)\<close>

  show \<open>f = (u\<^sub>V, u\<^sub>E)\<close> if \<open>case f of (u\<^sub>V, u\<^sub>E) \<Rightarrow> morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> for f
  proof -
    have \<open>(fst f) x = u\<^sub>V x\<close> if \<open>x \<in> V\<^sub>G\<close> for x
    proof -
      consider (a) \<open>\<exists>y \<in> V\<^sub>L- k'\<^sub>V ` V\<^sub>K. f\<^sub>V y = Some x\<close> | (b) \<open>x \<in> V\<close>
        using \<open>x \<in> V\<^sub>G\<close> i.inclusion_nodes m.v_morph_not_none by fastforce
      thus ?thesis
      proof cases
        case a

        obtain y where \<open>y \<in> V\<^sub>L \<and> f\<^sub>V y = Some x\<close>
          using a by blast

        have \<open>u\<^sub>V x = (u\<^sub>V \<circ>\<^sub>m f\<^sub>V) y\<close>
          by (simp add: \<open>y \<in> V\<^sub>L \<and> f\<^sub>V y = Some x\<close>)

        also have \<open>... = p\<^sub>V y\<close>
          by (metis (mono_tags, lifting) Diff_iff \<open>y \<in> V\<^sub>L \<and> f\<^sub>V y = Some x\<close> a calculation domI i.inclusion_nodes image_eqI m.node_injectivity_alt m.dom_gv m.g\<^sub>V_def option.sel the_equality u\<^sub>V_def)

        also have \<open>... = (u\<^sub>V \<circ>\<^sub>m f\<^sub>V) y\<close>
          using \<open>(u\<^sub>V \<circ>\<^sub>m f\<^sub>V) y = p\<^sub>V y\<close> by presburger

        also have \<open>... = (fst f) x\<close> if \<open>morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H (fst f) (snd f) \<and> (fst f) \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> (snd f) \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> (fst f) \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> (snd f) \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close>
          using \<open>p\<^sub>V y = (u\<^sub>V \<circ>\<^sub>m f\<^sub>V) y\<close> \<open>y \<in> V\<^sub>L \<and> f\<^sub>V y = Some x\<close> that by force

        also have \<open>... = (fst f) x\<close>
          by simp

        finally show ?thesis
          using \<open>case f of (u\<^sub>V, u\<^sub>E) \<Rightarrow> morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> \<open>morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H (fst f) (snd f) \<and> fst f \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> snd f \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> fst f \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> snd f \<circ>\<^sub>m g\<^sub>E = t\<^sub>E \<Longrightarrow> (u\<^sub>V \<circ>\<^sub>m f\<^sub>V) y = fst f x\<close> \<open>u\<^sub>V x = (u\<^sub>V \<circ>\<^sub>m f\<^sub>V) y\<close> by force

      next
        case b

        obtain y where \<open>y \<in> V \<and> g\<^sub>V y = Some x\<close>
          by (meson b g\<^sub>V_def)

        have \<open>u\<^sub>V x = (u\<^sub>V \<circ>\<^sub>m g\<^sub>V) y\<close>
          by (simp add: \<open>y \<in> V \<and> g\<^sub>V y = Some x\<close>)

        also have \<open>... = t\<^sub>V y\<close>
          by (metis \<open>y \<in> V \<and> g\<^sub>V y = Some x\<close> calculation g\<^sub>V_def option.sel u\<^sub>V_def)

        also have \<open>... = (fst f \<circ>\<^sub>m g\<^sub>V) y\<close>
          using \<open>case f of (u\<^sub>V, u\<^sub>E) \<Rightarrow> morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> by force


        also have \<open>... = (fst f) x\<close>
          by (simp add: \<open>y \<in> V \<and> g\<^sub>V y = Some x\<close>)

        finally show ?thesis 
          unfolding u\<^sub>V_def
          by presburger
      qed
    qed

    moreover have \<open>(fst f) x = u\<^sub>V x\<close> if \<open>x \<notin> V\<^sub>G\<close> for x
      using \<open>case f of (u\<^sub>V, u\<^sub>E) \<Rightarrow> morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> m.integrity_v_alt morphism.dom_gv that u\<^sub>V_def by fastforce

    moreover have \<open>(snd f) x = u\<^sub>E x\<close> if \<open>x \<in> E\<^sub>G\<close> for x
    proof -
      consider (a) \<open>\<exists>y \<in> E\<^sub>L- k'\<^sub>E ` E\<^sub>K. f\<^sub>E y = Some x\<close> | (b) \<open>x \<in> E\<close>
        using \<open>x \<in> E\<^sub>G\<close> i.inclusion_edges m.e_morph_not_none by fastforce
      thus ?thesis
      proof cases
        case a

        obtain y where \<open>y \<in> E\<^sub>L \<and> f\<^sub>E y = Some x\<close>
          using a by blast

        have \<open>u\<^sub>E x = (u\<^sub>E \<circ>\<^sub>m f\<^sub>E) y\<close>
          by (simp add: \<open>y \<in> E\<^sub>L \<and> f\<^sub>E y = Some x\<close>)

        also have \<open>... = p\<^sub>E y\<close>
          by (metis (mono_tags, lifting) Diff_iff \<open>y \<in> E\<^sub>L \<and> f\<^sub>E y = Some x\<close> a calculation domI i.inclusion_edges image_eqI m.edge_injectivity_alt m.dom_ge m.g\<^sub>E_def option.sel the_equality u\<^sub>E_def)

        also have \<open>... = (u\<^sub>E \<circ>\<^sub>m f\<^sub>E) y\<close>
          using \<open>(u\<^sub>E \<circ>\<^sub>m f\<^sub>E) y = p\<^sub>E y\<close> by presburger

        also have \<open>... = (snd f) x\<close> if \<open>morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H (fst f) (snd f) \<and> (fst f) \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> (snd f) \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> (fst f) \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> (snd f) \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close>
          using \<open>p\<^sub>E y = (u\<^sub>E \<circ>\<^sub>m f\<^sub>E) y\<close> \<open>y \<in> E\<^sub>L \<and> f\<^sub>E y = Some x\<close> that by force

        also have \<open>... = (snd f) x\<close>
          by simp

        finally show ?thesis
          using \<open>case f of (u\<^sub>V, u\<^sub>E) \<Rightarrow> morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> \<open>morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H (fst f) (snd f) \<and> fst f \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> snd f \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> fst f \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> snd f \<circ>\<^sub>m g\<^sub>E = t\<^sub>E \<Longrightarrow> (u\<^sub>E \<circ>\<^sub>m f\<^sub>E) y = snd f x\<close> \<open>u\<^sub>E x = (u\<^sub>E \<circ>\<^sub>m f\<^sub>E) y\<close> by force

      next
        case b

        obtain y where \<open>y \<in> E \<and> g\<^sub>E y = Some x\<close>
          by (meson b g\<^sub>E_def)

        have \<open>u\<^sub>E x = (u\<^sub>E \<circ>\<^sub>m g\<^sub>E) y\<close>
          by (simp add: \<open>y \<in> E \<and> g\<^sub>E y = Some x\<close>)

        also have \<open>... = t\<^sub>E y\<close>
          by (metis \<open>y \<in> E \<and> g\<^sub>E y = Some x\<close> calculation g\<^sub>E_def option.sel u\<^sub>E_def)

        also have \<open>... = (snd f \<circ>\<^sub>m g\<^sub>E) y\<close>
          using \<open>case f of (u\<^sub>V, u\<^sub>E) \<Rightarrow> morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> by force


        also have \<open>... = (snd f) x\<close>
          by (simp add: \<open>y \<in> E \<and> g\<^sub>E y = Some x\<close>)

        finally show ?thesis 
          unfolding u\<^sub>V_def
          by presburger
      qed
    qed

    moreover have \<open>(snd f) x = u\<^sub>E x\<close> if \<open>x \<notin> E\<^sub>G\<close> for x
      using \<open>case f of (u\<^sub>V, u\<^sub>E) \<Rightarrow> morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> m.integrity_e_alt morphism.dom_ge that u\<^sub>E_def by fastforce

    ultimately have \<open>fst f x = u\<^sub>V x \<and> snd f y = u\<^sub>E y\<close> for x and y
      by blast

    thus ?thesis
      using that
      by fastforce
  qed
qed
      

interpretation pushout_diagram
  V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K 
  V\<^sub>L E\<^sub>L s\<^sub>L s'\<^sub>L t\<^sub>L t'\<^sub>L l\<^sub>L l'\<^sub>L m\<^sub>L m'\<^sub>L
  V E s "totalize s" t "totalize t" l "totalize l" m "totalize m"
  V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G
  k\<^sub>V k'\<^sub>V k\<^sub>E k'\<^sub>E
  d\<^sub>V "totalize d\<^sub>V" d\<^sub>E "totalize d\<^sub>E"
  f\<^sub>V f'\<^sub>V f\<^sub>E f'\<^sub>E
  g\<^sub>V "totalize g\<^sub>V" g\<^sub>E "totalize g\<^sub>E"
proof
  show \<open>f\<^sub>V \<circ>\<^sub>m k\<^sub>V = g\<^sub>V \<circ>\<^sub>m d\<^sub>V\<close> (is "?f = ?g")
  proof -
    have \<open>?f x = ?g x\<close> if \<open>x \<notin> V\<^sub>K\<close> for x
      unfolding g\<^sub>V_def d\<^sub>V_def
      using i.dom_gv that by auto

    moreover have \<open>?f x = ?g x\<close> if \<open>x \<in> V\<^sub>K\<close> for x
      unfolding g\<^sub>V_def d\<^sub>V_def
      using d.integrity_v' d.v_morph_not_none d\<^sub>V_def i.inclusion_nodes_alt i.v_morph_not_none that by fastforce
      

    ultimately show ?thesis
      by blast
  qed
next
  show \<open>f\<^sub>E \<circ>\<^sub>m k\<^sub>E = g\<^sub>E \<circ>\<^sub>m d\<^sub>E\<close> (is "?f = ?g")
  proof -
    have \<open>?f x = ?g x\<close> if \<open>x \<notin> E\<^sub>K\<close> for x
      unfolding g\<^sub>E_def d\<^sub>E_def
      using i.dom_ge that by auto

    moreover have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<^sub>K\<close> for x
      unfolding g\<^sub>E_def d\<^sub>E_def
      using d.e_morph_not_none g\<^sub>E_def d\<^sub>E_def d.integrity_e' i.e_morph_not_none i.inclusion_edges_alt that by fastforce 

    ultimately show ?thesis
      by blast
  qed
next
  show \<open>\<And>V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V p\<^sub>E t\<^sub>V t\<^sub>E.
       \<lbrakk>graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H; morphism V\<^sub>L E\<^sub>L s\<^sub>L t\<^sub>L l\<^sub>L m\<^sub>L V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V p\<^sub>E; morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H t\<^sub>V t\<^sub>E; p\<^sub>V \<circ>\<^sub>m k\<^sub>V = t\<^sub>V \<circ>\<^sub>m d\<^sub>V;
        p\<^sub>E \<circ>\<^sub>m k\<^sub>E = t\<^sub>E \<circ>\<^sub>m d\<^sub>E\<rbrakk>
       \<Longrightarrow> \<exists>!(u\<^sub>V, u\<^sub>E). morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close>
    using univ_prop by blast
qed

end

end