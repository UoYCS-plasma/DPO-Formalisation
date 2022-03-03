theory Gluing
imports Pushout Morphism AuxLemmas
begin

section "Gluing"

text_raw \<open>
\begin{figure}[!htb]
  \centering
  \includegraphics{figs/fig-pushout-gluing.pdf}
  \caption{Gluing Pushout}
\end{figure}
\<close>


locale gluing =
  K: graph V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K +
  R: graph V\<^sub>R E\<^sub>R s\<^sub>R s'\<^sub>R t\<^sub>R t'\<^sub>R l\<^sub>R l'\<^sub>R m\<^sub>R m'\<^sub>R +
  D: graph V\<^sub>D E\<^sub>D s\<^sub>D s'\<^sub>D t\<^sub>D t'\<^sub>D l\<^sub>D l'\<^sub>D m\<^sub>D m'\<^sub>D +
  i: inclusion_morphism 
    V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K 
    V\<^sub>R E\<^sub>R s\<^sub>R s'\<^sub>R t\<^sub>R t'\<^sub>R l\<^sub>R l'\<^sub>R m\<^sub>R m'\<^sub>R
    k\<^sub>V k'\<^sub>V k\<^sub>E k'\<^sub>E +
  m: injective_morphism
    V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K 
    V\<^sub>D E\<^sub>D s\<^sub>D s'\<^sub>D t\<^sub>D t'\<^sub>D l\<^sub>D l'\<^sub>D m\<^sub>D m'\<^sub>D 
    f\<^sub>V f'\<^sub>V f\<^sub>E f'\<^sub>E
    for
    V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K 
    V\<^sub>R E\<^sub>R s\<^sub>R s'\<^sub>R t\<^sub>R t'\<^sub>R l\<^sub>R l'\<^sub>R m\<^sub>R m'\<^sub>R 
    V\<^sub>D E\<^sub>D s\<^sub>D s'\<^sub>D t\<^sub>D t'\<^sub>D l\<^sub>D l'\<^sub>D m\<^sub>D m'\<^sub>D
    k\<^sub>V k'\<^sub>V k\<^sub>E k'\<^sub>E
    f\<^sub>V f'\<^sub>V f\<^sub>E f'\<^sub>E
begin

abbreviation V where 
"V \<equiv> Inl ` V\<^sub>D \<union> Inr ` (V\<^sub>R - V\<^sub>K)"

abbreviation E where 
"E \<equiv> Inl ` E\<^sub>D \<union> Inr ` (E\<^sub>R - E\<^sub>K)"

fun s where
  "s (Inl e') = map_option Inl (s\<^sub>D e')"
| "s (Inr e') = (if e' \<in> E\<^sub>R - E\<^sub>K \<and> s'\<^sub>R e' \<in> V\<^sub>K
    then map_option Inl ((f\<^sub>V \<circ>\<^sub>m s\<^sub>R) e')
    else map_option Inr ((s\<^sub>R|`(E\<^sub>R-E\<^sub>K)) e'))"

lemma dom_s:
  shows \<open>dom s = E\<close>
proof -
  have \<open>s x \<noteq> None \<longleftrightarrow> x \<in> E\<close> for x
  proof (cases x)
    case (Inl a)
    then show ?thesis
      using D.integrity_s by auto
  next
    case (Inr b)
    then show ?thesis
      apply clarsimp
      apply (rule conjI)
      
      using R.integrity_s m.dom_gv apply force
      unfolding restrict_map_def
      by (simp add: R.integrity_s domD image_iff)
      
  qed
  then show ?thesis
    by blast
qed

lemma ran_s:
  shows \<open>ran s \<subseteq> V\<close>
proof -
  have \<open>s x = Some y \<longrightarrow> y \<in> V\<close> if \<open>x \<in> E\<close> for x and y
    proof (cases x)
      case (Inl a)
      then show ?thesis 
        using that D.integrity_s_alt by auto
    next
      case (Inr b)

      have \<open>(f\<^sub>V \<circ>\<^sub>m s\<^sub>R) b = Some c \<longrightarrow> (Inl c) \<in> V\<close> if \<open>b \<in> E\<^sub>R - E\<^sub>K \<and> s'\<^sub>R b \<in> V\<^sub>K\<close> for c
        using that Inr
        by (meson image_subset_iff m.integrity_v_alt map_comp_Some_iff sup_ge1)

      moreover have \<open>(s\<^sub>R|`(E\<^sub>R-E\<^sub>K)) b = Some c \<longrightarrow> (Inr c) \<in> V\<close> if \<open>b \<in> E\<^sub>R-E\<^sub>K \<and> s'\<^sub>R b \<notin> V\<^sub>K\<close> for c
        using that Inr R.integrity_s
        unfolding restrict_map_def
        by (metis Diff_iff R.integrity_s' R.s_def Un_iff image_subset_iff option.sel subsetI)

      ultimately show ?thesis 
        by (smt (verit, best) Inr map_option_eq_Some not_Some_eq restrict_map_def s.simps(2))
    qed

    moreover have \<open>s x = None\<close> if \<open>x \<notin> E\<close> for x
      using that dom_s
      by blast

    ultimately show ?thesis
      unfolding ran_def
      by (smt (z3) mem_Collect_eq option.distinct(1) subsetI)
  qed

fun t where
  "t (Inl e') = map_option Inl (t\<^sub>D e')"
| "t (Inr e') = (if e' \<in> E\<^sub>R - E\<^sub>K \<and> t'\<^sub>R e' \<in> V\<^sub>K
    then map_option Inl ((f\<^sub>V \<circ>\<^sub>m t\<^sub>R) e')
    else map_option Inr ((t\<^sub>R|` (E\<^sub>R-E\<^sub>K))e'))"

lemma dom_t:
  shows \<open>dom t = E\<close>
proof -
  have \<open>t x \<noteq> None \<longleftrightarrow> x \<in> E\<close> for x
  proof (cases x)
    case (Inl a)
    then show ?thesis
      using D.integrity_t by auto
  next
    case (Inr b)
    then show ?thesis
      apply clarsimp
      apply (rule conjI)
      
      using R.integrity_t m.dom_gv apply force
      unfolding restrict_map_def
      by (simp add: R.integrity_t domD image_iff)
      
  qed
  then show ?thesis
    by blast
qed

lemma ran_t:
  shows \<open>ran t \<subseteq> V\<close>
  proof -
   have \<open>t x = Some y \<longrightarrow> y \<in> V\<close> if \<open>x \<in> E\<close> for x and y
    proof (cases x)
    case (Inl a)
    then show ?thesis
      using that D.integrity_t_alt by auto
    next
      case (Inr b)
  
      have \<open>(f\<^sub>V \<circ>\<^sub>m t\<^sub>R) b = Some c \<longrightarrow> (Inl c) \<in> V\<close> if \<open>b \<in> E\<^sub>R - E\<^sub>K \<and> t'\<^sub>R b \<in> V\<^sub>K\<close> for c
        using that Inr
        by (meson image_subset_iff m.integrity_v_alt map_comp_Some_iff sup_ge1)
   
      moreover have \<open>(t\<^sub>R|`(E\<^sub>R-E\<^sub>K)) b = Some c \<longrightarrow> (Inr c) \<in> V\<close> if \<open>b \<in> E\<^sub>R-E\<^sub>K \<and> t'\<^sub>R b \<notin> V\<^sub>K\<close> for c
          using that Inr R.integrity_s
          unfolding restrict_map_def
          by (metis Diff_iff R.integrity_t' R.t_def Un_iff image_subset_iff option.sel subsetI)
  
        ultimately show ?thesis 
          by (smt (verit, best) Inr map_option_eq_Some not_Some_eq restrict_map_def t.simps(2))
   qed
  
    moreover have \<open>t x = None\<close> if \<open>x \<notin> E\<close> for x
      using that dom_t
      by blast

    ultimately show ?thesis
      by (smt (z3) mem_Collect_eq option.simps(3) ran_def subsetI)
  qed


abbreviation l where
"l \<equiv> case_sum l\<^sub>D (l\<^sub>R |` (V\<^sub>R-V\<^sub>K))"

lemma dom_l:
  shows "dom l = V"
proof -
  have "l x \<noteq> None \<longleftrightarrow> x \<in> V" for x
  proof (cases x)
    case (Inl a)
    then show ?thesis 
      using D.integrity_l by auto
  next
    case (Inr b)
    then show ?thesis    
      unfolding restrict_map_def
      using  R.integrity_l by auto
  qed
  thus ?thesis 
    by blast
qed

abbreviation m where
"m \<equiv> case_sum m\<^sub>D (m\<^sub>R |` (E\<^sub>R-E\<^sub>K))"


lemma dom_m:
  shows "dom m = E"
proof -
  have "m x \<noteq> None \<longleftrightarrow> x \<in> E" for x
  proof (cases x)
    case (Inl a)
    then show ?thesis 
      using D.integrity_m by auto
  next
    case (Inr b)
    then show ?thesis 
      unfolding restrict_map_def
      using R.integrity_m by auto
  qed
  thus ?thesis
    by blast
qed


interpretation object: graph V E s "totalize s" t "totalize t" l "totalize l" m "totalize m"
proof unfold_locales
  show \<open>finite V\<close>
    using D.finite_nodes R.finite_nodes by blast
next
  show \<open>finite E\<close>
    using D.finite_edges R.finite_edges by blast
next
  show \<open>dom s = E \<and> ran s \<subseteq> V\<close>
    using dom_s ran_s by blast
next
  show \<open>dom t = E \<and> ran t \<subseteq> V\<close>
    using dom_t ran_t by blast
next
  show \<open>dom l = V\<close>
    using dom_l by blast
next
  show \<open>dom m = E\<close>
    using dom_m by blast
qed simp_all

text \<open>Morphism from R to pushout object\<close>

definition h\<^sub>V where
"h\<^sub>V \<equiv> \<lambda>v. if v \<in> V\<^sub>R - V\<^sub>K then Some (Inr v) else map_option Inl (f\<^sub>V v)"

lemma dom_h\<^sub>V:
  shows \<open>dom h\<^sub>V = V\<^sub>R\<close>
  unfolding h\<^sub>V_def
  using i.v_inclusion_alt m.dom_gv by force

definition h\<^sub>E where
"h\<^sub>E \<equiv> \<lambda>e. if e \<in> E\<^sub>R - E\<^sub>K then Some (Inr e) else map_option Inl (f\<^sub>E e)"

lemma dom_h\<^sub>E:
  shows \<open>dom h\<^sub>E = E\<^sub>R\<close>
  unfolding h\<^sub>E_def
  using i.e_inclusion_alt m.dom_ge by force


interpretation h: injective_morphism 
  V\<^sub>R E\<^sub>R s\<^sub>R "totalize s\<^sub>R" t\<^sub>R "totalize t\<^sub>R" l\<^sub>R "totalize l\<^sub>R" m\<^sub>R "totalize m\<^sub>R"
  V E s "totalize s" t "totalize t" l "totalize l" m "totalize m"
  h\<^sub>V "totalize h\<^sub>V" h\<^sub>E "totalize h\<^sub>E"
proof intro_locales
  show \<open>morphism_axioms V\<^sub>R E\<^sub>R s\<^sub>R t\<^sub>R l\<^sub>R m\<^sub>R V E s t l m h\<^sub>V h\<^sub>E\<close>
  proof
    show \<open>dom h\<^sub>V = V\<^sub>R \<and> ran h\<^sub>V \<subseteq> V\<close>
    proof
      show \<open>dom h\<^sub>V = V\<^sub>R\<close>
        using dom_h\<^sub>V by blast
    next
      show \<open>ran h\<^sub>V \<subseteq> V\<close>
        unfolding ran_def h\<^sub>V_def
        using m.integrity_v_alt by auto
    qed
  next
    show \<open>dom h\<^sub>E = E\<^sub>R \<and> ran h\<^sub>E \<subseteq> E\<close>
    proof
      show \<open>dom h\<^sub>E = E\<^sub>R\<close>
        using dom_h\<^sub>E by blast
    next
      show \<open>ran h\<^sub>E \<subseteq> E\<close>
        unfolding ran_def h\<^sub>E_def
        using m.integrity_s_alt by auto
    qed
  next
    show \<open>h\<^sub>V \<circ>\<^sub>m s\<^sub>R = s \<circ>\<^sub>m h\<^sub>E\<close> (is "?f = ?g")
    proof -
      have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<^sub>R- E\<^sub>K\<close> for x
        unfolding h\<^sub>V_def h\<^sub>E_def
        using that R.integrity_s R.integrity_s_alt map_comp_simps(2) by auto

      moreover have \<open>?f x = ?g x\<close> if \<open>x \<notin> E\<^sub>R- E\<^sub>K\<close> for x
        unfolding h\<^sub>V_def h\<^sub>E_def
        using that
        by (smt (z3) D.integrity_s D.s_def Diff_iff K.integrity_s' R.integrity_s R.s_def domIff i.e_inclusion_alt i.s_equality_alt i.s_inclusion m.dom_ge m.g\<^sub>V_def m.g\<^sub>E_def m.integrity_e' m.source_preserve_alt m.v_morph_not_none map_comp_simps(1) map_comp_simps(2) map_option_is_None option.exhaust_sel option.simps(9) s.simps(1))

      ultimately show ?thesis
        by blast
    qed
  next
    show \<open>h\<^sub>V \<circ>\<^sub>m t\<^sub>R = t \<circ>\<^sub>m h\<^sub>E\<close> (is "?f = ?g")
    proof -
      have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<^sub>R- E\<^sub>K\<close> for x
        unfolding h\<^sub>V_def h\<^sub>E_def
        using that R.integrity_t R.integrity_t_alt map_option_case by auto

      moreover have \<open>?f x = ?g x\<close> if \<open>x \<notin> E\<^sub>R- E\<^sub>K\<close> for x
        using that 
        unfolding h\<^sub>V_def h\<^sub>E_def
        by (smt (z3) D.integrity_t D.t_def Diff_iff K.integrity_t' R.integrity_t R.t_def domIff i.e_inclusion_alt i.t_equality_alt i.t_inclusion m.dom_ge m.g\<^sub>V_def m.g\<^sub>E_def m.integrity_e' m.target_preserve_alt m.v_morph_not_none map_comp_simps(1) map_comp_simps(2) map_option_is_None option.exhaust_sel option.simps(9) t.simps(1))

      ultimately show ?thesis
        by blast
    qed
  next
    show \<open>l\<^sub>R = l \<circ>\<^sub>m h\<^sub>V\<close> (is "?f = ?g")
    proof -
      have \<open>?f x = ?g x\<close> if \<open>x \<in> V\<^sub>R- V\<^sub>K\<close> for x
        unfolding h\<^sub>V_def
        using that by auto

      moreover have \<open>?f x = ?g x\<close> if \<open>x \<notin> V\<^sub>R- V\<^sub>K\<close> for x
        unfolding h\<^sub>V_def
        by (smt (z3) Diff_iff R.integrity_l domIff dom_h\<^sub>V h\<^sub>V_def i.l_inclusion m.node_label_preserve map_comp_simps(1) map_comp_simps(2) old.sum.simps(5) option.collapse option.map_sel restrict_in that)

      ultimately show ?thesis
        by blast
    qed
  next
    show \<open>m\<^sub>R = m \<circ>\<^sub>m h\<^sub>E\<close> (is "?f = ?g")
    proof -
      have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<^sub>R- E\<^sub>K\<close> for x
        unfolding h\<^sub>E_def
        using that by auto

      moreover have \<open>?f x = ?g x\<close> if \<open>x \<notin> E\<^sub>R- E\<^sub>K\<close> for x
        using that
        unfolding h\<^sub>E_def
        by (smt (z3) Diff_iff R.integrity_m domIff dom_h\<^sub>E h\<^sub>E_def i.m_inclusion m.edge_label_preserve map_comp_simps(1) map_comp_simps(2) old.sum.simps(5) option.collapse option.map_sel restrict_in)

      ultimately show ?thesis
        by blast
    qed
  qed
next
  show \<open>injective_morphism_axioms V\<^sub>R E\<^sub>R h\<^sub>V h\<^sub>E\<close>
  proof
    show \<open>inj_on (totalize h\<^sub>V) V\<^sub>R\<close>
      unfolding h\<^sub>V_def
      by (smt (z3) Diff_iff Inl_Inr_False Inl_inject domD inj_on_def m.dom_gv m.node_injectivity m.g\<^sub>V_def old.sum.inject(2) option.sel option.simps(9))
  next
    show \<open>inj_on (totalize h\<^sub>E) E\<^sub>R\<close>
      unfolding h\<^sub>E_def
      by (smt (z3) Diff_iff Inl_Inr_False Inl_inject domD inj_on_def m.dom_ge m.edge_injectivity m.g\<^sub>E_def old.sum.inject(2) option.sel option.simps(9))
  qed
qed simp_all


text \<open>Morphism from D to pushout object\<close>

definition j\<^sub>V where
"j\<^sub>V \<equiv> \<lambda>v. if v \<in> V\<^sub>D then Some (Inl v) else None"

definition j\<^sub>E where
"j\<^sub>E \<equiv> \<lambda>e. if e \<in> E\<^sub>D then Some (Inl e) else None"

interpretation j: injective_morphism 
  V\<^sub>D E\<^sub>D s\<^sub>D "totalize s\<^sub>D" t\<^sub>D "totalize t\<^sub>D" l\<^sub>D "totalize l\<^sub>D" m\<^sub>D "totalize m\<^sub>D"
  V E s "totalize s" t "totalize t" l "totalize l" m "totalize m"
  j\<^sub>V "totalize j\<^sub>V"
  j\<^sub>E "totalize j\<^sub>E"
proof intro_locales
  show \<open>morphism_axioms V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V E s t l m j\<^sub>V j\<^sub>E\<close>
  proof
    show \<open>dom j\<^sub>V = V\<^sub>D \<and> ran j\<^sub>V \<subseteq> V\<close>
    proof
      show \<open>dom j\<^sub>V = V\<^sub>D\<close>
        unfolding dom_def j\<^sub>V_def
        by simp
    next
      show \<open>ran j\<^sub>V \<subseteq> V\<close>
        unfolding ran_def j\<^sub>V_def
        by auto
    qed
  next
    show \<open>dom j\<^sub>E = E\<^sub>D \<and> ran j\<^sub>E \<subseteq> E\<close>
    proof
      show \<open>dom j\<^sub>E = E\<^sub>D\<close>
        unfolding dom_def j\<^sub>E_def
        by simp
    next
      show \<open>ran j\<^sub>E \<subseteq> E\<close>
        unfolding ran_def j\<^sub>E_def
        by auto
    qed
  next
    show \<open>j\<^sub>V \<circ>\<^sub>m s\<^sub>D = s \<circ>\<^sub>m j\<^sub>E\<close>
      unfolding map_comp_def j\<^sub>V_def j\<^sub>E_def
      using D.integrity_s D.integrity_s_alt domIff by fastforce
  next
    show \<open>j\<^sub>V \<circ>\<^sub>m t\<^sub>D = t \<circ>\<^sub>m j\<^sub>E\<close>
      unfolding map_comp_def j\<^sub>V_def j\<^sub>E_def
      using D.integrity_t D.integrity_t_alt domIff by fastforce
  next
    show \<open>l\<^sub>D = l \<circ>\<^sub>m j\<^sub>V\<close>
      unfolding map_comp_def j\<^sub>V_def
      using D.integrity_l by fastforce
  next
    show \<open>m\<^sub>D = m \<circ>\<^sub>m j\<^sub>E\<close>
      unfolding map_comp_def j\<^sub>E_def
      using D.integrity_m by fastforce
  qed
next
  show \<open>injective_morphism_axioms V\<^sub>D E\<^sub>D j\<^sub>V j\<^sub>E\<close>
  proof
    show \<open>inj_on (totalize j\<^sub>V) V\<^sub>D\<close>
      unfolding j\<^sub>V_def
      by (smt (verit, ccfv_threshold) Inl_inject inj_onI option.sel)
  next
    show \<open>inj_on (totalize j\<^sub>E) E\<^sub>D\<close>
      unfolding j\<^sub>E_def
      by (smt (verit, ccfv_threshold) Inl_inject inj_onI option.sel)
  qed
qed

 lemma univ_prop:
  assumes 
    H: "graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H" and
    h': "morphism V\<^sub>R E\<^sub>R s\<^sub>R t\<^sub>R l\<^sub>R m\<^sub>R V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V p\<^sub>E" and
    c': "morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H t\<^sub>V t\<^sub>E" and
    commutativity_v: "p\<^sub>V \<circ>\<^sub>m k\<^sub>V = t\<^sub>V \<circ>\<^sub>m f\<^sub>V" and
    commutativity_e: "p\<^sub>E \<circ>\<^sub>m k\<^sub>E = t\<^sub>E \<circ>\<^sub>m f\<^sub>E"
  shows \<open>\<exists>!(u\<^sub>V, u\<^sub>E). 
        morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> 
        u\<^sub>V \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> 
        u\<^sub>V \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close>

proof
  define u\<^sub>V where \<open>u\<^sub>V = case_sum t\<^sub>V (p\<^sub>V |` (V\<^sub>R-V\<^sub>K))\<close> 
  define u\<^sub>E where \<open>u\<^sub>E = case_sum t\<^sub>E (p\<^sub>E |` (E\<^sub>R-E\<^sub>K))\<close>

show \<open>case (u\<^sub>V, u\<^sub>E) of (u\<^sub>V, u\<^sub>E) \<Rightarrow> morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close>
  proof (simp, intro conjI)
    show \<open>morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E\<close>
    proof intro_locales
      show \<open>graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close>
        using H by auto
    next
      show \<open>morphism_axioms V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E\<close>
      proof
        show \<open>dom u\<^sub>V = V \<and> ran u\<^sub>V \<subseteq> V\<^sub>H\<close>
        proof
          show \<open>dom u\<^sub>V = V\<close>
          proof -
            have \<open>u\<^sub>V x \<noteq> None \<longleftrightarrow> x \<in> V\<close> for x
            proof (cases x)
              case (Inl a)
              then show ?thesis
                unfolding u\<^sub>V_def
                by (metis Inl_Inr_False Un_iff c' domIff image_iff morphism.dom_gv old.sum.simps(5))
            next
              case (Inr b)
              then show ?thesis
                  unfolding u\<^sub>V_def
                  using domIff h' image_iff morphism.dom_gv by fastforce
              qed
              thus ?thesis
                by blast
            qed
          next
            show \<open>ran u\<^sub>V \<subseteq> V\<^sub>H\<close>
            proof -

              have \<open>ran t\<^sub>V \<subseteq> V\<^sub>H\<close>
                by (meson assms(3) morphism.ran_gv)

             moreover have \<open>ran p\<^sub>V \<subseteq> V\<^sub>H\<close>
               by (meson assms(2) morphism.ran_gv)

             ultimately show ?thesis
               using assms
               unfolding u\<^sub>V_def
               by (metis case_sum_ran_childs ranI ran_restrictD subset_iff)
           qed
         qed
       next
         show \<open>dom u\<^sub>E = E \<and> ran u\<^sub>E \<subseteq> E\<^sub>H\<close>
         proof
           show \<open>dom u\<^sub>E = E\<close>
           proof -
            have \<open>u\<^sub>E x \<noteq> None \<longleftrightarrow> x \<in> E\<close> for x
            proof (cases x)
              case (Inl a)
              then show ?thesis
                unfolding u\<^sub>E_def
                by (metis Inl_Inr_False Un_iff c' domIff image_iff morphism.dom_ge old.sum.simps(5))
              next
                case (Inr b)
                then show ?thesis
                  unfolding u\<^sub>E_def
                  using domIff h' image_iff morphism.dom_ge by fastforce
              qed
              thus ?thesis
                by blast
            qed
          next
            show \<open>ran u\<^sub>E \<subseteq> E\<^sub>H\<close>
            proof -
              have \<open>ran t\<^sub>E \<subseteq> E\<^sub>H\<close>
                by (meson c' morphism.ran_ge)

              moreover have \<open>ran p\<^sub>E \<subseteq> E\<^sub>H\<close>
                by (meson h' morphism.ran_ge)

              ultimately show ?thesis
                unfolding u\<^sub>E_def
                by (metis case_sum_ran_childs ranI ran_restrictD subset_eq)
            qed
          qed
        next
          show \<open>u\<^sub>V \<circ>\<^sub>m s = s\<^sub>H \<circ>\<^sub>m u\<^sub>E\<close> (is "?f = ?g")
          proof -
            have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<close> for x
            proof -
              consider
                (a) \<open>\<exists>y \<in> E\<^sub>D. x = Inl y\<close>
              | (b) \<open>\<exists>y \<in> E\<^sub>R-E\<^sub>K. x = Inr y \<and> s'\<^sub>R y \<in> V\<^sub>K\<close>
              | (c) \<open>\<exists>y \<in> E\<^sub>R-E\<^sub>K. x = Inr y \<and> s'\<^sub>R y \<in> V\<^sub>R - V\<^sub>K\<close>
                by (metis Diff_iff R.integrity_s' Un_iff \<open>x \<in> E\<close> image_iff)
              thus ?thesis
              proof cases
                case a

                obtain y where \<open>y \<in> E\<^sub>D \<and> x = Inl y\<close>
                  using a by blast
                
                let ?s\<^sub>D = \<open>\<lambda>v. map_option Inl (s\<^sub>D v) :: ('e + 'a) option\<close>

                have \<open>?f x =  (u\<^sub>V \<circ>\<^sub>m ?s\<^sub>D) y\<close>
                  using that a
                  unfolding map_comp_def
                  using \<open>y \<in> E\<^sub>D \<and> x = Inl y\<close> s.simps(1) by presburger

                also have \<open>... = (t\<^sub>V \<circ>\<^sub>m s\<^sub>D) y\<close>
                  using that a
                  unfolding map_comp_def u\<^sub>V_def
                  using \<open>y \<in> E\<^sub>D \<and> x = Inl y\<close> j.G.integrity_s by fastforce

                also have \<open>... = (s\<^sub>H \<circ>\<^sub>m t\<^sub>E) y\<close>
                  using c' morphism.source_preserve
                  by fastforce

                also have \<open>... = (s\<^sub>H \<circ>\<^sub>m u\<^sub>E) x\<close>
                  using that a
                  unfolding map_comp_def u\<^sub>E_def
                  by (simp add: \<open>y \<in> E\<^sub>D \<and> x = Inl y\<close>)

                finally show ?thesis .
              next
                case b

                obtain y where \<open>y \<in> E\<^sub>R-E\<^sub>K \<and> x = Inr y \<and> s'\<^sub>R y \<in> V\<^sub>K\<close>
                  using b by blast

                let ?tt = \<open>\<lambda>v. map_option Inl ((f\<^sub>V \<circ>\<^sub>m s\<^sub>R) v)\<close>

                have \<open>?f x = (u\<^sub>V \<circ>\<^sub>m ?tt) y\<close>
                  using b \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> s'\<^sub>R y \<in> V\<^sub>K\<close> s.simps
                  unfolding map_comp_def
                  by metis

                also have \<open>... = (t\<^sub>V \<circ>\<^sub>m f\<^sub>V \<circ>\<^sub>m s\<^sub>R) y\<close>
                  using b
                  unfolding map_comp_def u\<^sub>V_def
                  by (metis Diff_iff R.s_def \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> s'\<^sub>R y \<in> V\<^sub>K\<close> domD h.G.integrity_s m.v_morph_not_none old.sum.simps(5) option.case_eq_if option.distinct(1) option.exhaust_sel option.sel option.simps(9))

                also have \<open>... = (p\<^sub>V \<circ>\<^sub>m k\<^sub>V \<circ>\<^sub>m s\<^sub>R) y\<close>
                  using b commutativity_v
                  unfolding map_comp_def
                  by metis

                also have \<open>... = (p\<^sub>V \<circ>\<^sub>m s\<^sub>R) y\<close>
                  using b
                  unfolding map_comp_def
                  by (metis R.s_def \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> s'\<^sub>R y \<in> V\<^sub>K\<close> i.g\<^sub>V_def i.inclusion_nodes i.v_morph_not_none option.case_eq_if)

                also have \<open>... = (s\<^sub>H \<circ>\<^sub>m p\<^sub>E) y\<close>
                  using b
                  unfolding map_comp_def
                  by (metis h' map_comp_def morphism.source_preserve)

                also have \<open>... = ?g x\<close>
                  using b
                  unfolding map_comp_def u\<^sub>E_def
                  by (metis \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> s'\<^sub>R y \<in> V\<^sub>K\<close> old.sum.simps(6) restrict_in)

                finally show ?thesis .
              next
                case c
                obtain y where \<open>y \<in> E\<^sub>R-E\<^sub>K \<and> x = Inr y \<and> s'\<^sub>R y \<in> V\<^sub>R - V\<^sub>K\<close>
                  using c by blast

                let ?s\<^sub>R = \<open>\<lambda>v. map_option Inr (s\<^sub>R v) :: ('e + 'a) option\<close>

                have \<open>?f x = (u\<^sub>V \<circ>\<^sub>m ?s\<^sub>R) y\<close>
                  using c
                  unfolding map_comp_def
                  by (metis Diff_iff \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> s'\<^sub>R y \<in> V\<^sub>R - V\<^sub>K\<close> restrict_in s.simps(2))

                also have \<open>\<dots> = (p\<^sub>V \<circ>\<^sub>m s\<^sub>R) y\<close>
                  using c
                  unfolding map_comp_def u\<^sub>V_def
                  by (metis R.s_def \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> s'\<^sub>R y \<in> V\<^sub>R - V\<^sub>K\<close> map_option_case old.sum.simps(6) option.case_eq_if option.simps(5) restrict_in)

                also have \<open>\<dots> = (s\<^sub>H \<circ>\<^sub>m p\<^sub>E) y\<close>
                  using c
                  unfolding map_comp_def
                  by (metis h' map_comp_def morphism.source_preserve)

                also have \<open>\<dots> = ?g x\<close>
                  using c
                  unfolding map_comp_def u\<^sub>E_def
                  by (metis \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> s'\<^sub>R y \<in> V\<^sub>R - V\<^sub>K\<close> old.sum.simps(6) restrict_in)

                finally show ?thesis .
              qed
            qed

            moreover have \<open>?f x = ?g x\<close> if \<open>x \<notin> E\<close> for x
            proof (cases x)
              case (Inl a)
              then show ?thesis 
                using that
                unfolding map_comp_def u\<^sub>E_def
                by (smt (verit, best) Inr_Inl_False None_eq_map_option_iff c' domIff dom_s j.G.integrity_s morphism.dom_ge old.sum.simps(5) option.simps(4) s.elims)
            next
              case (Inr b)
              then show ?thesis
                using that restrict_out
                unfolding map_comp_def u\<^sub>V_def u\<^sub>E_def
                by (smt (verit, ccfv_SIG) UnCI dom_def dom_s image_iff mem_Collect_eq old.sum.simps(6) option.simps(4))

            qed

            moreover have \<open>?f x = ?g x\<close> for x
              by (meson calculation(1) calculation(2))

            ultimately show ?thesis
              by auto            
          qed
        next
          show \<open>u\<^sub>V \<circ>\<^sub>m t = t\<^sub>H \<circ>\<^sub>m u\<^sub>E\<close> (is "?f = ?g")
          proof -
            have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<close> for x
            proof -
              consider
                (a) \<open>\<exists>y \<in> E\<^sub>D. x = Inl y\<close>
              | (b) \<open>\<exists>y \<in> E\<^sub>R-E\<^sub>K. x = Inr y \<and> t'\<^sub>R y \<in> V\<^sub>K\<close>
              | (c) \<open>\<exists>y \<in> E\<^sub>R-E\<^sub>K. x = Inr y \<and> t'\<^sub>R y \<in> V\<^sub>R - V\<^sub>K\<close>
                by (metis Diff_iff R.integrity_t' Un_iff \<open>x \<in> E\<close> image_iff)
              thus ?thesis
              proof cases
                case a

                obtain y where \<open>y \<in> E\<^sub>D \<and> x = Inl y\<close>
                  using a by blast
                
                let ?t\<^sub>D = \<open>\<lambda>v. map_option Inl (t\<^sub>D v) :: ('e + 'a) option\<close>

                have \<open>?f x =  (u\<^sub>V \<circ>\<^sub>m ?t\<^sub>D) y\<close>
                  using that a
                  unfolding map_comp_def
                  using \<open>y \<in> E\<^sub>D \<and> x = Inl y\<close> t.simps(1) by presburger

                also have \<open>... = (t\<^sub>V \<circ>\<^sub>m t\<^sub>D) y\<close>
                  using that a
                  unfolding map_comp_def u\<^sub>V_def
                  using \<open>y \<in> E\<^sub>D \<and> x = Inl y\<close> j.G.integrity_t by fastforce

                also have \<open>... = (t\<^sub>H \<circ>\<^sub>m t\<^sub>E) y\<close>
                  using c' morphism.target_preserve
                  by fastforce

                also have \<open>... = (t\<^sub>H \<circ>\<^sub>m u\<^sub>E) x\<close>
                  using that a
                  unfolding map_comp_def u\<^sub>E_def
                  by (simp add: \<open>y \<in> E\<^sub>D \<and> x = Inl y\<close>)

                finally show ?thesis .
              next
                case b

                obtain y where \<open>y \<in> E\<^sub>R-E\<^sub>K \<and> x = Inr y \<and> t'\<^sub>R y \<in> V\<^sub>K\<close>
                  using b by blast

                let ?tt = \<open>\<lambda>v. map_option Inl ((f\<^sub>V \<circ>\<^sub>m t\<^sub>R) v)\<close>

                have \<open>?f x = (u\<^sub>V \<circ>\<^sub>m ?tt) y\<close>
                  using b \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> t'\<^sub>R y \<in> V\<^sub>K\<close> s.simps
                  unfolding map_comp_def
                  by (metis map_comp_def t.simps(2))

                also have \<open>... = (t\<^sub>V \<circ>\<^sub>m f\<^sub>V \<circ>\<^sub>m t\<^sub>R) y\<close>
                  using b
                  unfolding map_comp_def u\<^sub>V_def
                  by (metis Diff_iff R.t_def \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> t'\<^sub>R y \<in> V\<^sub>K\<close> domD h.G.integrity_t m.v_morph_not_none old.sum.simps(5) option.case_eq_if option.distinct(1) option.exhaust_sel option.sel option.simps(9))

                also have \<open>... = (p\<^sub>V \<circ>\<^sub>m k\<^sub>V \<circ>\<^sub>m t\<^sub>R) y\<close>
                  using b commutativity_v
                  unfolding map_comp_def
                  by metis

                also have \<open>... = (p\<^sub>V \<circ>\<^sub>m t\<^sub>R) y\<close>
                  using b
                  unfolding map_comp_def
                  by (metis R.t_def \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> t'\<^sub>R y \<in> V\<^sub>K\<close> i.g\<^sub>V_def i.inclusion_nodes i.v_morph_not_none option.case_eq_if)

                also have \<open>... = (t\<^sub>H \<circ>\<^sub>m p\<^sub>E) y\<close>
                  using b
                  unfolding map_comp_def
                  by (metis h' map_comp_def morphism.target_preserve)

                also have \<open>... = ?g x\<close>
                  using b
                  unfolding map_comp_def u\<^sub>E_def
                  by (metis \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> t'\<^sub>R y \<in> V\<^sub>K\<close> old.sum.simps(6) restrict_in)

                finally show ?thesis .
              next
                case c
                obtain y where \<open>y \<in> E\<^sub>R-E\<^sub>K \<and> x = Inr y \<and> t'\<^sub>R y \<in> V\<^sub>R - V\<^sub>K\<close>
                  using c by blast

                let ?t\<^sub>R = \<open>\<lambda>v. map_option Inr (t\<^sub>R v) :: ('e + 'a) option\<close>

                have \<open>?f x = (u\<^sub>V \<circ>\<^sub>m ?t\<^sub>R) y\<close>
                  using c
                  unfolding map_comp_def
                  by (metis Diff_iff \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> t'\<^sub>R y \<in> V\<^sub>R - V\<^sub>K\<close> restrict_in t.simps(2))

                also have \<open>... = (p\<^sub>V \<circ>\<^sub>m t\<^sub>R) y\<close>
                  using c
                  unfolding map_comp_def u\<^sub>V_def
                  by (metis R.t_def \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> t'\<^sub>R y \<in> V\<^sub>R - V\<^sub>K\<close> map_option_case old.sum.simps(6) option.case_eq_if option.simps(5) restrict_in)

                also have \<open>... = (t\<^sub>H \<circ>\<^sub>m p\<^sub>E) y\<close>
                  using c
                  unfolding map_comp_def
                  by (metis h' map_comp_def morphism.target_preserve)

                also have \<open>... = ?g x\<close>
                  using c
                  unfolding map_comp_def u\<^sub>E_def
                  by (metis \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> x = Inr y \<and> t'\<^sub>R y \<in> V\<^sub>R - V\<^sub>K\<close> old.sum.simps(6) restrict_in)

                finally show ?thesis .
              qed
            qed

            moreover have \<open>?f x = ?g x\<close> if \<open>x \<notin> E\<close> for x
            proof (cases x)
              case (Inl a)
              then show ?thesis 
                using that
                unfolding map_comp_def u\<^sub>V_def u\<^sub>E_def
                by (smt (verit, best) Inr_Inl_False None_eq_map_option_iff c' domIff dom_t j.G.integrity_t morphism.dom_ge old.sum.simps(5) option.simps(4) t.elims)
            next
              case (Inr b)
              then show ?thesis
                using that restrict_out
                unfolding map_comp_def u\<^sub>V_def u\<^sub>E_def
                by (metis (no_types, lifting) Un_iff domI dom_t image_iff old.sum.simps(6) option.exhaust_sel option.simps(4))

            qed

            moreover have \<open>?f x = ?g x\<close> for x
              by (meson calculation(1) calculation(2))

            ultimately show ?thesis
              by auto            
          qed
        next
          show \<open>l = l\<^sub>H \<circ>\<^sub>m u\<^sub>V\<close> (is "_ = ?g")
          proof -
            have \<open>l x = ?g x\<close> if \<open>x \<in> V\<close> for x
            proof (cases x)
              case (Inl a)

              have \<open>?g x = (l\<^sub>H \<circ>\<^sub>m t\<^sub>V) a\<close>
                unfolding map_comp_def u\<^sub>V_def
                using Inl by force

              also have \<open>... = l\<^sub>D a\<close>
                using c' morphism.node_label_preserve by blast

              also have \<open>... = l x\<close>
                using Inl by force

              finally show ?thesis ..

            next
              case (Inr b)

              have \<open>?g x = (l\<^sub>H \<circ>\<^sub>m p\<^sub>V) b\<close>
                unfolding map_comp_def u\<^sub>V_def
                using Inr that by fastforce

              also have \<open>... = l\<^sub>R b\<close>
                using h' morphism.node_label_preserve by blast

              also have \<open>... = l x\<close>
                using Inr that by fastforce

              finally show ?thesis ..
            qed
            moreover have \<open>l x = ?g x\<close> if \<open>x \<notin> V\<close> for x
            proof (cases x)
              case (Inl a)
              then show ?thesis
                unfolding u\<^sub>V_def
                by (metis c' map_comp_def morphism.node_label_preserve old.sum.simps(5))
            next
              case (Inr b)
              then show ?thesis
                unfolding u\<^sub>V_def
                by (metis UnCI image_iff map_comp_simps(1) old.sum.simps(6) restrict_map_def that)
            qed

            moreover have \<open>l x = ?g x\<close> for x
              by (meson calculation(1) calculation(2))

            ultimately show ?thesis
              by auto            
          qed
        next
          show \<open>m = m\<^sub>H \<circ>\<^sub>m u\<^sub>E\<close> (is "_ = ?g")
          proof -
            have \<open>m x = ?g x\<close> if \<open>x \<in> E\<close> for x
            proof (cases x)
              case (Inl a)

              have \<open>?g x = (m\<^sub>H \<circ>\<^sub>m t\<^sub>E) a\<close>
                unfolding map_comp_def u\<^sub>E_def
                using Inl by force

              also have \<open>... = m\<^sub>D a\<close>
                using c' morphism.edge_label_preserve by blast

              also have \<open>... = m x\<close>
                using Inl by force

              finally show ?thesis ..

            next
              case (Inr b)

              have \<open>?g x = (m\<^sub>H \<circ>\<^sub>m p\<^sub>E) b\<close>
                unfolding map_comp_def u\<^sub>E_def
                using Inr that by fastforce

              also have \<open>... = m\<^sub>R b\<close>
                using h' morphism.edge_label_preserve by blast

              also have \<open>... = m x\<close>
                using Inr that by fastforce

              finally show ?thesis ..
            qed
            moreover have \<open>m x = ?g x\<close> if \<open>x \<notin> E\<close> for x
            proof (cases x)
              case (Inl a)
              then show ?thesis
                unfolding u\<^sub>E_def
                by (metis c' map_comp_def morphism.edge_label_preserve old.sum.simps(5))
            next
              case (Inr b)
              then show ?thesis
                unfolding u\<^sub>E_def
                by (metis UnCI image_iff map_comp_simps(1) old.sum.simps(6) restrict_map_def that)
            qed

            moreover have \<open>m x = ?g x\<close> for x
              by (meson calculation(1) calculation(2))

            ultimately show ?thesis
              by auto            
          qed
        qed
      qed
    next

      show \<open>u\<^sub>V \<circ>\<^sub>m h\<^sub>V = p\<^sub>V\<close> (is "?f = ?g")
      proof -
        have \<open>?f x = ?g x\<close> if \<open>x \<in> V\<^sub>R\<close> for x
        proof -
          consider
              (a) \<open>x \<in> V\<^sub>R-V\<^sub>K\<close> 
            | (b) \<open>x \<in> V\<^sub>K\<close>
            using \<open>x \<in> V\<^sub>R\<close> by blast
          then show ?thesis
        proof (cases)
          case a
          then show ?thesis
            unfolding u\<^sub>V_def h\<^sub>V_def
            by force
        next
          case b
          let ?f\<^sub>V = \<open>\<lambda>v. map_option Inl (f\<^sub>V v)\<close>
          have \<open>?f x = (u\<^sub>V \<circ>\<^sub>m ?f\<^sub>V) x\<close>
            using b
            unfolding map_comp_def h\<^sub>V_def
            by simp

          also have \<open>... = (t\<^sub>V \<circ>\<^sub>m f\<^sub>V) x\<close>
            using b
            unfolding map_comp_def u\<^sub>V_def
            using m.dom_gv by force

          also have \<open>... = (p\<^sub>V \<circ>\<^sub>m k\<^sub>V) x\<close>
            using b
            unfolding map_comp_def
            by (metis commutativity_v map_comp_def)

          also have \<open>... = p\<^sub>V x\<close>
            using b
            unfolding map_comp_def
            by (metis i.g\<^sub>V_def i.inclusion_nodes i.v_morph_not_none option.case_eq_if)

          finally show ?thesis .
        qed
      qed
      moreover have \<open>?f x = ?g x\<close> if \<open>x \<notin> V\<^sub>R\<close> for x
        unfolding map_comp_def
        using that
        by (smt (z3) DiffD1 domIff h' h.dom_gv morphism.dom_gv option.case_eq_if)

      moreover have \<open>?f x = ?g x\<close>  for x
        using calculation(1) calculation(2) by blast

      ultimately show ?thesis
        by blast
    qed
  next

      show \<open>u\<^sub>E \<circ>\<^sub>m h\<^sub>E = p\<^sub>E\<close> (is "?f = ?g")
      proof -
        have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<^sub>R\<close> for x
        proof -
          consider
              (a) \<open>x \<in> E\<^sub>R-E\<^sub>K\<close> 
            | (b) \<open>x \<in> E\<^sub>K\<close>
            using \<open>x \<in> E\<^sub>R\<close> by blast
          then show ?thesis
        proof (cases)
          case a
          then show ?thesis
            unfolding u\<^sub>E_def h\<^sub>E_def
            by force
        next
          case b
          let ?f\<^sub>E = \<open>\<lambda>e. map_option Inl (f\<^sub>E e)\<close>
          have \<open>?f x = (u\<^sub>E \<circ>\<^sub>m ?f\<^sub>E) x\<close>
            using b
            unfolding map_comp_def u\<^sub>E_def h\<^sub>E_def
            by simp

          also have \<open>... = (t\<^sub>E \<circ>\<^sub>m f\<^sub>E) x\<close>
            using b
            unfolding map_comp_def u\<^sub>E_def
            using m.dom_ge by force

          also have \<open>... = (p\<^sub>E \<circ>\<^sub>m k\<^sub>E) x\<close>
            using b
            unfolding map_comp_def
            by (metis commutativity_e map_comp_def)

          also have \<open>... = p\<^sub>E x\<close>
            using b
            unfolding map_comp_def
            by (metis i.g\<^sub>E_def i.inclusion_edges i.e_morph_not_none option.case_eq_if)

          finally show ?thesis .
        qed
      qed
      moreover have \<open>?f x = ?g x\<close> if \<open>x \<notin> E\<^sub>R\<close> for x
        unfolding map_comp_def
        using that
        by (smt (z3) DiffD1 domIff h' h.dom_ge morphism.dom_ge option.case_eq_if)

      moreover have \<open>?f x = ?g x\<close>  for x
        using calculation(1) calculation(2) by blast

      ultimately show ?thesis
        by blast
    qed
  next
    show \<open>u\<^sub>V \<circ>\<^sub>m j\<^sub>V = t\<^sub>V\<close> (is "?f = ?g")
    proof -
      have \<open>?f x = ?g x\<close> if \<open>x \<in> V\<^sub>D\<close> for x
        unfolding u\<^sub>V_def j\<^sub>V_def
        using that by simp

      moreover have \<open>?f x = ?g x\<close> if \<open>x \<notin> V\<^sub>D\<close> for x
        unfolding map_comp_def u\<^sub>V_def j\<^sub>V_def
        using c' morphism.dom_gv by fastforce

      moreover have \<open>?f x = ?g x\<close> for x
        using calculation(1) calculation(2) by blast

      ultimately show ?thesis
        by blast
    qed

  next
    show \<open>u\<^sub>E \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close> (is "?f = ?g")
    proof -
      have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<^sub>D\<close> for x
        unfolding u\<^sub>E_def j\<^sub>E_def
        using that by simp

      moreover have \<open>?f x = ?g x\<close> if \<open>x \<notin> E\<^sub>D\<close> for x
        unfolding map_comp_def u\<^sub>E_def j\<^sub>E_def
        using c' morphism.dom_ge by fastforce

      moreover have \<open>?f x = ?g x\<close> for x
        using calculation(1) calculation(2) by blast

      ultimately show ?thesis
        by blast
    qed
  qed

(*   define u\<^sub>V where \<open>u\<^sub>V = case_sum t\<^sub>V (p\<^sub>V |` (V\<^sub>R-V\<^sub>K))\<close> 
  define u\<^sub>E where \<open>u\<^sub>E = case_sum t\<^sub>E (p\<^sub>E |` (E\<^sub>R-E\<^sub>K))\<close>
 *)
  show \<open>f = (u\<^sub>V, u\<^sub>E)\<close> if \<open>case f of (f\<^sub>V, f\<^sub>E) \<Rightarrow> morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E 
    \<and> f\<^sub>V \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> f\<^sub>E \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> f\<^sub>V \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> f\<^sub>E \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close> for f
  proof -

    have \<open>(fst f) x = u\<^sub>V x\<close> if \<open>x \<in> V\<close> for x
    proof -
      consider
          (a) \<open>\<exists>y \<in> V\<^sub>D. j\<^sub>V y = Some x\<close>
          | (b) \<open>\<exists>y \<in> V\<^sub>R-V\<^sub>K. h\<^sub>V y = Some x\<close>
        by (metis (no_types, hide_lams) Un_iff \<open>x \<in> V\<close> h\<^sub>V_def image_iff j\<^sub>V_def)

      then show ?thesis
      proof (cases)
        case a

         obtain y where \<open>y \<in> V\<^sub>D \<and> j\<^sub>V y = Some x\<close>
           using a
           by blast

         have \<open>u\<^sub>V x = (u\<^sub>V \<circ>\<^sub>m j\<^sub>V) y\<close>
          using assms
          by (simp add: \<open>y \<in> V\<^sub>D \<and> j\<^sub>V y = Some x\<close>)

        also have \<open>... = t\<^sub>V y\<close>
          by (simp add: \<open>y \<in> V\<^sub>D \<and> j\<^sub>V y = Some x\<close> j\<^sub>V_def u\<^sub>V_def)

        also have \<open>... = (u\<^sub>V \<circ>\<^sub>m j\<^sub>V) y\<close>
          by (simp add: \<open>(u\<^sub>V \<circ>\<^sub>m j\<^sub>V) y = t\<^sub>V y\<close>)

        also have \<open>... = (fst f) x\<close> if \<open>morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H (fst f) (snd f) 
          \<and> (fst f) \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> (snd f) \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> (fst f) \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> (snd f) \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close>
          using that
          by (metis \<open>(u\<^sub>V \<circ>\<^sub>m j\<^sub>V) y = t\<^sub>V y\<close> \<open>y \<in> V\<^sub>D \<and> j\<^sub>V y = Some x\<close> map_comp_def option.simps(5))

        also have \<open>... = (fst f) x\<close>
          by auto

        finally show ?thesis 
          using \<open>case f of (f\<^sub>V', f\<^sub>E') \<Rightarrow> morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V' f\<^sub>E' \<and> f\<^sub>V' \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> f\<^sub>E' \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> f\<^sub>V' \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> f\<^sub>E' \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close> \<open>morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H (fst f) (snd f) \<and> fst f \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> snd f \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> fst f \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> snd f \<circ>\<^sub>m j\<^sub>E = t\<^sub>E \<Longrightarrow> (u\<^sub>V \<circ>\<^sub>m j\<^sub>V) y = fst f x\<close> \<open>u\<^sub>V x = (u\<^sub>V \<circ>\<^sub>m j\<^sub>V) y\<close> by force
      
      next
        case b
        
        obtain y where \<open>y \<in> V\<^sub>R-V\<^sub>K \<and> h\<^sub>V y = Some x\<close>
           using b
           by blast

         have \<open>u\<^sub>V x = (u\<^sub>V \<circ>\<^sub>m h\<^sub>V) y\<close>
           by (simp add: \<open>y \<in> V\<^sub>R - V\<^sub>K \<and> h\<^sub>V y = Some x\<close>)

         also have \<open>... = p\<^sub>V y\<close>
           using \<open>y \<in> V\<^sub>R - V\<^sub>K \<and> h\<^sub>V y = Some x\<close> h\<^sub>V_def u\<^sub>V_def by force


         also have \<open>... = (fst f \<circ>\<^sub>m h\<^sub>V) y\<close>
           using \<open>case f of (f\<^sub>V', f\<^sub>E') \<Rightarrow> morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V' f\<^sub>E' \<and> f\<^sub>V' \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> f\<^sub>E' \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> f\<^sub>V' \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> f\<^sub>E' \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close> by force

         also have \<open>... = (fst f) x\<close> if \<open>morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H (fst f) (snd f) 
          \<and> (fst f) \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> (snd f) \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> (fst f) \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> (snd f) \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close>
           using that
           by (meson \<open>y \<in> V\<^sub>R - V\<^sub>K \<and> h\<^sub>V y = Some x\<close> map_comp_simps(2))

         also have \<open>... = (fst f) x\<close>
           by auto

        finally show ?thesis
          using \<open>(u\<^sub>V \<circ>\<^sub>m h\<^sub>V) y = p\<^sub>V y\<close> \<open>p\<^sub>V y = (fst f \<circ>\<^sub>m h\<^sub>V) y\<close> \<open>y \<in> V\<^sub>R - V\<^sub>K \<and> h\<^sub>V y = Some x\<close> by force
      qed
    qed

    moreover have \<open>dom u\<^sub>V = V\<close>
      by (metis (no_types, lifting) \<open>case (u\<^sub>V, u\<^sub>E) of (u\<^sub>V, u\<^sub>E) \<Rightarrow> morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close> case_prodE fst_conv morphism.dom_gv)
    moreover have \<open>(fst f) x = u\<^sub>V x\<close> if \<open>x \<notin> V\<close> for x
      by (metis (mono_tags, lifting) \<open>case f of (f\<^sub>V', f\<^sub>E') \<Rightarrow> morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V' f\<^sub>E' \<and> f\<^sub>V' \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> f\<^sub>E' \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> f\<^sub>V' \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> f\<^sub>E' \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close> calculation(2) case_prod_beta domIff morphism.dom_gv that)

    moreover have \<open>(snd f) x = u\<^sub>E x\<close> if \<open>x \<in> E\<close> for x
    proof -
      consider
          (a) \<open>\<exists>y \<in> E\<^sub>D. j\<^sub>E y = Some x\<close>
        | (b) \<open>\<exists>y \<in> E\<^sub>R-E\<^sub>K. h\<^sub>E y = Some x\<close>
        by (metis (no_types, hide_lams) Un_iff \<open>x \<in> E\<close> h\<^sub>E_def image_iff j\<^sub>E_def)

      then show ?thesis
      proof (cases)
        case a

         obtain y where \<open>y \<in> E\<^sub>D \<and> j\<^sub>E y = Some x\<close>
           using a
           by blast

         have \<open>u\<^sub>E x = (u\<^sub>E \<circ>\<^sub>m j\<^sub>E) y\<close>
          using assms
          by (simp add: \<open>y \<in> E\<^sub>D \<and> j\<^sub>E y = Some x\<close>)

        also have \<open>... = t\<^sub>E y\<close>
          by (simp add: \<open>y \<in> E\<^sub>D \<and> j\<^sub>E y = Some x\<close> j\<^sub>E_def u\<^sub>E_def)

        also have \<open>... = (u\<^sub>E \<circ>\<^sub>m j\<^sub>E) y\<close>
          using \<open>(u\<^sub>E \<circ>\<^sub>m j\<^sub>E) y = t\<^sub>E y\<close> by presburger

        also have \<open>... = (snd f) x\<close> if \<open>(snd f) \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close>
          using that
          using \<open>(u\<^sub>E \<circ>\<^sub>m j\<^sub>E) y = t\<^sub>E y\<close> \<open>y \<in> E\<^sub>D \<and> j\<^sub>E y = Some x\<close> by force

        also have \<open>... = (snd f) x\<close>
          by auto

        finally show ?thesis 
          using \<open>case f of (f\<^sub>V', f\<^sub>E') \<Rightarrow> morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V' f\<^sub>E' \<and> f\<^sub>V' \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> f\<^sub>E' \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> f\<^sub>V' \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> f\<^sub>E' \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close> \<open>snd f \<circ>\<^sub>m j\<^sub>E = t\<^sub>E \<Longrightarrow> (u\<^sub>E \<circ>\<^sub>m j\<^sub>E) y = snd f x\<close> \<open>u\<^sub>E x = (u\<^sub>E \<circ>\<^sub>m j\<^sub>E) y\<close> by force
      
      next
        case b
        
        obtain y where \<open>y \<in> E\<^sub>R-E\<^sub>K \<and> h\<^sub>E y = Some x\<close>
           using b
           by blast

         have \<open>u\<^sub>E x = (u\<^sub>E \<circ>\<^sub>m h\<^sub>E) y\<close>
           using \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> h\<^sub>E y = Some x\<close> by force
           
         also have \<open>... = p\<^sub>E y\<close>
           using \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> h\<^sub>E y = Some x\<close> h\<^sub>E_def u\<^sub>E_def by force


         also have \<open>... = (snd f \<circ>\<^sub>m h\<^sub>E) y\<close>
           using \<open>case f of (f\<^sub>V', f\<^sub>E') \<Rightarrow> morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V' f\<^sub>E' \<and> f\<^sub>V' \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> f\<^sub>E' \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> f\<^sub>V' \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> f\<^sub>E' \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close> by force

         also have \<open>... = (snd f) x\<close> if \<open>morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H (fst f) (snd f) 
          \<and> (fst f) \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> (snd f) \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> (fst f) \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> (snd f) \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close>
           using that
           by (meson \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> h\<^sub>E y = Some x\<close> map_comp_simps(2))

         also have \<open>... = (snd f) x\<close>
           by auto

         finally show ?thesis
          using \<open>(u\<^sub>E \<circ>\<^sub>m h\<^sub>E) y = p\<^sub>E y\<close> \<open>p\<^sub>E y = (snd f \<circ>\<^sub>m h\<^sub>E) y\<close> \<open>y \<in> E\<^sub>R - E\<^sub>K \<and> h\<^sub>E y = Some x\<close> by force
      qed
    qed

    moreover have \<open>dom u\<^sub>E = E\<close>
      by (metis (no_types, lifting) \<open>case (u\<^sub>V, u\<^sub>E) of (u\<^sub>V, u\<^sub>E) \<Rightarrow> morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close> case_prodE morphism.dom_ge snd_conv)

    ultimately have \<open>fst f x = u\<^sub>V x \<and> snd f y = u\<^sub>E y\<close> for x and y
      by (metis (no_types, lifting) case_prodE domIff morphism.dom_ge snd_conv that)

   thus  ?thesis
      using that
      by fastforce
  qed
qed


interpretation pushout_diagram
  V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K
  V\<^sub>R E\<^sub>R s\<^sub>R s'\<^sub>R t\<^sub>R t'\<^sub>R l\<^sub>R l'\<^sub>R m\<^sub>R m'\<^sub>R
  V\<^sub>D E\<^sub>D s\<^sub>D s'\<^sub>D t\<^sub>D t'\<^sub>D l\<^sub>D l'\<^sub>D m\<^sub>D m'\<^sub>D
  V E s "totalize s" t "totalize t" l "totalize l" m "totalize m"
\<comment> \<open>morph ab\<close>
  k\<^sub>V k'\<^sub>V
  k\<^sub>E k'\<^sub>E
\<comment> \<open>morph ac\<close>
  f\<^sub>V f'\<^sub>V
  f\<^sub>E f'\<^sub>E
\<comment> \<open>morph rd\<close>
  h\<^sub>V "totalize h\<^sub>V"
  h\<^sub>E "totalize h\<^sub>E"
\<comment> \<open>morph cd\<close>
  j\<^sub>V "totalize j\<^sub>V"
  j\<^sub>E "totalize j\<^sub>E"
proof unfold_locales
 show \<open>h\<^sub>V \<circ>\<^sub>m k\<^sub>V = j\<^sub>V \<circ>\<^sub>m f\<^sub>V\<close> (is "?f = ?g")
 proof
   show \<open>?f x = ?g x\<close> for x
   proof (cases \<open>x \<in> V\<^sub>K\<close>)
     case True
     then show ?thesis
      unfolding j\<^sub>V_def h\<^sub>V_def
      using i.inclusion_nodes_alt i.v_morph_not_none m.integrity_v' m.v_morph_not_none by fastforce
   next
     case False
     then show ?thesis
      using i.dom_gv m.dom_gv by auto
   qed
  qed
  show \<open>h\<^sub>E \<circ>\<^sub>m k\<^sub>E = j\<^sub>E \<circ>\<^sub>m f\<^sub>E\<close> (is "?f = ?g")
  proof -
    have \<open>?f x = ?g x\<close> if \<open>x \<in> E\<^sub>K\<close> for x
      unfolding j\<^sub>E_def h\<^sub>E_def
      using i.e_morph_not_none i.inclusion_edges m.e_morph_not_none m.integrity_e' that by fastforce

    moreover have \<open>?f x = ?g x\<close> if \<open>x \<notin> E\<^sub>K\<close> for x
      using i.dom_ge m.dom_ge that by auto

    ultimately show ?thesis
      by blast
  qed
next

  show \<open>\<And>V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V p\<^sub>E t\<^sub>V t\<^sub>E.
       \<lbrakk>graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H; 
        morphism V\<^sub>R E\<^sub>R s\<^sub>R t\<^sub>R l\<^sub>R m\<^sub>R V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V p\<^sub>E; 
        morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H t\<^sub>V t\<^sub>E; 
        p\<^sub>V \<circ>\<^sub>m k\<^sub>V = t\<^sub>V \<circ>\<^sub>m f\<^sub>V; 
        p\<^sub>E \<circ>\<^sub>m k\<^sub>E = t\<^sub>E \<circ>\<^sub>m f\<^sub>E\<rbrakk>
       \<Longrightarrow> \<exists>!(u\<^sub>V, u\<^sub>E). 
        morphism V E s t l m V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and> 
        u\<^sub>V \<circ>\<^sub>m h\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m h\<^sub>E = p\<^sub>E \<and> 
        u\<^sub>V \<circ>\<^sub>m j\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m j\<^sub>E = t\<^sub>E\<close>
    using univ_prop
    by fastforce
qed

end



end