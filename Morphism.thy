theory Morphism
  imports Graph AuxLemmas
begin

section \<open>Morphism\<close>

text_raw \<open>
\begin{figure}[!htb]
  \centering
  \includestandalone{figs/fig-morphism}
  \caption{Morphism: Structure-preserving mapping}
\end{figure}
\<close>

locale morphism =
  G: graph V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G +
  H: graph V\<^sub>H E\<^sub>H s\<^sub>H s'\<^sub>H t\<^sub>H t'\<^sub>H l\<^sub>H l'\<^sub>H m\<^sub>H m'\<^sub>H for
  V\<^sub>G :: "'v\<^sub>G set" and E\<^sub>G :: "'e\<^sub>G set" and s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G and
  V\<^sub>H :: "'v\<^sub>H set" and E\<^sub>H :: "'e\<^sub>H set" and s\<^sub>H s'\<^sub>H t\<^sub>H t'\<^sub>H l\<^sub>H l'\<^sub>H m\<^sub>H m'\<^sub>H +

  fixes
    g\<^sub>V  :: "'v\<^sub>G \<rightharpoonup> 'v\<^sub>H" and
    g'\<^sub>V :: "'v\<^sub>G \<Rightarrow> 'v\<^sub>H" and
    g\<^sub>E  :: "'e\<^sub>G \<rightharpoonup> 'e\<^sub>H" and
    g'\<^sub>E :: "'e\<^sub>G \<Rightarrow> 'e\<^sub>H"
  defines
    g\<^sub>V_def[simp]: \<open>g'\<^sub>V \<equiv> totalize g\<^sub>V\<close> and
    g\<^sub>E_def[simp]: \<open>g'\<^sub>E \<equiv> totalize g\<^sub>E\<close>

assumes
  integrity_v: "dom g\<^sub>V = V\<^sub>G \<and> ran g\<^sub>V \<subseteq> V\<^sub>H" and
  integrity_e: "dom g\<^sub>E = E\<^sub>G \<and> ran g\<^sub>E \<subseteq> E\<^sub>H" and
  source_preserve: "g\<^sub>V \<circ>\<^sub>m s\<^sub>G = s\<^sub>H \<circ>\<^sub>m g\<^sub>E" and
  target_preserve: "g\<^sub>V \<circ>\<^sub>m t\<^sub>G = t\<^sub>H \<circ>\<^sub>m g\<^sub>E" and
  node_label_preserve: "l\<^sub>G = l\<^sub>H \<circ>\<^sub>m g\<^sub>V" and
  edge_label_preserve: "m\<^sub>G = m\<^sub>H \<circ>\<^sub>m g\<^sub>E" 
begin

lemma source_preserve_alt:
  "e \<in> E\<^sub>G \<Longrightarrow> g'\<^sub>V (s'\<^sub>G e) = s'\<^sub>H (g'\<^sub>E e)"
proof -
  from source_preserve have "\<forall>e \<in> E\<^sub>G .g'\<^sub>V (s'\<^sub>G e) = s'\<^sub>H (g'\<^sub>E e)"
    by (metis (mono_tags, lifting) G.integrity_s G.s_def H.s_def domIff g\<^sub>V_def g\<^sub>E_def integrity_e map_comp_simps(2) option.exhaust_sel)
  thus "e \<in> E\<^sub>G \<Longrightarrow> g'\<^sub>V (s'\<^sub>G e) = s'\<^sub>H (g'\<^sub>E e)"
    by simp
qed

lemma target_preserve_alt:
  "e \<in> E\<^sub>G \<Longrightarrow> g'\<^sub>V (t'\<^sub>G e) = t'\<^sub>H (g'\<^sub>E e)"
proof -
  from target_preserve  have "\<forall>e \<in> E\<^sub>G .g'\<^sub>V (t'\<^sub>G e) = t'\<^sub>H (g'\<^sub>E e)" 
    by (metis (mono_tags, lifting) G.integrity_t G.t_def H.t_def domD g\<^sub>V_def g\<^sub>E_def integrity_e map_comp_simps(2) option.sel)
  thus "e \<in> E\<^sub>G \<Longrightarrow> g'\<^sub>V (t'\<^sub>G e) = t'\<^sub>H (g'\<^sub>E e)"
    by simp
qed

lemma v_morph_not_none:
  shows "v \<in> V\<^sub>G \<Longrightarrow> g\<^sub>V v \<noteq> None"
  using integrity_v by force

lemma e_morph_not_none:
  shows "e \<in> E\<^sub>G \<Longrightarrow> g\<^sub>E e \<noteq> None"
  using integrity_e by force

lemma integrity_v':
  shows "v \<in> V\<^sub>G \<Longrightarrow> g'\<^sub>V v \<in> V\<^sub>H"
  using integrity_v ranI by fastforce

lemma integrity_e':
  shows "e \<in> E\<^sub>G \<Longrightarrow> g'\<^sub>E e \<in> E\<^sub>H"
  using integrity_e ranI by fastforce

lemma integrity_s_alt:
  shows "g\<^sub>E e = Some e' \<Longrightarrow> e' \<in> E\<^sub>H"
  by (meson integrity_e ranI subset_eq)

lemma integrity_v_alt:
  shows "g\<^sub>V v = Some v' \<Longrightarrow> v' \<in> V\<^sub>H"
  by (meson integrity_v ranI subset_eq)

lemma integrity_e_alt:
  shows "g\<^sub>E e = Some e' \<Longrightarrow> e' \<in> E\<^sub>H"
  by (meson integrity_e ranI subset_eq)


lemma edge_label_preserve':
  shows "e \<in> E\<^sub>G \<Longrightarrow> m'\<^sub>G e = m'\<^sub>H (g'\<^sub>E e)"
  using edge_label_preserve G.integrity_m 
    by (metis (mono_tags, lifting) G.m_def H.m_def domD g\<^sub>E_def map_comp_Some_iff option.sel)

lemma node_label_preserve':
  shows "v \<in> V\<^sub>G \<Longrightarrow> l'\<^sub>G v = l'\<^sub>H (g'\<^sub>V v)"
  using node_label_preserve G.integrity_l
  by (metis (mono_tags, hide_lams) G.l_def H.l_def domD g\<^sub>V_def map_comp_Some_iff option.sel)

lemma dom_gv:
  shows "dom g\<^sub>V = V\<^sub>G"
  by (simp add: integrity_v)

lemma ran_gv:
  shows "ran g\<^sub>V \<subseteq> V\<^sub>H"
   by (simp add: integrity_v)

lemma dom_ge:
  shows "dom g\<^sub>E = E\<^sub>G"
  by (simp add: integrity_e)

lemma ran_ge:
  shows "ran g\<^sub>E \<subseteq> E\<^sub>H"
   by (simp add: integrity_e)

end

subsection \<open>Composition\<close>
text_raw \<open>
\begin{figure}[!htb]
  \centering
  \includestandalone{figs/fig-morphism-composition}
  \caption{Abstract Pushout}
\end{figure}
\<close>

lemma morph_composition:
  assumes 
    g:"morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H g\<^sub>V g\<^sub>E" and
    k:"morphism V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H V\<^sub>L E\<^sub>L s\<^sub>L t\<^sub>L l\<^sub>L m\<^sub>L k\<^sub>V k\<^sub>E"
  shows "morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>L E\<^sub>L s\<^sub>L t\<^sub>L l\<^sub>L m\<^sub>L (k\<^sub>V \<circ>\<^sub>m g\<^sub>V) (k\<^sub>E \<circ>\<^sub>m g\<^sub>E)"
proof intro_locales
  show "graph V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G"
    using assms(1) morphism_def by blast
next
  show \<open>graph V\<^sub>L E\<^sub>L s\<^sub>L t\<^sub>L l\<^sub>L m\<^sub>L\<close>
    using assms(2) morphism_def by blast
next
  show \<open>morphism_axioms V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>L E\<^sub>L s\<^sub>L t\<^sub>L l\<^sub>L m\<^sub>L (k\<^sub>V \<circ>\<^sub>m g\<^sub>V) (k\<^sub>E \<circ>\<^sub>m g\<^sub>E) \<close>
  proof
    show \<open>dom (k\<^sub>V \<circ>\<^sub>m g\<^sub>V) = V\<^sub>G \<and> ran (k\<^sub>V \<circ>\<^sub>m g\<^sub>V) \<subseteq> V\<^sub>L\<close>
    proof
      show \<open>dom (k\<^sub>V \<circ>\<^sub>m g\<^sub>V) = V\<^sub>G\<close> (is \<open>dom ?f = V\<^sub>G\<close>)
        using morphism.dom_gv[OF k] morphism.dom_gv[OF g] morphism.integrity_v'[OF g]
        by fastforce
    next
      show \<open>ran (k\<^sub>V \<circ>\<^sub>m g\<^sub>V) \<subseteq> V\<^sub>L \<close>
        by (auto simp add: morphism.ran_gv[OF k] morphism.ran_gv[OF g] morphism.integrity_v_alt[OF k] ran_def iff: map_comp_Some_iff)
    qed
  next
    show \<open>dom (k\<^sub>E \<circ>\<^sub>m g\<^sub>E) = E\<^sub>G \<and> ran (k\<^sub>E \<circ>\<^sub>m g\<^sub>E) \<subseteq> E\<^sub>L\<close>
    proof
      show \<open>dom (k\<^sub>E \<circ>\<^sub>m g\<^sub>E) = E\<^sub>G\<close>
        using morphism.dom_ge[OF k] morphism.dom_ge[OF g] morphism.integrity_e'[OF g]
        by fastforce
    next
      show \<open>ran (k\<^sub>E \<circ>\<^sub>m g\<^sub>E) \<subseteq> E\<^sub>L \<close>
        by (auto simp add: morphism.ran_ge[OF k] morphism.ran_ge[OF g] morphism.integrity_e_alt[OF k] ran_def iff: map_comp_Some_iff)
    qed
  next
    show \<open>(k\<^sub>V \<circ>\<^sub>m g\<^sub>V) \<circ>\<^sub>m s\<^sub>G = s\<^sub>L \<circ>\<^sub>m (k\<^sub>E \<circ>\<^sub>m g\<^sub>E)\<close>
    proof -
      have \<open>(k\<^sub>V \<circ>\<^sub>m g\<^sub>V) \<circ>\<^sub>m s\<^sub>G = (k\<^sub>V \<circ>\<^sub>m s\<^sub>H) \<circ>\<^sub>m g\<^sub>E\<close>
        by (simp add: map_comp_assoc morphism.source_preserve[OF g])
      also have \<open>\<dots> = s\<^sub>L \<circ>\<^sub>m (k\<^sub>E \<circ>\<^sub>m g\<^sub>E)\<close>
        by (simp add: map_comp_assoc morphism.source_preserve[OF k])
      finally show ?thesis .
    qed
  next
    show \<open>k\<^sub>V \<circ>\<^sub>m g\<^sub>V \<circ>\<^sub>m t\<^sub>G = t\<^sub>L \<circ>\<^sub>m (k\<^sub>E \<circ>\<^sub>m g\<^sub>E)\<close>
    proof -
      have \<open>(k\<^sub>V \<circ>\<^sub>m g\<^sub>V) \<circ>\<^sub>m t\<^sub>G = (k\<^sub>V \<circ>\<^sub>m t\<^sub>H) \<circ>\<^sub>m g\<^sub>E\<close>
        by (simp add: map_comp_assoc morphism.target_preserve[OF g])
      also have \<open>\<dots> = t\<^sub>L \<circ>\<^sub>m (k\<^sub>E \<circ>\<^sub>m g\<^sub>E)\<close>
        by (simp add: map_comp_assoc morphism.target_preserve[OF k])
      finally show ?thesis .
    qed
  next
    show \<open>l\<^sub>G = l\<^sub>L \<circ>\<^sub>m (k\<^sub>V \<circ>\<^sub>m g\<^sub>V)\<close>
      by (simp add: map_comp_assoc morphism.node_label_preserve[OF g] morphism.node_label_preserve[OF k])
  
  next
    show \<open>m\<^sub>G = m\<^sub>L \<circ>\<^sub>m (k\<^sub>E \<circ>\<^sub>m g\<^sub>E)\<close>
      by (simp add: map_comp_assoc morphism.edge_label_preserve[OF g] morphism.edge_label_preserve[OF k])
  qed
qed

subsection \<open>Injective Morphism\<close>

locale injective_morphism = morphism +
  assumes
    node_injectivity: "inj_on g'\<^sub>V V\<^sub>G" and
    edge_injectivity: "inj_on g'\<^sub>E E\<^sub>G"
begin

lemma node_injectivity_alt:
  assumes
    a: "a \<in> V\<^sub>G" and
    b: "b \<in> V\<^sub>G" and
    eq: "g\<^sub>V a = g\<^sub>V b"
  shows "a = b"
  by (metis a b eq g\<^sub>V_def inj_on_def node_injectivity)


lemma edge_injectivity_alt:
  assumes
    a: "a \<in> E\<^sub>G" and
    b: "b \<in> E\<^sub>G" and
    eq: "g\<^sub>E a = g\<^sub>E b"
  shows "a = b"
  by (metis a b eq g\<^sub>E_def inj_on_def edge_injectivity)
end


subsection \<open>Surjective Morphism\<close>
locale surjective_morphism = morphism +
  assumes 
    node_surjectivity: "\<forall>v \<in> V\<^sub>H. \<exists>v' \<in> V\<^sub>G. g'\<^sub>V v' = v" and 
    edge_surjectivity: "\<forall>e \<in> E\<^sub>H. \<exists>e' \<in> E\<^sub>G. g'\<^sub>E e' = e"

begin

lemma node_surjectivity_alt:
  assumes \<open>x \<in> V\<^sub>H\<close>
  obtains y where \<open>g\<^sub>V y = Some x\<close>
  by (metis assms g\<^sub>V_def node_surjectivity option.exhaust_sel v_morph_not_none)

lemma edge_surjectivity_alt:
  assumes \<open>x \<in> E\<^sub>H\<close>
  obtains y where \<open>g\<^sub>E y = Some x\<close>
  by (metis assms g\<^sub>E_def edge_surjectivity option.exhaust_sel e_morph_not_none)

lemma ran_node: \<open>ran g\<^sub>V = V\<^sub>H\<close>
  using integrity_v node_surjectivity ranI by fastforce

lemma ran_edge: \<open>ran g\<^sub>E = E\<^sub>H\<close>
  using integrity_e edge_surjectivity ranI by fastforce


end



subsection \<open>Bijective Morphism\<close>

locale bijective_morphism =
  I: injective_morphism +
  J: surjective_morphism 
begin

lemma unique_dom_gv:
  assumes \<open>y \<in> V\<^sub>H\<close>
  shows \<open>\<exists>!x. x\<in> V\<^sub>G \<and> g\<^sub>V x = Some y\<close>
  by (metis I.dom_gv I.node_injectivity_alt J.node_surjectivity_alt assms domI)

lemma unique_dom_ge:
  assumes \<open>y \<in> E\<^sub>H\<close>
  shows \<open>\<exists>!x. x\<in> E\<^sub>G \<and> g\<^sub>E x = Some y\<close>
  by (metis I.dom_ge I.edge_injectivity_alt J.edge_surjectivity_alt assms domI)

lemma existence_inverse:
  shows \<open>\<exists>f\<^sub>V f\<^sub>E. bijective_morphism V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G f\<^sub>V f\<^sub>E
    \<and> (\<forall>v \<in> V\<^sub>G. (f\<^sub>V \<circ>\<^sub>m g\<^sub>V) v = Some v) \<and> (\<forall>e \<in> E\<^sub>G. (f\<^sub>E \<circ>\<^sub>m g\<^sub>E) e = Some e)\<close>
proof (intro exI, rule conjI)
  show \<open>bijective_morphism V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G 
    (\<lambda>x. if x \<in> V\<^sub>H then Some ((inv_into V\<^sub>G g'\<^sub>V) x) else None)
    (\<lambda>x. if x \<in> E\<^sub>H then Some ((inv_into E\<^sub>G g'\<^sub>E) x) else None)\<close>
  proof
    show \<open>dom (\<lambda>x. if x \<in> V\<^sub>H then Some (inv_into V\<^sub>G g'\<^sub>V x) else None) = V\<^sub>H \<and>
          ran (\<lambda>x. if x \<in> V\<^sub>H then Some (inv_into V\<^sub>G g'\<^sub>V x) else None) \<subseteq> V\<^sub>G\<close>
      proof -
        have \<open>dom (\<lambda>x. if x \<in> V\<^sub>H then Some (inv_into V\<^sub>G g'\<^sub>V x) else None) = V\<^sub>H\<close>
          using subset_antisym by fastforce
        also have \<open>ran (\<lambda>x. if x \<in> V\<^sub>H then Some (inv_into V\<^sub>G g'\<^sub>V x) else None) \<subseteq> V\<^sub>G\<close>
          by (smt (z3) I.node_injectivity J.node_surjectivity calculation domI inv_into_f_eq mem_Collect_eq option.inject ran_def subsetI)
        ultimately show ?thesis 
          by simp
      qed
    next
      show \<open>dom (\<lambda>x. if x \<in> E\<^sub>H then Some (inv_into E\<^sub>G g'\<^sub>E x) else None) = E\<^sub>H \<and>
            ran (\<lambda>x. if x \<in> E\<^sub>H then Some (inv_into E\<^sub>G g'\<^sub>E x) else None) \<subseteq> E\<^sub>G\<close>
      proof -
        have \<open>dom (\<lambda>x. if x \<in> E\<^sub>H then Some (inv_into E\<^sub>G g'\<^sub>E x) else None) = E\<^sub>H\<close>
          using subset_antisym by fastforce
        also have \<open>ran (\<lambda>x. if x \<in> E\<^sub>H then Some (inv_into E\<^sub>G g'\<^sub>E x) else None) \<subseteq> E\<^sub>G\<close>
          by (smt (z3) I.edge_injectivity J.edge_surjectivity domI domIff inv_into_f_eq mem_Collect_eq option.inject ran_def subsetI)
        ultimately show ?thesis 
          by simp
      qed
    next
      show \<open>(\<lambda>x. if x \<in> V\<^sub>H then Some (inv_into V\<^sub>G g'\<^sub>V x) else None) \<circ>\<^sub>m s\<^sub>H =
          s\<^sub>G \<circ>\<^sub>m (\<lambda>x. if x \<in> E\<^sub>H then Some (inv_into E\<^sub>G g'\<^sub>E x) else None)\<close> (is \<open>?f = ?g\<close>)
      proof
        show \<open>?f x = ?g x\<close> for x
        proof (cases \<open>x \<in> E\<^sub>H\<close>)
          case True
          then show ?thesis
            by (smt (verit, ccfv_threshold) I.G.graph_axioms I.G.integrity_s I.G.s_def I.H.graph_axioms I.H.integrity_s I.H.s_def I.edge_injectivity I.g\<^sub>E_def I.node_injectivity I.source_preserve_alt J.surjective_morphism_axioms domD graph.integrity_s' inv_into_f_f map_comp_simps(2) option.sel surjective_morphism.edge_surjectivity)
        next
        case False
          then show ?thesis
            using I.H.integrity_s by auto
        qed
      qed
    next
      show \<open>(\<lambda>x. if x \<in> V\<^sub>H then Some (inv_into V\<^sub>G g'\<^sub>V x) else None) \<circ>\<^sub>m t\<^sub>H =
              t\<^sub>G \<circ>\<^sub>m (\<lambda>x. if x \<in> E\<^sub>H then Some (inv_into E\<^sub>G g'\<^sub>E x) else None)\<close> (is \<open>?f = ?g\<close>)
      proof
        show \<open>?f x = ?g x\<close> for x
        proof (cases \<open>x \<in> E\<^sub>H\<close>)
          case True
          then show ?thesis
            by (smt (verit, ccfv_SIG) I.G.graph_axioms I.G.integrity_t I.G.t_def I.H.graph_axioms I.H.integrity_t I.H.t_def I.edge_injectivity I.node_injectivity I.target_preserve_alt J.edge_surjectivity domD graph.integrity_t' inv_into_f_f map_comp_simps(2) option.sel)
        next
        case False
          then show ?thesis
            using I.H.integrity_t by auto
        qed
      qed
    next
      show \<open>l\<^sub>H = l\<^sub>G \<circ>\<^sub>m (\<lambda>x. if x \<in> V\<^sub>H then Some (inv_into V\<^sub>G g'\<^sub>V x) else None)\<close> (is \<open>l\<^sub>H = ?f\<close>)
      proof
        show \<open>l\<^sub>H x = ?f x\<close> for x
        proof (cases \<open>x \<in> V\<^sub>H\<close>)
          case True
          then show ?thesis
            using I.node_injectivity I.node_label_preserve I.morphism_axioms J.node_surjectivity inv_into_f_eq morphism.v_morph_not_none by fastforce
        next
          case False
          then show ?thesis
            using I.H.integrity_l by auto
        qed
      qed
    next
      show \<open>m\<^sub>H = m\<^sub>G \<circ>\<^sub>m (\<lambda>x. if x \<in> E\<^sub>H then Some (inv_into E\<^sub>G g'\<^sub>E x) else None)\<close> (is \<open>m\<^sub>H = ?f\<close>)
      proof
        show \<open>m\<^sub>H x = ?f x\<close> for x
        proof (cases \<open>x \<in> E\<^sub>H\<close>)
          case True
          then show ?thesis
            using I.edge_injectivity I.edge_label_preserve I.morphism_axioms J.edge_surjectivity inv_into_f_eq morphism.e_morph_not_none by fastforce
        next
          case False
          then show ?thesis
            using I.H.integrity_m by auto
        qed
      qed
    next
      show \<open>inj_on (\<lambda>a. totalize (If (a \<in> V\<^sub>H) (Some (inv_into V\<^sub>G g'\<^sub>V a))) None) V\<^sub>H\<close>
        by (smt (verit, ccfv_SIG) I.node_injectivity J.node_surjectivity inj_onI inv_into_f_eq option.sel)
    next
      show \<open>inj_on (\<lambda>a. totalize (If (a \<in> E\<^sub>H) (Some (inv_into E\<^sub>G g'\<^sub>E a))) None) E\<^sub>H\<close>
        by (smt (verit, ccfv_threshold) I.edge_injectivity J.edge_surjectivity inj_onI inv_into_f_eq option.sel)
    next
      show \<open>\<forall>v\<in>V\<^sub>G. \<exists>v'\<in>V\<^sub>H. totalize (If (v' \<in> V\<^sub>H) (Some (inv_into V\<^sub>G g'\<^sub>V v'))) None = v\<close>
        using I.integrity_v' I.node_injectivity inv_into_f_f by fastforce
    next
      show \<open>\<forall>e\<in>E\<^sub>G. \<exists>e'\<in>E\<^sub>H. totalize (If (e' \<in> E\<^sub>H) (Some (inv_into E\<^sub>G g'\<^sub>E e'))) None = e\<close>
        using I.edge_injectivity I.integrity_e' inv_into_f_f by fastforce
    qed
  next
    show \<open>(\<forall>v\<in>V\<^sub>G. ((\<lambda>x. if x \<in> V\<^sub>H then Some (inv_into V\<^sub>G g'\<^sub>V x) else None) \<circ>\<^sub>m g\<^sub>V) v = Some v) \<and> (\<forall>e\<in>E\<^sub>G. ((\<lambda>x. if x \<in> E\<^sub>H then Some (inv_into E\<^sub>G g'\<^sub>E x) else None) \<circ>\<^sub>m g\<^sub>E) e = Some e)\<close>
    proof
      show \<open>\<forall>v\<in>V\<^sub>G. ((\<lambda>x. if x \<in> V\<^sub>H then Some (inv_into V\<^sub>G g'\<^sub>V x) else None) \<circ>\<^sub>m g\<^sub>V) v = Some v\<close>
        using I.integrity_v' I.node_injectivity I.v_morph_not_none inv_into_f_eq by fastforce
    next
      show \<open>\<forall>e\<in>E\<^sub>G. ((\<lambda>x. if x \<in> E\<^sub>H then Some (inv_into E\<^sub>G g'\<^sub>E x) else None) \<circ>\<^sub>m g\<^sub>E) e = Some e\<close>
        using I.e_morph_not_none I.edge_injectivity I.integrity_e' inv_into_f_eq by fastforce
    qed
  qed
end

subsection \<open>Identity Morphism\<close>
context graph begin
interpretation identity:
  bijective_morphism 
  V E s s' t t' l l' m m'
  V E s s' t t' l l' m m'
  "\<lambda>v. if v \<in> V then Some v else None"
  "totalize (\<lambda>v. if v \<in> V then Some v else None)"
  "\<lambda>e. if e \<in> E then Some e else None"
  "totalize (\<lambda>e. if e \<in> E then Some e else None)"
proof (unfold_locales, simp_all)
  show \<open>dom (\<lambda>v. if v \<in> V then Some v else None) = V \<and> ran (\<lambda>v. if v \<in> V then Some v else None) \<subseteq> V\<close>
  proof
    show \<open>dom (\<lambda>v. if v \<in> V then Some v else None) = V\<close>
      unfolding dom_def
      by simp
  next
    show \<open>ran (\<lambda>v. if v \<in> V then Some v else None) \<subseteq> V\<close>
      unfolding ran_def
      by auto
  qed
next
  show \<open>dom (\<lambda>e. if e \<in> E then Some e else None) = E \<and> ran (\<lambda>e. if e \<in> E then Some e else None) \<subseteq> E\<close>
  proof
    show \<open>dom (\<lambda>e. if e \<in> E then Some e else None) = E\<close>
      unfolding dom_def
      by force
  next
    show \<open>ran (\<lambda>e. if e \<in> E then Some e else None) \<subseteq> E\<close>
      unfolding ran_def
      by auto
  qed
next
  show \<open>(\<lambda>v. if v \<in> V then Some v else None) \<circ>\<^sub>m s = s \<circ>\<^sub>m (\<lambda>e. if e \<in> E then Some e else None)\<close>
    unfolding map_comp_def
  proof
    show "\<And>k. (case s k of None \<Rightarrow> None | Some v \<Rightarrow> if v \<in> V then Some v else None) =
         (case if k \<in> E then Some k else None of None \<Rightarrow> None | Some x \<Rightarrow> s x)"
      by (smt (z3) domIff graph.integrity_s' graph_axioms integrity_s option.case_eq_if option.collapse option.simps(5))
  qed
next
  show "(\<lambda>v. if v \<in> V then Some v else None) \<circ>\<^sub>m t = t \<circ>\<^sub>m (\<lambda>e. if e \<in> E then Some e else None)"
    unfolding map_comp_def
  proof
show "\<And>k. (case t k of None \<Rightarrow> None | Some v \<Rightarrow> if v \<in> V then Some v else None) =
         (case if k \<in> E then Some k else None of None \<Rightarrow> None | Some x \<Rightarrow> t x) "
  by (smt (z3) domD domIff graph.integrity_t' graph_axioms integrity_t option.case_eq_if option.sel option.simps(5))
qed
next
  show \<open>l = l \<circ>\<^sub>m (\<lambda>v. if v \<in> V then Some v else None)\<close>
    unfolding map_comp_def
    using integrity_l by fastforce
next
  show "m = m \<circ>\<^sub>m (\<lambda>e. if e \<in> E then Some e else None)"
    unfolding map_comp_def
    using integrity_m by force
next
  show "inj_on (\<lambda>a. totalize (If (a \<in> V) (Some a)) None) V"
    by (simp add: inj_on_def)
next
  show "inj_on (\<lambda>a. totalize (If (a \<in> E) (Some a)) None) E" 
    by (simp add: inj_on_def)
qed

end


subsection \<open>Identity Morphism\<close>

locale identity_morphism = 
  bijective_morphism 
    V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G 
    V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G
    f\<^sub>V f'\<^sub>V f\<^sub>E f'\<^sub>E
  for V\<^sub>G :: "'v set" and E\<^sub>G :: "'e set" and s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G f\<^sub>V f'\<^sub>V f\<^sub>E f'\<^sub>E +
  assumes 
    identity_nodes: \<open>x \<in> V\<^sub>G \<Longrightarrow> f\<^sub>V x = Some x\<close> and
    identity_edges: \<open>e \<in> E\<^sub>G \<Longrightarrow> f\<^sub>E e = Some e\<close>


lemma comp_id_morph:
  assumes \<open>morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E\<close> and
    \<open>identity_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G lid\<^sub>V lid\<^sub>E\<close> and
    \<open>identity_morphism V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H rid\<^sub>V rid\<^sub>E\<close>
  shows 
    \<open>f\<^sub>V \<circ>\<^sub>m lid\<^sub>V = f\<^sub>V\<close> and 
    \<open>f\<^sub>E \<circ>\<^sub>m lid\<^sub>E = f\<^sub>E\<close> and
    \<open>f\<^sub>V = rid\<^sub>V \<circ>\<^sub>m f\<^sub>V\<close> and
    \<open>f\<^sub>E = rid\<^sub>E \<circ>\<^sub>m f\<^sub>E\<close>
proof -
  show \<open>f\<^sub>V \<circ>\<^sub>m lid\<^sub>V = f\<^sub>V\<close>
  proof
    show \<open>(f\<^sub>V \<circ>\<^sub>m lid\<^sub>V) x = f\<^sub>V x\<close> for x
    proof (cases \<open>x \<in> V\<^sub>G\<close>)
      case True
      then show ?thesis 
        unfolding map_comp_def
        by (metis assms(2) identity_morphism.identity_nodes option.simps(5))
    next
      case False
      then show ?thesis
        by (metis assms(1) assms(2) bijective_morphism.axioms(1) domIff domIff identity_morphism.axioms(1) injective_morphism_def map_comp_simps(1) morphism.dom_gv morphism.dom_gv)
    qed
  qed
next
  show \<open>f\<^sub>E \<circ>\<^sub>m lid\<^sub>E = f\<^sub>E\<close>
  proof
    show \<open>(f\<^sub>E \<circ>\<^sub>m lid\<^sub>E) x = f\<^sub>E x\<close> for x
    proof (cases \<open>x \<in> E\<^sub>G\<close>)
      case True
      then show ?thesis
        by (meson assms(2) identity_morphism.identity_edges map_comp_simps(2))
    next
      case False
      then show ?thesis
        by (metis assms(1) assms(2) bijective_morphism.axioms(1) domIff domIff identity_morphism.axioms(1) injective_morphism_def map_comp_simps(1) morphism.dom_ge morphism.dom_ge)
    qed
  qed
next
  show \<open>f\<^sub>V = rid\<^sub>V \<circ>\<^sub>m f\<^sub>V\<close>
  proof
    show \<open>f\<^sub>V x = (rid\<^sub>V \<circ>\<^sub>m f\<^sub>V) x\<close> for x
    proof (cases \<open>x \<in> V\<^sub>G\<close>)
      case True
      then show ?thesis
        using assms(1) assms(3) identity_morphism.identity_nodes morphism.v_morph_not_none morphism.integrity_v' by fastforce
    next
      case False
         then show ?thesis
           by (metis assms(1) domIff map_comp_simps(1) morphism.dom_gv)
    qed
  qed
next
  show \<open>f\<^sub>E = rid\<^sub>E \<circ>\<^sub>m f\<^sub>E\<close>
  proof
    show \<open>f\<^sub>E x = (rid\<^sub>E \<circ>\<^sub>m f\<^sub>E) x\<close> for x
    proof (cases \<open>x \<in> E\<^sub>G\<close>)
      case True
      then show ?thesis
        using assms(1) assms(3) identity_morphism.identity_edges morphism.e_morph_not_none morphism.integrity_e' by fastforce
next
  case False
  then show ?thesis 
    by (metis assms(1) domIff map_comp_simps(1) morphism.dom_ge)
    qed
  qed
qed

lemma bij_morphism_comp_idL:
  assumes 
    L: \<open>identity_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G lid\<^sub>V lid\<^sub>E\<close> and
    R: \<open>identity_morphism V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H rid\<^sub>V rid\<^sub>E\<close> and
    f: \<open>morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E\<close> and
    g: \<open>morphism V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G g\<^sub>V g\<^sub>E\<close> and
    \<open>g\<^sub>V \<circ>\<^sub>m f\<^sub>V = lid\<^sub>V\<close> and \<open>g\<^sub>E \<circ>\<^sub>m f\<^sub>E = lid\<^sub>E\<close> and
    \<open>f\<^sub>V \<circ>\<^sub>m g\<^sub>V = rid\<^sub>V\<close> and \<open>f\<^sub>E \<circ>\<^sub>m g\<^sub>E = rid\<^sub>E\<close>
  shows \<open>bijective_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E\<close>
proof intro_locales
  show \<open>injective_morphism_axioms V\<^sub>G E\<^sub>G f\<^sub>V f\<^sub>E\<close>
    by (smt (verit, ccfv_SIG) L assms(5) assms(6) domIff f identity_morphism.axioms(2) identity_morphism_axioms_def inj_onI injective_morphism_axioms.intro map_comp_def morphism.dom_gv morphism.e_morph_not_none option.expand option.inject)
next
  show \<open>surjective_morphism_axioms V\<^sub>G E\<^sub>G V\<^sub>H E\<^sub>H f\<^sub>V f\<^sub>E\<close>
    by (smt (verit, best) R assms(7) assms(8) domD domIff g identity_morphism.identity_edges identity_morphism.identity_nodes map_comp_def morphism.e_morph_not_none morphism.integrity_e' morphism.integrity_v' morphism.v_morph_not_none option.sel option.simps(5) surjective_morphism_axioms_def)
next
  show \<open>morphism_axioms V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E\<close>
    using f morphism_def by blast
next
  show \<open>graph V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G\<close>
    using f morphism_def by blast
next
  show \<open>graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close>
    using f morphism_def by blast
qed 

lemma bij_morphism_comp_idR:
  assumes 
    L: \<open>identity_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G lid\<^sub>V lid\<^sub>E\<close> and
    R: \<open>identity_morphism V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H rid\<^sub>V rid\<^sub>E\<close> and
    f: \<open>morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E\<close> and
    g: \<open>morphism V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G g\<^sub>V g\<^sub>E\<close> and
    \<open>g\<^sub>V \<circ>\<^sub>m f\<^sub>V = lid\<^sub>V\<close> and \<open>g\<^sub>E \<circ>\<^sub>m f\<^sub>E = lid\<^sub>E\<close> and
    \<open>f\<^sub>V \<circ>\<^sub>m g\<^sub>V = rid\<^sub>V\<close> and \<open>f\<^sub>E \<circ>\<^sub>m g\<^sub>E = rid\<^sub>E\<close>
  shows \<open>bijective_morphism V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G g\<^sub>V g\<^sub>E\<close>
proof intro_locales
  show \<open>injective_morphism_axioms V\<^sub>H E\<^sub>H g\<^sub>V g\<^sub>E\<close>
    by (metis L R assms(5) assms(6) assms(7) assms(8) bij_morphism_comp_idL bijective_morphism.axioms(1) f g injective_morphism_def)
next 
  show \<open>morphism_axioms V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G g\<^sub>V g\<^sub>E\<close>
    using g morphism_def by blast
next
  show \<open>surjective_morphism_axioms V\<^sub>H E\<^sub>H V\<^sub>G E\<^sub>G g\<^sub>V g\<^sub>E \<close>
    by (metis L R assms(5) assms(6) assms(7) assms(8) bij_morphism_comp_idL bijective_morphism.axioms(2) f g surjective_morphism_def)
next
  show \<open>graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close>
    using f morphism_def by blast
next
  show \<open>graph V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G\<close>
    using f morphism_def by blast
qed

lemma id_morphI:
  assumes G: \<open>graph V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G\<close>
  shows \<open>identity_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G (\<lambda>v. if v \<in> V\<^sub>G then Some v else None) (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
proof intro_locales
  show \<open>graph V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G\<close>
    using G .
next
  show \<open>morphism_axioms V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G (\<lambda>v. if v \<in> V\<^sub>G then Some v else None)
     (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
  proof
    show \<open>dom (\<lambda>v. if v \<in> V\<^sub>G then Some v else None) = V\<^sub>G \<and> ran (\<lambda>v. if v \<in> V\<^sub>G then Some v else None) \<subseteq> V\<^sub>G\<close>
      unfolding dom_def ran_def
      by auto
  next
    show \<open>dom (\<lambda>e. if e \<in> E\<^sub>G then Some e else None) = E\<^sub>G \<and> ran (\<lambda>e. if e \<in> E\<^sub>G then Some e else None) \<subseteq> E\<^sub>G\<close>
      unfolding dom_def ran_def
      by auto
  next
    show \<open>(\<lambda>v. if v \<in> V\<^sub>G then Some v else None) \<circ>\<^sub>m s\<^sub>G = s\<^sub>G \<circ>\<^sub>m (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
      unfolding map_comp_def
      using assms domIff graph.integrity_s graph.integrity_s' by fastforce
  next
    show \<open>(\<lambda>v. if v \<in> V\<^sub>G then Some v else None) \<circ>\<^sub>m t\<^sub>G = t\<^sub>G \<circ>\<^sub>m (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
      unfolding map_comp_def
      using assms domIff graph.integrity_t graph.integrity_t' by fastforce
  next
    show \<open>l\<^sub>G = l\<^sub>G \<circ>\<^sub>m (\<lambda>v. if v \<in> V\<^sub>G then Some v else None)\<close>
      unfolding map_comp_def
      using assms graph.integrity_l by fastforce
  next
    show \<open>m\<^sub>G = m\<^sub>G \<circ>\<^sub>m (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
      unfolding map_comp_def
      using assms graph.integrity_m by fastforce
  qed
next
  show \<open>injective_morphism_axioms V\<^sub>G E\<^sub>G (\<lambda>v. if v \<in> V\<^sub>G then Some v else None) (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
    by (smt (verit, ccfv_SIG) inj_onI injective_morphism_axioms.intro option.expand option.inject option.simps(3))
next
  show \<open>surjective_morphism_axioms V\<^sub>G E\<^sub>G V\<^sub>G E\<^sub>G (\<lambda>v. if v \<in> V\<^sub>G then Some v else None)
     (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
    by (simp add: surjective_morphism_axioms_def)
next
  show \<open>identity_morphism_axioms V\<^sub>G E\<^sub>G (\<lambda>v. if v \<in> V\<^sub>G then Some v else None) (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
    by (simp add: identity_morphism_axioms_def)
qed
 
lemma bij_impl_inv_l:
  assumes 
    f: \<open>bijective_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E\<close> and
    L: \<open>identity_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G lid\<^sub>V lid\<^sub>E\<close> and
    R: \<open>identity_morphism V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H rid\<^sub>V rid\<^sub>E\<close>
  obtains g\<^sub>V and g\<^sub>E where \<open>bijective_morphism V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G g\<^sub>V g\<^sub>E\<close> and
    \<open>g\<^sub>V \<circ>\<^sub>m f\<^sub>V = lid\<^sub>V\<close> and \<open>g\<^sub>E \<circ>\<^sub>m f\<^sub>E = lid\<^sub>E\<close> and
    \<open>f\<^sub>V \<circ>\<^sub>m g\<^sub>V = rid\<^sub>V\<close> and \<open>f\<^sub>E \<circ>\<^sub>m g\<^sub>E = rid\<^sub>E\<close>
proof -

  obtain f'\<^sub>V and f'\<^sub>E where inv:\<open>bijective_morphism V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G f'\<^sub>V f'\<^sub>E
    \<and> (\<forall>v \<in> V\<^sub>G. (f'\<^sub>V \<circ>\<^sub>m f\<^sub>V) v = Some v) \<and> (\<forall>e \<in> E\<^sub>G. (f'\<^sub>E \<circ>\<^sub>m f\<^sub>E) e = Some e) \<close>
    using bijective_morphism.existence_inverse f by blast

  have \<open>f'\<^sub>V \<circ>\<^sub>m f\<^sub>V = lid\<^sub>V\<close>
  proof 
    show \<open>(f'\<^sub>V \<circ>\<^sub>m f\<^sub>V) x = lid\<^sub>V x\<close> for x
    proof (cases \<open>x \<in> V\<^sub>G\<close>)
      case True
      then show ?thesis
        by (metis L identity_morphism.identity_nodes inv)
    next
      case False
      then show ?thesis
        by (metis L bijective_morphism.axioms(1) domIff f identity_morphism.axioms(1) injective_morphism.axioms(1) map_comp_simps(1) morphism.dom_gv)
    qed
  qed

  moreover have \<open>f'\<^sub>E \<circ>\<^sub>m f\<^sub>E = lid\<^sub>E\<close>
    proof 
    show \<open>(f'\<^sub>E \<circ>\<^sub>m f\<^sub>E) x = lid\<^sub>E x\<close> for x
    proof (cases \<open>x \<in> E\<^sub>G\<close>)
      case True
      then show ?thesis
        by (metis L identity_morphism.identity_edges inv)
    next
      case False
      then show ?thesis
        by (metis L bijective_morphism.axioms(1) domIff f identity_morphism.axioms(1) injective_morphism.axioms(1) map_comp_simps(1) morphism.dom_ge)
    qed
  qed

  
  moreover have \<open>f\<^sub>V \<circ>\<^sub>m f'\<^sub>V = rid\<^sub>V\<close>
  proof 
    show \<open>(f\<^sub>V \<circ>\<^sub>m f'\<^sub>V) x = rid\<^sub>V x\<close> for x
    proof (cases \<open>x \<in> V\<^sub>H\<close>)
      case True
      then show ?thesis
        using R bijective_morphism.unique_dom_gv f identity_morphism.identity_nodes inv by fastforce
    next
      case False
      have \<open>f'\<^sub>V x = None\<close>
        by (metis False bijective_morphism.axioms(1) domIff injective_morphism.axioms(1) inv morphism.dom_gv)
      then have \<open>(f\<^sub>V \<circ>\<^sub>m f'\<^sub>V) x = None\<close>
        by simp
      also have \<open>rid\<^sub>V x = None\<close>
        using assms(3)
        unfolding identity_morphism_def bijective_morphism_def injective_morphism_def 
        by (metis False domIff morphism.dom_gv)

      ultimately show ?thesis
        by simp
    qed
  qed

  moreover have \<open>f\<^sub>E \<circ>\<^sub>m f'\<^sub>E = rid\<^sub>E\<close>
  proof 
    show \<open>(f\<^sub>E \<circ>\<^sub>m f'\<^sub>E) x = rid\<^sub>E x\<close> for x
    proof (cases \<open>x \<in> E\<^sub>H\<close>)
      case True
      then show ?thesis
        using R bijective_morphism.unique_dom_ge f identity_morphism.identity_edges inv by fastforce
    next
      case False
      have \<open>f'\<^sub>E x = None\<close>
        by (metis False bijective_morphism.axioms(1) domIff injective_morphism.axioms(1) inv morphism.dom_ge)
      then have \<open>(f\<^sub>E \<circ>\<^sub>m f'\<^sub>E) x = None\<close>
        by simp
      also have \<open>rid\<^sub>E x = None\<close>
        using assms(3)
        unfolding identity_morphism_def bijective_morphism_def injective_morphism_def 
        by (metis False domIff morphism.dom_ge)

      ultimately show ?thesis
        by simp
    qed
  qed

  ultimately show ?thesis
    using inv that by blast
qed


subsection \<open>Isomorphic Graphs\<close>
locale isomorphic_graphs = 
  G: graph V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G +
  H: graph V\<^sub>H E\<^sub>H s\<^sub>H s'\<^sub>H t\<^sub>H t'\<^sub>H l\<^sub>H l'\<^sub>H m\<^sub>H m'\<^sub>H for
  V\<^sub>G :: "'v\<^sub>G set" and E\<^sub>G :: "'e\<^sub>G set" and s\<^sub>G and s'\<^sub>G and t\<^sub>G and t'\<^sub>G and l\<^sub>G and l'\<^sub>G and m\<^sub>G and m'\<^sub>G and
  V\<^sub>H :: "'v\<^sub>H set" and E\<^sub>H :: "'e\<^sub>H set" and s\<^sub>H and s'\<^sub>H and t\<^sub>H and t'\<^sub>H and l\<^sub>H and l'\<^sub>H and m\<^sub>H and m'\<^sub>H +
assumes 
  are_iso: "\<exists>f\<^sub>V f\<^sub>E. bijective_morphism 
    V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G 
    V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H
    f\<^sub>V f\<^sub>E"

subsection \<open>Inclusion\<close>
locale inclusion_morphism = morphism +
  assumes
     inclusion_nodes: "v \<in> V\<^sub>G \<Longrightarrow> g'\<^sub>V v = v" and
     inclusion_edges: "e \<in> E\<^sub>G \<Longrightarrow> g'\<^sub>E e = e"
begin                                                               

lemma inclusion_nodes_alt:
  "g\<^sub>V e = Some y \<Longrightarrow> e = y"
  by (metis domI g\<^sub>V_def inclusion_nodes integrity_v option.sel)

lemma inclusion_edges_alt:
  "g\<^sub>E e = Some y \<Longrightarrow> e = y"
  by (metis domI dom_ge g\<^sub>E_def inclusion_edges option.sel)

lemma s_inclusion:
  "s\<^sub>G = s\<^sub>H |` E\<^sub>G"
  unfolding restrict_map_def
  by (metis G.integrity_s G.integrity_s' G.s_def H.integrity_s H.s_def domIff inclusion_edges inclusion_nodes integrity_e' option.exhaust_sel source_preserve_alt)

lemma t_inclusion:
  "t\<^sub>G = t\<^sub>H |` E\<^sub>G"
  unfolding restrict_map_def
  by (metis G.integrity_t G.integrity_t' G.t_def H.integrity_t H.t_def domIff inclusion_edges inclusion_nodes integrity_e' option.exhaust_sel target_preserve_alt)

lemma l_inclusion:
  "l\<^sub>G = l\<^sub>H |` V\<^sub>G"
  unfolding restrict_map_def
  by (metis G.integrity_l G.l_def H.integrity_l H.l_def domIff inclusion_nodes integrity_v' node_label_preserve' option.exhaust_sel)

lemma m_inclusion:
  "m\<^sub>G = m\<^sub>H |` E\<^sub>G"
  unfolding restrict_map_def
  by (metis G.integrity_m G.m_def H.integrity_m H.m_def domIff edge_label_preserve' inclusion_edges integrity_e' option.exhaust_sel)

lemma v_inclusion_alt:
  shows "v \<in> V\<^sub>G \<Longrightarrow> v \<in> V\<^sub>H"
  using inclusion_nodes integrity_v' by presburger

lemma e_inclusion_alt:
  shows "e \<in> E\<^sub>G \<Longrightarrow> e \<in> E\<^sub>H"
  using inclusion_edges integrity_e' by presburger

end

sublocale inclusion_morphism \<subseteq> injective_morphism
proof
  show \<open>inj_on (totalize g\<^sub>V) V\<^sub>G\<close>
    using inclusion_nodes inj_on_def by force
next
  show \<open>inj_on (totalize g\<^sub>E) E\<^sub>G\<close>
    using inclusion_edges inj_on_def by force
qed


sublocale inclusion_morphism \<subseteq> subgraphs
proof 
  show \<open>V\<^sub>G \<subseteq> V\<^sub>H\<close>
    using inclusion_nodes integrity_v' by auto
next
  show \<open>E\<^sub>G \<subseteq> E\<^sub>H\<close>
    using inclusion_edges integrity_e' by auto
next 
  show \<open>s\<^sub>G = s\<^sub>H |` E\<^sub>G\<close>
    by (simp add: s_inclusion)
next
  show \<open>t\<^sub>G = t\<^sub>H |` E\<^sub>G\<close>
    by (simp add: t_inclusion)
next
  show \<open>l\<^sub>G = l\<^sub>H |` V\<^sub>G\<close>
    by (simp add: l_inclusion)
next
  show \<open>m\<^sub>G = m\<^sub>H |` E\<^sub>G\<close>
    by (simp add: m_inclusion)
qed


text \<open>
For all graphs G and H, G is a subgraph of H if and only if there
is an inclusion inc : G to H.
\<close>

lemma "\<exists>f\<^sub>V f\<^sub>E. inclusion_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E \<longleftrightarrow> subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H"
proof -
  have a: \<open>\<exists>f\<^sub>V f\<^sub>E. inclusion_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E \<Longrightarrow> subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close>
    proof intro_locales
  show \<open>\<exists>f\<^sub>V f\<^sub>E. inclusion_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E \<Longrightarrow> graph V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G\<close>
    by (meson inclusion_morphism.axioms(1) morphism_def)
next
  show \<open>\<exists>f\<^sub>V f\<^sub>E. inclusion_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E \<Longrightarrow> graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close>
    by (meson inclusion_morphism.axioms(1) morphism_def)
next
  show \<open>\<exists>f\<^sub>V f\<^sub>E. inclusion_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E \<Longrightarrow> subgraphs_axioms V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close>
  proof
    show \<open> \<exists>f\<^sub>V f\<^sub>E. inclusion_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E \<Longrightarrow> V\<^sub>G \<subseteq> V\<^sub>H\<close>
      by (metis inclusion_morphism.axioms(1) inclusion_morphism.inclusion_nodes morphism.integrity_v' subsetI)
  next
    show \<open>\<exists>f\<^sub>V f\<^sub>E. inclusion_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E \<Longrightarrow> E\<^sub>G \<subseteq> E\<^sub>H\<close>
      by (metis inclusion_morphism.axioms(1) inclusion_morphism.inclusion_edges morphism.integrity_e' subsetI)
  next
    show \<open>\<exists>f\<^sub>V f\<^sub>E. inclusion_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E \<Longrightarrow> s\<^sub>G = s\<^sub>H |` E\<^sub>G\<close>
      by (meson inclusion_morphism.s_inclusion)
  next
    show \<open>\<exists>f\<^sub>V f\<^sub>E. inclusion_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E \<Longrightarrow> t\<^sub>G = t\<^sub>H |` E\<^sub>G\<close>
      by (meson inclusion_morphism.t_inclusion)
  next
    show \<open>\<exists>f\<^sub>V f\<^sub>E. inclusion_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E \<Longrightarrow> l\<^sub>G = l\<^sub>H |` V\<^sub>G\<close>
      by (meson inclusion_morphism.l_inclusion)
  next
    show \<open>\<exists>f\<^sub>V f\<^sub>E. inclusion_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E \<Longrightarrow> m\<^sub>G = m\<^sub>H |` E\<^sub>G\<close>
      by (meson inclusion_morphism.m_inclusion)
  qed
qed
  have b: \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> \<exists>f\<^sub>V f\<^sub>E. inclusion_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H f\<^sub>V f\<^sub>E\<close>
    proof (rule exI)+
  show \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow>
    inclusion_morphism V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H (\<lambda>v. if v \<in> V\<^sub>G then Some v else None) (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
  proof intro_locales
    show \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> graph V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G\<close>
      by (simp add: subgraphs_def)
  next
    show \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close>
      by (simp add: subgraphs_def)
  next
    show \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow>
    morphism_axioms V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H (\<lambda>v. if v \<in> V\<^sub>G then Some v else None)
     (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
    proof
      have a: \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> dom (\<lambda>v. if v \<in> V\<^sub>G then Some v else None) = V\<^sub>G\<close>
        by (simp add: dom_def)
      have b: \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> ran (\<lambda>v. if v \<in> V\<^sub>G then Some v else None) \<subseteq> V\<^sub>H\<close>
        by (smt (z3) mem_Collect_eq option.inject option.simps(3) ran_def subgraphs.subset_nodes subset_iff)
      from a b show \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow>
    dom (\<lambda>v. if v \<in> V\<^sub>G then Some v else None) = V\<^sub>G \<and> ran (\<lambda>v. if v \<in> V\<^sub>G then Some v else None) \<subseteq> V\<^sub>H\<close>
        by fastforce
    next
      show \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> dom (\<lambda>e. if e \<in> E\<^sub>G then Some e else None) = E\<^sub>G \<and> ran (\<lambda>e. if e \<in> E\<^sub>G then Some e else None) \<subseteq> E\<^sub>H\<close>
      proof
        show \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> dom (\<lambda>e. if e \<in> E\<^sub>G then Some e else None) = E\<^sub>G\<close>
          by (simp add: dom_def)
      next
        show \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> ran (\<lambda>e. if e \<in> E\<^sub>G then Some e else None) \<subseteq> E\<^sub>H\<close>
          by (smt (z3) mem_Collect_eq option.simps(1) option.simps(3) ran_def subgraphs.subset_edges subset_eq)
      qed
    next
      show \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> (\<lambda>v. if v \<in> V\<^sub>G then Some v else None) \<circ>\<^sub>m s\<^sub>G = s\<^sub>H \<circ>\<^sub>m (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
        unfolding map_comp_def
      proof
        show \<open>\<And>k. subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> (case s\<^sub>G k of None \<Rightarrow> None | Some v \<Rightarrow> if v \<in> V\<^sub>G then Some v else None) = (case if k \<in> E\<^sub>G then Some k else None of None \<Rightarrow> None | Some x \<Rightarrow> s\<^sub>H x)\<close>
        by (smt (z3) domIff graph.integrity_s graph.integrity_s' option.case_eq_if option.exhaust_sel option.simps(5) restrict_in subgraphs.axioms(1) subgraphs.s_equality)
    qed
  next
    show \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> (\<lambda>v. if v \<in> V\<^sub>G then Some v else None) \<circ>\<^sub>m t\<^sub>G = t\<^sub>H \<circ>\<^sub>m (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
      unfolding map_comp_def
    proof
      show \<open>\<And>k. subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> (case t\<^sub>G k of None \<Rightarrow> None | Some v \<Rightarrow> if v \<in> V\<^sub>G then Some v else None) = (case if k \<in> E\<^sub>G then Some k else None of None \<Rightarrow> None | Some x \<Rightarrow> t\<^sub>H x) \<close>
        by (smt (z3) domIff graph.integrity_t graph.integrity_t' option.case_eq_if option.exhaust_sel option.simps(5) restrict_in subgraphs.axioms(1) subgraphs.t_equality)
    qed
  next
    show \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> l\<^sub>G = l\<^sub>H \<circ>\<^sub>m (\<lambda>v. if v \<in> V\<^sub>G then Some v else None)\<close>
      unfolding map_comp_def
      by (metis (mono_tags, hide_lams) domIff graph.integrity_l option.simps(4) option.simps(5) restrict_in subgraphs.axioms(1) subgraphs.l_equality)
  next
    show \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> m\<^sub>G = m\<^sub>H \<circ>\<^sub>m (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
      unfolding map_comp_def
      using subgraphs.m_equality by fastforce
  qed
next
  show \<open>subgraphs V\<^sub>G E\<^sub>G s\<^sub>G t\<^sub>G l\<^sub>G m\<^sub>G V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H \<Longrightarrow> inclusion_morphism_axioms V\<^sub>G E\<^sub>G (\<lambda>v. if v \<in> V\<^sub>G then Some v else None) (\<lambda>e. if e \<in> E\<^sub>G then Some e else None)\<close>
    by (simp add: inclusion_morphism_axioms_def)
qed
qed
  from a b show ?thesis 
    by blast
qed



end