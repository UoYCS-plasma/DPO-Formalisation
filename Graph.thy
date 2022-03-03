
theory Graph
  imports Main
begin

  (* 

text \<open>
\begin{enumerate}
  \item dfsdf
\end{enumerate}

\begin{tikzpicture}
\draw [red] (0,0) rectangle (1,1);
\end{tikzpicture}
\<close> *)

section \<open>Graph\<close>
 

abbreviation totalize :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
"totalize f a \<equiv> the (f a)"

locale graph =
  fixes 
    V :: "'v set" and
    E :: "'e set" and
    s :: "'e \<rightharpoonup> 'v" and
    s':: "'e \<Rightarrow> 'v" and
    t :: "'e \<rightharpoonup> 'v" and
    t':: "'e \<Rightarrow> 'v" and
    l :: "'v \<rightharpoonup> '\<L>\<^sub>V" and
    l':: "'v \<Rightarrow> '\<L>\<^sub>V" and
    m :: "'e \<rightharpoonup> '\<L>\<^sub>E" and
    m':: "'e \<Rightarrow> '\<L>\<^sub>E"
  defines 
    s_def[simp]: \<open>s' \<equiv> totalize s\<close> and
    t_def[simp]: \<open>t' \<equiv> totalize t\<close> and
    l_def[simp]: \<open>l' \<equiv> totalize l\<close> and
    m_def[simp]: \<open>m' \<equiv> totalize m\<close>

assumes
  finite_nodes: "finite V" and
  finite_edges: "finite E" and
  integrity_s: "dom s = E \<and> ran s \<subseteq> V" and
  integrity_t: "dom t = E \<and> ran t \<subseteq> V" and
  integrity_l: "dom l = V" and
  integrity_m: "dom m = E"
begin


lemma integrity_s':
  shows "e \<in> E \<Longrightarrow>  s' e \<in> V"
    using integrity_s ranI by fastforce

lemma integrity_t':
  shows "e \<in> E \<Longrightarrow> t' e \<in> V"
using integrity_t ranI by fastforce 

lemma integrity_l':
  shows "v \<in> V \<Longrightarrow> l' v \<in> UNIV"
  by simp

lemma integrity_s_alt:
  shows "s e = Some y \<Longrightarrow> y \<in> V"
  by (meson integrity_s ranI subset_eq)

lemma integrity_t_alt:
  shows "t e = Some y \<Longrightarrow> y \<in> V"
  by (meson integrity_t ranI subset_eq)

end

text \<open>Empty Graph\<close>
interpretation \<emptyset>: graph 
  "{}" "{}" 
  "Map.empty" "totalize Map.empty"
  "Map.empty" "totalize Map.empty"
  "Map.empty" "totalize Map.empty"
  "Map.empty" "totalize Map.empty"
  by unfold_locales simp_all


locale subgraphs =
  G: graph V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G +
  H: graph V\<^sub>H E\<^sub>H s\<^sub>H s'\<^sub>H t\<^sub>H t'\<^sub>H l\<^sub>H l'\<^sub>H m\<^sub>H m'\<^sub>H for
  V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G
  V\<^sub>H E\<^sub>H s\<^sub>H s'\<^sub>H t\<^sub>H t'\<^sub>H l\<^sub>H l'\<^sub>H m\<^sub>H m'\<^sub>H +
assumes
  subset_nodes: "V\<^sub>G \<subseteq> V\<^sub>H" and
  subset_edges: "E\<^sub>G \<subseteq> E\<^sub>H" and
  s_equality: "s\<^sub>G = s\<^sub>H |` E\<^sub>G" and
  t_equality: "t\<^sub>G = t\<^sub>H |` E\<^sub>G" and
  l_equality: "l\<^sub>G = l\<^sub>H |` V\<^sub>G" and
  m_equality: "m\<^sub>G = m\<^sub>H |` E\<^sub>G"
begin

lemma s_equality_alt:
  assumes "s\<^sub>G = s\<^sub>H |` E\<^sub>G"
  shows "\<forall>e \<in> E\<^sub>G. s'\<^sub>G e = s'\<^sub>H e"
  by (simp add: s_equality)

lemma t_equality_alt:
  assumes "t\<^sub>G = t\<^sub>H |` E\<^sub>G"
  shows "\<forall>e \<in> E\<^sub>G. t'\<^sub>G e = t'\<^sub>H e"
  by (simp add: t_equality)

end


end