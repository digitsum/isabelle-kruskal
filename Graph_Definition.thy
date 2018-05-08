theory Graph_Definition
  imports
    Dijkstra_Shortest_Path.Graph
    Dijkstra_Shortest_Path.Weight
begin

section \<open>Definition\<close>

fun is_path_undir :: "('v, 'w) graph \<Rightarrow> 'v \<Rightarrow> ('v,'w) path \<Rightarrow> 'v \<Rightarrow> bool" where
    "is_path_undir G v [] v' \<longleftrightarrow> v=v' \<and> v'\<in>nodes G" |
    "is_path_undir G v ((v1,w,v2)#p) v' \<longleftrightarrow> v=v1 \<and> ((v1,w,v2)\<in>edges G \<or> (v2,w,v1)\<in>edges G) \<and> is_path_undir G v2 p v'"

abbreviation "edges_connected G a b \<equiv> \<exists>p. is_path_undir G a p b"

definition degree :: "('v, 'w) graph \<Rightarrow> 'v \<Rightarrow> nat" where
  "degree G v = card {e\<in>edges G. fst e = v \<or> snd (snd e) = v}"

locale forest = valid_graph G
  for G :: "('v,'w) graph" +
  assumes cycle_free:
    "\<forall>(a,w,b)\<in>E. \<not> edges_connected (delete_edge a w b G) a b"

locale connected_graph = valid_graph G
  for G :: "('v,'w) graph" +
  assumes connected:
    "\<forall>v\<in>V. \<forall>v'\<in>V. edges_connected G v v'"

locale tree = forest + connected_graph

locale finite_graph = valid_graph G
  for G :: "('v,'w) graph" +
  assumes finite_E: "finite E"

locale finite_weighted_graph = finite_graph G
  for G :: "('v,'w::weight) graph"

definition subgraph :: "('v, 'w) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "subgraph G H \<equiv> nodes G = nodes H \<and> edges G \<subseteq> edges H"

definition edge_weight :: "('v, 'w) graph \<Rightarrow> 'w::weight" where
  "edge_weight G \<equiv> sum (fst o snd) (edges G)"

definition edges_less_eq :: "('a \<times> 'w::weight \<times> 'a) \<Rightarrow> ('a \<times> 'w \<times> 'a) \<Rightarrow> bool"
  where "edges_less_eq a b \<equiv> fst(snd a) \<le> fst(snd b)"

definition maximal_connected :: "('v, 'w) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "maximal_connected H G \<equiv> \<forall>v\<in>nodes G. \<forall>v'\<in>nodes G.
    (edges_connected G v v') \<longrightarrow> (edges_connected H v v')"

definition is_spanning_forest :: "('v, 'w) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "is_spanning_forest F G \<equiv> forest F \<and> maximal_connected F G \<and> subgraph F G"

definition is_optimal_forest :: "('v, 'w::weight) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "is_optimal_forest F G \<equiv> (\<forall>F'::('v, 'w) graph.
      is_spanning_forest F' G \<longrightarrow> edge_weight F \<le> edge_weight F')"

definition is_minimum_spanning_forest :: "('v, 'w::weight) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "is_minimum_spanning_forest F G \<equiv> is_spanning_forest F G \<and> is_optimal_forest F G"

definition is_spanning_tree :: "('v, 'w) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "is_spanning_tree F G \<equiv> tree F \<and> subgraph F G"

definition is_optimal_tree :: "('v, 'w::weight) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "is_optimal_tree F G \<equiv> (\<forall>F'::('v, 'w) graph.
      is_spanning_tree F' G \<longrightarrow> edge_weight F \<le> edge_weight F')"

definition is_minimum_spanning_tree :: "('v, 'w::weight) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "is_minimum_spanning_tree F G \<equiv> is_spanning_tree F G \<and> is_optimal_tree F G"

section \<open>Helping lemmas\<close>

lemma nodes_delete_edge[simp]:
  "nodes (delete_edge v e v' G) = nodes G"
  by (simp add: delete_edge_def)

lemma edges_delete_edge[simp]:
  "edges (delete_edge v e v' G) = edges G - {(v,e,v')}"
  by (simp add: delete_edge_def)

lemma subgraph_node:
  assumes "subgraph H G"
  shows "v \<in> nodes G \<longleftrightarrow> v \<in> nodes H"
  using assms
  unfolding subgraph_def
  by simp

lemma delete_add_edge:
  assumes "a \<in> nodes H"
  assumes "c \<in> nodes H"
  assumes "(a, w, c) \<notin> edges H"
  shows "delete_edge a w c (add_edge a w c H) = H"
  using assms unfolding delete_edge_def add_edge_def
  by (simp add: insert_absorb)

lemma swap_delete_add_edge:
  assumes "(a, b, c) \<noteq> (x, y, z)"
  shows "delete_edge a b c (add_edge x y z H) = add_edge x y z (delete_edge a b c H)"
  using assms unfolding delete_edge_def add_edge_def
  by auto

lemma swap_delete_edges: "delete_edge a b c (delete_edge x y z H) = delete_edge x y z (delete_edge a b c H)"
  unfolding delete_edge_def
  by auto

context valid_graph
begin
  lemma valid_subgraph:
    assumes "subgraph H G"
    shows "valid_graph H"
    using assms E_valid unfolding subgraph_def valid_graph_def
    by blast

  lemma is_path_undir_simps[simp, intro!]:
    "is_path_undir G v [] v \<longleftrightarrow> v\<in>V"
    "is_path_undir G v [(v,w,v')] v' \<longleftrightarrow> (v,w,v')\<in>E \<or> (v',w,v)\<in>E"
    by (auto dest: E_validD)

  lemma is_path_undir_memb[simp]:
    "is_path_undir G v p v' \<Longrightarrow> v\<in>V \<and> v'\<in>V"
    apply (induct p arbitrary: v)
    apply (auto dest: E_validD)
    done

  lemma is_path_undir_memb_edges:
    assumes "is_path_undir G v p v'"
    shows "\<forall>(a,w,b) \<in> set p. (a,w,b) \<in> E \<or> (b,w,a) \<in> E"
    using assms
    by (induct p arbitrary: v) fastforce+

  lemma is_path_undir_split:
    "is_path_undir G v (p1@p2) v' \<longleftrightarrow> (\<exists>u. is_path_undir G v p1 u \<and> is_path_undir G u p2 v')"
    by (induct p1 arbitrary: v) auto

  lemma is_path_undir_split'[simp]:
    "is_path_undir G v (p1@(u,w,u')#p2) v'
      \<longleftrightarrow> is_path_undir G v p1 u \<and> ((u,w,u')\<in>E \<or> (u',w,u)\<in>E) \<and> is_path_undir G u' p2 v'"
    by (auto simp add: is_path_undir_split)

  lemma is_path_undir_sym:
    assumes "is_path_undir G v p v'"
    shows "is_path_undir G v' (rev (map (\<lambda>(u, w, u'). (u', w, u)) p)) v"
    using assms
    by (induct p arbitrary: v) (auto simp: E_validD)

  lemma is_path_undir_subgraph:
    assumes "is_path_undir H x p y"
    assumes "subgraph H G"
    shows "is_path_undir G x p y"
    using assms is_path_undir.simps
    unfolding subgraph_def
    by (induction p arbitrary: x y) auto

  lemma no_path_in_empty_graph:
    assumes "E = {}"
    assumes "p \<noteq> []"
    shows "\<not>is_path_undir G v p v"
    using assms by (cases p) auto

  lemma is_path_undir_split_distinct:
    assumes "is_path_undir G v p v'"
    assumes "(a, w, b) \<in> set p \<or> (b, w, a) \<in> set p"
    shows "(\<exists>p' p'' u u'.
            is_path_undir G v p' u \<and> is_path_undir G u' p'' v' \<and>
            length p' < length p \<and> length p'' < length p \<and>
            (u \<in> {a, b} \<and> u' \<in> {a, b}) \<and>
            (a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p' \<and>
            (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p'')"
    using assms
  proof (induction n == "length p" arbitrary: p v v' rule: nat_less_induct)
    case 1
    then obtain u u' where "(u, w, u') \<in> set p" and u: "u \<in> {a, b} \<and> u' \<in> {a, b}"
      by blast
    with split_list obtain p' p''
      where p: "p = p' @ (u, w, u') # p''"
      by fast
    then have len_p': "length p' < length p" and len_p'': "length p'' < length p"
      by auto
    from 1 p have p': "is_path_undir G v p' u" and p'': "is_path_undir G u' p'' v'"
      by auto
    from 1 len_p' p' have "(a, w, b) \<in> set p' \<or> (b, w, a) \<in> set p' \<longrightarrow> (\<exists>p'' p''' u' u''.
            is_path_undir G v p'' u' \<and> is_path_undir G u'' p''' u \<and>
            length p'' < length p' \<and> length p''' < length p' \<and>
            (u' \<in> {a, b} \<and> u'' \<in> {a, b}) \<and>
            (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p'' \<and>
            (a, w, b) \<notin> set p''' \<and> (b, w, a) \<notin> set p''')"
      by simp
    with len_p' p' u have p': "\<exists>p' u. is_path_undir G v p' u \<and> length p' < length p \<and>
      u \<in> {a,b} \<and> (a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p'"
      by fastforce
    from 1 len_p'' p'' have "(a, w, b) \<in> set p'' \<or> (b, w, a) \<in> set p'' \<longrightarrow> (\<exists>p' p''' u u''.
            is_path_undir G u' p' u \<and> is_path_undir G u'' p''' v' \<and>
            length p' < length p'' \<and> length p''' < length p'' \<and>
            (u \<in> {a, b} \<and> u'' \<in> {a, b}) \<and>
            (a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p' \<and>
            (a, w, b) \<notin> set p''' \<and> (b, w, a) \<notin> set p''')"
      by simp
    with len_p'' p'' u have "\<exists>p'' u'. is_path_undir G u' p'' v'\<and> length p'' < length p \<and>
      u' \<in> {a,b} \<and> (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p''"
      by fastforce
    with p' show ?case by auto
  qed

  lemma add_edge_is_path:
    assumes "is_path_undir G x p y"
    shows "is_path_undir (add_edge a b c G) x p y"
  proof -
    from E_valid have "valid_graph (add_edge a b c G)"
      unfolding valid_graph_def add_edge_def
      by auto
    with assms is_path_undir.simps[of "add_edge a b c G"]
    show "is_path_undir (add_edge a b c G) x p y"
      by (induction p arbitrary: x y) auto
  qed

  lemma add_edge_was_path:
    assumes "is_path_undir (add_edge a b c G) x p y"
    assumes "(a, b, c) \<notin> set p"
    assumes "(c, b, a) \<notin> set p"
    assumes "a \<in> V"
    assumes "c \<in> V"
    shows "is_path_undir G x p y"
  proof -
    from E_valid have "valid_graph (add_edge a b c G)"
      unfolding valid_graph_def add_edge_def
      by auto
    with assms is_path_undir.simps[of "add_edge a b c G"]
    show "is_path_undir G x p y"
      by (induction p arbitrary: x y) auto
  qed

  lemma delete_edge_is_path:
    assumes "is_path_undir G x p y"
    assumes "(a, b, c) \<notin> set p"
    assumes "(c, b, a) \<notin> set p"
    shows "is_path_undir (delete_edge a b c G) x p y"
  proof -
    from E_valid have "valid_graph (delete_edge a b c G)"
      unfolding valid_graph_def delete_edge_def
      by auto
    with assms is_path_undir.simps[of "delete_edge a b c G"]
    show ?thesis
      by (induction p arbitrary: x y) auto
  qed

  lemma delete_edge_was_path:
    assumes "is_path_undir (delete_edge a b c G) x p y"
    shows "is_path_undir G x p y"
    using assms
    by (induction p arbitrary: x y) auto

  lemma subset_was_path:
    assumes "is_path_undir H x p y"
    assumes "edges H \<subseteq> E"
    assumes "nodes H \<subseteq> V"
    shows "is_path_undir G x p y"
    using assms
    by (induction p arbitrary: x y) auto

  lemma delete_node_was_path:
    assumes "is_path_undir (delete_node v G) x p y"
    shows "is_path_undir G x p y"
    using assms
    unfolding delete_node_def
    by (induction p arbitrary: x y) auto

  lemma add_edge_preserve_subgraph:
    assumes "subgraph H G"
    assumes "(a, w, b) \<in> E"
    shows "subgraph (add_edge a w b H) G"
  proof -
    from assms E_validD have "a \<in> nodes H \<and> b \<in> nodes H"
      unfolding subgraph_def by simp
    with assms show ?thesis
      unfolding subgraph_def
      by auto
  qed

  lemma delete_edge_preserve_subgraph:
    assumes "subgraph H G"
    shows "subgraph (delete_edge a w b H) G"
    using assms
    unfolding subgraph_def
    by auto

  lemma add_delete_edge:
    assumes "(a, w, c) \<in> E"
    shows "add_edge a w c (delete_edge a w c G) = G"
    using assms E_validD unfolding delete_edge_def add_edge_def
    by (simp add: insert_absorb)

  lemma swap_add_edge_in_path:
    assumes "is_path_undir (add_edge a w b G) v p v'"
    assumes "(a,w',a') \<in> E \<or> (a',w',a) \<in> E"
    shows "\<exists>p. is_path_undir (add_edge a' w'' b G) v p v'"
  using assms(1)
  proof (induction p arbitrary: v)
    case Nil
    with assms(2) E_validD
    have "is_path_undir (add_edge a' w'' b G) v [] v'"
      by auto
    then show ?case
      by blast
  next
    case (Cons e p')
    then obtain v2 x e_w where "e = (v2, e_w, x)"
      using prod_cases3 by blast
    with Cons(2)
    have e: "e = (v, e_w, x)" and
         edge_e: "(v, e_w, x) \<in> edges (add_edge a w b G) \<or> (x, e_w, v) \<in> edges (add_edge a w b G)" and
         p': "is_path_undir (add_edge a w b G) x p' v'"
      by auto
    have "\<exists>p. is_path_undir (add_edge a' w'' b G) v p x"
    proof (cases "e = (a, w, b) \<or> e = (b, w, a)")
      case True
      from True e assms(2) E_validD have "is_path_undir (add_edge a' w'' b G) v [(a,w',a'), (a',w'',b)] x
          \<or> is_path_undir (add_edge a' w'' b G) v [(b,w'',a'), (a',w',a)] x"
        by auto
      then show ?thesis
        by blast
    next
      case False
      with edge_e e
      have "is_path_undir (add_edge a' w'' b G) v [e] x"
        by (auto simp: E_validD)
      then show ?thesis
        by auto
    qed
    with p' Cons.IH valid_graph.is_path_undir_split[OF add_edge_valid[OF valid_graph.intro[OF E_valid]]]
    show ?case
      by blast
  qed

  lemma induce_maximal_connected:
    assumes "subgraph H G"
    assumes "\<forall>(a,w,b)\<in>E. edges_connected H a b"
    shows "maximal_connected H G"
  proof -
    from valid_subgraph[OF \<open>subgraph H G\<close>]
    have valid_H: "valid_graph H" .
    have "(edges_connected G v v') \<longrightarrow> (edges_connected H v v')" (is "?lhs \<longrightarrow> ?rhs")
      if v: "v\<in>V" and v': "v'\<in>V" for v v'
    proof
      assume ?lhs
      then obtain p where "is_path_undir G v p v'"
        by blast
      with v show ?rhs
      proof (induction p arbitrary: v v')
        case Nil
        with subgraph_node[OF assms(1)] show ?case
          by (metis is_path_undir.simps(1))
      next
        case (Cons e p)
        then show ?case
        proof (cases e)
          case (fields a w b)
          with assms Cons valid_graph.is_path_undir_sym[OF valid_H, of b _ a]
          obtain p' where p': "is_path_undir H a p' b"
            by fastforce
          from assms fields Cons.prems Cons.IH[of b v']
          obtain p'' where "is_path_undir H b p'' v'"
            unfolding subgraph_def by auto
          with Cons.prems fields assms p' valid_graph.is_path_undir_split[OF valid_H]
            have "is_path_undir H v (p'@p'') v'"
              by auto
          then show ?thesis ..
        qed
      qed
    qed
    with assms show ?thesis
      unfolding maximal_connected_def
      by auto
  qed

  lemma sub_spanning_forest_eq:
    assumes "is_spanning_forest H G"
    assumes "is_spanning_forest T G"
    assumes "subgraph H T"
    shows "H = T"
  proof -
    from \<open>is_spanning_forest H G\<close> \<open>is_spanning_forest T G\<close>
    have valid_H: "valid_graph H" and valid_T: "valid_graph T"
      and forest_H: "forest H" and forest_T: "forest T"
      unfolding is_spanning_forest_def forest_def
      by auto
    have "edges T \<subseteq> edges H"
    proof
      fix x
      assume asm: "x \<in> edges T"
      show "x \<in> edges H"
      proof (rule ccontr)
        assume asm': "x \<notin> edges H"
        from prod_cases3 obtain a w b where x: "x = (a, w, b)" .
        with asm asm' \<open>subgraph H T\<close> have subgraph': "subgraph H (delete_edge a w b T)"
          unfolding subgraph_def delete_edge_def
          by auto
        from valid_T have valid_delete_T: "valid_graph (delete_edge a w b T)"
          by simp
        from asm x E_validD \<open>is_spanning_forest T G\<close>
        have "a \<in> V" "b \<in> V"
          unfolding is_spanning_forest_def subgraph_def
          by auto
        from \<open>is_spanning_forest T G\<close> is_path_undir_subgraph
          valid_graph.is_path_undir_simps(2)[OF valid_T]
          asm x
        have "\<exists>p. is_path_undir G a p b"
          unfolding is_spanning_forest_def
          by blast
        with \<open>is_spanning_forest H G\<close> \<open>a\<in>V\<close> \<open>b\<in>V\<close>
        obtain p where p:"is_path_undir H a p b"
          unfolding is_spanning_forest_def maximal_connected_def
          by blast
        from valid_graph.is_path_undir_subgraph[OF valid_delete_T p subgraph']
        have "is_path_undir (delete_edge a w b T) a p b"
          by simp
        with forest.cycle_free[OF forest_T] asm x show False
          by auto
      qed
    qed
    with assms show ?thesis
      unfolding subgraph_def by simp
  qed

  lemma add_edge_maximal_connected:
    assumes "maximal_connected H G"
    assumes "subgraph H G"
    assumes "(a, w, b) \<in> E"
    shows "maximal_connected (add_edge a w b H) G"
  proof -
    have "(edges_connected G v v') \<longrightarrow> (edges_connected (add_edge a w b H) v v')" (is "?lhs \<longrightarrow> ?rhs")
      if vv': "v \<in> V" "v' \<in> V" for v v'
    proof
      assume ?lhs
      with \<open>maximal_connected H G\<close> vv' obtain p where "is_path_undir H v p v'"
        unfolding maximal_connected_def
        by auto
      with valid_graph.add_edge_is_path[OF valid_subgraph[OF \<open>subgraph H G\<close>] this]
      show ?rhs
        by auto
    qed
    then show ?thesis
      unfolding maximal_connected_def
      by auto
  qed

  lemma delete_edge_maximal_connected:
    assumes "maximal_connected H G"
    assumes "subgraph H G"
    assumes pab: "is_path_undir (delete_edge a w b H) a pab b"
    shows "maximal_connected (delete_edge a w b H) G"
  proof -
    from valid_subgraph[OF \<open>subgraph H G\<close>]
    have valid_H: "valid_graph H" .
    have "(edges_connected G v v') \<longleftrightarrow> (edges_connected (delete_edge a w b H) v v')" (is "?lhs \<longleftrightarrow> ?rhs")
      if vv': "v \<in> V" "v' \<in> V" for v v'
    proof
      assume ?lhs
      with \<open>maximal_connected H G\<close> vv' obtain p where p: "is_path_undir H v p v'"
        unfolding maximal_connected_def
        by auto
      show ?rhs
      proof (cases "(a, w, b) \<notin> set p \<and> (b, w, a) \<notin> set p")
        case True
        with valid_graph.delete_edge_is_path[OF valid_H p] show ?thesis
          by auto
      next
        case False
        with p valid_graph.is_path_undir_split_distinct[OF valid_H p, of a w b] obtain p' p'' u u'
          where "is_path_undir H v p' u \<and> is_path_undir H u' p'' v'" and
            u: "(u \<in> {a, b} \<and> u' \<in> {a, b})" and
            "(a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p' \<and>
            (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p''"
          by auto
        with valid_graph.delete_edge_is_path[OF valid_H] obtain p' p''
          where p': "is_path_undir (delete_edge a w b H) v p' u \<and>
                 is_path_undir (delete_edge a w b H) u' p'' v'"
          by blast
        from valid_graph.is_path_undir_sym[OF delete_edge_valid[OF valid_H] pab] obtain pab'
          where "is_path_undir (delete_edge a w b H) b pab' a"
          by auto
        with assms u p' valid_graph.is_path_undir_split[OF delete_edge_valid[OF valid_H], of a w b v p' p'' v']
          valid_graph.is_path_undir_split[OF delete_edge_valid[OF valid_H], of a w b v p' pab b]
          valid_graph.is_path_undir_split[OF delete_edge_valid[OF valid_H], of a w b v "p'@pab" p'' v']
          valid_graph.is_path_undir_split[OF delete_edge_valid[OF valid_H], of a w b v p' pab' a]
          valid_graph.is_path_undir_split[OF delete_edge_valid[OF valid_H], of a w b v "p'@pab'" p'' v']
        show ?thesis by auto
      qed
    next
      assume ?rhs
      from delete_edge_preserve_subgraph[OF \<open>subgraph H G\<close>]
      have "subgraph (delete_edge a w b H) G" .
      with \<open>?rhs\<close> is_path_undir_subgraph show ?lhs
        by blast
    qed
    then show ?thesis
      unfolding maximal_connected_def
      by auto
  qed

  lemma connected_impl_maximal_connected:
    assumes "connected_graph H"
    assumes subgraph: "subgraph H G"
    shows "maximal_connected H G"
    using assms valid_subgraph[OF subgraph]
      is_path_undir_subgraph[OF _ subgraph]
    unfolding connected_graph_def connected_graph_axioms_def maximal_connected_def
      subgraph_def
    by blast

  lemma add_edge_is_connected:
    "edges_connected (add_edge a b c G) a c"
    "edges_connected (add_edge a b c G) c a"
  using valid_graph.is_path_undir_simps(2)[OF
        add_edge_valid[OF valid_graph_axioms], of a b c a b c]
      valid_graph.is_path_undir_simps(2)[OF
        add_edge_valid[OF valid_graph_axioms], of a b c c b a]
  by fastforce+

  lemma swap_edges:
    assumes "edges_connected (add_edge a w b G) v v'"
    assumes "a \<in> V"
    assumes "b \<in> V"
    shows "edges_connected (add_edge v w' v' G) a b \<or> edges_connected G v v'"
  proof -
    from assms(1) obtain p where p: "is_path_undir (add_edge a w b G) v p v'"
      by auto
    show ?thesis
    proof (cases "(a, w, b) \<in> set p \<or> (b, w, a) \<in> set p")
      case True
      from valid_graph.is_path_undir_split_distinct[OF
          add_edge_valid[OF valid_graph_axioms] p True]
      obtain p' p'' u u' where
           "is_path_undir (add_edge a w b G) v p' u \<and>
            is_path_undir (add_edge a w b G) u' p'' v'" and
            u: "u \<in> {a, b} \<and> u' \<in> {a, b}" and
            "(a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p' \<and>
            (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p'' "
        by auto
      with assms add_edge_was_path
      have paths: "is_path_undir G v p' u \<and>
                   is_path_undir G u' p'' v'"
        by blast
      show ?thesis
      proof (cases "u = u'")
        case True
        with paths is_path_undir_split[of v p' p'' v']
        show ?thesis
          by auto
      next
        case False
        from paths assms add_edge_is_path
        obtain p' p'' where
          paths': "is_path_undir (add_edge v w' v' G) v p' u \<and>
                  is_path_undir (add_edge v w' v' G) u' p'' v'"
          by blast
        from add_edge_is_connected obtain p''' where
          "is_path_undir (add_edge v w' v' G) v' p''' v"
          by blast
        with paths' valid_graph.is_path_undir_split[OF add_edge_valid[OF valid_graph_axioms], of v w' v' u' p'' p''' v]
        have "is_path_undir (add_edge v w' v' G) u' (p''@p''') v"
            by auto
        with paths' valid_graph.is_path_undir_split[OF add_edge_valid[OF valid_graph_axioms], of v w' v' u' "p''@p'''" p' u]
        have "is_path_undir (add_edge v w' v' G) u' (p''@p'''@p') u"
            by auto
        with u False valid_graph.is_path_undir_sym[OF add_edge_valid[OF valid_graph_axioms] this]
        show ?thesis
          by auto
      qed
    next
      case False
      with add_edge_was_path[OF p _ _ assms(2,3)]
      show ?thesis by auto
    qed
  qed

  lemma subgraph_impl_connected:
    assumes "connected_graph H"
    assumes subgraph: "subgraph H G"
    shows "connected_graph G"
    using assms is_path_undir_subgraph[OF _ subgraph] valid_graph_axioms
    unfolding connected_graph_def connected_graph_axioms_def maximal_connected_def
      subgraph_def
    by blast

  lemma add_node_connected:
    assumes "\<forall>a\<in>V - {v}. \<forall>b\<in>V - {v}. edges_connected G a b"
    assumes "(v, w, v') \<in> E \<or> (v', w, v) \<in> E"
    assumes "v \<noteq> v'"
    shows "\<forall>a\<in>V. \<forall>b\<in>V. edges_connected G a b"
  proof -
    have "edges_connected G a b" if a: "a\<in>V" and b: "b\<in>V" for a b
    proof (cases "a = v")
      case True
      show ?thesis
      proof (cases "b = v")
        case True
        with \<open>a = v\<close> a is_path_undir_simps(1) show ?thesis
          by blast
      next
        case False
        from assms(2) have "v' \<in> V"
          by (auto simp: E_validD)
        with b assms(1) \<open>b \<noteq> v\<close> \<open>v \<noteq> v'\<close> have "edges_connected G v' b"
          by blast
        with assms(2) \<open>a = v\<close> is_path_undir.simps(2)[of G v v w v' _ b]
        show ?thesis
          by blast
      qed
    next
      case False
      show ?thesis
      proof (cases "b = v")
        case True
        from assms(2) have "v' \<in> V"
          by (auto simp: E_validD)
        with a assms(1) \<open>a \<noteq> v\<close> \<open>v \<noteq> v'\<close> have "edges_connected G a v'"
          by blast
        with assms(2) \<open>b = v\<close> is_path_undir.simps(2)[of G v v w v' _ a]
          is_path_undir_sym
        show ?thesis
          by blast
      next
        case False
        with \<open>a \<noteq> v\<close> assms(1) a b show ?thesis
          by simp
      qed
    qed
    then show ?thesis by simp
  qed
end

context connected_graph
begin
  lemma maximal_connected_impl_connected:
    assumes "maximal_connected H G"
    assumes subgraph: "subgraph H G"
    shows "connected_graph H"
    using assms connected_graph_axioms valid_subgraph[OF subgraph]
    unfolding connected_graph_def connected_graph_axioms_def maximal_connected_def
      subgraph_def
    by auto
end

context forest
begin
  lemma delete_edge_from_path:
    assumes "edges_connected G a b"
    assumes "subgraph H G"
    assumes "\<not> edges_connected H a b"
    shows "\<exists>(x, w, y) \<in> E - edges H.  (\<not> edges_connected (delete_edge x w y G) a b) \<and>
      (edges_connected (add_edge a w' b (delete_edge x w y G)) x y)"
  proof -
    from assms(1) obtain p where "is_path_undir G a p b"
      by auto
    from this assms(3) show ?thesis
    proof (induction n == "length p" arbitrary: p a rule: nat_less_induct)
      case 1
      from valid_subgraph[OF assms(2)] have valid_H: "valid_graph H" .
      show ?case
      proof (cases p)
        case Nil
        with 1(2) have "a = b"
          by simp
        with 1(2) assms(2) have "is_path_undir H a [] b"
          unfolding subgraph_def
          by auto
        with 1(3) show ?thesis
          by blast
      next
        case (Cons e p')
        from 1 obtain a2 a' w where "e = (a2, w, a')"
          using prod_cases3 by blast
        with 1(2) Cons have e: "e = (a, w, a')"
          by simp
        with 1(2) Cons obtain e1 e2 where e12: "e = (e1, w, e2) \<or> e = (e2, w, e1)" and
          edge_e12: "(e1, w, e2) \<in> E"
          by auto
        from 1(2) Cons e have "is_path_undir G a' p' b"
          by simp
        with is_path_undir_split_distinct[OF this, of a w a'] Cons
        obtain p'_dst u' where  p'_dst: "is_path_undir G u' p'_dst b \<and> u' \<in> {a, a'}" and
            e_not_in_p': "(a, w, a') \<notin> set p'_dst \<and> (a', w, a) \<notin> set p'_dst" and
            len_p': "length p'_dst < length p"
          by fastforce
        show ?thesis
        proof (cases "u' = a'")
          case False
          with 1 len_p' p'_dst show ?thesis
            by auto
        next
          case True
          with p'_dst have path_p': "is_path_undir G a' p'_dst b"
            by auto
          show ?thesis
          proof (cases "(e1, w, e2) \<in> edges H")
            case True
            have "\<nexists>p. is_path_undir H a' p b"
            proof
              assume "\<exists>p. is_path_undir H a' p b"
              then obtain p_H where "is_path_undir H a' p_H b"
                by auto
              with True e12 e have "is_path_undir H a (e#p_H) b"
                by auto
              with 1(3) show False
                by simp
            qed
            with path_p' 1(1) len_p' obtain x z y where xy: "(x, z, y) \<in> E - edges H" and
              IH1: "(\<not>edges_connected (delete_edge x z y G) a' b)" and
              IH2: "(edges_connected (add_edge a' w' b (delete_edge x z y G)) x y)"
              by blast
            have xy_neq_aa': "(x, z, y) \<noteq> (a', w, a) \<and> (x, z, y) \<noteq> (a, w, a')"
            proof (rule ccontr)
              assume "\<not> ((x, z, y) \<noteq> (a', w, a) \<and> (x, z, y) \<noteq> (a, w, a'))"
              with e_not_in_p' have "(x, z, y) \<notin> set p'_dst \<and> (y, z, x) \<notin> set p'_dst"
                by auto
              with delete_edge_is_path[OF path_p'] IH1
              show False
                by auto
            qed
            have thm1: "\<not> edges_connected (delete_edge x z y G) a b"
            proof
              assume "edges_connected (delete_edge x z y G) a b"
              then obtain p_e where "is_path_undir (delete_edge x z y G) a p_e b"
                by auto
              with True edge_e12 e12 e xy_neq_aa' have "is_path_undir (delete_edge x z y G) a' ((a', w, a)#p_e) b"
                by auto
              with IH1 show False
                by blast
            qed
            from IH2 obtain p_ad where "is_path_undir (add_edge a' w' b (delete_edge x z y G)) x p_ad y"
              by auto
            from valid_graph.swap_add_edge_in_path[OF delete_edge_valid[OF valid_graph_axioms] this, of w a] edge_e12
              e12 e edges_delete_edge[of x z y G] xy_neq_aa'
            have thm2: "\<exists>p. is_path_undir (add_edge a w' b (delete_edge x z y G)) x p y"
              by blast
            with thm1 show ?thesis
              using xy by auto
          next
            case False
            have thm1: "\<not> edges_connected (delete_edge e1 w e2 G) a b"
            proof
              assume "edges_connected (delete_edge e1 w e2 G) a b"
              then obtain p_e where p_e: "is_path_undir (delete_edge e1 w e2 G) a p_e b"
                by auto
              from delete_edge_is_path[OF path_p', of e1 w e2] e_not_in_p' e12 e
              obtain p_d where "is_path_undir (delete_edge e1 w e2 G) a' p_d b"
                by auto
              with valid_graph.is_path_undir_sym[OF delete_edge_valid[OF valid_graph_axioms] this]
              obtain p_rev where "is_path_undir (delete_edge e1 w e2 G) b p_rev a'"
                by auto
              with p_e valid_graph.is_path_undir_split[OF delete_edge_valid[OF valid_graph_axioms]]
              have "is_path_undir (delete_edge e1 w e2 G) a (p_e@p_rev) a'"
                by auto
              with cycle_free edge_e12 e12 e valid_graph.is_path_undir_sym[OF delete_edge_valid[OF valid_graph_axioms] this]
              show False
                unfolding valid_graph_def
                by auto
            qed
            from valid_graph.is_path_undir_split[OF add_edge_valid[OF delete_edge_valid[OF valid_graph_axioms]]]
              valid_graph.add_edge_is_path[OF delete_edge_valid[OF valid_graph_axioms]
                                              delete_edge_is_path[OF path_p', of e1 w e2], of a w' b]
              valid_graph.is_path_undir_simps(2)[OF add_edge_valid[OF delete_edge_valid[OF valid_graph_axioms]],
                                                 of a w' b e1 w e2 b w' a]
              e_not_in_p' e12 e
            have "is_path_undir (add_edge a w' b (delete_edge e1 w e2 G)) a' (p'_dst@[(b,w',a)]) a"
              by auto
            with valid_graph.is_path_undir_sym[OF add_edge_valid[OF delete_edge_valid[OF valid_graph_axioms]] this]
              e12 e
            have "edges_connected (add_edge a w' b (delete_edge e1 w e2 G)) e1 e2"
              by blast
            with thm1 show ?thesis
              using False edge_e12 by auto
          qed
        qed
      qed
    qed
  qed

  lemma forest_add_edge:
    assumes "a \<in> V"
    assumes "c \<in> V"
    assumes "\<not> edges_connected G a c"
    shows "forest (add_edge a w c G)"
  proof -
    from assms(3) have "\<not> is_path_undir G a [(a, w, c)] c"
      by blast
    with assms(2) have awc: "(a, w, c) \<notin> E \<and> (c, w, a) \<notin> E"
      by auto
    have "\<not> edges_connected (delete_edge v w' v' (add_edge a w c G)) v v'"
       if e: "(v,w',v')\<in> edges (add_edge a w c G)" for v w' v'
    proof (cases "(v,w',v') = (a, w, c)")
      case True
      with assms awc delete_add_edge[of a G c w]
      show ?thesis by simp
    next
      case False
      with e have e': "(v,w',v')\<in> edges G"
        by auto
      show ?thesis
      proof
        assume asm: "edges_connected (delete_edge v w' v' (add_edge a w c G)) v v'"
        with swap_delete_add_edge[OF False, of G]
          valid_graph.swap_edges[OF delete_edge_valid[OF valid_graph_axioms], of a w c v w' v' v v' w']
          add_delete_edge[OF e'] cycle_free assms(1,2) e'
        have "edges_connected G a c"
          by force
        with assms show False
          by simp
      qed
    qed
    with cycle_free add_edge_valid[OF valid_graph_axioms] show ?thesis
      unfolding forest_def forest_axioms_def by auto
  qed

  lemma forest_subsets:
    assumes "valid_graph H"
    assumes "edges H \<subseteq> E"
    assumes "nodes H \<subseteq> V"
    shows "forest H"
  proof -
    have "\<not> edges_connected (delete_edge a w b H) a b"
      if e: "(a, w, b)\<in>edges H" for a w b
    proof
      assume asm: "edges_connected (delete_edge a w b H) a b"
      from \<open>edges H \<subseteq> E\<close> have edges: "edges (delete_edge a w b H) \<subseteq> edges (delete_edge a w b G)"
        by auto
      from \<open>nodes H \<subseteq> V\<close> have nodes: "nodes (delete_edge a w b H) \<subseteq> nodes (delete_edge a w b G)"
        by auto
      from asm valid_graph.subset_was_path[OF delete_edge_valid[OF valid_graph_axioms] _ edges nodes]
      have "edges_connected (delete_edge a w b G) a b"
        by auto
      with cycle_free e \<open>edges H \<subseteq> E\<close> show False
        by blast
    qed
    with assms(1) show ?thesis
    unfolding forest_def forest_axioms_def
    by auto
  qed

  lemma forest_delete_edge: "forest (delete_edge a w c G)"
    using forest_subsets[OF delete_edge_valid[OF valid_graph_axioms]]
    unfolding delete_edge_def
    by auto

  lemma forest_delete_node: "forest (delete_node n G)"
    using forest_subsets[OF delete_node_valid[OF valid_graph_axioms]]
    unfolding delete_node_def
    by auto

inductive path_from_edges where
  "(v,w,v') \<in> E \<or> (v',w,v) \<in> E \<Longrightarrow> path_from_edges v [(v',w,v)]" |
  "path_from_edges v es \<and> ((a',w',a) \<in> E \<or> (a',w',a) \<in> E)
    \<and> es \<noteq> []
    \<and> a = fst (hd es)
    \<and> (a' = v \<or> a' \<notin> fst`set es \<union> snd`snd`set es)
    \<Longrightarrow> path_from_edges v ((a',w',a)#es)"

  lemma forest_no_cycle:
    assumes "is_path_undir G v p v"
    assumes "distinct (p@(map (\<lambda>(a,b,c). (c,b,a)) p))"
    shows "p = []"
    using assms cycle_free delete_edge_is_path apply (cases p) apply auto
    sorry
  (*proof (rule ccontr)
    assume "p \<noteq> []"
    then obtain a w b where "(a,w,b)\<in>set p"
      using last_in_set prod_cases3 by metis
    with is_path_undir_split_distinct[OF assms, of a w b]
    obtain p' p'' u u' where
       "is_path_undir G v p' u \<and>
       is_path_undir G u' p'' v \<and>
       (u \<in> {a, b} \<and> u' \<in> {a, b}) \<and>
       (a, w, b) \<notin> set p' \<and>
       (b, w, a) \<notin> set p' \<and> (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p''"
      by auto
    with is_path_undir_split[of u' p'' p' u] is_path_undir_split[of v p' p'' v]
      is_path_undir_sym[of u' "p''@p'" u]
    have "\<exists>p. (is_path_undir G v p v \<or> is_path_undir G a p b) \<and>
     (a, w, b) \<notin> set p \<and> (b, w, a) \<notin> set p"
      by fastforce
    show False
      sorry
  qed*)

  lemma path_from_edges_valid:
    assumes "path_from_edges v p"
    shows "is_path_undir G (fst (hd p)) p v" "p \<noteq> []"
    using assms
    by (induct) (auto simp: E_validD)

  lemma leaf_exists:
    assumes "E \<noteq> {}"
    assumes "finite E"
    shows "\<exists>v\<in>V. degree G v = 1"
  proof (rule ccontr)
    assume asm: "\<not> (\<exists>v\<in>V. degree G v = 1)"
    term "\<lambda>v. {v'. \<exists>p. fst (hd p) = v' \<and> path_from_edges v p}"
    have "\<exists>v p. fst (hd p) = v \<and> path_from_edges v p"
      sorry
    with path_from_edges_valid obtain v p where
      "is_path_undir G v p v" "p \<noteq> []"
      by blast
    with forest_no_cycle
    show False
      sorry
    (*then have asm': "\<forall>v\<in>V. degree G v \<noteq> 1"
      by blast
    have "\<exists>v\<in>V. degree G v > 1"
    proof (rule ccontr)
      assume "\<not> (\<exists>v\<in>V. degree G v > 1)"
      with asm have "\<forall>v\<in>V. degree G v = 0"
        by fastforce
      with E_valid \<open>finite E\<close> have "E = {}"
        unfolding degree_def
        by fastforce
      with \<open>E \<noteq> {}\<close> show False
        by simp
    qed
    then obtain v where v: "degree G v > 1"
      by blast
    then have "{e \<in> E. fst e = v \<or> snd (snd e) = v} \<noteq> {}"
      unfolding degree_def
      by force
    then have "\<exists>e. e \<in> {e \<in> E. fst e = v \<or> snd (snd e) = v}"
      by blast
    then obtain a w a' where e: "(a, w, a') \<in> E \<and> (a = v \<or> a' = v)"
      unfolding degree_def
      using prod_cases3
      by auto
    then obtain v' where e': "v = a \<and> v' = a' \<or> v = a' \<and> v' = a"
      by blast
    with e have "path_from_edges v [(v',w,v)]"
      sorry
    from v have "\<exists>p. p\<noteq>[] \<and> is_path_undir G v p v"
      sorry
    then obtain p where p: "p\<noteq>[]" "is_path_undir G v p v"
      by blast
    with e have "edges_connected (delete_edge a w a' G) a a' \<or>
      edges_connected (delete_edge a w a' G) v v"
    proof (cases "(a,w,a')\<in>set p \<or> (a',w,a)\<in>set p")
      case True
      with is_path_undir_split_distinct[OF p(2) True]
      show ?thesis
        sorry
    next
      case False
      with delete_edge_is_path[OF p(2)] show ?thesis
        by blast
    qed
    with e cycle_free show False
      sorry (*by auto*)*)
  qed

  lemma connected_by_number_of_edges:
    assumes "finite V"
    assumes  "card E = card V - 1"
    shows "connected_graph G"
  using assms forest_axioms
  proof (induction n == "card (nodes G)" arbitrary: G)
    case 0
    then show ?case
      unfolding forest_def connected_graph_def connected_graph_axioms_def
        valid_graph_def
      by auto
  next
    case (Suc n)
    from forest.axioms(1)[OF \<open>forest G\<close>] have valid_G: "valid_graph G" .
    show ?case
    proof (cases "n = 0")
      case True
      with Suc(2) obtain v where "nodes G = {v}"
        by (metis One_nat_def card_1_singletonE)
      with valid_graph.is_path_undir_simps(1)[OF valid_G, of v]
      have "edges_connected G v v"
        by blast
      with valid_G \<open>nodes G = {v}\<close> show ?thesis
        unfolding connected_graph_def connected_graph_axioms_def
        by auto
    next
      case False
      with Suc(2,4) have "edges G \<noteq> {}"
        by auto
      from Suc(2,4) \<open>finite (nodes G)\<close> False card_infinite
      have "finite (edges G)"
        by fastforce
      from forest.leaf_exists[OF \<open>forest G\<close> \<open>edges G \<noteq> {}\<close> this]
      obtain v where v: "v\<in>nodes G" "degree G v = 1"
        by blast
      with card_1_singletonE
      obtain e where e: "{e\<in>edges G. fst e = v \<or> snd (snd e) = v} = {e}"
        unfolding degree_def
        by blast
      then have e': "e \<in> edges G" "fst e = v \<or> snd (snd e) = v"
        by auto
      with prod_cases3 obtain a w b where awb: "e = (a, w, b)"
        by blast
      with e' obtain v' where
        v': "(v, w, v') \<in> edges G \<or> (v', w, v) \<in> edges G"
        by auto
      from valid_graph.is_path_undir_simps(1)[OF delete_edge_valid[OF valid_G], of v w v v] v(1)
      have "edges_connected (delete_edge v w v G) v v"
        unfolding delete_edge_def
        by fastforce
      from \<open>edges_connected (delete_edge v w v G) v v\<close> v' \<open>forest G\<close>
      have v_neq_v': "v \<noteq> v'"
        unfolding forest_def forest_axioms_def
        by auto
      let ?G = "delete_node v (delete_edge a w b G)"
      from awb have edges_del_edge: "edges (delete_edge a w b G) = edges G - {e}"
        by simp
      with e have "{e\<in>edges (delete_edge a w b G). fst e = v \<or> snd (snd e) = v} = {}"
        by blast
      with edges_del_edge have "edges ?G = edges G - {e}"
        unfolding delete_node_def
        by auto
      moreover have nodes: "nodes ?G = nodes G - {v}"
        unfolding delete_node_def delete_edge_def
        by auto
      ultimately have card: "card (edges ?G) = card (nodes ?G) - 1"
        using Suc(4) v(1) e'(1)
        by (metis False One_nat_def Suc.hyps(2) Suc.prems(1) card_Diff_singleton card_infinite diff_Suc_1)
      from card_Diff_singleton[OF Suc(3) v(1)] Suc(2) nodes
      have "n = card (nodes ?G)"
        by simp
      moreover have "finite (nodes ?G)"
        by (simp add: Suc(3) nodes)
      moreover from forest.forest_delete_node[OF forest.forest_delete_edge[OF \<open>forest G\<close>]]
        have "forest ?G" .
      ultimately show ?thesis
        using Suc(1)[OF _ _ card] valid_G nodes
          valid_graph.add_node_connected[OF valid_G _ v' v_neq_v']
          valid_graph.delete_edge_was_path[OF valid_G
            valid_graph.delete_node_was_path[OF delete_edge_valid[OF valid_G]], of v a w b]
        unfolding connected_graph_def connected_graph_axioms_def
        by blast
    qed
  qed
    
end

context finite_graph
begin
  lemma forest_connecting_all_edges_exists: "\<exists>F. forest F \<and> subgraph F G \<and>
      (\<forall>(a,w,b)\<in>edges G. edges_connected F a b)"
    using finite_E valid_graph_axioms
  proof (induction n == "card (edges G)" arbitrary: G)
    case  (0 G)
    then have empty: "edges G = {}"
      by simp
    with "0.prems"(2) show ?case
      unfolding forest_def forest_axioms_def subgraph_def
      by auto
  next
    case (Suc n G)
    from Suc.hyps(2) have "edges G \<noteq> {}"
      by auto
    with prod_cases3 obtain a w b where e: "(a, w, b) \<in> edges G"
      by auto
    with Suc.prems have "valid_graph (delete_edge a w b G)"
      unfolding valid_graph_def delete_edge_def
      by auto
    moreover from e Suc.hyps(2) Suc.prems(1)
      have "n = card (edges (delete_edge a w b G))"
      unfolding delete_edge_def
      by simp
    moreover from Suc.prems have "finite (edges (delete_edge a w b G))"
      unfolding delete_edge_def
      by auto
    ultimately obtain F where F: "forest F" "subgraph F (delete_edge a w b G)"
        "(\<forall>(a,w,b)\<in>edges (delete_edge a w b G). edges_connected F a b)"
      using Suc.hyps(1)
      unfolding valid_graph_def
      by blast
    then have subgraph_F: "subgraph F G"
      unfolding subgraph_def delete_edge_def
      by auto
    show ?case
    proof (cases "edges_connected F a b")
      case True
      from F True have "(\<forall>(a,w,b)\<in>edges G. edges_connected F a b)"
        unfolding delete_edge_def by fastforce
      with F subgraph_F show ?thesis
        by auto
    next
      case False
      from subgraph_F e Suc.prems(2)
      have ab: "a \<in> nodes F" "b \<in> nodes F"
        unfolding subgraph_def
        by (auto simp: valid_graph.E_validD)
      with False forest.forest_add_edge[OF F(1) this]
      have "forest (add_edge a w b F)"
        by auto
      moreover from F e Suc.prems(2)
      have "subgraph (add_edge a w b F) G"
        unfolding subgraph_def add_edge_def delete_edge_def
        by (auto simp: valid_graph.E_validD)
      moreover have "edges_connected (add_edge a w b F) c d"
        if asm: "(c,w',d)\<in>edges G" for c w' d
      proof (cases "(c, w', d) = (a, w, b)")
        case True
        with valid_graph.add_edge_is_connected[OF forest.axioms(1)[OF F(1)]]
        show ?thesis by auto
      next
        case False
        with F(3) asm have "edges_connected F c d"
          by fastforce
        with valid_graph.add_edge_is_path[OF forest.axioms(1)[OF F(1)]]
        show ?thesis
          by blast
      qed
      ultimately show ?thesis
        by auto
    qed
  qed

  lemma finite_subgraphs: "finite {T. subgraph T G}"
  proof -
    from finite_E have "finite {E'. E' \<subseteq> E}"
      by simp
    then have "finite {\<lparr>nodes = V, edges = E'\<rparr>| E'. E' \<subseteq> E}"
      by simp
    also have "{\<lparr>nodes = V, edges = E'\<rparr>| E'. E' \<subseteq> E} = {T. subgraph T G}"
      unfolding subgraph_def
      by (metis (mono_tags, lifting) old.unit.exhaust select_convs(1) select_convs(2) surjective)
    finally show ?thesis .
  qed

  lemma spanning_forest_exists: "\<exists>F. is_spanning_forest F G"
  proof -
    from forest_connecting_all_edges_exists
    obtain F where F: "forest F" "subgraph F G"
      "(\<forall>(a, w, b)\<in>edges G. edges_connected F a b)"
      unfolding finite_graph_def finite_graph_axioms_def valid_graph_def
      by blast
    from F(2,3) forest.axioms(1)[OF F(1)] induce_maximal_connected[of F]
    have "maximal_connected F G"
      unfolding maximal_connected_def
      by simp
    with F(1,2) show ?thesis
      unfolding is_spanning_forest_def
      by auto
  qed
end

context finite_weighted_graph
begin
  lemma minimum_spanning_forest_exists: "\<exists>F. is_minimum_spanning_forest F G"
  proof -
    let ?weights = "{edge_weight F |F. is_spanning_forest F G}"
    from spanning_forest_exists
    obtain T where "is_spanning_forest T G"
      by auto
    then have non_empty: "edge_weight T \<in> ?weights"
      by auto
    from finite_subgraphs have finite: "finite ?weights"
      unfolding is_spanning_forest_def
      by auto
    with non_empty have "\<forall>w \<in> ?weights. Min ?weights \<le> w"
      by simp
    moreover from finite non_empty have "Min ?weights \<in> ?weights"
      using Min_in by blast
    ultimately obtain T' where "(\<forall>w \<in> ?weights. edge_weight T' \<le> w) \<and> is_spanning_forest T' G"
      by auto
    then show ?thesis
      unfolding is_minimum_spanning_forest_def is_optimal_forest_def
      by blast
  qed
end

lemma minimum_spanning_forest_impl_tree:
  assumes "is_minimum_spanning_forest F G"
  assumes valid_G: "valid_graph G"
  assumes "connected_graph F"
  shows "is_minimum_spanning_tree F G"
  using assms valid_graph.connected_impl_maximal_connected[OF valid_G]
  unfolding is_minimum_spanning_forest_def is_minimum_spanning_tree_def
    is_spanning_forest_def is_spanning_tree_def tree_def
    is_optimal_forest_def is_optimal_tree_def
  by auto

lemma minimum_spanning_forest_impl_tree2:
  assumes "is_minimum_spanning_forest F G"
  assumes connected_G: "connected_graph G"
  shows "is_minimum_spanning_tree F G"
  using assms connected_graph.maximal_connected_impl_connected[OF connected_G]
    minimum_spanning_forest_impl_tree connected_graph.axioms(1)[OF connected_G]
  unfolding is_minimum_spanning_forest_def is_spanning_forest_def
  by auto

end
