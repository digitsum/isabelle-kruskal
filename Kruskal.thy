theory Kruskal
  imports
    "./Graph_Definition"
    "./SeprefUF"
    Refine_Imperative_HOL.IICF
begin

definition valid_union_find_graph :: "('v, 'w) graph \<Rightarrow> 'v per \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool"
  where "valid_union_find_graph G uf H \<equiv> (\<forall>a\<in>nodes G. \<forall>b\<in>nodes G.
      (edges_connected H a b) \<longleftrightarrow> (a,b) \<in> uf)"

definition "uf_graph_invar G uf_H \<equiv> case uf_H of (uf, H) \<Rightarrow>
    part_equiv uf \<and>
    valid_union_find_graph G uf H \<and>
    Domain uf = nodes G"

definition "uf_graph_rel G \<equiv> br snd (uf_graph_invar G)"

definition "graph_of_list l \<equiv> \<lparr>
  nodes = fst`set l \<union> (snd o snd)`set l,
  edges = set l \<rparr>"

definition "lst_graph_rel \<equiv> br graph_of_list (\<lambda>_. True)"

definition "lst_subgraph_invar l \<equiv> distinct l"
definition "subgraph_of_lst G l \<equiv> \<lparr>
  nodes = nodes G,
  edges = set l \<rparr>"
definition "lst_subgraph_rel G \<equiv> br (subgraph_of_lst G) lst_subgraph_invar"

definition "is_linorder_rel R \<equiv> (\<forall>x y. R x y \<or> R y x) \<and> (\<forall>x y z. R x y \<longrightarrow> R y z \<longrightarrow> R x z)"

definition "max_node l \<equiv> Max (insert 0 (nodes (graph_of_list l))) + 1"

lemma max_node_impl[code]: "max_node l = fold (\<lambda>(u,_,w) x. max u (max w x)) l 0 + 1"
proof -
  have "fold (\<lambda>(u,_,w) x. max u (max w x)) l a = Max (insert a (nodes (graph_of_list l)))" for a
    apply (induction l arbitrary: a)
    apply (auto simp: graph_of_list_def)
    subgoal for a b l aa
      apply (cases l)
      by (auto simp: ac_simps)
    done
  thus ?thesis unfolding max_node_def by auto
qed


locale Kruskal = finite_weighted_graph G
  for G :: "('v,'w::weight) graph"
begin

section \<open>Kruskal 0\<close>

definition empty_forest :: "('v, 'w) graph"
  where "empty_forest \<equiv> \<lparr> nodes = V, edges = {} \<rparr>"

definition previous_edges_connected :: "('v, 'w) graph \<Rightarrow> ('v \<times> 'w \<times> 'v) set \<Rightarrow> bool"
  where "previous_edges_connected H E' \<equiv>
    (\<forall>(a, w, b)\<in>E - E'. edges_connected H a b)"

definition exists_min_spanning_forest :: "('v, 'w) graph \<Rightarrow> bool"
  where "exists_min_spanning_forest H \<equiv>
    (\<exists>T. subgraph H T \<and> is_minimum_spanning_forest T G)"

definition loop_invar_kruskal :: "('v \<times> 'w \<times> 'v) set \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool"
  where "loop_invar_kruskal E' H \<equiv>
    forest H \<and>
    subgraph H G \<and>
    previous_edges_connected H E' \<and>
    exists_min_spanning_forest H"

definition kruskal0 :: "('v, 'w) graph nres"
  where "kruskal0 \<equiv> do {
    ASSERT (finite E);
    l \<leftarrow> SPEC (\<lambda>l. set l = E \<and> sorted_by_rel edges_less_eq l);
    spanning_forest \<leftarrow> nfoldli l (\<lambda>_. True)
      (\<lambda>(a, w, b) H. do {
        ASSERT (subgraph H G);
        ASSERT (a\<in>V \<and> b\<in>V);
        if (edges_connected H a b)
        then
          RETURN H
        else do {
          ASSERT ((a, w, b) \<in> E - edges H);
          RETURN (add_edge a w b H)
        }
      }) empty_forest;
    RETURN spanning_forest
  }"

lemma empty_forest_valid: "valid_graph empty_forest"
  unfolding empty_forest_def valid_graph_def
  by auto

lemma empty_exists_min_spanning_forest: "exists_min_spanning_forest empty_forest"
proof -
  from minimum_spanning_forest_exists obtain T where "is_minimum_spanning_forest T G"
    by auto
  moreover from this have "subgraph empty_forest T"
    unfolding subgraph_def empty_forest_def is_minimum_spanning_forest_def
      is_spanning_forest_def
    by simp
  ultimately show ?thesis
    unfolding exists_min_spanning_forest_def
    by auto
qed

lemma loop_invar_kruskal_empty: "loop_invar_kruskal E empty_forest"
  using empty_forest_valid empty_exists_min_spanning_forest
  unfolding loop_invar_kruskal_def empty_forest_def forest_def
    forest_axioms_def subgraph_def previous_edges_connected_def
  by auto

lemma loop_invar_kruskal_valid_graph:
  assumes "loop_invar_kruskal E' H"
  shows "valid_graph H"
  using assms
  unfolding loop_invar_kruskal_def forest_def by simp


lemma loop_invar_kruskal_subgraph:
  assumes "loop_invar_kruskal E' H"
  shows "subgraph H G"
  using assms
  unfolding loop_invar_kruskal_def by simp

lemma loop_invar_kruskal_edge_not_in_graph:
  assumes invar: "loop_invar_kruskal (insert (a, w, b) E') H"
  assumes "(a, w, b) \<in> E"
  assumes "\<not> edges_connected H a b"
  shows "(a, w, b) \<notin> edges H"
proof -
  from assms have "\<not> is_path_undir H a [(a, w, b)] b"
    by blast
  with \<open>(a, w, b)\<in>E\<close> valid_graph.is_path_undir_simps(2)[OF
      valid_subgraph[OF loop_invar_kruskal_subgraph[OF invar]]]
  show ?thesis
    by auto
qed

lemma preserve_previous_edges_connected_no_add:
  assumes "previous_edges_connected H (insert (a, w, b) E')"
  assumes "edges_connected H a b"
  shows "previous_edges_connected H E'"
  using assms
  unfolding previous_edges_connected_def
  by blast

lemma preserve_previous_edges_connected_add:
  assumes "previous_edges_connected H (insert (a, w, b) E')"
  assumes "valid_graph H"
  shows "previous_edges_connected (add_edge a w b H) E'"
  using assms
proof -
  have "edges_connected (add_edge a w b H) v v'"
    if e: "(v, w', v')\<in>E - E'" for v w' v'
  proof (cases "(v, w', v') = (a, w, b)")
    case True
    with valid_graph.add_edge_is_connected[OF \<open>valid_graph H\<close>] show ?thesis
      by simp
  next
    case False
    with assms(1) e valid_graph.add_edge_is_path[OF \<open>valid_graph H\<close>]
    show ?thesis
      unfolding previous_edges_connected_def
      by blast
  qed
  then show ?thesis
    unfolding previous_edges_connected_def
    by auto
qed

lemma exists_min_spanning_forest_add:
  assumes "exists_min_spanning_forest H"
  assumes "previous_edges_connected H (insert (a, w, b) (set l2))"
  assumes "subgraph H G"
  assumes "(a,w,b) \<in> E"
  assumes "\<not> edges_connected H a b"
  assumes "sorted_by_rel edges_less_eq (l1 @ (a, w, b) # l2)"
  shows "exists_min_spanning_forest (add_edge a w b H)"
proof -
  from \<open>exists_min_spanning_forest H\<close> obtain T where subgraph_H_T: "subgraph H T"
      and msf_T: "is_minimum_spanning_forest T G"
      and valid_T: "valid_graph T" and forest_T: "forest T"
      and maximal_connected_T: "maximal_connected T G"
      and subgraph_T: "subgraph T G"
    unfolding exists_min_spanning_forest_def is_minimum_spanning_forest_def
      is_spanning_forest_def forest_def
    by blast
  from subgraph_T finite_E have finite_T: "finite (edges T)"
    unfolding subgraph_def by (auto simp: finite_subset)
  from subgraph_node[OF subgraph_T] E_validD[OF \<open>(a,w,b)\<in>E\<close>]
    have ab: "a\<in>nodes T" "b\<in>nodes T"
    by auto
  from valid_subgraph[OF \<open>subgraph H G\<close>]
  have valid_H: "valid_graph H"
    unfolding forest_def
    by simp
  show ?thesis
  proof (cases "(a,w,b) \<in> edges T")
    case True
    with subgraph_H_T ab have "subgraph (add_edge a w b H) T"
      unfolding subgraph_def add_edge_def
      by auto
    with msf_T show ?thesis
      unfolding exists_min_spanning_forest_def
      by auto
  next
    case False
    from maximal_connected_T \<open>(a,w,b)\<in>E\<close> is_path_undir_simps(2)[of a w b]
    obtain p where p: "is_path_undir T a p b"
      unfolding maximal_connected_def
      by (meson E_validD)
    with forest.delete_edge_from_path[OF forest_T _ subgraph_H_T \<open>\<not> edges_connected H a b\<close>]
    obtain x w' y where xy: "(x, w', y) \<in> edges T" "(x, w', y) \<notin> edges H" and
      not_connected: "\<not> edges_connected (delete_edge x w' y T) a b" and
      connected_xy: "edges_connected (add_edge a w b (delete_edge x w' y T)) x y"
      by blast
    obtain T' where T': "T' = add_edge a w b (delete_edge x w' y T)"
      by blast
    from valid_T have valid_delete_T: "valid_graph (delete_edge x w' y T)"
      by simp
    with T' have valid_T': "valid_graph T'"
      by simp
    from False have False': "(a, w, b) \<notin> edges (delete_edge x w' y T)"
      unfolding delete_edge_def by simp
    from forest.forest_delete_edge[OF forest_T]
    have forest_delete_T: "forest (delete_edge x w' y T)"
      by simp
    from False xy(1) have ab_neq_xy: "(x, w', y) \<noteq> (a, w, b)"
      by auto
    from T' subgraph_T \<open>(a,w,b) \<in> E\<close> have subgraph_T': "subgraph T' G"
      unfolding subgraph_def
      by (auto simp: E_validD)
    from subgraph_H_T xy have subgraph_H_delete_T: "subgraph H (delete_edge x w' y T)"
      unfolding subgraph_def delete_edge_def
      by auto
    have "\<not> edges_connected H x y"
    proof
      assume asm: "edges_connected H x y"
      from forest.cycle_free[OF forest_T] xy(1)
        have contr: "\<not> edges_connected (delete_edge x w' y T) x y"
        by auto
      with asm valid_graph.is_path_undir_subgraph[OF valid_delete_T _ subgraph_H_delete_T]
      show False by blast
    qed
    with assms(2) ab_neq_xy have "(x, w', y) \<notin> E - (set l2)"
      unfolding previous_edges_connected_def by blast
    moreover from xy(1) subgraph_T have "(x, w', y) \<in> E"
      unfolding subgraph_def
      by auto
    ultimately have "(x, w', y) \<in> set l2"
      by auto
    with assms(6) sorted_by_rel_append[of edges_less_eq l1 "(a, w, b) # l2"]
      sorted_by_rel_Cons[of edges_less_eq "(a, w, b)" l2]
    have *: "w \<le> w'"
      unfolding edges_less_eq_def
      by auto
    with T' False xy(1) finite_T sum.subset_diff[of "{(x, w', y)}" "edges T" "fst \<circ> snd"]
    have improvement: "edge_weight T' \<le> edge_weight T"
      unfolding edge_weight_def
      apply auto
      apply(subst ab_semigroup_add.add_commute[OF class.ordered_ab_semigroup_add.axioms(1)[OF class.weight.axioms(2)[OF weight_class.weight_axioms]], of _ w'])
      apply(auto simp: add_right_mono)
      done
    from T' subgraph_H_delete_T have "subgraph (add_edge a w b H) T'"
      unfolding subgraph_def
      by auto
    moreover from T' ab forest.forest_add_edge[OF forest_delete_T _ _ not_connected]
      have "forest T'"
        by simp
    moreover from connected_xy T' swap_delete_add_edge[OF ab_neq_xy, of T]
      delete_edge_maximal_connected[OF
        add_edge_maximal_connected[OF maximal_connected_T subgraph_T \<open>(a,w,b)\<in>E\<close>]
        add_edge_preserve_subgraph[OF subgraph_T \<open>(a,w,b)\<in>E\<close>]]
      have "maximal_connected T' G"
      unfolding subgraph_def by metis
    moreover from improvement msf_T have "is_optimal_forest T' G"
      unfolding is_minimum_spanning_forest_def is_optimal_forest_def
      by auto
    ultimately show ?thesis using subgraph_T'
      unfolding exists_min_spanning_forest_def is_minimum_spanning_forest_def
        is_spanning_forest_def
      by auto
  qed
qed

lemma union_preserves_forest:
  assumes "forest H"
  assumes "\<not> edges_connected H a b"
  assumes "subgraph H G"
  assumes "a \<in> V"
  assumes "b \<in> V"
  shows "forest (add_edge a w b H)"
  using forest.forest_add_edge[OF \<open>forest H\<close> _ _ \<open>\<not>edges_connected H a b\<close>]
    subgraph_node[OF \<open>subgraph H G\<close>] \<open>a\<in>V\<close> \<open>b\<in>V\<close>
  by simp

lemma union_preserves_loop_invar:
  assumes "loop_invar_kruskal (insert (a, w, b) (set l2)) H"
  assumes "\<not> edges_connected H a b"
  assumes "insert (a, w, b) (set l1 \<union> set l2) = E"
  assumes "sorted_by_rel edges_less_eq (l1 @ (a, w, b) # l2)"
  shows "loop_invar_kruskal (set l2) (add_edge a w b H)"
  using assms insertI1[of "(a, w, b)" "(set l1 \<union> set l2)"]
  unfolding loop_invar_kruskal_def
  apply (auto simp: add_edge_preserve_subgraph)
  apply (meson E_validD union_preserves_forest)
  apply (auto simp: valid_subgraph E_validD exists_min_spanning_forest_add
          dest: preserve_previous_edges_connected_add)
  done

lemma same_component_preserves_loop_invar:
  assumes "loop_invar_kruskal (insert (a, w, b) E') H"
  assumes "edges_connected H a b"
  shows "loop_invar_kruskal E' H"
  using assms preserve_previous_edges_connected_no_add
  unfolding loop_invar_kruskal_def
  by blast

lemma result_maximal_connected:
  assumes "subgraph H G"
  assumes "previous_edges_connected H {}"
  shows "maximal_connected H G"
  using assms induce_maximal_connected
  unfolding previous_edges_connected_def
  by auto

lemma loop_invar_kruskal_final:
  assumes "loop_invar_kruskal {} H"
  shows "is_minimum_spanning_forest H G"
proof -
  from assms obtain T where T: "subgraph H T" "is_minimum_spanning_forest T G"
    unfolding loop_invar_kruskal_def exists_min_spanning_forest_def by auto
  with assms result_maximal_connected sub_spanning_forest_eq[of H T]
  show ?thesis
    unfolding loop_invar_kruskal_def is_minimum_spanning_forest_def
      is_spanning_forest_def
    by simp
qed

theorem kruskal0_refine: "(kruskal0, SPEC (\<lambda>F. is_minimum_spanning_forest F G))\<in>\<langle>Id\<rangle>nres_rel"
  unfolding kruskal0_def
  apply(refine_vcg nfoldli_rule[where I="\<lambda>l1 l2 s. loop_invar_kruskal (set l2) s"])
  apply (auto
      simp: finite_E loop_invar_kruskal_empty loop_invar_kruskal_final
            loop_invar_kruskal_subgraph
      dest: same_component_preserves_loop_invar
            loop_invar_kruskal_edge_not_in_graph
            union_preserves_loop_invar)
  apply (metis insertI1 E_validD(1))
  apply (metis insertI1 E_validD(2))
  done

section \<open>Kruskal 1\<close>

definition kruskal1 :: "('v, 'w) graph nres"
  where "kruskal1 \<equiv> do {
    let initial_union_find = per_init V;
    ASSERT (finite E);
    l \<leftarrow> SPEC (\<lambda>l. set l = E \<and> sorted_by_rel edges_less_eq l);
    (per, spanning_forest) \<leftarrow> nfoldli l (\<lambda>_. True)
      (\<lambda>(a, w, b) (uf, H). do {
        ASSERT (subgraph H G);
        ASSERT (a\<in>Domain uf \<and> b\<in>Domain uf);
        if per_compare uf a b
        then
          RETURN (uf, H)
        else do {
          let uf = per_union uf a b;
          ASSERT ((a, w, b) \<in> E - edges H);
          RETURN (uf, add_edge a w b H)
        }
      }) (initial_union_find, empty_forest);
    RETURN spanning_forest
  }"

lemma preserve_valid_union_find_graph_add:
  assumes "valid_union_find_graph G uf H"
  assumes "a \<in> V"
  assumes "b \<in> V"
  assumes "Domain uf = V"
  assumes "subgraph H G"
  assumes PER: "part_equiv uf"
  shows "valid_union_find_graph G (per_union uf a b) (add_edge a w b H)"
proof -
  from valid_subgraph[OF \<open>subgraph H G\<close>]
  have valid_H: "valid_graph H" .
  have "(edges_connected (add_edge a w b H) x y) \<longleftrightarrow> (x,y) \<in> per_union uf a b"
    if xy: "x\<in>V \<and> y\<in>V" for x y
  proof
    assume "edges_connected (add_edge a w b H) x y"
    then obtain p where p: "is_path_undir (add_edge a w b H) x p y"
      by blast
    from \<open>a\<in>V\<close> \<open>b\<in>V\<close> \<open>Domain uf = V\<close>
    have [simp]: "a\<in>Domain (per_union uf a b)" "b\<in>Domain (per_union uf a b)"
      by auto
    from PER have PER': "part_equiv (per_union uf a b)"
      by (auto simp: union_part_equivp)
    show "(x,y) \<in> per_union uf a b"
    proof (cases "(a, w, b) \<in> set p \<or> (b, w, a) \<in> set p")
      case True
      from valid_graph.is_path_undir_split_distinct[OF add_edge_valid[OF valid_H] p True]
      obtain p' p'' u u' where
        "is_path_undir (add_edge a w b H) x p' u \<and>
        is_path_undir (add_edge a w b H) u' p'' y" and
        u: "u\<in>{a,b} \<and> u'\<in>{a,b}" and
        "(a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p' \<and>
        (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p''"
        by auto
      with \<open>a\<in>V\<close> \<open>b\<in>V\<close> \<open>Domain uf = V\<close> \<open>subgraph H G\<close>
        valid_graph.add_edge_was_path[OF valid_H]
      have "is_path_undir H x p' u \<and> is_path_undir H u' p'' y"
        unfolding subgraph_def by auto
      with assms(1-5) xy u have comps: "(x,u) \<in> uf \<and> (u', y) \<in> uf"
        unfolding valid_union_find_graph_def
        by auto
      from comps per_union_impl have "(x,u) \<in> per_union uf a b"
        by auto
      also from u \<open>a\<in>V\<close> \<open>b\<in>V\<close> \<open>Domain uf = V\<close> part_equiv_refl'[OF PER' \<open>a\<in>Domain (per_union uf a b)\<close>]
        part_equiv_refl'[OF PER' \<open>b\<in>Domain (per_union uf a b)\<close>] part_equiv_sym[OF PER']
        per_union_related[OF PER]
      have "(u,u') \<in> per_union uf a b"
        by auto
      also (part_equiv_trans[OF PER']) from comps per_union_impl
      have "(u',y) \<in> per_union uf a b"
        by auto
      finally (part_equiv_trans[OF PER']) show ?thesis by simp
    next
      case False
      with \<open>a\<in>V\<close> \<open>b\<in>V\<close> \<open>Domain uf = V\<close> \<open>subgraph H G\<close>
        valid_graph.add_edge_was_path[OF valid_H p(1)]
      have "is_path_undir H x p y"
        unfolding subgraph_def by auto
      with assms(1) xy have "(x,y)\<in>uf"
        unfolding valid_union_find_graph_def
        by auto
      from per_union_impl[OF this] show ?thesis .
    qed
  next
    assume asm: "(x, y) \<in> per_union uf a b"
    show "edges_connected (add_edge a w b H) x y"
      proof (cases "(x, y) \<in> uf")
        case True
        with assms(1) xy have "edges_connected H x y"
          unfolding valid_union_find_graph_def
          by blast
        with valid_graph.add_edge_is_path[OF valid_H] show ?thesis
          by blast
      next
        case False
        with asm part_equiv_sym[OF PER]
        have "(x,a) \<in> uf \<and> (b,y) \<in> uf \<or>
              (b,x) \<in> uf \<and> (y,a) \<in> uf"
          unfolding per_union_def
          by auto
        with assms(1) \<open>a\<in>V\<close> \<open>b\<in>V\<close> xy obtain p q
          where "is_path_undir H x p a \<and> is_path_undir H b q y \<or>
                 is_path_undir H b p x \<and> is_path_undir H y q a"
          unfolding valid_union_find_graph_def
          by blast
        with valid_graph.add_edge_is_path[OF valid_H] obtain p' q'
          where "is_path_undir (add_edge a w b H) x p' a \<and>
                is_path_undir (add_edge a w b H) b q' y \<or>
                is_path_undir (add_edge a w b H) b p' x \<and>
                is_path_undir (add_edge a w b H) y q' a"
          by blast
        with valid_graph.is_path_undir_split'[OF add_edge_valid[OF valid_H]]
        have "is_path_undir (add_edge a w b H) x (p' @ (a, w, b) # q') y \<or>
              is_path_undir (add_edge a w b H) y (q' @ (a, w, b) # p') x"
          by auto
        with valid_graph.is_path_undir_sym[OF add_edge_valid[OF valid_H]]
        show ?thesis
          by blast
      qed
  qed
  then show ?thesis unfolding valid_union_find_graph_def by simp
qed

lemma valid_union_find_graph_empty:
  shows "valid_union_find_graph G (per_init V) empty_forest"
proof -
  have "(edges_connected empty_forest a b) \<longleftrightarrow> (a,b) \<in> per_init V"
    if ab: "a\<in>V \<and> b\<in>V" for a b
  proof
    assume "edges_connected empty_forest a b"
    then obtain p where p: "is_path_undir empty_forest a p b"
      by blast
    then have "a = b"
      unfolding empty_forest_def
      by (induction p) auto
    with ab show "(a,b) \<in> per_init V"
      by (auto intro: part_equiv_refl')
  next
    assume "(a,b) \<in> per_init V"
    hence "a=b" by (auto intro: per_init_self)
    from ab have "is_path_undir empty_forest a [] a"
      unfolding empty_forest_def
      by auto
    with \<open>a=b\<close> show "edges_connected empty_forest a b"
      by blast
  qed
  then show ?thesis
    unfolding valid_union_find_graph_def
    by simp
qed

lemma empty_forest_refine1: "((per_init V, empty_forest), empty_forest)\<in>uf_graph_rel G"
  unfolding  uf_graph_rel_def uf_graph_invar_def
  by (auto simp: in_br_conv valid_union_find_graph_empty)

theorem kruskal1_refine: "(kruskal1, kruskal0)\<in>\<langle>Id\<rangle>nres_rel"
  unfolding kruskal1_def kruskal0_def
  apply (rewrite at "let initial_union_find = per_init V in _" Let_def)
  apply (refine_rcg empty_forest_refine1)
  apply refine_dref_type
  using preserve_valid_union_find_graph_add
  unfolding uf_graph_rel_def uf_graph_invar_def valid_union_find_graph_def
  apply (auto simp: in_br_conv union_part_equivp)
  done

end

section \<open>Kruskal 2\<close>

locale Kruskal_list = Kruskal "graph_of_list l"
  for l :: "('v \<times> 'w::weight \<times> 'v) list"
begin

abbreviation "G\<equiv>graph_of_list l"

lemma l_G_refine: "(l, G) \<in> lst_graph_rel"
  unfolding lst_graph_rel_def
  by (auto simp: in_br_conv)

lemma E_impl: "set l = E"
  unfolding graph_of_list_def
  by simp

lemma finite_V: "finite V"
  unfolding graph_of_list_def
  by auto

definition kruskal2 :: "('v, 'w) graph nres"
  where "kruskal2 \<equiv> do {
    let initial_union_find = per_init (V);
    let l = quicksort_by_rel edges_less_eq [] l;
    (per, spanning_forest) \<leftarrow> nfoldli l (\<lambda>_. True)
      (\<lambda>(a, w, b) (uf, H). do {
        ASSERT (a\<in>Domain uf \<and> b\<in>Domain uf);
        if per_compare uf a b
        then
          RETURN (uf, H)
        else do {
          let uf = per_union uf a b;
          ASSERT ((a, w, b) \<in> E - edges H);
          RETURN (uf, add_edge a w b H)
        }
      }) (initial_union_find, empty_forest);
    RETURN spanning_forest
  }"

lemma edges_less_eq_linorder: "is_linorder_rel edges_less_eq"
  unfolding edges_less_eq_def is_linorder_rel_def
  by (metis linear order_trans)

lemma sort_edges_correct: "sorted_by_rel edges_less_eq (quicksort_by_rel edges_less_eq [] l)"
  by (metis (no_types, hide_lams) edges_less_eq_linorder is_linorder_rel_def sorted_by_rel_quicksort_by_rel)

theorem kruskal2_refine: "(kruskal2, kruskal1)\<in>\<langle>Id\<rangle>nres_rel"
  unfolding kruskal2_def kruskal1_def
  apply (refine_rcg)
  apply refine_dref_type
  apply (vc_solve simp: E_impl sort_edges_correct)
  done

section \<open>Kruskal 3\<close>

definition "lst_empty_forest \<equiv> []"

definition kruskal3 :: "('v \<times> 'w \<times> 'v) list nres"
  where "kruskal3 \<equiv> do {
    let initial_union_find = per_init V;
    (per, spanning_forest) \<leftarrow> nfoldli (quicksort_by_rel edges_less_eq [] l) (\<lambda>_. True)
      (\<lambda>(a, w, b) (uf, l_H). do {
        ASSERT (a\<in>Domain uf \<and> b\<in>Domain uf);
        if per_compare uf a b
        then
          RETURN (uf, l_H)
        else do {
          let uf = per_union uf a b;
          ASSERT ((a, w, b) \<in> set l - set l_H);
          RETURN (uf, (a, w, b)#l_H)
        }
      }) (initial_union_find, lst_empty_forest);
    RETURN spanning_forest
  }"

lemma add_edge_refine:
  assumes "(l_H, H) \<in> lst_subgraph_rel G"
  assumes "(a, w, b) \<in> set l - set l_H"
  shows "((a, w, b) # l_H, add_edge a w b H) \<in> lst_subgraph_rel G"
  using assms
  unfolding E_impl add_edge_def lst_subgraph_rel_def lst_subgraph_invar_def list_set_rel_def subgraph_of_lst_def
  by (auto simp: in_br_conv E_validD)

lemma empty_forest_refine3: "((per_init V, lst_empty_forest), (per_init V, empty_forest))\<in>Id \<times>\<^sub>r lst_subgraph_rel G"
  unfolding empty_forest_def lst_empty_forest_def lst_subgraph_rel_def lst_subgraph_invar_def subgraph_of_lst_def
  by (auto simp: in_br_conv)

theorem kruskal3_refine: "(kruskal3, kruskal2)\<in>\<langle>lst_subgraph_rel G\<rangle>nres_rel"
  unfolding kruskal3_def kruskal2_def
  apply (rewrite at "let l = quicksort_by_rel edges_less_eq [] l in _" Let_def)
  apply (refine_vcg empty_forest_refine3)
  apply refine_dref_type
  using E_impl add_edge_refine
  unfolding lst_subgraph_rel_def subgraph_of_lst_def
  by (auto simp: in_br_conv)

end

section \<open>Kruskal 4\<close>

locale Kruskal_list_nat = Kruskal_list l for
  l :: "(nat \<times> int \<times> nat) list"
begin

definition kruskal4 :: "(nat \<times> int \<times> nat) list nres"
  where "kruskal4 \<equiv> do {
    let initial_union_find = per_init' (max_node l);
    (per, spanning_forest) \<leftarrow> nfoldli (quicksort_by_rel edges_less_eq [] l) (\<lambda>_. True)
      (\<lambda>(a, w, b) (uf, l_H). do {
        ASSERT (a\<in>Domain uf \<and> b\<in>Domain uf);
        if per_compare uf a b
        then
          RETURN (uf, l_H)
        else do {
          let uf = per_union uf a b;
          RETURN (uf, (a, w, b)#l_H)
        }
      }) (initial_union_find, []);
    RETURN spanning_forest
  }"

lemma per_initN_refine: "(per_init' (max_node l), per_init V) \<in> per_supset_rel"
  unfolding per_supset_rel_def per_init'_def per_init_def max_node_def
  by (auto simp: less_Suc_eq_le finite_V)

theorem kruskal4_refine: "(kruskal4, kruskal3)\<in>\<langle>Id\<rangle>nres_rel"
  unfolding kruskal4_def kruskal3_def lst_empty_forest_def
  apply (refine_vcg)
  supply RELATESI[where R="per_supset_rel::(nat per \<times> _) set", refine_dref_RELATES]
  apply refine_dref_type
  apply (vc_solve simp: per_initN_refine)
  apply (auto dest: per_supset_rel_dom per_supset_compare per_supset_union)
  done

end

section \<open>Kruskal 5\<close>

concrete_definition kruskal5 uses Kruskal_list_nat.kruskal4_def

section \<open>Kruskal\<close>

definition "sort_edges \<equiv> quicksort_by_rel edges_less_eq []"

lemma [sepref_import_param]: "(sort_edges,sort_edges)\<in>\<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow>\<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel" by simp
lemma [sepref_import_param]: "(max_node, max_node) \<in> \<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow> nat_rel" by simp

sepref_definition kruskal is
  "kruskal5" :: "(list_assn (nat_assn\<times>\<^sub>aint_assn\<times>\<^sub>anat_assn))\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
  unfolding kruskal5_def sort_edges_def[symmetric]
  apply (rewrite at "nfoldli _ _ _ (_,\<hole>)" HOL_list.fold_custom_empty)
  by sepref

context Kruskal_list_nat begin
  lemmas kruskal5_ref_spec = kruskal4_refine[
    unfolded kruskal5.refine[OF Kruskal_list_nat_axioms],
    FCOMP kruskal3_refine,
    FCOMP kruskal2_refine,
    FCOMP kruskal1_refine,
    FCOMP kruskal0_refine
    ]

  lemma kruskal6_refine: "(uncurry0 (kruskal l), uncurry0 (kruskal5 l))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
    using kruskal.refine
    unfolding list_assn_pure_conv prod_assn_pure_conv
    unfolding hfref_def hn_refine_def pure_def hn_ctxt_def
    by auto

  lemma [fcomp_norm_simps]: "list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn) = id_assn"
    by (auto simp: list_assn_pure_conv)

  lemmas kruskal_ref_spec = kruskal6_refine[FCOMP kruskal5_ref_spec]
end

lemma kruskal_correct_forest:
  fixes l
  defines "G \<equiv> graph_of_list l"
  shows "<emp> kruskal l <\<lambda>r. \<up>(lst_subgraph_invar r \<and> is_minimum_spanning_forest (subgraph_of_lst G r) G)>\<^sub>t"
proof -
  interpret Kruskal "graph_of_list l"
    apply unfold_locales
    unfolding graph_of_list_def
    by auto force

  interpret Kruskal_list_nat l
    by unfold_locales

  show ?thesis
    using kruskal_ref_spec[to_hnr]
    unfolding hn_refine_def lst_subgraph_rel_def
    apply clarsimp
    apply (erule cons_post_rule)
    apply (sep_auto simp: hn_ctxt_def pure_def in_br_conv G_def)
    done
qed

lemma kruskal_correct_tree:
  fixes l
  defines "G \<equiv> graph_of_list l"
  assumes connected_G: "connected_graph G"
  shows "<emp> kruskal l <\<lambda>r. \<up>(lst_subgraph_invar r \<and> is_minimum_spanning_tree (subgraph_of_lst G r) G)>\<^sub>t"
  using kruskal_correct_forest minimum_spanning_forest_impl_tree2[OF _ connected_G]
  apply clarsimp
  apply (rule cons_post_rule)
  apply (auto simp: G_def)
  done

section \<open>Kruskal tree\<close>

definition kruskal_tree_spec :: "('v, 'w::weight) graph \<Rightarrow> ('v, 'w) graph option nres"
  where "kruskal_tree_spec G \<equiv> do {
    ASSERT (valid_graph G \<and> finite (nodes G) \<and> finite (edges G));
    SPEC (\<lambda>F.
      if connected_graph G
      then \<exists>F'. F = Some F' \<and> is_minimum_spanning_tree F' G
      else F = None)
    }"

definition kruskal_tree1 :: "('v, 'w::weight) graph \<Rightarrow> ('v, 'w) graph option nres"
  where "kruskal_tree1 G \<equiv> do {
    ASSERT (valid_graph G \<and> finite (nodes G) \<and> finite (edges G));
    spanning_forest \<leftarrow> SPEC (\<lambda>F. is_minimum_spanning_forest F G);
    ASSERT (forest spanning_forest \<and> finite (nodes spanning_forest));
    connected \<leftarrow> SPEC (\<lambda>conn. conn = connected_graph spanning_forest);
    if connected
    then RETURN (Some spanning_forest)
    else RETURN None
  }"

theorem kruskal_tree1_refine:
  "(kruskal_tree1 G, kruskal_tree_spec G) \<in> \<langle>Id\<rangle>nres_rel"
  unfolding kruskal_tree1_def kruskal_tree_spec_def
  apply(refine_vcg)
  apply (auto simp: minimum_spanning_forest_impl_tree)
  unfolding is_minimum_spanning_forest_def is_spanning_forest_def
  using connected_graph.maximal_connected_impl_connected valid_graph.subgraph_impl_connected
  by (auto simp: subgraph_def)

definition is_connected_spec :: "('v, 'w) graph \<Rightarrow> bool nres"
  where "is_connected_spec F \<equiv> do {
    ASSERT (forest F \<and> finite (nodes F) \<and> finite (edges F));
    SPEC (\<lambda>conn. conn = connected_graph F)
  }"

definition is_connected :: "('v, 'w) graph \<Rightarrow> bool nres"
  where "is_connected F \<equiv> do {
    ASSERT (forest F \<and> finite (nodes F) \<and> finite (edges F));
    let N = card (nodes F);
    RETURN (card (edges F) = N - 1)
  }"

lemma is_connected_refine:
  "(is_connected, is_connected_spec) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding is_connected_def is_connected_spec_def
  apply(refine_vcg)
  using forest.connected_by_number_of_edges
  by auto

definition is_connected_list :: "(nat \<times> int \<times> nat) list \<Rightarrow> (nat \<times> int \<times> nat) list \<Rightarrow> bool"
  where "is_connected_list l f \<equiv>
    let N = length (remdups ((map fst l) @ (map (snd o snd) l)))
    in length f = N - 1"

definition kruskal_tree2 :: "(nat \<times> int \<times> nat) list \<Rightarrow> (nat \<times> int \<times> nat) list option nres"
  where "kruskal_tree2 l \<equiv> do {
    spanning_forest \<leftarrow> kruskal5 l;
    let connected = is_connected_list l spanning_forest;
    if connected
    then RETURN (Some spanning_forest)
    else RETURN None
  }"

context Kruskal_list_nat
begin

lemma (in Kruskal_list_nat) is_connected_list_refine:
  "(RETURN o (is_connected_list l), is_connected) \<in> lst_subgraph_rel G \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding is_connected_list_def is_connected_def
  apply(refine_rcg)
  unfolding lst_subgraph_rel_def subgraph_of_lst_def graph_of_list_def lst_subgraph_invar_def
  by (auto simp: in_br_conv distinct_card length_remdups_card_conv)

theorem kruskal_tree2_refine:
  "(kruskal_tree2 l, kruskal_tree1 G) \<in> \<langle>\<langle>lst_subgraph_rel G\<rangle>option_rel\<rangle>nres_rel"
  unfolding kruskal_tree1_def kruskal_tree2_def
  apply (refine_rcg)
  using kruskal5_ref_spec[param_fo, THEN nres_relD]
        is_connected_list_refine[FCOMP is_connected_refine, param_fo, THEN nres_relD]
  unfolding lst_subgraph_rel_def is_connected_spec_def subgraph_of_lst_def
  apply (auto simp: in_br_conv)
  by fastforce+

end

lemma [sepref_import_param]: "(is_connected_list,is_connected_list)\<in>\<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow> \<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow> bool_rel"
  by simp

lemmas [sepref_fr_rules] = kruskal.refine

sepref_definition kruskal_tree is
  "kruskal_tree2" :: "(list_assn (nat_assn\<times>\<^sub>aint_assn\<times>\<^sub>anat_assn))\<^sup>k \<rightarrow>\<^sub>a option_assn (list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn))"
  unfolding kruskal_tree2_def
  by sepref

context Kruskal_list_nat
begin
  lemma kruskal_tree3_refine: "(uncurry0 (kruskal_tree l), uncurry0 (kruskal_tree2 l))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn (list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn))"
    using kruskal_tree.refine
    unfolding list_assn_pure_conv prod_assn_pure_conv
    unfolding hfref_def hn_refine_def pure_def hn_ctxt_def
    by auto

  lemmas kruskal_tree_ref_spec = kruskal_tree3_refine[FCOMP kruskal_tree2_refine[FCOMP kruskal_tree1_refine]]
end

lemma kruskal_tree_correct:
  fixes l
  defines "G \<equiv> graph_of_list l"
  shows "<emp> kruskal_tree l <\<lambda>r. \<up>(r = None \<and> \<not> connected_graph G \<or> lst_subgraph_invar (the r) \<and> is_minimum_spanning_tree (subgraph_of_lst G (the r)) G)>\<^sub>t"
proof -
  interpret Kruskal "graph_of_list l"
    apply unfold_locales
    unfolding graph_of_list_def
    by auto force

  interpret Kruskal_list_nat l
    by unfold_locales

  have "finite V" "finite E"
    unfolding graph_of_list_def
    by auto

  then show ?thesis
    using kruskal_tree_ref_spec[to_hnr]
    unfolding hn_refine_def lst_subgraph_rel_def kruskal_tree_spec_def
    apply (auto simp: valid_graph_axioms)
    apply (erule cons_post_rule)
    unfolding option_assn_pure_conv option_rel_def
    apply (sep_auto simp: pure_def in_br_conv G_def)
    done
qed

section \<open>Code export\<close>

export_code kruskal checking SML_imp
export_code kruskal in SML_imp module_name Kruskal (*file "Kruskal.sml"*)

export_code kruskal_tree checking SML_imp
export_code kruskal_tree in SML_imp module_name Kruskal (*file "Kruskal_tree.sml"*)


ML_val \<open>
  val export_nat = @{code integer_of_nat}
  val import_nat = @{code nat_of_integer}
  val export_int = @{code integer_of_int}
  val import_int = @{code int_of_integer}
  val import_list = map (fn (a,b,c) => (import_nat a, (import_int b, import_nat c)))
  val export_list = map (fn (a,(b,c)) => (export_nat a, export_int b, export_nat c))

  fun kruskal l = @{code kruskal} (import_list l) () |> export_list
  fun kruskal_tree l = @{code kruskal_tree} (import_list l) () |> Option.map export_list

  val result = kruskal [(1,~9,2),(2,~3,3),(3,~4,1)]

  val result_tree = kruskal_tree [(1,~9,2),(2,~3,3),(3,~4,1),(4,3,5)]
\<close>


end