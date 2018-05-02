theory Kruskal
  imports
    "./Graph_Definition"
    "./SeprefUF"
    Refine_Imperative_HOL.IICF
begin

term FOREACHcd

locale Kruskal = fcw_graph G
  for G :: "('v,'w::weight) graph"
begin

section \<open>Kruskal 1\<close>

definition empty_tree :: "('v, 'w) graph"
  where "empty_tree \<equiv> \<lparr> nodes = V, edges = {} \<rparr>"

definition previous_edges_connected :: "'v per \<Rightarrow> ('v \<times> 'w \<times> 'v) set \<Rightarrow> bool"
  where "previous_edges_connected uf E' \<equiv> (\<forall>(a, w, b)\<in>E - E'. (a,b)\<in> uf)"

definition valid_union_find_graph :: "'v per \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool"
  where "valid_union_find_graph uf H \<equiv> (\<forall>a\<in>V. \<forall>b\<in>V.
      (\<exists>p. valid_graph.is_path_undir H a p b) \<longleftrightarrow> (a,b) \<in> uf)"

definition exists_min_spanning_tree :: "('v, 'w) graph \<Rightarrow> bool"
  where "exists_min_spanning_tree H \<equiv> (\<exists>T. subgraph H T \<and> is_minimum_spanning_tree T)"

definition loop_invar_kruskal :: "('v \<times> 'w \<times> 'v) set \<Rightarrow> 'v per \<times> ('v, 'w) graph \<Rightarrow> bool"
  where "loop_invar_kruskal E' args \<equiv> case args of (uf, H) \<Rightarrow>
    part_equiv uf \<and>
    forest H \<and>
    subgraph H G \<and>
    edges H \<subseteq> E - E' \<and>
    previous_edges_connected uf E' \<and>
    valid_union_find_graph uf H \<and>
    Domain uf = V \<and>
    exists_min_spanning_tree H"

definition kruskal1 :: "('v, 'w) graph nres"
  where "kruskal1 \<equiv> do {
    let initial_union_find = per_init V;
    ASSERT (finite E);
    l \<leftarrow> SPEC (\<lambda>l. set l = E \<and> sorted_by_rel edges_less_eq l);

    (per, spanning_tree) \<leftarrow> nfoldli l (\<lambda>_. True)
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
      }) (initial_union_find, empty_tree);
    RETURN spanning_tree
  }"

lemma empty_tree_valid: "valid_graph empty_tree"
  unfolding empty_tree_def valid_graph_def
  by auto

lemma empty_tree_weighted: "weighted_graph empty_tree"
  using empty_tree_valid
  unfolding weighted_graph_def empty_tree_def
  by simp

lemma empty_exists_min_spanning_tree: "exists_min_spanning_tree empty_tree"
proof -
  from minimum_spanning_tree_exists obtain T where "is_minimum_spanning_tree T"
    by auto
  moreover from this have "subgraph empty_tree T"
    unfolding subgraph_def empty_tree_def is_minimum_spanning_tree_def
      is_spanning_tree_def
    by simp
  ultimately show ?thesis
    unfolding exists_min_spanning_tree_def
    by auto
qed

lemma loop_invar_kruskal_empty:
  shows "loop_invar_kruskal E (per_init V, empty_tree)"
proof -
  have "(\<exists>p. valid_graph.is_path_undir empty_tree a p b) \<longleftrightarrow> (a,b) \<in> per_init V"
    if ab: "a\<in>V \<and> b\<in>V" for a b
  proof
    assume "\<exists>p. valid_graph.is_path_undir empty_tree a p b"
    then obtain p where p: "valid_graph.is_path_undir empty_tree a p b"
      by blast
    with valid_graph.is_path_undir.simps[OF empty_tree_valid] have "a = b"
      unfolding empty_tree_def
      by (induction rule:valid_graph.is_path_undir.induct[OF empty_tree_valid]) auto
    with ab show "(a,b) \<in> per_init V"
      by (auto intro: part_equiv_refl')
  next
    assume "(a,b) \<in> per_init V"
    hence [simp]: "a=b" by (auto intro: per_init_self)
    from valid_graph.is_path_undir.simps(1)[OF empty_tree_valid] ab
      have "valid_graph.is_path_undir empty_tree a [] a"
      unfolding empty_tree_def
      by auto
    then show "\<exists>p. valid_graph.is_path_undir empty_tree a p b"
      by auto
  qed
  with empty_exists_min_spanning_tree show ?thesis
  unfolding loop_invar_kruskal_def empty_tree_def forest_def
    forest_axioms_def valid_graph_def subgraph_def previous_edges_connected_def
    valid_union_find_graph_def
  by auto
qed

lemma loop_invar_kruskal_valid_uf[simp]:
  assumes "loop_invar_kruskal E' (uf, H)"
  shows "part_equiv uf"
  using assms
  unfolding loop_invar_kruskal_def by simp

lemma loop_invar_kruskal_valid_graph:
  assumes "loop_invar_kruskal E' (uf, H)"
  shows "valid_graph H"
  using assms
  unfolding loop_invar_kruskal_def forest_def by simp

lemma loop_invar_kruskal_valid_ufg[simp]:
  assumes "loop_invar_kruskal E' (uf, H)"
  shows "valid_union_find_graph uf H"
  using assms
  unfolding loop_invar_kruskal_def by simp

lemma loop_invar_kruskal_edge_not_in_graph:
  assumes "loop_invar_kruskal E' (uf, H)"
  assumes "e \<in> E'"
  assumes "E' \<subseteq> E"
  shows "e \<in> E - edges H"
  using assms
  unfolding loop_invar_kruskal_def by auto

lemma preserve_previous_edges_connected_no_add:
  assumes "previous_edges_connected uf E'"
  assumes "Domain uf = V"
  assumes "(a,b) \<in> uf"
  shows "previous_edges_connected uf (E'-{(a, w, b)})"
proof -
  from assms(1) have "(a,b)\<in>uf" if e: "(a, w, b)\<in>E - E'" for a w b
    using e unfolding previous_edges_connected_def by blast
  with assms(3) show ?thesis
    unfolding previous_edges_connected_def by auto
qed

lemma preserve_previous_edges_connected_add:
  assumes "previous_edges_connected uf E'"
  assumes "part_equiv uf"
  assumes "Domain uf = V"
  assumes "a \<in> V"
  assumes "b \<in> V"
  shows "previous_edges_connected (per_union uf a b) (E'-{(a, w, b)})"
  using assms
  unfolding previous_edges_connected_def
  using per_union_impl[of _ _ uf a b] per_union_related[of uf a b]
  by fastforce

lemma preserve_valid_union_find_graph_add:
  assumes "valid_union_find_graph uf H"
  assumes UF'_def: "uf' = per_union uf a b"
  assumes "valid_graph H"
  assumes "a \<in> Domain uf"
  assumes "b \<in> Domain uf"
  assumes "Domain uf = V"
  assumes "subgraph H G"
  assumes PER: "part_equiv uf"
  shows "valid_union_find_graph uf' (add_edge a w b H)"
proof -
  have "(\<exists>p. valid_graph.is_path_undir (add_edge a w b H) x p y) \<longleftrightarrow> (x,y) \<in> uf'"
    if xy: "x\<in>V \<and> y\<in>V" for x y
  proof
    assume "\<exists>p. valid_graph.is_path_undir (add_edge a w b H) x p y"
    then obtain p where p: "valid_graph.is_path_undir (add_edge a w b H) x p y"
      by blast
    from \<open>a\<in>Domain uf\<close> \<open>b\<in>Domain uf\<close> have [simp]: "a\<in>Domain uf'" "b\<in>Domain uf'"
      by (auto simp: UF'_def)
    from PER have PER': "part_equiv uf'"
      by (auto simp: UF'_def union_part_equivp)
    show "(x,y) \<in> uf'"
    proof (cases "(a, w, b) \<in> set p \<or> (b, w, a) \<in> set p")
      case True
      from valid_graph.is_path_undir_split_distinct[OF add_edge_valid[OF assms(3)] p True]
      obtain p' p'' u u' where
        "valid_graph.is_path_undir (add_edge a w b H) x p' u \<and>
        valid_graph.is_path_undir (add_edge a w b H) u' p'' y" and
        u: "u\<in>{a,b} \<and> u'\<in>{a,b}" and
        "(a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p' \<and>
        (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p''"
        by auto
      with assms(4-7) valid_graph.add_edge_was_path[OF assms(3)]
      have "valid_graph.is_path_undir H x p' u \<and> valid_graph.is_path_undir H u' p'' y"
        unfolding subgraph_def by auto
      with assms(1,2,4,5,6) xy u have comps: "(x,u) \<in> uf \<and> (u', y) \<in> uf"
        unfolding valid_union_find_graph_def
        by auto
      have "(x,u)\<in>uf'" using comps per_union_impl UF'_def by auto
      also from u assms(4-6) part_equiv_refl'[OF PER' \<open>a\<in>Domain uf'\<close>]
        part_equiv_refl'[OF PER' \<open>b\<in>Domain uf'\<close>] part_equiv_sym[OF PER']
        per_union_related[OF PER] UF'_def
      have "(u,u') \<in> uf'"
        by auto
      also (part_equiv_trans[OF PER']) have "(u',y)\<in>uf'" using comps per_union_impl UF'_def by auto
      finally (part_equiv_trans[OF PER']) show ?thesis by simp
    next
      case False
      with assms(4-7) valid_graph.add_edge_was_path[OF assms(3) p(1)]
      have "valid_graph.is_path_undir H x p y"
        unfolding subgraph_def by auto
      with assms(1) xy have "(x,y)\<in>uf"
        unfolding valid_union_find_graph_def
        by auto
      with per_union_impl UF'_def show ?thesis
        by simp
    qed
  next
    assume asm: "(x, y) \<in> uf'"
    show "\<exists>p. valid_graph.is_path_undir (add_edge a w b H) x p y"
      proof (cases "(x, y) \<in> uf")
        case True
        with assms(1) xy obtain p where "valid_graph.is_path_undir H x p y"
          unfolding valid_union_find_graph_def
          by blast
        with valid_graph.add_edge_is_path[OF assms(3) this] show ?thesis
          by auto
      next
        case False
        with asm part_equiv_sym[OF PER]
        have "(x,a) \<in> uf \<and> (b,y) \<in> uf \<or>
              (b,x) \<in> uf \<and> (y,a) \<in> uf"
          unfolding per_union_def UF'_def
          by auto
        with assms(1,2,4,5,6) xy obtain p q
          where "valid_graph.is_path_undir H x p a \<and> valid_graph.is_path_undir H b q y \<or>
                 valid_graph.is_path_undir H b p x \<and> valid_graph.is_path_undir H y q a"
          unfolding valid_union_find_graph_def
          by blast
        with valid_graph.add_edge_is_path[OF assms(3)] obtain p' q'
          where "valid_graph.is_path_undir (add_edge a w b H) x p' a \<and>
                valid_graph.is_path_undir (add_edge a w b H) b q' y \<or>
                valid_graph.is_path_undir (add_edge a w b H) b p' x \<and>
                valid_graph.is_path_undir (add_edge a w b H) y q' a"
          by blast
        with valid_graph.is_path_undir_split'[OF add_edge_valid[OF assms(3)]]
        have "valid_graph.is_path_undir (add_edge a w b H) x (p' @ (a, w, b) # q') y \<or>
              valid_graph.is_path_undir (add_edge a w b H) y (q' @ (a, w, b) # p') x"
          by auto
        with valid_graph.is_path_undir_sym[OF add_edge_valid[OF assms(3)]]
        show ?thesis
          by auto
      qed
  qed
  then show ?thesis unfolding valid_union_find_graph_def by simp
qed

lemma exists_min_spanning_tree_add:
  assumes "exists_min_spanning_tree H"
  assumes "previous_edges_connected uf E'"
  assumes "a \<in> V"
  assumes "b \<in> V"
  assumes "subgraph H G"
  assumes "forest H"
  assumes "(a,w,b) \<in> E"
  assumes "(a,b) \<notin> uf"
  assumes "valid_union_find_graph uf H"
  assumes "Domain uf = V"
  assumes "\<forall>e\<in>E' - {(a, w, b)}. edges_less_eq (a, w, b) e"
  shows "exists_min_spanning_tree (add_edge a w b H)"
proof -
  from assms(1) obtain T where T: "subgraph H T" "is_minimum_spanning_tree T"
    unfolding exists_min_spanning_tree_def
    by blast
  from T(2) have valid_T: "valid_graph T"
    unfolding is_minimum_spanning_tree_def is_spanning_tree_def
      tree_def forest_def
    by simp
  from T(2) have forest_T: "forest T"
    unfolding is_minimum_spanning_tree_def is_spanning_tree_def
      tree_def
    by simp
  from T(2) have connected_T: "connected_graph T"
    unfolding is_minimum_spanning_tree_def is_spanning_tree_def
      tree_def
    by simp
  from T(2) have subgraph_T: "subgraph T G"
    unfolding is_minimum_spanning_tree_def is_spanning_tree_def
    by simp
  with finite_E have finite_T: "finite (edges T)"
    unfolding subgraph_def by (auto simp: finite_subset)
  from T(2) assms(3,4) have ab: "a\<in>nodes T" "b\<in>nodes T"
    unfolding subgraph_def is_minimum_spanning_tree_def
      is_spanning_tree_def
    by auto
  from assms(6) have valid_H: "valid_graph H"
    unfolding forest_def
    by simp
  show ?thesis
  proof (cases "(a,w,b) \<in> edges T")
    case True
    with T(1) ab have "subgraph (add_edge a w b H) T"
      unfolding subgraph_def add_edge_def
      by auto
    with T(2) show ?thesis
      unfolding exists_min_spanning_tree_def
      by auto
  next
    case False
    from T(2) ab obtain p where p: "valid_graph.is_path_undir T a p b"
      unfolding is_minimum_spanning_tree_def is_spanning_tree_def
        tree_def connected_graph_def connected_graph_axioms_def
      by blast
    from assms(3,4,8,9,10) have "\<nexists>p. valid_graph.is_path_undir H a p b"
        unfolding valid_union_find_graph_def
        by simp
    from forest.delete_edge_from_path[OF forest_T p T(1) this]
    obtain x w' y where xy: "(x, w', y) \<in> edges T" "(x, w', y) \<notin> edges H" and
      not_connected: "\<forall>p. \<not> valid_graph.is_path_undir (delete_edge x w' y T) a p b" and
      connected_xy: "\<exists>p. valid_graph.is_path_undir (add_edge a w b (delete_edge x w' y T)) x p y"
      by blast
    obtain T' where T': "T' = add_edge a w b (delete_edge x w' y T)"
      by blast
    from valid_T have valid_delete_T: "valid_graph (delete_edge x w' y T)"
      by simp
    with T' have valid_T': "valid_graph T'"
      by simp
    from False have False': "(a, w, b) \<notin> edges (delete_edge x w' y T)"
      unfolding delete_edge_def by simp
    from forest_delete_edge[of T x w' y] T(2)
    have forest_delete_T: "forest (delete_edge x w' y T)"
      unfolding is_minimum_spanning_tree_def is_spanning_tree_def tree_def
      by simp
    from False xy(1) have ab_neq_xy: "(x, w', y) \<noteq> (a, w, b)"
      by auto
    from T' T(2) assms(3,4,7) have subgraph_T': "subgraph T' G"
      unfolding subgraph_def is_minimum_spanning_tree_def
        is_spanning_tree_def add_edge_def delete_edge_def
      by auto
    from subgraph_T valid_T
    have weighted_T: "weighted_graph T"
      unfolding weighted_graph_def subgraph_def
      by auto
    from subgraph_T' valid_T'
    have weighted_T': "weighted_graph T'"
      unfolding weighted_graph_def subgraph_def
      by auto
    from T(1) xy have subgraph_H_delete_T: "subgraph H (delete_edge x w' y T)"
      unfolding subgraph_def delete_edge_def
      by auto
    have "\<forall>p. \<not> valid_graph.is_path_undir H x p y"
    proof (rule ccontr)
      assume "\<not> (\<forall>p. \<not> valid_graph.is_path_undir H x p y)"
      then obtain p where p: "valid_graph.is_path_undir H x p y"
        by auto
      from forest.cycle_free[OF forest_T] xy(1)
        have contr: "\<forall>p. \<not> valid_graph.is_path_undir (delete_edge x w' y T) x p y"
        by auto
      with valid_graph.is_path_undir_subgraph[OF valid_H p subgraph_H_delete_T valid_delete_T]
      show False by simp
    qed
    with assms(9,10) valid_graph.E_validD[OF valid_T xy(1)] subgraph_T
    have "(x,y)\<notin>uf"
      unfolding valid_union_find_graph_def subgraph_def
      by auto
    with assms(2) xy(2) have "(x, w', y) \<notin> E - E'"
      unfolding previous_edges_connected_def by blast
    moreover from xy(1) subgraph_T have "(x, w', y) \<in> E"
      unfolding subgraph_def
      by auto
    ultimately have "(x, w', y) \<in> E'"
      by auto
    with assms(11) ab_neq_xy have *: "w \<le> w'"
      unfolding edges_less_eq_def
      by force
    with T' False xy(1) finite_T sum.subset_diff[of "{(x, w', y)}" "edges T" "fst \<circ> snd"]
    have improvement: "weighted_graph.edge_weight T' \<le> weighted_graph.edge_weight T"
      unfolding weighted_graph.edge_weight_def[OF weighted_T]
                weighted_graph.edge_weight_def[OF weighted_T']
      apply auto
      apply(subst ab_semigroup_add.add_commute[OF class.ordered_ab_semigroup_add.axioms(1)[OF class.weight.axioms(2)[OF weight_class.weight_axioms]], of _ w'])
      apply(auto simp: add_right_mono)
      done
    from T' subgraph_H_delete_T have "subgraph (add_edge a w b H) T'"
      unfolding subgraph_def
      by auto
    moreover from T' ab forest_add_edge[OF forest_delete_T _ _ not_connected]
      have "forest T'"
        by simp
    moreover from connected_xy T' swap_delete_add_edge[OF ab_neq_xy, of T]
      assms(3,4) subgraph_T
      connected_graph.delete_edge_connected[OF connected_graph.add_edge_connected[OF connected_T], of a b x w' y w]
      have "connected_graph T'"
      unfolding subgraph_def by auto
    moreover from improvement T(2) have "is_optimal_tree T'"
      unfolding is_minimum_spanning_tree_def is_optimal_tree_def
      by auto
    ultimately show ?thesis using subgraph_T'
      unfolding exists_min_spanning_tree_def is_minimum_spanning_tree_def
        is_spanning_tree_def tree_def
      by auto
  qed
qed

lemma union_preserves_forest:
  assumes "forest H"
  assumes "\<not> (a,b) \<in> uf"
  assumes "subgraph H G"
  assumes "Domain uf = V"
  assumes "a \<in> V"
  assumes "b \<in> V"
  assumes "valid_union_find_graph uf H"
  shows "forest (add_edge a w b H)"
  using assms forest_add_edge[of H]
  unfolding valid_union_find_graph_def subgraph_def
  by metis

lemma union_preserves_loop_invar:
  assumes "loop_invar_kruskal E' (uf, H)"
  assumes "(a,b) \<notin> uf"
  assumes "E' \<subseteq> E"
  assumes "(a, w, b) \<in> E'"
  assumes "\<forall>e\<in>E' - {(a, w, b)}. edges_less_eq (a, w, b) e"
  shows "loop_invar_kruskal (E' - {(a, w, b)}) (per_union uf a b, add_edge a w b H)"
  using assms preserve_previous_edges_connected_add union_preserves_forest
    preserve_valid_union_find_graph_add[OF _ _ loop_invar_kruskal_valid_graph]
    add_edge_preserve_subgraph exists_min_spanning_tree_add
  unfolding loop_invar_kruskal_def
  by (auto simp: union_part_equivp E_validD)

lemma same_component_preserves_loop_invar:
  assumes "loop_invar_kruskal E' (uf, H)"
  assumes "(a,b)\<in>uf"
  shows "loop_invar_kruskal (E' - {(a, w, b)}) (uf, H)"
  using assms preserve_previous_edges_connected_no_add
  unfolding loop_invar_kruskal_def
  by auto

lemma loop_invar_node_exists:
  assumes "loop_invar_kruskal E' (uf, H)"
  assumes "E' \<subseteq> E"
  assumes "(a, w, b) \<in> E'"
  shows "a\<in>Domain uf" and "b\<in>Domain uf"
  using assms E_valid
  unfolding loop_invar_kruskal_def
  by blast+

lemma all_connected_edges:
  assumes "valid_graph H"
  assumes "subgraph H G"
  assumes "Domain uf = V"
  assumes "previous_edges_connected uf {}"
  assumes "valid_union_find_graph uf H"
  shows "connected_graph H"
proof -
  from assms(3,4,5) E_validD have "\<exists>p. valid_graph.is_path_undir H a p b"
    if e: "(a, w, b) \<in> E"  for a w b
    using e
    unfolding subgraph_def valid_union_find_graph_def previous_edges_connected_def
    by auto
  with assms induce_connected show ?thesis
    by blast
qed

lemma loop_invar_kruskal_final:
  assumes "loop_invar_kruskal {} (uf, H)"
  shows "is_minimum_spanning_tree H"
  using assms
proof -
  from assms obtain T where T: "subgraph H T" "is_minimum_spanning_tree T"
    unfolding loop_invar_kruskal_def exists_min_spanning_tree_def by auto
  from assms all_connected_edges[of H uf] have "tree H"
    unfolding loop_invar_kruskal_def forest_def tree_def by simp
  with T sub_tree_eq[of H T] show ?thesis
    unfolding is_minimum_spanning_tree_def is_spanning_tree_def
    by simp
qed

theorem kruskal1_spanning_tree: "(kruskal1, SPEC is_minimum_spanning_tree)\<in>\<langle>Id\<rangle>nres_rel"
  unfolding kruskal1_def
  thm nfoldli_rule[where I="\<lambda>l1 l2 s. loop_invar_kruskal (set l2) s"]
  apply(refine_vcg nfoldli_rule[where I="\<lambda>l1 l2 s. loop_invar_kruskal (set l2) s"])
  apply clarsimp_all
  apply (rule finite_E)
  apply (rule loop_invar_kruskal_empty)
  sorry
(*
  subgoal by (fastforce simp: same_component_preserves_loop_invar)
  subgoal by (fastforce simp: loop_invar_node_exists)
  subgoal by (fastforce simp: loop_invar_node_exists)
  subgoal by (meson loop_invar_kruskal_edge_not_in_graph)
  subgoal by (simp add: union_preserves_loop_invar)
  subgoal by (simp add: loop_invar_kruskal_final)
*)

section \<open>Kruskal 2\<close>

definition (in -) "graph_of_list l \<equiv> \<lparr>nodes = fst`set l \<union> (snd o snd)`set l, edges = set l \<rparr>"

(*definition (in -) "lst_graph_invar l \<equiv> distinct l"*)
definition (in -) "lst_graph_invar l \<equiv> distinct l"
definition (in -) "lst_graph_rel \<equiv> br graph_of_list (\<lambda>_. True)"

lemma mset_eq_impl_distinct_iff: "mset x = mset y \<Longrightarrow> distinct x = distinct y"
  by (metis distinct_count_atmost_1 set_mset_mset)

definition "is_linorder_rel R \<equiv> (\<forall>x y. R x y \<or> R y x) \<and> (\<forall>x y z. R x y \<longrightarrow> R y z \<longrightarrow> R x z)"

lemma it_to_sorted_list_by_quicksort:
  assumes "is_linorder_rel R"
  shows "(RETURN o quicksort_by_rel R [], it_to_sorted_list R) \<in> \<langle>Id\<rangle>list_set_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (auto simp: list_set_rel_def in_br_conv it_to_sorted_list_def
    simp: mset_eq_impl_distinct_iff[OF quicksort_by_rel_permutes]
     intro!: nres_relI)
  apply (rule sorted_by_rel_quicksort_by_rel)
  using assms unfolding is_linorder_rel_def by blast+

lemma quicksort_nfoldli_refine_foreachoci:
  assumes "is_linorder_rel R"
  assumes "(l,s)\<in>\<langle>Id\<rangle>list_set_rel" and [simplified,simp]: "(c,c')\<in>Id" "(f,f')\<in>Id" "(\<sigma>,\<sigma>')\<in>Id"
  shows "nfoldli (quicksort_by_rel R [] l) c f \<sigma> \<le> \<Down>Id (FOREACHoci R I s c' f' \<sigma>')"
  apply simp
  apply (rule order_trans[OF _ FOREACHoci_itsl])
  using it_to_sorted_list_by_quicksort[OF assms(1), param_fo, THEN nres_relD] assms(2)
  by (auto simp: refine_pw_simps pw_le_iff)

definition (in -) "V_impl_aux l \<equiv> remdups (map fst l @ map (snd o snd) l)"

definition (in -) "subgraph_of_lst G l \<equiv> \<lparr>
  nodes = nodes G,
  edges = set l \<rparr>"
definition (in -) "lst_subgraph_rel G \<equiv> br (subgraph_of_lst G) lst_graph_invar"


context
  fixes l
  assumes l_G_refine: "(l,G) \<in> lst_graph_rel"
begin

(*abbreviation "V_impl \<equiv> V_impl_aux l"*)

(*lemma V_impl_refine:
  shows "(V_impl,V) \<in> \<langle>Id\<rangle>list_set_rel"
  using l_G_refine unfolding lst_graph_rel_def list_set_rel_def lst_graph_invar_def V_impl_aux_def
  by (auto simp: in_br_conv graph_of_list_def)
*)

(*lemma E_impl_refine:
  "(l, E) \<in> \<langle>Id\<rangle>list_set_rel"
  using l_G_refine unfolding lst_graph_rel_def list_set_rel_def lst_graph_invar_def
  by (auto simp: in_br_conv graph_of_list_def intro: distinct_mapI)
*)

corollary E_impl:
  "set l = E"
  using l_G_refine unfolding lst_graph_rel_def lst_graph_invar_def
  by (auto simp: in_br_conv graph_of_list_def)

(*
lemma init_uf_refine: "per_init (set (V_impl)) = per_init V"
  using V_impl_refine
  unfolding set_rel_def list_set_rel_def
  by (auto simp: in_br_conv)
*)

definition "kruskal_loop_tmpl B I \<equiv> FOREACHoi edges_less_eq loop_invar_kruskal E B I"
definition "kruskal_loop_tmpl2 B I \<equiv> nfoldli (quicksort_by_rel edges_less_eq [] l) (\<lambda>_. True) B I"

lemma edges_less_eq_linorder: "is_linorder_rel edges_less_eq"
  unfolding edges_less_eq_def is_linorder_rel_def
  by (metis linear order_trans)

(*
lemma kruskal_loop_tmpl_refine: "(kruskal_loop_tmpl2,kruskal_loop_tmpl) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding kruskal_loop_tmpl2_def kruskal_loop_tmpl_def FOREACHoi_def
  apply (refine_rcg quicksort_nfoldli_refine_foreachoci)
  apply (vc_solve simp: E_impl_refine edges_less_eq_linorder)
  done
  *)

definition kruskal2 :: "('v, 'w) graph nres"
  where "kruskal2 \<equiv> do {
    let initial_union_find = per_init (V);
    let l = quicksort_by_rel edges_less_eq [] l;
    (per, spanning_tree) \<leftarrow> nfoldli l (\<lambda>_. True)
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
      }) (initial_union_find, empty_tree);
    RETURN spanning_tree
  }"

lemma sort_edges_correct: "sorted_by_rel edges_less_eq (quicksort_by_rel edges_less_eq [] l)"
  by (metis (no_types, hide_lams) edges_less_eq_linorder is_linorder_rel_def sorted_by_rel_quicksort_by_rel)


theorem kruskal2_refine: "(kruskal2, kruskal1)\<in>\<langle>Id\<rangle>nres_rel"
  unfolding kruskal2_def kruskal1_def
  apply (refine_rcg)
  apply refine_dref_type
  apply (vc_solve simp: E_impl sort_edges_correct)
  done

section \<open>Kruskal 3\<close>

definition "lst_empty_tree \<equiv> []"


definition kruskal3 :: "('v \<times> 'w \<times> 'v) list nres"
  where "kruskal3 \<equiv> do {
    let initial_union_find = per_init V;
    (per, spanning_tree) \<leftarrow> nfoldli (quicksort_by_rel edges_less_eq [] l) (\<lambda>_. True)
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
      }) (initial_union_find, lst_empty_tree);
    RETURN spanning_tree
  }"

definition "kruskal_loop_body2 a w b uf H \<equiv> do {
        ASSERT (a\<in>Domain uf \<and> b\<in>Domain uf);
        if per_compare uf a b
        then
          RETURN (uf, H)
        else do {
          let uf = per_union uf a b;
          ASSERT ((a, w, b) \<in> E - edges H);
          RETURN (uf, add_edge a w b H)
        }
      }"

definition "kruskal_loop_body3 a w b uf l_H \<equiv> do {
        ASSERT (a\<in>Domain uf \<and> b\<in>Domain uf);
        if per_compare uf a b
        then
          RETURN (uf, l_H)
        else do {
          let uf = per_union uf a b;
          ASSERT ((a, w, b) \<in> set l - set l_H);
          RETURN (uf, (a, w, b)#l_H)
        }}"


lemma empty_tree_refine: "(lst_empty_tree, empty_tree) \<in> lst_subgraph_rel G"
  unfolding empty_tree_def lst_empty_tree_def lst_subgraph_rel_def lst_graph_invar_def subgraph_of_lst_def
  by (auto simp: in_br_conv)

lemma add_edge_refine:
  assumes "(l_H, H) \<in> lst_subgraph_rel G"
  assumes "(a, w, b) \<in> set l - set l_H"
  shows "((a, w, b) # l_H, add_edge a w b H) \<in> lst_subgraph_rel G"
  using assms
  unfolding E_impl add_edge_def lst_subgraph_rel_def lst_graph_invar_def list_set_rel_def subgraph_of_lst_def
  by (auto simp: in_br_conv E_validD)


lemma kruskal_loop_body_refine: "(kruskal_loop_body3, kruskal_loop_body2)\<in>Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id
    \<rightarrow> lst_subgraph_rel G \<rightarrow> \<langle>{((uf, l_H), (uf', H)) | uf uf' l_H H. (uf, uf') \<in> Id \<and> (l_H, H) \<in> lst_subgraph_rel G}\<rangle>nres_rel"
  unfolding kruskal_loop_body3_def kruskal_loop_body2_def
  apply (refine_vcg)
  apply (vc_solve simp: add_edge_refine)
  using E_impl
  unfolding lst_subgraph_rel_def list_set_rel_def subgraph_of_lst_def
  by (auto simp: in_br_conv)

theorem kruskal3_refine: "(kruskal3, kruskal2)\<in>\<langle>lst_subgraph_rel G\<rangle>nres_rel"
  unfolding kruskal3_def kruskal2_def
  apply (fold kruskal_loop_body3_def kruskal_loop_body2_def)
  apply (rewrite at "let l = quicksort_by_rel edges_less_eq [] l in _" Let_def)
  apply (refine_vcg kruskal_loop_body_refine[param_fo, THEN nres_relD])
  apply refine_dref_type
  apply (vc_solve simp: empty_tree_refine)
  done

end
end

term "\<exists>N. nodes (graph_of_list l) = {i. i<N}"

locale Kruskal_nat = Kruskal "graph_of_list l" for
  l :: "(nat \<times> nat \<times> nat) list"
  (*assumes distinct: "distinct l"*)
  (*
  assumes nat_nodes: "N = card (fst`set l \<union> (snd o snd)`set l) \<Longrightarrow> fst`set l \<union> (snd o snd)`set l = {i. i<N}"
  *)
  (*assumes nat_nodes': "\<exists>N. nodes (graph_of_list l) = {i. i<N}"*)
begin


(*
locale Kruskal_nat =
  fixes l :: "(nat \<times> nat \<times> nat) list"
  assumes distinct: "distinct l"
  assumes Kruskal_G: "Kruskal \<lparr>nodes = fst`set l \<union> (snd o snd)`set l, edges = set l \<rparr>"
  assumes nat_nodes: "N = card (fst`set l \<union> (snd o snd)`set l) \<Longrightarrow> fst`set l \<union> (snd o snd)`set l = {i. i<N}"
begin

sublocale Kruskal "\<lparr>nodes = fst`set l \<union> (snd o snd)`set l, edges = set l \<rparr>"
  using Kruskal_G .
*)

abbreviation "G\<equiv>graph_of_list l"

definition (in -) "N l \<equiv> Max (insert 0 (nodes (graph_of_list l))) + 1"

lemma (in -) N_impl[code]: "N l = fold (\<lambda>(u,_,w) x. max u (max w x)) l 0 + 1"
proof -
  have "fold (\<lambda>(u,_,w) x. max u (max w x)) l a = Max (insert a (nodes (graph_of_list l)))" for a
    apply (induction l arbitrary: a)
    apply (auto simp: graph_of_list_def)
    subgoal for a b l aa
      apply (cases l)
      by (auto simp: ac_simps)
    done
  thus ?thesis unfolding N_def by auto
qed


lemma l_G_refine: "(l, G) \<in> lst_graph_rel"
  unfolding lst_graph_rel_def
  by (auto simp: in_br_conv)

definition kruskal4 :: "(nat \<times> nat \<times> nat) list nres"
  where "kruskal4 \<equiv> do {
    let initial_union_find = per_init' (N l);
    (per, spanning_tree) \<leftarrow> nfoldli (quicksort_by_rel edges_less_eq [] l) (\<lambda>_. True)
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
    RETURN spanning_tree
  }"

definition per_supset_rel :: "('a per \<times> 'a per) set" where "per_supset_rel
  \<equiv> {(p1,p2). p1 \<inter> Domain p2 \<times> Domain p2 = p2 \<and> p1 \<inter> -(Domain p2 \<times> Domain p2) \<subseteq> Id}"

lemma per_initN_refine: "(per_init' (N l), per_init V) \<in> per_supset_rel"
  unfolding per_supset_rel_def per_init'_def per_init_def N_def
  by (auto simp: less_Suc_eq_le finite_V)

lemma per_supset_rel_dom: "(p1, p2) \<in> per_supset_rel \<Longrightarrow> Domain p1 \<supseteq> Domain p2"
  by (auto simp: per_supset_rel_def)

lemma per_supset_compare:
  "(p1, p2) \<in> per_supset_rel \<Longrightarrow> x1\<in>Domain p2 \<Longrightarrow> x2\<in>Domain p2 \<Longrightarrow> per_compare p1 x1 x2 \<longleftrightarrow> per_compare p2 x1 x2"
  by (auto simp: per_supset_rel_def)

lemma per_supset_union: "(p1, p2) \<in> per_supset_rel \<Longrightarrow> x1\<in>Domain p2 \<Longrightarrow> x2\<in>Domain p2 \<Longrightarrow>
  (per_union p1 x1 x2, per_union p2 x1 x2) \<in> per_supset_rel"
  apply (clarsimp simp: per_supset_rel_def per_union_def Domain_unfold )
  apply (intro subsetI conjI)
  apply blast
  apply force
  done


theorem kruskal4_refine: "(kruskal4, kruskal3 l)\<in>\<langle>Id\<rangle>nres_rel"
  unfolding kruskal4_def kruskal3_def[OF l_G_refine] lst_empty_tree_def[OF l_G_refine]
  apply (refine_vcg)
  supply RELATESI[where R="per_supset_rel::(nat per \<times> _) set", refine_dref_RELATES]
  apply refine_dref_type
  apply (vc_solve simp: per_initN_refine)
  apply (auto dest: per_supset_rel_dom per_supset_compare per_supset_union)
  done

end

concrete_definition kruskal5 uses Kruskal_nat.kruskal4_def
print_theorems

definition "sort_edges \<equiv> quicksort_by_rel edges_less_eq []"

lemma [sepref_import_param]: "(sort_edges,sort_edges)\<in>\<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow>\<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel" by simp
lemma [sepref_import_param]: "(N, N) \<in> \<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow> nat_rel" by simp

sepref_definition kruskal6 is
  "kruskal5" :: "(list_assn (nat_assn\<times>\<^sub>anat_assn\<times>\<^sub>anat_assn))\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a nat_assn \<times>\<^sub>a nat_assn)"
  unfolding kruskal5_def sort_edges_def[symmetric]
  apply (rewrite at "nfoldli _ _ _ (_,\<hole>)" HOL_list.fold_custom_empty)
  by sepref

context Kruskal_nat begin

  thm kruskal1_spanning_tree
  thm kruskal2_refine[OF l_G_refine]
  thm kruskal3_refine[OF l_G_refine]
  thm kruskal4_refine
  thm kruskal5.refine[OF Kruskal_nat_axioms]
  thm kruskal6.refine

  lemmas kruskal5_ref_spec = kruskal4_refine[
    unfolded kruskal5.refine[OF Kruskal_nat_axioms],
    FCOMP kruskal3_refine[OF l_G_refine],
    FCOMP kruskal2_refine[OF l_G_refine],
    FCOMP kruskal1_spanning_tree
    ]

  lemma kruskal6_refine': "(uncurry0 (kruskal6 l), uncurry0 (kruskal5 l))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a nat_assn \<times>\<^sub>a nat_assn)"
    using kruskal6.refine
    unfolding list_assn_pure_conv prod_assn_pure_conv
    unfolding hfref_def hn_refine_def pure_def hn_ctxt_def
    by auto

  lemma [fcomp_norm_simps]: "list_assn (nat_assn \<times>\<^sub>a nat_assn \<times>\<^sub>a nat_assn) = id_assn"
    by (auto simp: list_assn_pure_conv)

  lemmas kruskal6_ref_spec = kruskal6_refine'[FCOMP kruskal5_ref_spec]
end


lemma kruskal6_refine:
  fixes l
  defines "G \<equiv> graph_of_list l"
  assumes CONN: "connected_graph G"
  shows "<emp> kruskal6 l <\<lambda>r. \<up>(lst_graph_invar r \<and> weighted_graph.is_minimum_spanning_tree G (subgraph_of_lst G r))>\<^sub>t"
proof -

  interpret connected_graph "graph_of_list l"
    using CONN
    unfolding G_def
    by simp

  interpret Kruskal "graph_of_list l"
    apply unfold_locales
    unfolding graph_of_list_def
    by auto

  interpret Kruskal_nat l by unfold_locales

  show ?thesis
    using kruskal6_ref_spec[to_hnr]
    unfolding hn_refine_def lst_subgraph_rel_def
    apply clarsimp
    apply (erule cons_post_rule)
    apply (sep_auto simp: hn_ctxt_def pure_def in_br_conv G_def)
    done
qed


export_code kruskal6 checking SML_imp
export_code kruskal6 in SML_imp module_name Kruskal (*file "Kruskal.sml"*)





ML_val \<open>
  val export_nat = @{code integer_of_nat}
  val import_nat = @{code nat_of_integer}
  val import_list = map (fn (a,b,c) => (import_nat a, (import_nat b, import_nat c)))
  val export_list = map (fn (a,(b,c)) => (export_nat a, export_nat b, export_nat c))

  fun kruskal l = @{code kruskal6} (import_list l) () |> export_list

  val result = kruskal [(10,2,200000),(200000,3,30),(30,5,10)]


\<close>


end