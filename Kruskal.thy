theory Kruskal
  imports
    "./Graph_Definition"
    "./Union_Find2"
    Refine_Imperative_HOL.IICF
begin

locale Kruskal = fcw_graph G
  for G :: "('v,'w::weight) graph"
begin

section \<open>Kruskal 1\<close>

definition empty_tree :: "('v, 'w) graph"
  where "empty_tree \<equiv> \<lparr> nodes = V, edges = {} \<rparr>"

definition previous_edges_connected :: "'v union_find \<Rightarrow> ('v \<times> 'w \<times> 'v) set \<Rightarrow> bool"
  where "previous_edges_connected l E' \<equiv> (\<forall>(a, w, b)\<in>E - E'.
    same_component l a b)"

definition valid_union_find_graph :: "'v union_find \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool"
  where "valid_union_find_graph uf H \<equiv> (\<forall>a\<in>dom uf. \<forall>b\<in>dom uf.
      (\<exists>p. valid_graph.is_path_undir H a p b) \<longleftrightarrow> same_component uf a b)"

definition exists_min_spanning_tree :: "('v, 'w) graph \<Rightarrow> bool"
  where "exists_min_spanning_tree H \<equiv> (\<exists>T. subgraph H T \<and> is_minimum_spanning_tree T)"

definition loop_invar_kruskal :: "('v \<times> 'w \<times> 'v) set \<Rightarrow> 'v union_find \<times> ('v, 'w) graph \<Rightarrow> bool"
  where "loop_invar_kruskal E' args \<equiv> case args of (uf, H) \<Rightarrow>
    valid_union_find uf \<and>
    forest H \<and>
    subgraph H G \<and>
    edges H \<subseteq> E - E' \<and>
    previous_edges_connected uf E' \<and>
    valid_union_find_graph uf H \<and>
    dom uf = V \<and>
    exists_min_spanning_tree H"

definition loop_invar_init :: "'v set \<Rightarrow> 'v union_find \<Rightarrow> bool"
  where "loop_invar_init V' uf \<equiv>
    valid_union_find uf \<and>
    V' \<inter> dom uf = {} \<and>
    V' \<union> dom uf = V \<and>
    (\<forall>v \<in> dom uf. in_component uf v v)"


definition kruskal1 :: "('v, 'w) graph nres"
  where "kruskal1 \<equiv> do {
    initial_union_find \<leftarrow> FOREACHi loop_invar_init V
      (\<lambda>v uf. do {
        add_node_spec uf v
      }) empty_union_find;
    (union_find, spanning_tree) \<leftarrow> FOREACHoi edges_less_eq loop_invar_kruskal E
      (\<lambda>(a, w, b) (uf, H). do {
        (uf', root_a) \<leftarrow> find_spec uf a;
        (uf'', root_b) \<leftarrow> find_spec uf' b;
        ASSERT (preserve_component uf uf'' \<and> in_component uf'' a root_a \<and> in_component uf'' b root_b);
        if root_a \<noteq> root_b
        then do {
          uf''' \<leftarrow> union_spec uf'' a b;
          ASSERT ((a, w, b) \<in> E - edges H);
          RETURN (uf''', add_edge a w b H)
        } else
          RETURN (uf'', H)
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

lemma loop_invar_init_empty: "loop_invar_init V empty_union_find"
  unfolding loop_invar_init_def by simp

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
  assumes "loop_invar_init {} uf"
  shows "loop_invar_kruskal E (uf, empty_tree)"
proof -
  have "(\<exists>p. valid_graph.is_path_undir empty_tree a p b) \<longleftrightarrow> same_component uf a b"
    if ab: "a\<in>dom uf \<and> b\<in>dom uf" for a b
  proof
    assume "\<exists>p. valid_graph.is_path_undir empty_tree a p b"
    then obtain p where p: "valid_graph.is_path_undir empty_tree a p b"
      by blast
    with valid_graph.is_path_undir.simps[OF empty_tree_valid] have "a = b"
      unfolding empty_tree_def
      by (induction rule:valid_graph.is_path_undir.induct[OF empty_tree_valid]) auto
    with ab assms same_component_refl[of uf] show "same_component uf a b"
      unfolding loop_invar_init_def
      by blast
  next
    assume "same_component uf a b"
    then obtain c where c: "in_component uf a c \<and> in_component uf b c"
      unfolding same_component_def by auto
    from c ab assms in_component_unique[of uf] have "a = c \<and> b = c"
      unfolding loop_invar_init_def
      by fast
    also from valid_graph.is_path_undir.simps(1)[OF empty_tree_valid] ab assms
      have "valid_graph.is_path_undir empty_tree a [] a"
      unfolding empty_tree_def loop_invar_init_def
      by auto
    ultimately show "\<exists>p. valid_graph.is_path_undir empty_tree a p b"
      by auto
  qed
  with assms empty_exists_min_spanning_tree show ?thesis
  unfolding loop_invar_kruskal_def empty_tree_def forest_def
    forest_axioms_def valid_graph_def subgraph_def previous_edges_connected_def
    valid_union_find_graph_def loop_invar_init_def
  by auto
qed

lemma loop_invar_init_valid_uf[simp]:
  assumes "loop_invar_init V' uf"
  shows "valid_union_find uf"
  using assms
  unfolding loop_invar_init_def by simp

lemma loop_invar_init_not_exist:
  assumes "loop_invar_init V' uf"
  assumes "v \<in> V'"
  shows "v \<notin> dom uf"
  using assms
  unfolding loop_invar_init_def by auto


lemma loop_invar_kruskal_valid_uf[simp]:
  assumes "loop_invar_kruskal E' (uf, H)"
  shows "valid_union_find uf"
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

lemma preserve_previous_edges_connected:
  assumes "previous_edges_connected uf E'"
  assumes "preserve_component uf uf'"
  assumes "dom uf = V"
  shows "previous_edges_connected uf' E'"
proof -
  have "same_component uf' a b" if e: "(a, w, b)\<in>E - E'" for a w b
  proof -
    from assms(1) e have "same_component uf a b"
      unfolding previous_edges_connected_def by blast
    also from assms(3) e E_valid have "a \<in> dom uf \<and> b \<in> dom uf"
      by blast
    ultimately show ?thesis
      using assms(2)
      unfolding preserve_component_def same_component_def
      by blast
  qed
  then show ?thesis
    unfolding previous_edges_connected_def by auto
qed

lemma preserve_previous_edges_connected_no_add:
  assumes "previous_edges_connected uf E'"
  assumes "preserve_component uf uf'"
  assumes "dom uf = V"
  assumes "same_component uf' a b"
  shows "previous_edges_connected uf' (E'-{(a, w, b)})"
proof -
  have "same_component uf' a b" if e: "(a, w, b)\<in>E - E'" for a w b
  proof -
    from assms(1) e have "same_component uf a b"
      unfolding previous_edges_connected_def by blast
    also from assms(3) e E_valid have "a \<in> dom uf \<and> b \<in> dom uf"
      by blast
    ultimately show ?thesis
      using assms(2)
      unfolding preserve_component_def same_component_def
      by blast
  qed
  with assms(4) show ?thesis
    unfolding previous_edges_connected_def by auto
qed

lemma preserve_previous_edges_connected_add:
  assumes "previous_edges_connected uf E'"
  assumes "preserve_component_union uf uf' a b"
  assumes "dom uf = V"
  assumes "same_component uf' a b"
  shows "previous_edges_connected uf' (E'-{(a, w, b)})"
  using assms preserve_component_union_impl[OF assms(2)]
  unfolding previous_edges_connected_def preserve_component_union_def
  by blast

lemma preserve_valid_union_find_graph:
  assumes "valid_union_find_graph uf H"
  assumes "preserve_component uf uf'"
  assumes "dom uf = dom uf'"
  shows "valid_union_find_graph uf' H"
  using assms
  unfolding valid_union_find_graph_def preserve_component_def same_component_def
  by auto

lemma preserve_valid_union_find_graph_add:
  assumes "valid_union_find_graph uf H"
  assumes "preserve_component_union uf uf' a b"
  assumes "valid_graph H"
  assumes "same_component uf' a b"
  assumes "dom uf = dom uf'"
  assumes "a \<in> dom uf"
  assumes "b \<in> dom uf"
  assumes "dom uf = V"
  assumes "subgraph H G"
  assumes "valid_union_find uf'"
  shows "valid_union_find_graph uf' (add_edge a w b H)"
proof -
  have "(\<exists>p. valid_graph.is_path_undir (add_edge a w b H) x p y) \<longleftrightarrow> same_component uf' x y"
    if xy: "x\<in>dom uf' \<and> y\<in>dom uf'" for x y
  proof
    assume "\<exists>p. valid_graph.is_path_undir (add_edge a w b H) x p y"
    then obtain p where p: "valid_graph.is_path_undir (add_edge a w b H) x p y"
      by blast
    show "same_component uf' x y"
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
      with assms(6,7,8,9) valid_graph.add_edge_was_path[OF assms(3)]
      have "valid_graph.is_path_undir H x p' u \<and> valid_graph.is_path_undir H u' p'' y"
        unfolding subgraph_def by auto
      with assms(1,5,6,7) xy u have comps: "same_component uf x u \<and> same_component uf u' y"
        unfolding valid_union_find_graph_def
        by auto
      from u assms(4,5,6,7) same_component_refl[OF assms(10), of a]
        same_component_refl[OF assms(10), of b] same_component_sym[OF assms(4)]
      have "same_component uf' u u'"
        by auto
      from comps preserve_component_union_impl[OF assms(2)]
           same_component_trans[OF same_component_trans[OF _ this]]
      show ?thesis
        by auto
    next
      case False
      with assms(6,7,8,9) valid_graph.add_edge_was_path[OF assms(3) p(1)]
      have "valid_graph.is_path_undir H x p y"
        unfolding subgraph_def by auto
      with assms(1,5,6,7) xy have "same_component uf x y"
        unfolding valid_union_find_graph_def
        by auto
      with preserve_component_union_impl[OF assms(2)] show ?thesis
        by simp
    qed
  next
    assume asm: "same_component uf' x y"
    show "\<exists>p. valid_graph.is_path_undir (add_edge a w b H) x p y"
      proof (cases "same_component uf x y")
        case True
        with assms(1,5) xy obtain p where "valid_graph.is_path_undir H x p y"
          unfolding valid_union_find_graph_def
          by blast
        with valid_graph.add_edge_is_path[OF assms(3)] show ?thesis
          by auto
      next
        case False
        with asm assms(5) preserve_component_union_impl_rev[OF assms(2)]
        have "same_component uf x a \<and> same_component uf b y \<or>
              same_component uf b x \<and> same_component uf y a"
          by blast
        with assms(1,5,6,7) xy obtain p q
          where "valid_graph.is_path_undir H x p a \<and> valid_graph.is_path_undir H b q y \<or>
                 valid_graph.is_path_undir H b p x \<and> valid_graph.is_path_undir H y q a"
          unfolding valid_union_find_graph_def
          by metis
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
  assumes "\<not> same_component uf a b"
  assumes "valid_union_find_graph uf H"
  assumes "dom uf = V"
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
    have "\<not> same_component uf x y"
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

lemma loop_invar_kruskal_preserve_component:
  assumes "loop_invar_kruskal E' (uf, H)"
  assumes "preserve_component uf uf'"
  assumes "valid_union_find uf'"
  assumes "dom uf = dom uf'"
  shows "loop_invar_kruskal E' (uf', H)"
  using assms
        preserve_previous_edges_connected[OF _ assms(2)]
        preserve_valid_union_find_graph[OF _ assms(2)]
  unfolding loop_invar_kruskal_def
  by auto

lemma loop_invar_init_preserve_component_add:
  assumes "loop_invar_init V' uf"
  assumes "preserve_component uf uf'"
  assumes "valid_union_find uf'"
  assumes "v\<in>V'"
  assumes "dom uf' = insert v (dom uf)"
  assumes "in_component uf' v v"
  shows "loop_invar_init (V'-{v}) uf'"
  using assms preserve_component_impl[OF assms(2)]
  unfolding loop_invar_init_def
  by auto

lemma union_preserves_forest:
  assumes "forest H"
  assumes "\<not> same_component uf a b"
  assumes "subgraph H G"
  assumes "dom uf = V"
  assumes "a \<in> V"
  assumes "b \<in> V"
  assumes "valid_union_find_graph uf H"
  shows "forest (add_edge a w b H)"
  using assms forest_add_edge[of H]
  unfolding valid_union_find_graph_def subgraph_def
  by fast

lemma union_preserves_loop_invar:
  assumes "loop_invar_kruskal E' (uf, H)"
  assumes "preserve_component uf uf'"
  assumes "preserve_component_union uf' uf'' a b"
  assumes "dom uf = dom uf''"
  assumes "dom uf' = dom uf''"
  assumes "valid_union_find uf''"
  assumes "in_component uf' a ca"
  assumes "in_component uf' b cb"
  assumes "ca \<noteq> cb"
  assumes "same_component uf'' a b"
  assumes "E' \<subseteq> E"
  assumes "(a, w, b) \<in> E'"
  assumes "\<forall>e\<in>E' - {(a, w, b)}. edges_less_eq (a, w, b) e"
  shows "loop_invar_kruskal (E' - {(a, w, b)}) (uf'', add_edge a w b H)"
  using assms not_same_component[OF assms(7,8,9)]
        E_validD preserve_valid_union_find_graph[OF _ assms(2)]
        union_preserves_forest
        add_edge_preserve_subgraph
        exists_min_spanning_tree_add[OF _ preserve_previous_edges_connected[OF _ assms(2)]]
        preserve_previous_edges_connected_add[OF _ preserve_component_union_trans]
        preserve_valid_union_find_graph_add[OF _ preserve_component_union_trans
                                            loop_invar_kruskal_valid_graph]
  unfolding loop_invar_kruskal_def
  by auto

lemma same_component_preserves_loop_invar:
  assumes "loop_invar_kruskal E' (uf, H)"
  assumes "preserve_component uf uf'"
  assumes "valid_union_find uf'"
  assumes "dom uf = dom uf'"
  assumes "in_component uf' a c"
  assumes "in_component uf' b c"
  shows "loop_invar_kruskal (E' - {(a, w, b)}) (uf', H)"
  using assms preserve_previous_edges_connected_no_add[OF _ assms(2)]
        preserve_valid_union_find_graph[OF _ assms(2)]
  unfolding loop_invar_kruskal_def same_component_def
  by fast

lemma loop_invar_node_exists:
  assumes "loop_invar_kruskal E' (uf, H)"
  assumes "E' \<subseteq> E"
  assumes "(a, w, b) \<in> E'"
  shows "(\<exists>node_a. uf a = Some node_a)" and "(\<exists>node_b. uf b = Some node_b)"
  using assms E_valid
  unfolding loop_invar_kruskal_def
  by auto blast+

lemma all_connected_edges:
  assumes "valid_graph H"
  assumes "subgraph H G"
  assumes "dom uf = V"
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
  unfolding kruskal1_def add_node_spec_def find_spec_def union_spec_def
  apply(refine_vcg)
  apply (rule finite_V)
  apply (simp add: loop_invar_init_empty)
  apply simp
  apply (simp add: loop_invar_init_not_exist)
  apply (simp add: loop_invar_init_preserve_component_add)
  apply (rule finite_E)
  apply (simp add: loop_invar_kruskal_empty)
  apply (fastforce simp: loop_invar_node_exists)
  apply simp
  apply (fastforce simp: loop_invar_node_exists)
  apply simp
  apply (fast elim: preserve_component_trans)
  apply (fastforce simp: preserve_component_impl)
  apply (fastforce simp: preserve_component_impl)
  apply simp
  apply simp
  apply simp
  apply (meson loop_invar_kruskal_edge_not_in_graph)
  apply (fastforce simp: union_preserves_loop_invar)
  apply (fastforce simp: same_component_preserves_loop_invar)
  apply (simp add: loop_invar_kruskal_final)
  done

section \<open>Kruskal 2\<close>

definition "lst_graph_invar l \<equiv> distinct l"    
definition "lst_graph_rel \<equiv> br (\<lambda>l. \<lparr> 
  nodes = fst`set l \<union> (snd o snd)`set l, 
  edges = set l \<rparr>) lst_graph_invar"

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

  
context   
  fixes l
  assumes l_G_refine: "(l,G) \<in> lst_graph_rel"
begin

definition "V_impl \<equiv> remdups (map fst l @ map (snd o snd) l)"

lemma V_impl_refine:
  shows "(V_impl,V) \<in> \<langle>Id\<rangle>list_set_rel"
  using l_G_refine unfolding lst_graph_rel_def list_set_rel_def lst_graph_invar_def V_impl_def
  by (auto simp: in_br_conv)
  
lemma E_impl_refine:  
  "(l, E) \<in> \<langle>Id\<rangle>list_set_rel"
  using l_G_refine unfolding lst_graph_rel_def list_set_rel_def lst_graph_invar_def
  by (auto simp: in_br_conv intro: distinct_mapI)

corollary E_impl:
  "set l = E"
  using l_G_refine unfolding lst_graph_rel_def lst_graph_invar_def
  by (auto simp: in_br_conv)

definition "init_uf \<equiv> FOREACHi loop_invar_init V
      (\<lambda>v uf. do {
        add_node_spec uf v
      }) empty_union_find"
      
definition "init_uf2 \<equiv> nfoldli V_impl (\<lambda>_. True)
      (\<lambda>v uf. do {
        add_node_spec uf v
      }) empty_union_find"
      
lemma init_uf_refine: "(init_uf2, init_uf) \<in> \<langle>Id\<rangle>nres_rel"
  unfolding init_uf2_def init_uf_def
  apply (refine_vcg LFOi_refine[OF V_impl_refine])
  apply auto
  done


definition "kruskal_loop_tmpl B I \<equiv> FOREACHoi edges_less_eq loop_invar_kruskal E B I"  
definition "kruskal_loop_tmpl2 B I \<equiv> nfoldli (quicksort_by_rel edges_less_eq [] l) (\<lambda>_. True) B I"
  
lemma edges_less_eq_linorder: "is_linorder_rel edges_less_eq" 
  unfolding edges_less_eq_def is_linorder_rel_def
  by (metis linear order_trans)

lemma kruskal_loop_tmpl_refine: "(kruskal_loop_tmpl2,kruskal_loop_tmpl) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding kruskal_loop_tmpl2_def kruskal_loop_tmpl_def FOREACHoi_def
  apply (refine_rcg quicksort_nfoldli_refine_foreachoci)
  apply (vc_solve simp: E_impl_refine edges_less_eq_linorder)
  done

definition kruskal2 :: "('v, 'w) graph nres"
  where "kruskal2 \<equiv> do {
    initial_union_find \<leftarrow> nfoldli V_impl (\<lambda>_. True)
      (\<lambda>v uf. do {
        add_node_spec uf v
      }) empty_union_find;
    (union_find, spanning_tree) \<leftarrow> nfoldli (quicksort_by_rel edges_less_eq [] l) (\<lambda>_. True)
      (\<lambda>(a, w, b) (uf, H). do {
        (uf', root_a) \<leftarrow> find_spec uf a;
        (uf'', root_b) \<leftarrow> find_spec uf' b;
        ASSERT (preserve_component uf uf'' \<and> in_component uf'' a root_a \<and> in_component uf'' b root_b);
        if root_a \<noteq> root_b
        then do {
          uf''' \<leftarrow> union_spec uf'' a b;
          ASSERT ((a, w, b) \<in> set l - edges H);
          RETURN (uf''', add_edge a w b H)
        } else
          RETURN (uf'', H)
      }) (initial_union_find, empty_tree);
    RETURN spanning_tree
  }"

theorem kruskal2_refine: "(kruskal2, kruskal1)\<in>\<langle>Id\<rangle>nres_rel"
  unfolding kruskal2_def kruskal1_def
  apply (fold init_uf2_def init_uf_def)
  apply (fold kruskal_loop_tmpl_def kruskal_loop_tmpl2_def)
  apply (simp only: E_impl)
  apply (refine_vcg init_uf_refine[THEN nres_relD] kruskal_loop_tmpl_refine[param_fo,THEN nres_relD] inj_on_id)
  apply (vc_solve)
  done

section \<open>Kruskal 3\<close>

definition "lst_subgraph_rel \<equiv> br (\<lambda>l. \<lparr> 
  nodes = V,
  edges = set l \<rparr>) lst_graph_invar"

definition "lst_empty_tree \<equiv> []"


definition kruskal3 :: "('v \<times> 'w \<times> 'v) list nres"
  where "kruskal3 \<equiv> do {
    initial_union_find \<leftarrow> nfoldli V_impl (\<lambda>_. True)
      (\<lambda>v uf. do {
        add_node_spec uf v
      }) empty_union_find;
    (union_find, spanning_tree) \<leftarrow> nfoldli (quicksort_by_rel edges_less_eq [] l) (\<lambda>_. True)
      (\<lambda>(a, w, b) (uf, l_H). do {
        (uf', root_a) \<leftarrow> find_spec uf a;
        (uf'', root_b) \<leftarrow> find_spec uf' b;
        ASSERT (preserve_component uf uf'' \<and> in_component uf'' a root_a \<and> in_component uf'' b root_b);
        if root_a \<noteq> root_b
        then do {
          uf''' \<leftarrow> union_spec uf'' a b;
          ASSERT ((a, w, b) \<in> set l - set l_H);
          RETURN (uf''', (a, w, b)#l_H)
        } else
          RETURN (uf'', l_H)
      }) (initial_union_find, lst_empty_tree);
    RETURN spanning_tree
  }"

definition "kruskal_loop_body2 a w b uf H \<equiv> do {
        (uf', root_a) \<leftarrow> find_spec uf a;
        (uf'', root_b) \<leftarrow> find_spec uf' b;
        ASSERT (preserve_component uf uf'' \<and> in_component uf'' a root_a \<and> in_component uf'' b root_b);
        if root_a \<noteq> root_b
        then do {
          uf''' \<leftarrow> union_spec uf'' a b;
          ASSERT ((a, w, b) \<in> set l - edges H);
          RETURN (uf''', add_edge a w b H)
        } else
          RETURN (uf'', H)
      }"

definition "kruskal_loop_body3 a w b uf l_H \<equiv> do {
        (uf', root_a) \<leftarrow> find_spec uf a;
        (uf'', root_b) \<leftarrow> find_spec uf' b;
        ASSERT (preserve_component uf uf'' \<and> in_component uf'' a root_a \<and> in_component uf'' b root_b);
        if root_a \<noteq> root_b
        then do {
          uf''' \<leftarrow> union_spec uf'' a b;
          ASSERT ((a, w, b) \<in> set l - set l_H);
          RETURN (uf''', (a, w, b)#l_H)
        } else
          RETURN (uf'', l_H)
      }"


lemma empty_tree_refine: "(lst_empty_tree, empty_tree) \<in> lst_subgraph_rel"
  unfolding empty_tree_def lst_empty_tree_def lst_subgraph_rel_def lst_graph_invar_def
  by (auto simp: in_br_conv)

lemma add_edge_refine:
  assumes "(l_H, H) \<in> lst_subgraph_rel"
  assumes "(a, w, b) \<in> set l - set l_H"
  shows "((a, w, b) # l_H, add_edge a w b H) \<in> lst_subgraph_rel"
  using assms E_impl_refine
  unfolding add_edge_def lst_subgraph_rel_def lst_graph_invar_def list_set_rel_def
  by (auto simp: in_br_conv E_validD)


lemma kruskal_loop_body_refine: "(kruskal_loop_body3, kruskal_loop_body2)\<in>Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id
    \<rightarrow> lst_subgraph_rel \<rightarrow> \<langle>{((uf, l_H), (uf', H)) | uf uf' l_H H. (uf, uf') \<in> Id \<and> (l_H, H) \<in> lst_subgraph_rel}\<rangle>nres_rel"
  unfolding kruskal_loop_body3_def kruskal_loop_body2_def
  apply (refine_vcg)
  apply refine_dref_type
  apply (vc_solve simp: add_edge_refine)
  unfolding lst_subgraph_rel_def
  apply (simp add: in_br_conv)
  done

theorem kruskal3_refine: "(kruskal3, kruskal2)\<in>\<langle>lst_subgraph_rel\<rangle>nres_rel"
  unfolding kruskal3_def kruskal2_def
  apply (fold kruskal_loop_body3_def kruskal_loop_body2_def)
  apply (refine_vcg kruskal_loop_body_refine[param_fo, THEN nres_relD])
  apply refine_dref_type
  apply (vc_solve simp: empty_tree_refine)
  done

sepref_definition kruskalN_spec is
  "uncurry0 kruskal3" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding kruskal3_def
  oops (* by sepref *)

end

end
end