theory Graph_Definition
  imports
    Dijkstra_Shortest_Path.Graph
    Dijkstra_Shortest_Path.Weight
begin

section \<open> Definition \<close>

context valid_graph
begin
  fun is_path_undir :: "'v \<Rightarrow> ('v,'w) path \<Rightarrow> 'v \<Rightarrow> bool" where
    "is_path_undir v [] v' \<longleftrightarrow> v=v' \<and> v'\<in>V" |
    "is_path_undir v ((v1,w,v2)#p) v' \<longleftrightarrow> v=v1 \<and> ((v1,w,v2)\<in>E \<or> (v2,w,v1)\<in>E) \<and> is_path_undir v2 p v'"
end

locale forest = valid_graph G
  for G :: "('v,'w) graph" +
  assumes cycle_free:
    "\<forall>(a,w,b)\<in>E. \<forall>p. \<not> valid_graph.is_path_undir (delete_edge a w b G) a p b"

locale connected_graph = valid_graph G
  for G :: "('v,'w) graph" +
  assumes connected:
    "\<forall>v\<in>V. \<forall>v'\<in>V. \<exists>p. is_path_undir v p v'"

locale tree = forest + connected_graph

locale finite_graph = valid_graph G
  for G :: "('v,'w) graph" +
  assumes finite_E: "finite E"

locale finite_connected_graph = finite_graph + connected_graph

locale weighted_graph = valid_graph G
  for G :: "('v,'w::weight) graph"

locale fcw_graph = weighted_graph + finite_connected_graph

definition subgraph :: "('v, 'w) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "subgraph G H \<equiv> nodes G = nodes H \<and> edges G \<subseteq> edges H"

context valid_graph
begin
  abbreviation is_connected :: "('v \<times> 'w \<times> 'v) \<Rightarrow> bool" where
    "is_connected e \<equiv> (case e of
      (a, w, b) \<Rightarrow> \<exists>p. is_path_undir a p b)"

  definition is_spanning_tree :: "('v, 'w) graph \<Rightarrow> bool" where
    "is_spanning_tree T \<equiv> tree T \<and> subgraph T G"
end

context weighted_graph
begin
  definition edge_weight :: "'w" where
    "edge_weight \<equiv> sum (fst o snd) E"

  definition (in -) edges_less_eq :: "('a \<times> 'w::weight \<times> 'a) \<Rightarrow> ('a \<times> 'w \<times> 'a) \<Rightarrow> bool"
    where "edges_less_eq a b \<equiv> fst(snd a) \<le> fst(snd b)"

  definition is_optimal_tree :: "('v, 'w) graph \<Rightarrow> bool" where
    "is_optimal_tree T \<equiv> (\<forall>T'::('v, 'w) graph.
        is_spanning_tree T' \<longrightarrow>
        weighted_graph.edge_weight T \<le> weighted_graph.edge_weight T')"

  definition is_minimum_spanning_tree :: "('v, 'w) graph \<Rightarrow> bool" where
    "is_minimum_spanning_tree T \<equiv> is_spanning_tree T \<and> is_optimal_tree T"
end

section \<open> Helping lemmas \<close>

lemma nodes_delete_edge[simp]:
  "nodes (delete_edge v e v' G) = nodes G"
  by (simp add: delete_edge_def)

lemma edges_delete_edge[simp]:
  "edges (delete_edge v e v' g) = edges g - {(v,e,v')}"
  by (simp add: delete_edge_def)

lemma valid_subgraph:
  assumes "subgraph H G"
  assumes "valid_graph G"
  shows "valid_graph H"
  using assms unfolding subgraph_def valid_graph_def by blast

context valid_graph
begin
  lemma is_path_undir_simps[simp, intro!]:
    "is_path_undir v [] v \<longleftrightarrow> v\<in>V"
    "is_path_undir v [(v,w,v')] v' \<longleftrightarrow> (v,w,v')\<in>E \<or> (v',w,v)\<in>E"
    by (auto dest: E_validD)

  lemma is_path_undir_memb[simp]:
    "is_path_undir v p v' \<Longrightarrow> v\<in>V \<and> v'\<in>V"
    apply (induct p arbitrary: v)
    apply (auto dest: E_validD)
    done

  lemma is_path_undir_memb_edges:
    assumes "is_path_undir v p v'"
    shows "\<forall>(a,w,b) \<in> set p. (a,w,b) \<in> E \<or> (b,w,a) \<in> E"
    using assms
    by (induct p arbitrary: v) fastforce+

  lemma is_path_undir_split:
    "is_path_undir v (p1@p2) v' \<longleftrightarrow> (\<exists>u. is_path_undir v p1 u \<and> is_path_undir u p2 v')"
    by (induct p1 arbitrary: v) auto

  lemma is_path_undir_split'[simp]:
    "is_path_undir v (p1@(u,w,u')#p2) v'
      \<longleftrightarrow> is_path_undir v p1 u \<and> ((u,w,u')\<in>E \<or> (u',w,u)\<in>E) \<and> is_path_undir u' p2 v'"
    by (auto simp add: is_path_undir_split)

  lemma is_path_undir_sym:
    assumes "is_path_undir v p v'"
    shows "\<exists>p'. is_path_undir v' p' v"
  proof
    from assms show "is_path_undir v' (rev (map (\<lambda>(u, w, u'). (u', w, u)) p)) v"
      by (induct v p v' rule: is_path_undir.induct) (auto simp: E_validD)
  qed

  lemma is_path_undir_subgraph:
    assumes "is_path_undir x p y"
    assumes "subgraph G H"
    assumes "valid_graph H"
    shows "valid_graph.is_path_undir H x p y"
    using assms valid_graph.is_path_undir.simps[of "H"]
    unfolding subgraph_def
    by (induction p arbitrary: x y) auto

  lemma no_path_in_empty_graph:
    assumes "E = {}"
    assumes "p \<noteq> []"
    shows "\<not>is_path_undir v p v"
    using assms by (cases p) auto

  lemma is_path_undir_split_distinct:
    assumes "is_path_undir v p v'"
    assumes "(a, w, b) \<in> set p \<or> (b, w, a) \<in> set p"
    shows "(\<exists>p' p'' u u'.
            is_path_undir v p' u \<and> is_path_undir u' p'' v' \<and>
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
    from 1 p have p': "is_path_undir v p' u" and p'': "is_path_undir u' p'' v'"
      by auto
    from 1 len_p' p' have "(a, w, b) \<in> set p' \<or> (b, w, a) \<in> set p' \<longrightarrow> (\<exists>p'' p''' u' u''.
            is_path_undir v p'' u' \<and> is_path_undir u'' p''' u \<and>
            length p'' < length p' \<and> length p''' < length p' \<and>
            (u' \<in> {a, b} \<and> u'' \<in> {a, b}) \<and>
            (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p'' \<and>
            (a, w, b) \<notin> set p''' \<and> (b, w, a) \<notin> set p''')"
      by simp
    with len_p' p' u have p': "\<exists>p' u. is_path_undir v p' u \<and> length p' < length p \<and>
      u \<in> {a,b} \<and> (a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p'"
      by fastforce
    from 1 len_p'' p'' have "(a, w, b) \<in> set p'' \<or> (b, w, a) \<in> set p'' \<longrightarrow> (\<exists>p' p''' u u''.
            is_path_undir u' p' u \<and> is_path_undir u'' p''' v' \<and>
            length p' < length p'' \<and> length p''' < length p'' \<and>
            (u \<in> {a, b} \<and> u'' \<in> {a, b}) \<and>
            (a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p' \<and>
            (a, w, b) \<notin> set p''' \<and> (b, w, a) \<notin> set p''')"
      by simp
    with len_p'' p'' u have "\<exists>p'' u'. is_path_undir u' p'' v'\<and> length p'' < length p \<and>
      u' \<in> {a,b} \<and> (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p''"
      by fastforce
    with p' show ?case by auto
  qed

  lemma add_edge_is_path:
    assumes "is_path_undir x p y"
    shows "valid_graph.is_path_undir (add_edge a b c G) x p y"
  proof -
    from E_valid have "valid_graph (add_edge a b c G)"
      unfolding valid_graph_def add_edge_def
      by auto
    with assms valid_graph.is_path_undir.simps[of "add_edge a b c G"]
    show "valid_graph.is_path_undir (add_edge a b c G) x p y"
      by (induction p arbitrary: x y) auto
  qed

  lemma add_edge_was_path:
    assumes "valid_graph.is_path_undir (add_edge a b c G) x p y"
    assumes "(a, b, c) \<notin> set p"
    assumes "(c, b, a) \<notin> set p"
    assumes "a \<in> V"
    assumes "c \<in> V"
    shows "is_path_undir x p y"
  proof -
    from E_valid have "valid_graph (add_edge a b c G)"
      unfolding valid_graph_def add_edge_def
      by auto
    with assms valid_graph.is_path_undir.simps[of "add_edge a b c G"]
    show "is_path_undir x p y"
      by (induction p arbitrary: x y) auto
  qed

  lemma delete_edge_is_path:
    assumes "is_path_undir x p y"
    assumes "(a, b, c) \<notin> set p"
    assumes "(c, b, a) \<notin> set p"
    shows "valid_graph.is_path_undir (delete_edge a b c G) x p y"
  proof -
    from E_valid have "valid_graph (delete_edge a b c G)"
      unfolding valid_graph_def delete_edge_def
      by auto
    with assms valid_graph.is_path_undir.simps[of "delete_edge a b c G"]
    show ?thesis
      by (induction p arbitrary: x y) auto
  qed

  lemma delete_edge_was_path:
    assumes "valid_graph.is_path_undir (delete_edge a b c G) x p y"
    shows "is_path_undir x p y"
  proof -
    from E_valid have "valid_graph (delete_edge a b c G)"
      unfolding valid_graph_def delete_edge_def
      by auto
    with assms valid_graph.is_path_undir.simps[OF this]
    show "is_path_undir x p y"
      by (induction p arbitrary: x y) auto
  qed

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

  lemma add_delete_edge:
    assumes "(a, w, c) \<in> E"
    shows "add_edge a w c (delete_edge a w c G) = G"
    using assms E_validD unfolding delete_edge_def add_edge_def
    by (simp add: insert_absorb)

  lemma swap_add_edge_in_path:
    assumes "valid_graph.is_path_undir (add_edge a w b G) v p v'"
    assumes "(a,w',a') \<in> E \<or> (a',w',a) \<in> E"
    shows "\<exists>p. valid_graph.is_path_undir (add_edge a' w'' b G) v p v'"
  using assms(1)
  proof (induction p arbitrary: v)
    case Nil
    with assms(2) E_validD
    have "valid_graph.is_path_undir (add_edge a' w'' b G) v [] v'"
      by (auto simp: valid_graph.is_path_undir.simps(1)[OF add_edge_valid[OF valid_graph.intro[OF E_valid]]])
    then show ?case
      by auto
  next
    case (Cons e p')
    then obtain v2 x e_w where "e = (v2, e_w, x)"
      using prod_cases3 by blast
    with valid_graph.is_path_undir.simps(2)[OF add_edge_valid[OF valid_graph.intro[OF E_valid]]] Cons(2)
    have e: "e = (v, e_w, x)" and
         edge_e: "(v, e_w, x) \<in> edges (add_edge a w b G) \<or> (x, e_w, v) \<in> edges (add_edge a w b G)" and
         p': "valid_graph.is_path_undir (add_edge a w b G) x p' v'"
      by auto
    have "\<exists>p. valid_graph.is_path_undir (add_edge a' w'' b G) v p x"
    proof (cases "e = (a, w, b) \<or> e = (b, w, a)")
      case True
      from True e assms(2) E_validD have "valid_graph.is_path_undir (add_edge a' w'' b G) v [(a,w',a'), (a',w'',b)] x
          \<or> valid_graph.is_path_undir (add_edge a' w'' b G) v [(b,w'',a'), (a',w',a)] x"
        by (auto simp: valid_graph.is_path_undir.simps[OF add_edge_valid[OF valid_graph.intro[OF E_valid]]])
      then show ?thesis
        by auto
    next
      case False
      with edge_e e
      have "valid_graph.is_path_undir (add_edge a' w'' b G) v [e] x"
        by (auto simp: valid_graph.is_path_undir_simps(2)[OF add_edge_valid[OF valid_graph.intro[OF E_valid]]])
      then show ?thesis
        by auto
    qed
    with p' Cons.IH valid_graph.is_path_undir_split[OF add_edge_valid[OF valid_graph.intro[OF E_valid]]]
    show ?case
      by blast
  qed

end

context forest
begin
  lemma delete_edge_from_path:
    assumes "is_path_undir a p b"
    assumes "subgraph H G"
    assumes "\<nexists>p. valid_graph.is_path_undir H a p b"
    shows "\<exists>(x, w, y) \<in> E - edges H.  (\<forall>p. \<not>valid_graph.is_path_undir (delete_edge x w y G) a p b) \<and>
      (\<exists>p. valid_graph.is_path_undir (add_edge a w' b (delete_edge x w y G)) x p y)"
  using assms(1,3)
  proof (induction n == "length p" arbitrary: p a rule: nat_less_induct)
    case 1
    from E_valid have valid_G: "valid_graph G"
      unfolding valid_graph_def
      by simp
    with valid_subgraph[OF assms(2)] have valid_H: "valid_graph H" .
    show ?case
    proof (cases p)
      case Nil
      with 1(2) have "a = b"
        by simp
      with `a = b` 1(2) assms(2) have "valid_graph.is_path_undir H a [] b"
        unfolding subgraph_def
        by (auto simp: valid_graph.is_path_undir.simps[OF valid_H])
      with 1(3) show ?thesis
        by simp
    next
      case (Cons e p')
      from 1 obtain a2 a' w where "e = (a2, w, a')"
        using prod_cases3 by blast
      with 1(2) Cons have e: "e = (a, w, a')"
        by simp
      with 1(2) Cons obtain e1 e2 where e12: "e = (e1, w, e2) \<or> e = (e2, w, e1)" and
        edge_e12: "(e1, w, e2) \<in> E"
        by auto
      from 1(2) Cons e have "is_path_undir a' p' b"
        by simp
      with is_path_undir_split_distinct[OF this, of a w a'] Cons
      obtain p'_dst u' where  p'_dst: "is_path_undir u' p'_dst b \<and> u' \<in> {a, a'}" and
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
        with p'_dst have path_p': "is_path_undir a' p'_dst b"
          by auto
        show ?thesis
        proof (cases "(e1, w, e2) \<in> edges H")
          case True
          have "\<nexists>p. valid_graph.is_path_undir H a' p b"
          proof
            assume "\<exists>p. valid_graph.is_path_undir H a' p b"
            then obtain p_H where "valid_graph.is_path_undir H a' p_H b"
              by auto
            with True e12 e have "valid_graph.is_path_undir H a (e#p_H) b"
              by (auto simp: valid_graph.is_path_undir.simps[OF valid_H])
            with 1(3) show False
              by simp
          qed
          with path_p' 1(1) len_p' obtain x z y where xy: "(x, z, y) \<in> E - edges H" and
            IH1: "(\<forall>p. \<not>valid_graph.is_path_undir (delete_edge x z y G) a' p b)" and
            IH2: "(\<exists>p. valid_graph.is_path_undir (add_edge a' w' b (delete_edge x z y G)) x p y)"
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
          have thm1: "\<forall>p. \<not>valid_graph.is_path_undir (delete_edge x z y G) a p b"
          proof (rule ccontr)
            assume "\<not> (\<forall>p. \<not>valid_graph.is_path_undir (delete_edge x z y G) a p b)"
            then obtain p_e where "valid_graph.is_path_undir (delete_edge x z y G) a p_e b"
              by auto
            with True edge_e12 e12 e xy_neq_aa' have "valid_graph.is_path_undir (delete_edge x z y G) a' ((a', w, a)#p_e) b"
              by (auto simp: valid_graph.is_path_undir.simps[OF delete_edge_valid[OF valid_G]])
            with IH1 show False
              by simp
          qed
          from IH2 obtain p_ad where "valid_graph.is_path_undir (add_edge a' w' b (delete_edge x z y G)) x p_ad y"
            by auto
          with valid_graph.swap_add_edge_in_path[OF delete_edge_valid[OF valid_G] this, of w a] edge_e12
            e12 e edges_delete_edge[of x z y G] xy_neq_aa'
          have thm2: "\<exists>p. valid_graph.is_path_undir (add_edge a w' b (delete_edge x z y G)) x p y"
            by blast
          with thm1 show ?thesis
            using xy by auto
        next
          case False
          have thm1: "\<forall>p. \<not>valid_graph.is_path_undir (delete_edge e1 w e2 G) a p b"
          proof (rule ccontr)
            assume "\<not> (\<forall>p. \<not>valid_graph.is_path_undir (delete_edge e1 w e2 G) a p b)"
            then obtain p_e where p_e: "valid_graph.is_path_undir (delete_edge e1 w e2 G) a p_e b"
              by auto
            from delete_edge_is_path[OF path_p', of e1 w e2] e_not_in_p' e12 e
            obtain p_d where "valid_graph.is_path_undir (delete_edge e1 w e2 G) a' p_d b"
              by auto
            with valid_graph.is_path_undir_sym[OF delete_edge_valid[OF valid_G] this]
            obtain p_rev where "valid_graph.is_path_undir (delete_edge e1 w e2 G) b p_rev a'"
              by auto
            with p_e valid_graph.is_path_undir_split[OF delete_edge_valid[OF valid_G]]
            have "valid_graph.is_path_undir (delete_edge e1 w e2 G) a (p_e@p_rev) a'"
              by auto
            with cycle_free edge_e12 e12 e valid_graph.is_path_undir_sym[OF delete_edge_valid[OF valid_G] this]
            show False
              unfolding valid_graph_def
              by auto
          qed
          from valid_graph.is_path_undir_split[OF add_edge_valid[OF delete_edge_valid[OF valid_G]]]
            valid_graph.add_edge_is_path[OF delete_edge_valid[OF valid_G]
                                            delete_edge_is_path[OF path_p', of e1 w e2], of a w' b]
            valid_graph.is_path_undir_simps(2)[OF add_edge_valid[OF delete_edge_valid[OF valid_G]],
                                               of a w' b e1 w e2 b w' a]
            e_not_in_p' e12 e
          have "valid_graph.is_path_undir (add_edge a w' b (delete_edge e1 w e2 G)) a' (p'_dst@[(b,w',a)]) a"
            by auto
          with valid_graph.is_path_undir_sym[OF add_edge_valid[OF delete_edge_valid[OF valid_G]] this]
            e12 e
          have "\<exists>p. valid_graph.is_path_undir (add_edge a w' b (delete_edge e1 w e2 G)) e1 p e2"
            by auto
          with thm1 show ?thesis
            using False edge_e12 by auto
        qed
      qed
    qed
  qed
end

context connected_graph
begin
  lemma induce_connected:
    assumes "valid_graph H"
    assumes "subgraph H G"
    assumes "\<forall>e\<in>E. valid_graph.is_connected H e"
    shows "connected_graph H"
  proof -
    have "\<exists>p. valid_graph.is_path_undir H v p v'"
      if v: "v\<in>nodes H" and v': "v'\<in>nodes H" for v v'
    proof -
      from v v' assms have "v\<in>V" and "v'\<in>V"
        unfolding subgraph_def by auto
      with connected obtain p where "is_path_undir v p v'"
        by blast
      with v show ?thesis
      proof (induction p arbitrary: v v')
        case Nil
        with assms valid_graph.is_path_undir_simps[of H] show ?case
          by auto
      next
        case (Cons e p)
        then show ?case
        proof (cases e)
          case (fields a w b)
          with assms Cons valid_graph.is_path_undir_sym[of H b _ a]
          obtain p' where p': "valid_graph.is_path_undir H a p' b"
            by fastforce
          from assms fields Cons.prems Cons.IH[of b v']
          obtain p'' where "valid_graph.is_path_undir H b p'' v'"
            unfolding subgraph_def by auto
          with Cons.prems fields assms p' valid_graph.is_path_undir_split[of H]
            have "valid_graph.is_path_undir H v (p'@p'') v'"
              by auto
          then show ?thesis ..
        qed
      qed
    qed
    with assms show ?thesis
      unfolding connected_graph_def connected_graph_axioms_def
      by auto
  qed

  lemma add_edge_connected:
    assumes "a \<in> V"
    assumes "b \<in> V"
    shows "connected_graph (add_edge a w b G)"
  proof -
    from E_valid have valid: "valid_graph (add_edge a w b G)"
      unfolding valid_graph_def add_edge_def by auto
    have "\<exists>p. valid_graph.is_path_undir (add_edge a w b G) v p v'"
      if vv': "v \<in> V" "v' \<in> V" for v v'
    proof -
      from connected vv' obtain p where "is_path_undir v p v'"
        by auto
      with add_edge_is_path[OF this] show ?thesis
        by auto
    qed
    with valid assms show ?thesis
      unfolding connected_graph_def connected_graph_axioms_def
      by auto
  qed

  lemma delete_edge_connected:
    assumes "valid_graph.is_path_undir (delete_edge a w b G) a pab b"
    shows "connected_graph (delete_edge a w b G)"
  proof -
    from E_valid have valid: "valid_graph (delete_edge a w b G)"
      unfolding valid_graph_def add_edge_def by auto
    have "\<exists>p. valid_graph.is_path_undir (delete_edge a w b G) v p v'"
      if vv': "v \<in> V" "v' \<in> V" for v v'
    proof -
      from connected vv' obtain p where p: "is_path_undir v p v'"
        by auto
      show ?thesis
      proof (cases "(a, w, b) \<notin> set p \<and> (b, w, a) \<notin> set p")
        case True
        with delete_edge_is_path[OF p] show ?thesis
          by auto
      next
        case False
        with p is_path_undir_split_distinct[OF p, of a w b] obtain p' p'' u u'
          where "is_path_undir v p' u \<and> is_path_undir u' p'' v'" and
            u: "(u \<in> {a, b} \<and> u' \<in> {a, b})" and
            "(a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p' \<and>
            (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p''"
          by auto
        with delete_edge_is_path obtain p' p''
          where p': "valid_graph.is_path_undir (delete_edge a w b G) v p' u \<and>
                 valid_graph.is_path_undir (delete_edge a w b G) u' p'' v'"
          by blast
        from valid_graph.is_path_undir_sym[OF valid assms] obtain pab'
          where "valid_graph.is_path_undir (delete_edge a w b G) b pab' a"
          by auto
        with assms u p' valid_graph.is_path_undir_split[OF valid, of v p' p'' v']
          valid_graph.is_path_undir_split[OF valid, of v p' pab b]
          valid_graph.is_path_undir_split[OF valid, of v "p'@pab" p'' v']
          valid_graph.is_path_undir_split[OF valid, of v p' pab' a]
          valid_graph.is_path_undir_split[OF valid, of v "p'@pab'" p'' v']
        show ?thesis by auto
      qed
    qed
    with valid assms show ?thesis
      unfolding connected_graph_def connected_graph_axioms_def
      by auto
  qed

end

context finite_connected_graph
begin
  lemma finite_V: "finite V"
  proof (cases "\<forall>v\<in>V. \<exists>v'. v' \<in> V-{v}")
    case False
    then have "\<exists>v. V = {v}"
      by blast
    then show ?thesis
      by auto
  next
    case True
    have "\<exists>w v'. (v, w, v') \<in> E \<or> (v', w, v) \<in> E" if v: "v\<in>V" for v
    proof -
      from True v obtain v' where v': "v'\<in>V-{v}"
        by blast
      with connected v obtain p where p: "is_path_undir v p v'"
        by blast
      with v' have "p \<noteq> []"
        by auto
      with list.exhaust obtain e p' where p': "p = e#p'"
        by blast
      from prod_cases3 obtain x w y where "e = (x, w, y)"
        by blast
      with p p' show ?thesis
        by auto
    qed
    then have "V \<subseteq> fst`E \<union> snd`snd`E"
      by force
    also from finite_E have "finite (fst`E \<union> snd`snd`E)"
      by simp
    ultimately show ?thesis
      by (auto simp: finite_subset)
  qed
end

lemma add_edge_is_connected:
  assumes "valid_graph H"
  shows "\<exists>p p'. valid_graph.is_path_undir (add_edge a b c H) a p c \<and>
                valid_graph.is_path_undir (add_edge a b c H) c p' a"
  using assms valid_graph.is_path_undir_simps(2)[of "add_edge a b c H"]
  by auto

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

lemma swap_edges:
  assumes "valid_graph H"
  assumes "valid_graph.is_path_undir (add_edge a w b H) v p v'"
  assumes "a \<in> nodes H"
  assumes "b \<in> nodes H"
  shows "\<exists>p'. valid_graph.is_path_undir (add_edge v w' v' H) a p' b \<or> valid_graph.is_path_undir H v p' v'"
proof (cases "(a, w, b) \<in> set p \<or> (b, w, a) \<in> set p")
  case True
  from valid_graph.is_path_undir_split_distinct[OF _ assms(2) True] assms(1)
  obtain p' p'' u u' where
       "valid_graph.is_path_undir (add_edge a w b H) v p' u \<and>
        valid_graph.is_path_undir (add_edge a w b H) u' p'' v'" and
        u: "u \<in> {a, b} \<and> u' \<in> {a, b}" and
        "(a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p' \<and>
        (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p'' "
    by auto
  with assms valid_graph.add_edge_was_path[OF assms(1)]
  have paths: "valid_graph.is_path_undir H v p' u \<and>
               valid_graph.is_path_undir H u' p'' v'"
    by auto
  show ?thesis
  proof (cases "u = u'")
    case True
    with paths valid_graph.is_path_undir_split[OF assms(1), of v p' p'' v']
    show ?thesis
      by auto
  next
    case False
    from paths assms valid_graph.add_edge_is_path[OF assms(1)]
    obtain p' p'' where
      paths': "valid_graph.is_path_undir (add_edge v w' v' H) v p' u \<and>
              valid_graph.is_path_undir (add_edge v w' v' H) u' p'' v'"
      by blast
    from add_edge_is_connected[OF assms(1)] obtain p''' where
      "valid_graph.is_path_undir (add_edge v w' v' H) v' p''' v"
      by blast
    with assms(1) paths' valid_graph.is_path_undir_split[of "add_edge v w' v' H" u' p'' p''' v]
    have "valid_graph.is_path_undir (add_edge v w' v' H) u' (p''@p''') v"
        by auto
    with assms(1) paths' valid_graph.is_path_undir_split[of "add_edge v w' v' H" u' "p''@p'''" p' u]
    have "valid_graph.is_path_undir (add_edge v w' v' H) u' (p''@p'''@p') u"
        by auto
    with u False assms(1) valid_graph.is_path_undir_sym[OF _ this]
    show ?thesis
      by auto
  qed
next
  case False
  with valid_graph.add_edge_was_path[OF assms(1,2)] assms(3,4)
  show ?thesis by auto
qed

lemma forest_add_edge:
  assumes "forest H"
  assumes "a \<in> nodes H"
  assumes "c \<in> nodes H"
  assumes "\<forall>p. \<not> valid_graph.is_path_undir H a p c"
  shows "forest (add_edge a w c H)"
proof -
  from assms(4) have "\<not> valid_graph.is_path_undir H a [(a, w, c)] c"
    by simp
  with assms(1) have awc: "(a, w, c) \<notin> edges H \<and> (c, w, a) \<notin> edges H"
    unfolding forest_def
    by (auto simp: valid_graph.is_path_undir_simps(2)[of H])
  have "\<not> valid_graph.is_path_undir (delete_edge v w' v' (add_edge a w c H)) v p v'"
     if e: "(v,w',v')\<in> edges (add_edge a w c H)" for p v w' v'
  proof (cases "(v,w',v') = (a, w, c)")
    case True
    with assms awc delete_add_edge[of a H c w]
    show ?thesis by simp
  next
    case False
    with e have e': "(v,w',v')\<in> edges H"
      by auto
    show ?thesis
    proof
      assume asm: "valid_graph.is_path_undir (delete_edge v w' v' (add_edge a w c H)) v p v'"
      with swap_delete_add_edge[OF False, of H] swap_edges[of "delete_edge v w' v' H" a w c v p v' w']
           valid_graph.add_delete_edge[OF _ e'] assms(1,2,3) e'
      have "\<exists>p'. valid_graph.is_path_undir H a p' c"
        unfolding forest_def forest_axioms_def by auto
      with assms show False
        by simp
    qed
  qed
  with assms(1) show ?thesis
    unfolding forest_def forest_axioms_def by auto
qed


lemma forest_delete_edge:
  assumes "forest H"
  shows "forest (delete_edge a w c H)"
proof -
  have "\<not> valid_graph.is_path_undir (delete_edge v w' v' (delete_edge a w c H)) v p v'"
     if e: "(v,w',v')\<in> edges (delete_edge a w c H)" for p v w' v'
  proof
    assume asm: "valid_graph.is_path_undir (delete_edge v w' v' (delete_edge a w c H)) v p v'"
    with swap_delete_edges[of v w' v' a w c H]
    have "valid_graph.is_path_undir (delete_edge a w c (delete_edge v w' v' H)) v p v'"
      by simp
    from forest.axioms(1)[OF assms] valid_graph.delete_edge_was_path[OF _ this]
    have "valid_graph.is_path_undir (delete_edge v w' v' H) v p v'"
      by simp
    moreover from forest.cycle_free[OF assms] e
      have "\<not> valid_graph.is_path_undir (delete_edge v w' v' H) v p v'"
        unfolding delete_edge_def by auto
    ultimately show False
      by simp
  qed
  with assms(1) show ?thesis
    unfolding forest_def forest_axioms_def by auto
qed

context finite_graph
begin
  lemma spanning_forest_exists: "\<exists>F. forest F \<and> subgraph F G \<and>
      (\<forall>(a,w,b)\<in>edges G. \<exists>p. valid_graph.is_path_undir F a p b)"
    using finite_E E_valid
  proof (induction n == "card (edges G)" arbitrary: G)
    case  (0 G)
    then have empty: "edges G = {}"
      by simp
    with "0.prems"(2,3) show ?case
      unfolding forest_def forest_axioms_def subgraph_def valid_graph_def
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
        "(\<forall>(a,w,b)\<in>edges (delete_edge a w b G). \<exists>p. valid_graph.is_path_undir F a p b)"
      using Suc.hyps(1)
      unfolding valid_graph_def
      by blast
    then have subgraph_F: "subgraph F G"
      unfolding subgraph_def delete_edge_def
      by auto
    show ?case
    proof (cases "\<exists>p. valid_graph.is_path_undir F a p b")
      case True
      from F True have "(\<forall>(a,w,b)\<in>edges G. \<exists>p. valid_graph.is_path_undir F a p b)"
        unfolding delete_edge_def by fastforce
      with F subgraph_F show ?thesis
        by auto
    next
      case False
      from subgraph_F e Suc.prems
      have ab: "a \<in> nodes F" "b \<in> nodes F"
        unfolding subgraph_def
        by force+
      with False F forest_add_edge[of F a b w] have "forest (add_edge a w b F)"
        by auto
      moreover from F e Suc.prems
      have "subgraph (add_edge a w b F) G"
        unfolding subgraph_def add_edge_def delete_edge_def
        by force
      moreover have "\<exists>p. valid_graph.is_path_undir (add_edge a w b F) c p d"
        if asm: "(c,w',d)\<in>edges G" for c w' d
      proof (cases "(c, w', d) = (a, w, b)")
        case True
        with valid_graph.is_path_undir_simps(2)[of "add_edge a w b F" a w b]
          forest.axioms(1)[OF F(1)]
        show ?thesis by auto
      next
        case False
        with F(3) asm obtain p where "valid_graph.is_path_undir F c p d"
          unfolding delete_edge_def by fastforce
        then have "valid_graph.is_path_undir (add_edge a w b F) c p d"
          by (induction c p d rule: valid_graph.is_path_undir.induct[OF forest.axioms(1)[OF F(1)]])
             (auto simp: valid_graph.is_path_undir.simps[OF forest.axioms(1)[OF F(1)]]
                         valid_graph.is_path_undir.simps[OF add_edge_valid[OF forest.axioms(1)[OF F(1)]], of a w b])
        then show ?thesis by auto
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

end

context finite_connected_graph
begin
  lemma spanning_tree_exists: "\<exists>T. is_spanning_tree T"
  proof -
    from spanning_forest_exists
    obtain F where F: "forest F" "subgraph F G"
      "(\<forall>(a, w, b)\<in>edges G. \<exists>p. valid_graph.is_path_undir F a p b)"
      unfolding finite_graph_def finite_graph_axioms_def valid_graph_def
      by blast
    from F(2,3) forest.axioms(1)[OF F(1)] induce_connected[of F]
    have "connected_graph F"
      by simp
    with F(1,2) show ?thesis
      unfolding is_spanning_tree_def tree_def
      by auto
  qed
end

context fcw_graph
begin
  lemma minimum_spanning_tree_exists: "\<exists>T. is_minimum_spanning_tree T"
  proof -
    let ?weights = "{weighted_graph.edge_weight T |T. is_spanning_tree T}"
    from spanning_tree_exists obtain T where "is_spanning_tree T"
      by auto
    then have non_empty: "weighted_graph.edge_weight T \<in> ?weights"
      by auto
    from finite_subgraphs have finite: "finite ?weights"
      unfolding is_spanning_tree_def
      by auto
    with non_empty have "\<forall>w \<in> ?weights. Min ?weights \<le> w"
      by simp
    moreover from finite non_empty have "Min ?weights \<in> ?weights"
      using Min_in by blast
    ultimately obtain T' where "(\<forall>w \<in> ?weights. weighted_graph.edge_weight T' \<le> w) \<and> is_spanning_tree T'"
      by auto
    then show ?thesis
      unfolding is_minimum_spanning_tree_def is_optimal_tree_def
      by blast
  qed
end

lemma sub_tree_eq:
  assumes "tree H"
  assumes "tree T"
  assumes "subgraph H T"
  shows "H = T"
proof -
  from forest.axioms(1)[OF tree.axioms(1)[OF assms(1)]]
  have valid_H: "valid_graph H" .
  from forest.axioms(1)[OF tree.axioms(1)[OF assms(2)]]
  have valid_T: "valid_graph T" .
  have "edges T \<subseteq> edges H"
  proof
    fix x
    assume asm: "x \<in> edges T"
    show "x \<in> edges H"
    proof (rule ccontr)
      assume asm': "x \<notin> edges H"
      from prod_cases3 obtain a w b where x: "x = (a, w, b)" .
      with asm asm' assms(3) have subgraph': "subgraph H (delete_edge a w b T)"
        unfolding subgraph_def delete_edge_def
        by auto
      from valid_T have valid_delete_T: "valid_graph (delete_edge a w b T)"
        by simp
      from asm x forest.cycle_free[OF tree.axioms(1)[OF assms(2)]]
      have contr: "\<forall>p. \<not> valid_graph.is_path_undir (delete_edge a w b T) a p b"
        by auto
      from assms(3) asm x valid_graph.E_validD[OF forest.axioms(1)[OF tree.axioms(1)[OF assms(2)]]]
      have "a \<in> nodes H" "b \<in> nodes H"
        unfolding subgraph_def
        by auto
      with connected_graph.connected[OF tree.axioms(2)[OF assms(1)]]
      obtain p where p:"valid_graph.is_path_undir H a p b"
        by auto
      from valid_graph.is_path_undir_subgraph[OF valid_H p subgraph' valid_delete_T]
      have "valid_graph.is_path_undir (delete_edge a w b T) a p b"
        by simp
      with contr show False
        by simp
    qed
  qed
  with assms show ?thesis
    unfolding subgraph_def by simp
qed

end