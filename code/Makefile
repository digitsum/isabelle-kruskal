
all: Kruskal Kruskal_tree

Kruskal: Kruskal.mlb Kruskal.sml Kruskal_cli.sml
	mlton -verbose 1 -default-type intinf -output Kruskal Kruskal.mlb

Kruskal_tree: Kruskal_tree.mlb Kruskal_tree.sml Kruskal_tree_cli.sml
	mlton -verbose 1 -default-type intinf -output Kruskal_tree Kruskal_tree.mlb

