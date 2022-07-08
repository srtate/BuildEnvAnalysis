#!/usr/bin/python3

# This is for repeatability - since dependency resolution can depend on
# the order of a set's enumeration, which is randomized in Python >3.6,
# we set a fixed random seed to make this deterministic. This really isn't
# necessary for correctness, but we need it so that the results in the
# paper are reproducible.

# Saves the full graph in gr_nametovnum.lst and gr_graph.txt
# Graph is in DIMACS ASCII graph format

import builddep as bd

bd.init()
(vlist, adj) = bd.make_graph()
bd.save_graph(vlist, adj)

( sdcos, smap ) = bd.get_uniq_dcos()
sgr = bd.make_sgraph(sdcos)
(mgr,mmap) = bd.merge_iso(sgr, smap)

bd.save_sgraph(mmap, mgr)
