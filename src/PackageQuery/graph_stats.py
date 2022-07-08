#!/usr/bin/python3

# Print binary packages that are used in some build environment, but don't
# have any conflicts. These are packages that can all be installed in a
# base build environment, without fear of creating conflicts.

import builddep as bd

bd.init()
ogr = bd.make_graph()
( sdcos, smap ) = bd.get_uniq_dcos()
sgr = bd.make_sgraph(sdcos)
(mgr,dummy) = bd.merge_iso(sgr, dict())
print("Original graph:", len(ogr[0]), "vertices", sum([len(x) for x in ogr[1]]), "edges")
print("Unique graph:", len(sdcos), "vertices", sum([len(x) for x in sgr]), "edges")
print("Minimized graph:", len(mgr), "vertices", sum([len(x) for x in mgr]), "edges")
