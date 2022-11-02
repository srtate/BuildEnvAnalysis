# Conflict Graph Generation Code (and Data)

Research code for analyzing debian package dependencies and conflicts,
for computing minimum build environments. This is research-quality
code, and is not necessarily developed the point of being robust and
easy to use. Nonetheless, it should work pretty much out of the box
for generating full and simplified conflict graphs for Debian-based
Linux distributions, as described in the paper:

S. R. Tate and B. Yuan.  Minimum Size Build Environment Sets and Graph
Coloring. In *Proceedings of the 17th International Conference on
Software Technologies (ICSOFT)*, July 2022.

The script used to generate the graphs and data reported in that paper
can be found in `src/PackageQuery` where the `get_graphs.sh` shell
script runs the appropriate Python code.

The exact graphs generated on our systems, for Ubuntu LTS releases
from 14.04 through 20.04, as well as the "TopX" graphs (see the
paper), are in the `graphs` directory.

