#!/usr/bin/python3

# Research code for exploring apt repositories of packages, and in particular
# for constructing a conflict graph as described in
#
# S. R. Tate and B. Yuan. Minimum Size Build Environment Sets and Graph
# Coloring. In Proceedings of the 17th International Conference on Software
# Technologies (ICSOFT), July 2022.
#
# Code written by Stephen R. Tate and Bo Yuan.
# Copyright (C) Stephen R. Tate, 2022
#
# Distributed under GPL v3 licence. See the LICENSE file in this distribution
# or at https://github.com/srtate/BuildEnvAnalysis for more information.

import apt_pkg

class _State:
    pass

_state = _State()

def init():
    if not hasattr(_state, 'init_done'):
        apt_pkg.init()
        _state.cache = apt_pkg.Cache(None)
        _state.depcache = apt_pkg.DepCache(_state.cache)
        _state.records = apt_pkg.PackageRecords(_state.cache)
        _state.srcrec = apt_pkg.SourceRecords()
        _state.binusedby = dict()
        _state.binrejectby = dict()
        _state.sdco = dict()  # for dep,con,opt triples
        _state.bdco = dict()
        _state.blist = []
        _state.bclosure = dict()
        _state.sclosure = dict()
        _state.sbuildenv = dict()
        _state.btos = dict()
        _state.ess_dco = None
        _state.bess_dco = None
        _state.pref_arch = apt_pkg.get_architectures()[0]
        
        _init_bdco()
        _init_bclosure()
        _init_sdco()
        _init_sclosure()
        
        _state.init_done = True

##############################################################################
# The fundamental data type in our analysis is a "DCO" - a 3-tuple that
# consists of a set of depenencies (the "D"), a set of conflicts (the "C"),
# and a list of option lists (the "O" - an option list is a dependency that
# can be satisfied in multiple ways, with options given in order of preference.
# In general our analysis keeps DCOs as DCOs throughout the analysis, and only
# revolves the options (picks which dependency to use) as a very last step.
# The functions below are the main functions to manipulate DCOs, and are
# only used internally.

def _simplify_dco(triple):
    """ Remove impossible options, and if unique way to satisfy an option
    just make it a dependency.
    """
    (deps, cons, opts) = triple
    # remove any directly conflicting opts
    opts = [ [ x for x in olist if not x in cons ] for olist in opts ]
    # remove all unsatisfiable opts - again, shouldn't happen
    opts = [ x for x in opts if len(x) > 0 ]
    # if only one satisfying option left in opt, move it to deps
    deps.update([ x[0] for x in opts if len(x) == 1 ])
    # remove the opts already satisfied
    opts = [ x for x in opts if len(deps.intersection(x))==0]
    return (deps, cons, opts)
  
def _dco_update(dest, src):
    """ Merge the src dco into the destination - merges dependencies and
    conflicts, and adds any new opt lists (ignores duplicates). Does not
    simply the dco, so may result in unnecessary opt lists - if you're doing
    a bunch of merges it's better to do all the updates first, and then call
    _simplify_dco() at the end.
    """
    (dd, dc, do) = dest
    (sd, sc, so) = src
    dd.update(sd)
    dc.update(sc)
    optstrs = set()
    for dopt in do:
        work = list(dopt)
        work.sort()
        wstr = ','.join(work)
        optstrs.add(wstr)
    for nopt in so:
        work = list(nopt)
        work.sort()
        wstr = ','.join(work)
        if not wstr in optstrs:
            optstrs.add(wstr)
            do.append(nopt)

def _resolve_opt(dco):
    """ Given a DCO, resolve all opt lists by picking one and making it a
    direct dependency, and then merging in all of its DCOs (in the bclosure).
    This is a recursive exploration of all possible ways of satisfying each
    opt list, which stops at the first one found. Theoretically this could
    be exponential time, but in practice the first opt in each opt list is
    generally the one to use, and this is very fast in that situation.
    """
    new_dco = ( set(), set(), [] )
    _dco_update(new_dco, dco)
    if len(dco[2]) == 0: return new_dco
    thisorlist = new_dco[2].pop(0)
    for usep in thisorlist:
        tmp_dco = ( set(), set(), [] )
        _dco_update(tmp_dco, new_dco)
        tmp_dco[0].add(usep)
        bclosure = _bpkg_getclosure(usep)
        tmp_dco[0].update(bclosure[0])  # new deps
        tmp_dco[1].update(bclosure[1])  # new conflicts
        tmp_dco[2].extend(bclosure[2])  # new opts
        tmp_dco = _simplify_dco(tmp_dco)
        if not tmp_dco[0].isdisjoint(tmp_dco[1]): return None
        if len(tmp_dco[2]) == 0:
            return tmp_dco
        else:
            tmp_dco = _resolve_opt(tmp_dco)
            if tmp_dco != None: return tmp_dco
    return None

##############################################################################

def _collect_tags(deplist, taglist):
    """Concatenates lists with given tags from given dependency list"""
    res = []
    for t in taglist:
        res += deplist.get(t, [])
    return res

            
##############################################################################

def _bpkg_conflicts_helper(bpkg):
    """Gets actual conflicts for binary package."""
    names = set()
    cand = _state.depcache.get_candidate_ver(bpkg)
    if cand == None: return names
    worry = _collect_tags(cand.depends_list, ['Conflicts','Breaks'])
    if len([ x for x in worry if len(x)>1 ]) > 0:
        print("***** disjunction in conflicts/breaks list -- shouldn't happen")
    for p in [ w[0] for w in worry ]:
        if p.parent_pkg.architecture == _state.pref_arch and p.target_pkg.architecture == _state.pref_arch:
            t = p.all_targets()
            for targ in t:
                if targ.parent_pkg.architecture == _state.pref_arch:
                    tname = targ.parent_pkg.get_fullname()
                    cc = _state.depcache.get_candidate_ver(_state.cache[tname])
                    if cc == targ:
                        names.add(tname)
    return names
    
##############################################################################

# Functions to initial binary package DCO (direct and closure) information

def _init_bdco():
    """Go through all packages, finding all conflicts, storing for later.
    Conflicts are considered (and stored) symmetrically (A conflicts with
    B means that B conflicts with A). Only works with target architecture
    packages, but those are the important ones (no true ":any" in
    Ubuntu 18.04).
    """
    # Pass 1 - initialize direct binary conflicts (bcons[]) - make symmetric
    bcons = dict()
    for p in _state.cache.packages:
        if p.architecture == _state.pref_arch:
            pname = p.get_fullname()
            if not pname in bcons: bcons[pname] = set()
            for c in _bpkg_conflicts_helper(p):
                bcons[pname].add(c)
                if not c in bcons: bcons[c] = set()
                bcons[c].add(pname)

    # Pass 2 - gather dependencies and create (dependencies, conflicts, opts) triples
    for p in _state.cache.packages:
        if p.architecture == _state.pref_arch:
            pname = p.get_fullname()
            v = _state.depcache.get_candidate_ver(p)
            if v == None:
                (deps, opts) = ( set(), set() )
            else:
                dl = _collect_tags(v.depends_list_str,['Depends','PreDepends'])
                (deps,opts) = _deplist_direct_deps(dl)
            _state.bdco[pname] = _simplify_dco( (deps, bcons[pname], opts) )

    _state.blist = [ pname for pname in _state.bdco.keys() ]
                
##############################################################################

# To get a transitive closure of the dependency graph (binary package deps)
# we first compute the strongly connected components of the direct dependencies.
# Every package in any SCC must be installed any time any of them are, so we
# compute a single shared DCO for every package in that SCC. The closure is
# then done on a graph of SCCs, which is acyclic making that analysis a little
# easier. The DFS code here is an implementation of the linear time algorithm
# in Section 22.5 of the Cormen, Leiserson, Rivest, and Stein algorithms
# textbook (3rd edition), which they credit to Rao Kosaraju.

# After running _init_scc, the _state is updated with two entries:

#   _state.bscc gives the SCCs in a list, where each list item is a set of
#               vertices in that SCC using vertex numbers (positions in the
#               _state.blist list of binary package names).

#   _state.binscc is a mapping from binary package names to SCC numbers

# Note that SCCs are almost all single-vertices in practice. For
# example, in Ubuntu 20.04, there are 87,857 vertices (binary package)
# and 87,358 of these are single-vertex SCCs. The largest SCC has 13 vertices.

class _DFS_State:
    pass

_dfs_s = _DFS_State()

def _dfs1(vnum):
    global _dfs_s
    _dfs_s.dfsfinish[vnum] = -1
    # make adjacency list of direct dependencies, using vertex numbers
    adjlist = [ _dfs_s.name_to_num[n] for n in _state.bdco[_state.blist[vnum]][0] ]
    for w in adjlist:
        _dfs_s.revadj[w].append(vnum) # reverse direction edge
        if _dfs_s.dfsfinish[w] == -2:
            _dfs1(w)
    _dfs_s.dfsfinish[vnum] = _dfs_s.dfscounter
    _dfs_s.order[_dfs_s.dfscounter] = vnum
    _dfs_s.dfscounter = _dfs_s.dfscounter+1
    
    
def _drive_dfs1():
    global _dfs_s
    n = len(_state.blist)
    _dfs_s.dfsfinish = [ -2 for i in range(n) ]
    _dfs_s.order = [ -2 for i in range(n) ]
    _dfs_s.revadj = [ list() for i in range(n) ]
    _dfs_s.dfscounter = 0
    for i in range(n):
        if _dfs_s.dfsfinish[i] == -2:
            _dfs1(i)

    # order revadj lists by decreasing finish time
    for alist in _dfs_s.revadj:
        alist.sort(key=lambda x: _dfs_s.dfsfinish[x], reverse=True)
    _dfs_s.order.reverse()

def _dfs2(vnum,scc):
    global _dfs_s
    scc.add(vnum)
    _dfs_s.dfsfinish[vnum] = -1
    for w in _dfs_s.revadj[vnum]:
        if _dfs_s.dfsfinish[w] == -2:
            _dfs2(w,scc)
    _dfs_s.dfsfinish[vnum] = 0
    
def _drive_dfs2():
    global _dfs_s
    allscc = []
    n = len(_state.blist)
    _dfs_s.dfsfinish = [ -2 for i in range(n) ]
    for i in range(n):
        if _dfs_s.dfsfinish[_dfs_s.order[i]] == -2:
            thisscc = set()
            _dfs2(_dfs_s.order[i],thisscc)
            allscc.append(thisscc)
    return allscc

def _init_scc():
    global _dfs_s
    _dfs_s.name_to_num = dict()
    for pos,pn in enumerate(_state.blist):
        _dfs_s.name_to_num[pn] = pos

    _drive_dfs1()
    _state.bscc = _drive_dfs2()
    for snum,scc in enumerate(_state.bscc):
        for pnum in scc:
            _state.binscc[_state.blist[pnum]] = snum
                                                                   
##############################################################################

def _bpkg_getclosure(bpkg):
    """Gets transitive closure of dependencies for bpkg. Returns result as
    a dco, so or-lists are not resolved."""
    # No cycles in SCC graph, but can have SCCs with in-degree > 1, so cache!
    if bpkg in _state.bclosure: return _state.bclosure[bpkg]
    myscc = _state.binscc[bpkg]
    scc_dco = ( set(), set(), [] )
    if _state.ess_dco != None:
        _dco_update(scc_dco, _state.ess_dco)
    for pnum in _state.bscc[myscc]:
        pkg_dco = _state.bdco[_state.blist[pnum]]
        _dco_update(scc_dco, pkg_dco)
    toexplore = set([_state.binscc[x] for x in scc_dco[0]])
    if myscc in toexplore: toexplore.remove(myscc)
    plist = [ _state.blist[next(iter(_state.bscc[x]))] for x in toexplore]
    for bpkg in plist:
        trans_dco = _bpkg_getclosure(bpkg)
        _dco_update(scc_dco, trans_dco)
    scc_dco = _simplify_dco(scc_dco)
    for pnum in _state.bscc[myscc]:
        _state.bclosure[_state.blist[pnum]] = scc_dco
    return scc_dco

def _get_essential_direct():
    """Gets set of essential packages (Priority 1, appropriate arch), but
    does not do a closure -- used internally (public methods always do
    closure before returning).
    """
    ess = set()
    archok = [ _state.pref_arch, 'all' ]
    for p in _state.cache.packages:
        cv = _state.depcache.get_candidate_ver(p)
        if cv != None and cv.priority == 1 and cv.arch in archok:
            ess.add(cv.parent_pkg.get_fullname())
    return ess
    
##############################################################################

def _init_bclosure():
    """Initializes transitive closure of all binary packages, which are stored
    in the _state.bclosure dict. These are dcos, so or-lists are not resolved.
    Closure includes all binary packages in "essentials", so this is in fact
    a full installable environment."""
    _state.bscc = []
    _state.binscc = dict()
    _init_scc()
 
    # Start with essential (binary) packages (plus apt)
    _state.ess_dco = None   # so closure doesn't try to add them...
    ess = _get_essential_direct()
    ess.add('apt:amd64')
    cons = set()
    # Really shouldn't be any conflicts in "essentials", but check anyway
    for bp in ess:
        cons.update(_state.bdco[bp][1])
    dco = ( set(ess), cons, [] )
    dco = _simplify_dco(dco)
    for bp in ess:
        _dco_update(dco, _bpkg_getclosure(bp))
    dco = _simplify_dco(dco)
    dco = _resolve_opt(dco)
    _state.ess_dco = dco

    # All of the "essentials" share the same closure dco
    for bp in dco[0]:
        _state.bclosure[bp] = dco

    # Run through all packages now to pre-buid the bclosure[] values
    for pname in _state.blist:
        _bpkg_getclosure(pname)

##############################################################################

# Functions to initialize source package DCO (direct and closure) information

def _get_sdco(allbd):
    """ Get direct dependency and conflict information (a dco) for a source
    package build_depends entry.  Used to initialize sdco dict."""
    cons = set()
    bc = _collect_tags(allbd,['Build-Conflicts','Build-Conflicts-Arch','Build-Conflicts-Indep'])
    for d in [ x[0] for x in bc ]:
        if not d[0] in _state.cache:
            continue
        cand = _state.depcache.get_candidate_ver(_state.cache[d[0]])
        if cand != None and apt_pkg.check_dep(cand.ver_str, d[2], d[1]):
            cons.add(cand.parent_pkg.get_fullname())

    # Find all direct dependencies
    dep1 = _collect_tags(allbd,['Build-Depends', 'Build-Depends-Arch', 'Build-Depends-Indep'])
    alldeps = [ _dep_get_plist_for_orlist(dis) for dis in dep1 ]
    if alldeps == None: return (set(), cons, [])
    # if it contains None, that means a dependency couldn't be met
    # this is really a problem, but it shouldn't happen - we'll just remove it
    alldeps = [ x for x in alldeps if x != None ]
    alldeps = [ x for x in alldeps if len(x) != 0 ]
    deps = set([ x[0] for x in alldeps if len(x) == 1 ])
    opts = [ x for x in alldeps if len(x) > 1 ]
    (deps, cons, opts) = _simplify_dco( (deps, cons, opts) )
    return (deps, cons, opts)

##############################################################################
# Note that this requires version 0.9.3.7 or newer of python-apt -- in
# particular, the version packaged with Ubuntu 14.04 will not work. I tested
# a "work around" using the older library interface, but it was too slow (58
# seconds vs 2.5 seconds with a newer version of python-apt) and ended up
# creating other problems. If you want to analyze Ubuntu 14.04, the best
# way to do that is to copy the apt cache files over to a newer version to
# analyze with the newer python-apt library (I used a Docker container for
# this to keep everything isolated from the main system).

def _init_sdco():
    """ Initializes an sdco entry for each source package that is used to
    build some binary in this distribution."""
    _state.srcrec.restart()
    while _state.srcrec.step():
        sname = _state.srcrec.package
        used = False
        # Some binaries are not kept in binary repos (e.g., 'anna' for installer)
        for bpkg in _state.srcrec.binaries:
            if bpkg in _state.cache:
                p = _state.cache[bpkg]
                cv = _state.depcache.get_candidate_ver(p)
                # Not all potential binaries have a candidate version
                # (e.g., 'libc6-sparc' on an amd64 system)
                if cv != None:
                    # Some spkgs have only binaries listed that are build by
                    # different spkgs - this is probably an error? For example,
                    # 'astroid2-for-python' spkg builds python3-astroid, but
                    # python3-astroid lists 'astroid' as source.
                    _state.records.lookup(cv.file_list[0])
                    sn = p.name
                    if _state.records.source_pkg != "":
                        sn = _state.records.source_pkg
                    if sn == sname:
                        _state.btos[p.get_fullname()] = sname
                        used = True
        if used:
            if sname not in _state.sdco:
                _state.sdco[sname] = _get_sdco(_state.srcrec.build_depends)

def _init_bess():
    """ Initializes _state.bess_dco to a DCO describing all essential and
    build-essential packages. Since these packages must be installed in any
    build environment, we will include all of them in each sclosure.
    """
    bess_dco = ( {'build-essential:amd64'}, set(), [] )
    _dco_update(bess_dco, _state.ess_dco)
    _dco_update(bess_dco, _bpkg_getclosure('build-essential:amd64'))
    bess_dco = _simplify_dco(bess_dco)
    bess_dco = _resolve_opt(bess_dco)
    _state.bess_dco = bess_dco
    
def _spkg_getclosure(spkg):
    """ Get transitive closure of dependencies for a source package. Returns
    result as a dco, so or-lists are not resolved yet. """
    if _state.bess_dco == None: _init_bess()
    if spkg in _state.sclosure: return _state.sclosure[spkg]
    my_dco = ( set(), set(), [] )
    _dco_update(my_dco, _state.bess_dco)
    _dco_update(my_dco, _state.sdco[spkg])
    my_dco = _simplify_dco(my_dco)
    basebpkg = list(my_dco[0])
    for bpkg in basebpkg:
        _dco_update(my_dco, _bpkg_getclosure(bpkg))
    my_dco = _simplify_dco(my_dco)
    _state.sclosure[spkg] = my_dco
    return my_dco

def _init_sclosure():
    """ Initialized closure of every source package, caching results in
    _state.sclosure. Also initializes _state.sbuildenv for final build env.
    These entries are saved as dco's to preserve conflicts, but each or-list
    is empty -- the or-lists are already resolved. _state.sbuildenv is also
    simplified, so it only includes binary dependencies and conflicts if they
    are relevant to the conflict graph construction. For example, if a conflict
    technically exists with a binary package, but that binary package is not
    in any other build environment (e.g., make-guile), it is removed."""
    for sname in _state.sdco.keys():
        this_dco = _spkg_getclosure(sname)
        if len(this_dco[2]) > 0:
            this_dco = _resolve_opt(this_dco)
        if this_dco == None or not this_dco[0].isdisjoint(this_dco[1]):
            print("ERROR - package db inconsistency - impossible to build", sname)
            continue
        _state.sbuildenv[sname] = this_dco
        for bp in _state.sbuildenv[sname][0]:
            if not bp in _state.binusedby: _state.binusedby[bp] = set()
            _state.binusedby[bp].add(sname)
        # Make sure every mentioned bpkg has an entry in binusedby...
        for bp in _state.sbuildenv[sname][1]:
            if not bp in _state.binusedby: _state.binusedby[bp] = set()
        for bp in _state.sdco[sname][1]:
            if not bp in _state.binrejectby: _state.binrejectby[bp] = set()
            _state.binrejectby[bp].add(sname)

    # Simplify buildenv's -- remove all dependencies and conflicts that are
    # not relevant to creating the conflict graph. This simplifies things a
    # lot, helping to speed up graph construction.
    for sname,sdco in _state.sbuildenv.items():
        usedcons = set([ x for x in sdco[1] if (len(_state.binusedby[x])>0) ])
        newdep = set([ bp for bp in sdco[0] if not _state.bdco[bp][1].isdisjoint(usedcons)])
        newdep.update([ bp for bp in sdco[0] if bp in _state.binrejectby ])
        _state.sbuildenv[sname] = (newdep, usedcons, sdco[2])


def make_graph():
    """ Create the full conflict graph. Returns a pair, with the first item
    being a list of source package names for each vertex, and the second being
    a list of adjacency lists defining the graph. Adjacency lists use vertex
    numbers (positions in the source package/vertex list), not names."""
    tmp = list(_state.sbuildenv.items())
    sn_to_int = dict()
    vnames = [ tt[0] for tt in tmp ]
    adjnames = [ 0 for i in range(len(tmp)) ]
    for i in range(len(tmp)):
        sn_to_int[tmp[i][0]] = i
        thisadj = set()
        for c in tmp[i][1][1]:
            thisadj.update(_state.binusedby[c])
        for p in tmp[i][1][0]:
            if p in _state.binrejectby:
                thisadj.update(_state.binrejectby[p])
        adjnames[i] = thisadj
    adjnums = [ [ sn_to_int[sn] for sn in anames ] for anames in adjnames ]
    return (vnames, adjnums)

def save_graph(vnames, adj):
    """ Given a graph in the format described in make_graph, this saves the
    graph in two files: one giving the name-to-vertex-number mapping, and one
    file that defines the graph in DIMACS file format, using just vertex
    numbers. """
    fo = open('gr_full_ntov.lst', 'w')
    for vnum,vname in enumerate(vnames):
        print(vname, vnum+1, file=fo)
    fo.close()
    fo = open('gr_full_graph.txt', 'w')
    nedges = sum([len(x) for x in adj])//2
    print('p edge', len(vnames), nedges, file=fo)
    for vnum,adjlist in enumerate(adj):
        for wnum in adjlist:
            if wnum > vnum:
                print('e', vnum+1, wnum+1, file=fo)
    fo.close()
    
##############################################################################

def _vers_sort(vlist):
    """Take a list of Version objects and sort from most desirable to least.

    Pakages must be for this architecture and must be downloadable, and then
    they are sorted from highest priority to lowest. This is a stable sort,
    so the original vlist order is used in case of ties. What is returned is
    a list of fullnames of packages with no duplicates.
    """
    at = [ x for x in vlist if x.arch == 'all' or x.arch == _state.pref_arch ]
    at = [ x for x in at if x.downloadable ]
    if len(at) == 0: return at
    at.sort(key = lambda x: x.priority)
    out = []
    for p in at:
        nm = p.parent_pkg.get_fullname()
        if not nm in out: out.append(nm)
    return out

##############################################################################

def _dep_tuple_to_plist(tuple):
    """ For a single dependency triple (pkg, vers, compare), get a sorted
    list of packages whose current (candidate) version satisfies the
    dependency. If version requirements are given, only an actual package
    can satisfy the dependency. Otherwise, any package that provides a
    virtual package can also satisfy the dependency.
    """
    if not tuple[0] in _state.cache: return None
    vlist = []
    p = _state.cache[tuple[0]]
    if p.has_versions:
        for x in p.version_list:
            if apt_pkg.check_dep(x.ver_str, tuple[2], tuple[1]):
                vlist.append(x)
    if p.has_provides:
        for x in p.provides_list:
            if x[1] == None or tuple[2] != '' or apt_pkg.check_dep(x[1], tuple[2], tuple[1]):
                vlist.append(x[2])
    return _vers_sort(vlist)

##############################################################################

def _dep_get_plist_for_orlist(dep_disj):
    """Get sorted package list for an or-list of dependency tuples."""
    deps = [ _dep_tuple_to_plist(x) for x in dep_disj ]
    deps = [ x for x in deps if x != None ]
    if deps == None or len(deps) == 0: return None
    flat = [ x for y in deps for x in y ]
    if len(flat) == 0: return None
    if len(flat) == 1: return flat
    sorted = _vers_sort([ _state.depcache.get_candidate_ver(_state.cache[x]) for x in flat ])
    return sorted

##############################################################################

def _deplist_direct_deps(deplist):
    """Get a full set of preferred package dependencies for a dependency
    list (list of or-lists). Note that we adjust preferences so that any
    package selected to satisfy an earlier dependency will be a preference
    for any later dependency. This may actually never make a difference,
    but it seems like a good idea...
    """
    all = [ _dep_get_plist_for_orlist(dis) for dis in deplist ]
    if all == None: return None
    # if it contains None, that means a dependency couldn't be met - just remove
    all = [ x for x in all if x != None ]
    using = set([ x[0] for x in all if len(x) == 1 ])
    opts = [ x for x in all if len(x) > 1 and len(using.intersection(x))==0]
    return (using, opts)

##############################################################################

def get_bpkg_conflicts(bpkg):
    """Get set of direct conflicts for binary package bpkg.

    A conflict is only included if it is between packages of the target
    architecture, so for example conflicts between amd64 and i386 versions
    of a package will not be included. Note that in a standard amd64
    install of Ubuntu 18.04, all conflicts are i386 and amd64 and there
    are no disjunctions.
    """
    init()  # Make sure state has been initialized
    if type(bpkg) != type(""):
        bpkg = bpkg.get_fullname()
    if bpkg not in _state.bdco: return set()
    return _state.bdco[bpkg][1]

##############################################################################

def get_bpkg_all_used():
    """Get all binary packages that are used in some build environment."""
    init()
    return _state.binusedby.keys()

##############################################################################

def get_bpkg_usedby(bpkg):
    """Return set of all source packages that use bpkg in build env."""
    init()
    if bpkg not in _state.binusedby: return None
    return _state.binusedby[bpkg]

##############################################################################

def get_spkg_conflicts(sname):
    """Get all conflicts listed in source package record."""
    init()
    return _state.sdco[sname][1]
    
##############################################################################

def get_bpkg_deps_all(pname):
    """ Get all binary package dependencies (all=with transitive closure) for
    named binary package. Resolves all opt lists, so just a dependency set.
    """
    init() #  Make sure state is initialized
    if not pname in _state.bclosure: return None
    dco = _resolve_opt(_state.bclosure[pname])
    return dco[0]

##############################################################################

def get_bpkg_deps_direct(pname):
    """Get all direct dependencies for binary package pname"""
    init() #  Make sure state is initialized
    if not pname in _state.bdco: return None
    ret = set(_state.bdco[pname][0])
    # If no or-lists, just return dep set
    if len(_state.bdco[pname][2]) == 0:
        return ret
    # Otherwise we need to figure out which option we pick in the closure
    adco = get_bpkg_deps_all(pname)
    for orlist in _state.bdco[pname][2]:
        for p in orlist:
            if p in adco:
                ret.add(p)
                break
    return ret

##############################################################################

def get_spkg_deps_all(sname):
    """ Get all build dependencies (all=with transitive closure) for named
    source package. Resolves all opt lists first, so just a dependency set.
    """
    init() #  Make sure state is initialized
    if not sname in _state.sclosure: return None
    dco = _resolve_opt(_state.sclosure[sname])
    return dco[0]

##############################################################################

def get_spkg_deps_direct(sname):
    """Get all direct dependencies for source package sname"""
    init() #  Make sure state is initialized
    if not sname in _state.sdco: return None
    ret = set(_state.sdco[sname][0])
    # If no or-lists, just return dep set
    if len(_state.sdco[sname][2]) == 0:
        return ret
    # Otherwise we need to figure out which option we pick in the closure
    adco = get_spkg_deps_all(sname)
    for orlist in _state.sdco[sname][2]:
        for p in orlist:
            if p in adco:
                ret.add(p)
                break
    return ret

##############################################################################
# Get all binary package requirements/dependencies of a named source package,
# listing only those that have a conflict with some other binary package
# (conflict-free packages are removed) that is used by another source package

def get_spkg_deps_wcon(sname):
    allp = get_spkg_deps_all(sname)
    rset = set()
    if allp != None:
        for p in allp:
            if p in _state.bclosure[p][1]:
                if len([ r for r in _state.bclosure[p][1] if r in _state.binusedby ]) > 0:
                    rset.add(p)
    return rset

def _set_to_str(s):
    ls = list(s)
    ls.sort()
    return ','.join(ls)

##############################################################################
# Turn dependency sets into canonical strings, so duplicates can be detected.
# All we want here are dependency sets - spkgs aren't important for the graph
# analysis (would need them to construct build environments though!)

def get_all_spkg_deps_uniq():
    rlist = []
    sset = dict()
    spkgmap = dict()
    for s,dco in _state.sbuildenv.items():
        ds = dco[0]
        if len(ds) == 0:
            spkgmap[s] = -1
        else:
            str = _set_to_str(ds)
            if str in sset:
                spkgmap[s] = sset[str]
            else:
                sset[str] = len(rlist)
                spkgmap[s] = len(rlist)
                rlist.append(ds)
    return ( rlist , spkgmap )

def make_sgraph(sdcos):
    iusedby = dict()
    for i,dco in enumerate(sdcos):
        for b in dco[0]:
            if not b in iusedby: iusedby[b] = set()
            iusedby[b].add(i)
    alladj = [ set() for x in sdcos ]
    for i,dco in enumerate(sdcos):
        for bp in dco[1]:
            cons = iusedby[bp]
            alladj[i].update(cons)
            for x in cons:
                alladj[x].add(i)
    for i in range(len(alladj)):
        alladj[i] = list(alladj[i])
        alladj[i].sort()
    return alladj

def save_sgraph(vmap, adj):
    nlist = list(vmap.keys())
    nlist.sort()
    fo = open('gr_simp_ntov.lst', 'w')
    for vname in nlist:
        print(vname, vmap[vname]+1, file=fo)
    fo.close()
    fo = open('gr_simp_graph.txt', 'w')
    nedges = sum([len(x) for x in adj])//2
    print('p edge', len(adj), nedges, file=fo)
    for vnum,adjlist in enumerate(adj):
        for wnum in adjlist:
            if wnum > vnum:
                print('e', vnum+1, wnum+1, file=fo)
    fo.close()
    
def get_uniq_dcos():
    (rlist, smap) = get_all_spkg_deps_uniq()
    xx = [ ( dset, set(), [] ) for dset in rlist ]
    for k,v in smap.items():
        if v >= 0:
            xx[v][1].update(_state.sbuildenv[k][1])
    return ( xx, smap )

def get_scon_list(mycons, allbdeps):
    return [ i for i in range(len(allbdeps)) if not mycons.isdisjoint(allbdeps[i]) ]

def get_scon_graph(allbdeps, allbcons):
    return [ get_scon_list(allbcons[i], allbdeps) for i in range(len(allbcons)) ]

def merge_iso_once(gr,sp):
    newvert = dict()
    vmap = dict()
    ngr = []
    for (i,v) in enumerate(gr):
        neighbors = ",".join([str(a) for a in v])
        if not neighbors in newvert:
            newvert[neighbors] = len(ngr)
            ngr.append(v)
        vmap[i] = newvert[neighbors]
    for (i,adjlist) in enumerate(ngr):
        n = list(set([vmap[v] for v in adjlist]))
        n.sort()
        ngr[i] = n
    nsp = dict()
    for (pname,vnum) in sp.items():
        if vnum >= 0:
            nsp[pname] = vmap[vnum]
        else:
            nsp[pname] = vnum
    return (ngr, nsp)

def merge_iso(gr,sp):
    (ngr,nsp) = merge_iso_once(gr,sp)
    while len(ngr) < len(gr):
        (gr,sp) = (ngr,nsp)
        (ngr,nsp) = merge_iso_once(gr,sp)
    return(ngr,nsp)

def get_stats():
    ogr = make_graph()
    ( sdcos, smap ) = get_uniq_dcos()
    sgr = make_sgraph(sdcos)
    (mgr,dummy) = merge_iso(sgr, smap)
    print("Original graph:", len(ogr[0]), "vertices", sum([len(x) for x in ogr[1]]), "edges")
    print("Unique graph:", len(sdcos), "vertices", sum([len(x) for x in sgr]), "edges")
    print("Minimized graph:", len(mgr), "vertices", sum([len(x) for x in mgr]), "edges")

##############################################################################

def bpkg_to_spkg(bname):
    """Get name of source package for the named binary package.

    Note that if you want to look up binary packages that are not built for
    the native architecture (e.g., packages built only for i386 on an amd64
    system) then you need to make sure this is a full name, incluing
    architecture.
    """
    init()
    rval = _state.btos[bname] if bname in _state.btos else None
    if rval == None:  # Try again...  might be non-full name
        if bname in _state.cache:
            bpkg = _state.cache[bname]
            bname = bpkg.get_fullname()
            rval = _state.btos[bname] if bname in _state.btos else None
            if rval == None:    # One last try, if foreign arch
                cand = _state.depcache.get_candidate_ver(bpkg)
                if cand != None:
                    _state.records.lookup(cand.file_list[0])
                    src = _state.records.source_pkg
                    if src == None or src == '':
                        rval = bpkg.name
                    else:
                        rval = src

    return rval
    
##############################################################################

def get_all_spkgs():
    """Returns an iterable (dict_keys) of all source package names."""
    init()
    return _state.sdco.keys()

##############################################################################

def get_essential():
    """Returns a set of essential packages (Priority 1, appropriate arch),
    plus the "apt" package and others it depends on.
    """
    init()
    dco = _state.ess_dco
    return _resolve_opt(dco)[0]

##############################################################################

def get_buildessential():
    """Returns a set of "build essential" packages -- basically all the
    essential packages (see get_essential()) plus the build-essential
    pseudo-package.
    """
    init()
    dco = _state.bess_dco
    return _resolve_opt(dco)[0]

