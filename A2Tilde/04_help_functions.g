LoadPackage("Grape");

#this function checks if a given grape-graph is a nice bipartite graph
#a bipartite graph is nice if each of its bicomponents is an integer interval
CheckNiceBipartiteGraph := function(grapegraph)
    local bi, nice;
    if not IsBipartite(grapegraph) then
        nice := false;
    else
        bi := Bicomponents(grapegraph);
        if Flat(bi) = [1..OrderGraph(grapegraph)] then
            nice := true;
        else
            nice := false;
        fi;
    fi;
    return nice;
end;

SingleAction := function(geo, tau)
    local geocopy, newgeo, n, lines;
    n := geo[1];
    lines := StructuralCopy(geo[2]);
    newgeo := [geo[1], List([1..Size(lines)], i -> lines[i^(tau^(-1))])];
    return newgeo;
end;

#This function takes geoemtry and returns the corresponding grape graph
#if the geometry contains n points and m lines, then the first n vertices
#in the corresponding grape graph will correspond to the points and the latter
#m vertices will correspond to the lines (respecting the order of course)
GrapeGraphGeo := function(geo)
    local vertices, rel, trivialaction, points, lines;
    points := [1..geo[1]];
    lines := geo[2];
    vertices := Concatenation(points, lines);
    rel := function(i,j)
        local incident, x, y;
        x := vertices[i];
        y := vertices[j];
        if (x in points and y in points) or (x in lines and y in lines) then
            incident := false;
        elif x in lines then
            incident := y in x;
        elif y in lines then
            incident := x in y;
        else
            Print("Something weird happened. \n \n");
            return fail;
        fi;
        return incident;
    end;
    trivialaction := function(x,g)
        return x;
    end;
    return Graph(Group(()), [1..Size(vertices)], trivialaction, rel, true);
end;

#this function takes a grape-graph checks if it is nice
#if it is nice then it returns a geometry with points being the vertex set of first type
#and lines corresponding to the second type of vertices
GeoGrapeGraph := function(grapegraph)
    local nice, bi, lines, n;
    nice := CheckNiceBipartiteGraph(grapegraph);
    if not nice then
        Print("The bipartite grape graph is not nice.\n\n");
        return fail;
    else
        bi := Bicomponents(grapegraph);
        n := Size(bi[1]);
        lines := List(bi[2], l->Filtered([1..n], p->IsEdge(grapegraph, [l, p])));
        return [n, lines];
    fi;
end;

GroupGeo := function(geo)
    local n, gamma, a;
    n := geo[1];
    gamma := GrapeGraphGeo(geo);
    a := AutomorphismGroup(gamma);
    a := Stabilizer(a, [1..n], OnSets);
    a := Group(List(SmallGeneratingSet(a), g->RestrictedPerm(g, [1..n])));
    return a;
end;

##########################################

#this is not a GAP-action
TripleAction := function(radu_datum, tau)
    local geo1, geo2, geo3;
    geo1 := SingleAction(radu_datum[1], tau[1]);
    geo2 := SingleAction(radu_datum[2], tau[2]);
    geo3 := SingleAction(radu_datum[3], tau[3]);
    return [geo1, geo2, geo3];
end;

Mod3 := function(k)
    local rest;
    rest := k mod 3;
    if not rest = 0 then
        return rest;
    else
        return 3;
    fi;
end;

#edges are of the form [i,j,k] where k denotes the geometry the edge lies in
TrianglesEdge_RaduDatum := function(radu_datum, e)
    local followups, f, triangles, t, k;
    k := e[3];
    triangles := [];
    #we compute triangles by going backwards
    followups := radu_datum[Mod3(k-1)][2][e[1]];
    for f in followups do
        if e[2] in radu_datum[Mod3(k-2)][2][f] then
            t := [e, [f,e[1],Mod3(k-1)], [e[2],f,Mod3(k-2)] ];
            SortBy(t, e->e[3]);
            Add(triangles, t);
        fi;
    od;
    return triangles;
end;

IsEmptyRaduDatum := function(radu_datum)
    return ForAll(radu_datum, geo->ForAll(geo[2],l->l =[]));
end;

EdgesOfRaduDatum := function(radu_datum)
    local edges, i, j, k;
    edges := [];
    for k in [1..3] do
        for i in [1..Size(radu_datum[k][2])] do
            for j in radu_datum[k][2][i] do
                Add(edges, [j,i,k]);
            od;
        od;
    od;
    return edges;
end;

TrianglesOfRaduDatum := function(radu_datum)
    local triangles, edges, e;
    triangles := [];
    edges := EdgesOfRaduDatum(radu_datum);
    for e in edges do
        Append(triangles,TrianglesEdge_RaduDatum(radu_datum, e));
    od;
    triangles := DuplicateFreeList(triangles);
    Sort(triangles);
    return triangles;
end;

TriangleGraphOfRaduDatum := function(radu_datum)
    local triangles, gamma, edgestg, k;
    triangles := TrianglesOfRaduDatum(radu_datum);
    k := Size(triangles);
    edgestg := Filtered(Combinations([1..k],2), x->Intersection(triangles[x[1]],triangles[x[2]]) = []);
    Append(edgestg, List(edgestg, x->[x[2],x[1]]));
    gamma := EdgeOrbitsGraph(Group(()), edgestg, k);
    return [gamma, triangles];
end;

ScoreOfRaduDatum := function(radu_datum)
    local data, gamma, edges, i, clique;
    edges := EdgesOfRaduDatum(radu_datum);
    data := TriangleGraphOfRaduDatum(radu_datum);
    gamma := data[1];
    i := Size(edges)/3;
    clique := CompleteSubgraphsOfGivenSize(gamma, i, 0, false, false);
    while clique = [] do
        i := i-1;
        clique := CompleteSubgraphsOfGivenSize(gamma, i, 0, false, false);
    od;
    return i*3;
end;

#takes RaduGraph
#removes all edges that are contained in zero triangles
#and all edges, that are contained in a triangle, that contains an edge, that
#is contained in just that triangle
#the triangles which are removed are returned
#interpret the results as follows:
#if delta is empty after PruneRaduDatum then Radu's algorithm suceeded
#in this case the number of edges in the returned triangles is the score
#if delta is not empty, then one should apply PruneRaduDatum again,
#if nothing changes then there are edges contained in more than one triangle
#and Radu's algorithm fails
#this function changes delta
PruneRaduDatum := function(delta)
    local i, j, k, deletedtriangles, triangles, t, e, n, x, y;
    deletedtriangles := [];
    y := Random(SymmetricGroup(3));
    for k in [1..3] do
        n := Size(delta[k^y][2]);
        x := Random(SymmetricGroup(n));
        for i in [1..n] do
            for j in delta[k^y][2][i^x] do
                triangles := TrianglesEdge_RaduDatum(delta, [j, i^x ,k^y]);
                if Size(triangles) = 1 then
                    t := triangles[1];
                    for e in t do
                        RemoveSet(delta[e[3]][2][e[2]], e[1]);
                    od;
                    Add(deletedtriangles, t);
                elif Size(triangles) = 0 then
                    RemoveSet(delta[k^y][2][i^x], j);
                fi;
            od;
        od;
    od;
    return deletedtriangles;
end;

#destructive
#prunes delta until pruning does not change anything anymore
#returns the triangles and a boolean that indicates if there was something left
RaduTrianglesRaduDatum := function(delta)
    local triangles, copydelta, moretriangles, empty;
    triangles := [];
    repeat
        #this copy is just to check if the pruning still changes radu_datum
        copydelta := StructuralCopy(delta);
        moretriangles := PruneRaduDatum(delta);
        Append(triangles, moretriangles);
        empty := IsEmptyRaduDatum(delta);
    until empty or (copydelta = delta);
    return [triangles, empty];
end;

RaduScoreRaduDatum_Destructive := function(delta)
    local triangles;
    triangles := RaduTrianglesRaduDatum(delta);
    if triangles[2] = true then
        return Size(triangles[1])*3;
    else
        Print("Calculating this score is more expensive...\n");
        return Size(triangles[1])*3 + ScoreOfRaduDatum(delta);
    fi;
end;

#this function is not destructive
RaduScoreRaduDatum := function(delta)
    local copydelta;
    copydelta := StructuralCopy(delta);
    return RaduScoreRaduDatum_Destructive(copydelta);
end;

PerfectScoreRaduDatum := function(radu_datum)
    return Size(EdgesOfRaduDatum(radu_datum));
end;

#takes a Radu datum and returns all triangle covers
#if the input is not perfect, it returns the empty list
TriangleCoversRaduDatum := function(radu_datum)
    local data, gamma, edges, perfecttrianglescore, covers, cliques, triangles;
    edges := EdgesOfRaduDatum(radu_datum);
    data := TriangleGraphOfRaduDatum(radu_datum);
    gamma := data[1];
    triangles := data[2];
    perfecttrianglescore := PerfectScoreRaduDatum(radu_datum)/3;
    cliques := CompleteSubgraphsOfGivenSize(gamma, perfecttrianglescore, 2, false, false);
    if cliques = [] then
        covers := fail;
    else
        covers := List(cliques, c->List(c, i->triangles[i]));
    fi;
    Perform(covers, Sort);
    return covers;
end;

RaduDatumsWithCoversPerfectRaduDatum := function(radudatum)
    local covers, datumswithcover, copy, almost_cover, cover;
    #check if we can use cheap approach
    copy := StructuralCopy(radudatum);
    almost_cover := RaduTrianglesRaduDatum(copy);
    if almost_cover[2] = true then
        cover := almost_cover[1];
        Sort(cover);
        return[[radudatum, cover]];
    else
        covers := TriangleCoversRaduDatum(radudatum);
        if covers = [] then
            return fail;
        else
            datumswithcover := List(covers, cover -> [StructuralCopy(radudatum), StructuralCopy(cover)]);
            return datumswithcover;
        fi;
    fi;
end;

##########################################

#return a graph a partition into 3 sets of the vertices
#assume the radu datum is perfect
#then the vertices in the graph will correspond to edges in a potential delta complex
#and the partition corresponds to the colouring of the edges
#adjacencent vertices correspond to edges sharing a triangle
RaduGraphClasses := function(radu_datum)
local vertices, edges, geo1, geo2, geo3, n1, n2, n3, lines1, lines2, lines3,
m1, m2, m3, i, j, l, edges12, edges23, edges31, sigma;
    ###
    geo1 := radu_datum[1];
    geo2 := radu_datum[2];
    geo3 := radu_datum[3];
    #the points in geo1 correspond to [1..n1]
    #the points in geo2 correspond to [n1+1..n1+n2]
    #the points in geo3 correspond to [n1+n2+1..n1+n2+n3]
    n1 := geo1[1];
    n2 := geo2[1];
    n3 := geo3[1];
    #the lines in geo1 correspond to [n1+1..n1+n2]
    #the lines in geo2 correspond to [n1+n2+1..n1+n2+n3]
    #the lines in geo3 correspond to [1..n1]
    lines1 := geo1[2];
    lines2 := geo2[2];
    lines3 := geo3[2];
    #
    vertices := [1..n1+n2+n3];
    #
    edges12 := [];
    for j in [1..n2] do
    l := lines1[j];
        for i in l do
            Add(edges12, [i, j+n1]);
            Add(edges12, [j+n1, i]);
        od;
    od;
    #
    edges23 := [];
    for j in [1..n3] do
     l := lines2[j];
     for i in l do
         Add(edges23, [i+n1, j+n1+n2]);
         Add(edges23, [j+n1+n2, i+n1]);
     od;
    od;
    #
    edges31 := [];
    for j in [1..n1] do
     l := lines3[j];
     for i in l do
         Add(edges31, [i+n1+n2, j]);
         Add(edges31, [j, i+n1+n2]);
     od;
    od;
    edges := Concatenation(edges12, edges23, edges31);
    sigma := EdgeOrbitsGraph(Group(()), edges, n1+n2+n3);
    return [sigma, [[1..n1],[n1+1..n1+n2],[n1+n2+1..n1+n2+n3]]];
end;

#the triangle cover in the radu graph vertex labelling
ShiftedTriangleCover := function(radu_datum_with_cover)
    local geo1, geo2, geo3, n1, n2, n3, newtrianglecover, t, radu_datum, trianglecover;
    radu_datum := radu_datum_with_cover[1];
    trianglecover := radu_datum_with_cover[2];
    geo1 := radu_datum[1];
    geo2 := radu_datum[2];
    geo3 := radu_datum[3];
    #the points in geo1 correspond to [1..n1]
    #the points in geo2 correspond to [n1+1..n1+n2]
    #the points in geo3 correspond to [n1+n2+1..n1+n2+n3]
    n1 := geo1[1];
    n2 := geo2[1];
    n3 := geo3[1];
    ###
    newtrianglecover := [];
    for t in trianglecover do
        t := [t[1][1], t[2][1], t[3][1] ];
        Add(newtrianglecover, [t[1], t[2]+n1, t[3]+n1+n2]);
    od;
    return newtrianglecover;
end;

#returns the corresponding Radu graph,
#the partition of the vertices into types (corssesponds to edges in the delta complex)
#the triangles, which given in the vertices of the Radu graph
#they correspond to triangles in the delta complex but are given by their boundaries
RaduGraphClassesCoverRaduDatumWithCover := function(radu_datum_with_cover)
    local radu_graph_classes;
    radu_graph_classes := RaduGraphClasses(radu_datum_with_cover[1]);
    return [radu_graph_classes[1], radu_graph_classes[2], ShiftedTriangleCover(radu_datum_with_cover)];
end;

LocalStructuresRaduGraphClassesCover := function(radu_graph_classes_cover)
    local classes, sigma, triangles, edgetypes, raduedges,
    localgeometry12, localgeometry23, localgeometry31,
    vertextypes12, vertextypes23, vertextypes31,
    vertextypes, vertextypesedgetypes, raduedgesvertextype, vertextypepositions;
    #sigma is the radu graph
    sigma := radu_graph_classes_cover[1];
    edgetypes := Vertices(sigma);
    #classes can be though of s the type function on the edge types
    classes := radu_graph_classes_cover[2];
    #the triangles given by their boundaries (edges)
    triangles := radu_graph_classes_cover[3];
    Perform(triangles, Sort);
    raduedges := UndirectedEdges(sigma);
    ###
    #setting up the vertextypes
    #the vertex types are subsets of vertices of the radu graph
    #so they correpond to the set of edges in the delta complex incident with
    #a given vertex
    ###
    localgeometry12 := InducedSubgraph(sigma, Concatenation(classes[1], classes[2]));
    vertextypes12 := ConnectedComponents(localgeometry12);
    Sort(vertextypes12);
    vertextypes12 := List(vertextypes12, c->List(c, x->VertexName(localgeometry12, x)));
    ###
    localgeometry23 := InducedSubgraph(sigma, Concatenation(classes[2], classes[3]));
    vertextypes23 := ConnectedComponents(localgeometry23);
    Sort(vertextypes23);
    vertextypes23 := List(vertextypes23, c->List(c, x->VertexName(localgeometry23, x)));
    ###
    localgeometry31 := InducedSubgraph(sigma, Concatenation(classes[1], classes[3]));
    vertextypes31 := ConnectedComponents(localgeometry31);
    Sort(vertextypes31);
    vertextypes31 := List(vertextypes31, c->List(c, x->VertexName(localgeometry31, x)));
    ###
    vertextypes := Concatenation(vertextypes12, vertextypes23, vertextypes31);
    ###
    #a list with the property that if e edgetype[i] than the i-th entry of this
    #list contains the two vertex types containing e
    vertextypesedgetypes := List(edgetypes, et -> Filtered(vertextypes, vt -> et in vt));
    ###
    vertextypepositions :=[
        [1..Size(vertextypes12)],
        [1..Size(vertextypes23)]+Size(vertextypes12),
        [1..Size(vertextypes31)]+Size(vertextypes12)+Size(vertextypes23)
    ];
    ###
    return [vertextypes, edgetypes, vertextypesedgetypes, triangles, vertextypepositions, classes];
end;

#this function eats a Radu datum and a triangle cover, it returns:
#a list of the connected components of the local geometries -> consider them as vertex types
#a list of the vertices of the Radu datum -> consider them as edge types
#for each vertex type, we have the a list of edge types that should adjacent to this vertex,
#we also want to know the vertex type such an edge is pointing to
#we also need the information which pairs of edges point to vertices, that are connected by
#an edge and the type of that edge (here we need the triangles)
LocalStructuresRaduDatumWithCover := function(radu_datum_with_cover)
    local radu_graph_classes_cover, classes, sigma, triangles, edgetypes, raduedges,
    localgeometry12, localgeometry23, localgeometry31,
    vertextypes12, vertextypes23, vertextypes31,
    vertextypes, vertextypesedgetypes, raduedgesvertextype, vertextypepositions;
    ####
    radu_graph_classes_cover := RaduGraphClassesCoverRaduDatumWithCover(radu_datum_with_cover);
    return LocalStructuresRaduGraphClassesCover(radu_graph_classes_cover);
end;

##############

LabelSimplex := function(local_structure, simplex)
    local vertextypes, edgetypes, triangles, vertextypepositions, classes, k;
    vertextypes := local_structure[1];
    edgetypes := local_structure[2];
    triangles := local_structure[4];
    vertextypepositions := local_structure[5];
    classes := local_structure[6];
    #
    if simplex in vertextypes then
        k := Position(vertextypes, simplex);
        if k in vertextypepositions[1] then
            return Concatenation("u", String(k));
        elif k in vertextypepositions[2] then
            return Concatenation("v", String(k-Size(vertextypepositions[1])));
        elif k in vertextypepositions[3] then
            return Concatenation("w", String(k-Size(vertextypepositions[1])-Size(vertextypepositions[2])));
        fi;
    elif simplex in edgetypes then
        if simplex in classes[1] then
            return Concatenation("e", String(simplex));
        elif simplex in classes[2] then
            return Concatenation("f", String(simplex-Size(classes[1])));
        elif simplex in classes[3] then
            return Concatenation("g", String(simplex-Size(classes[1]) - Size(classes[2])));
        fi;
    elif simplex in triangles then
        return Concatenation("t", String(Position(triangles, simplex)));
    fi;
end;

DescriptionLocalStructure := function(ls)
    local vertextypes, edgetypes, triangles, t,e,v, classes, i, w, vw;
    vertextypes := ls[1];
    edgetypes := ls[2];
    triangles := ls[4];
    classes := ls[6];
    Print("We have ", Size(vertextypes), " vertices:\n");
    for i in [1..Size(vertextypes)-1] do
        Print(LabelSimplex(ls,vertextypes[i]), ", ");
    od;
    Print(LabelSimplex(ls,vertextypes[Size(vertextypes)]), ".\n\n");
    ###
    Print("We have ", Size(edgetypes), " edges:\n");
    Print(LabelSimplex(ls,classes[1][1]), ", ..., ", LabelSimplex(ls,classes[1][Size(classes[1])]), ",\n");
    Print(LabelSimplex(ls,classes[2][1]), ", ..., ", LabelSimplex(ls,classes[2][Size(classes[2])]), ",\n");
    Print(LabelSimplex(ls,classes[3][1]), ", ..., ", LabelSimplex(ls,classes[3][Size(classes[3])]), ".\n\n");
    ####
    Print("We have ", Size(triangles), " triangles:\n");
    Print(LabelSimplex(ls,triangles[1]), ", ..., ", LabelSimplex(ls,triangles[Size(triangles)]), ".\n\n");
    ###
    for t in triangles do
        Print("The boundary of ", LabelSimplex(ls, t), " is ", LabelSimplex(ls, t[1]), ", ", LabelSimplex(ls, t[2]), ", ", LabelSimplex(ls, t[3]), ".\n");
    od;
    Print("\n");
    ###
    for e in edgetypes do
        vw := Filtered(vertextypes, x -> e in x);
        v := vw[1];
        w := vw[2];
        Print("The boundary of ", LabelSimplex(ls, e), " is ", LabelSimplex(ls, v), ", ", LabelSimplex(ls, w), ".\n");
    od;
end;

DescriptionRaduDatumWithCover := function(rdwc)
    local ls;
    Print("We actually describe the corresponding delta complex.\n");
    Print("We did not orient the delta complex.\n\n");
    ls := LocalStructuresRaduDatumWithCover(rdwc);
    DescriptionLocalStructure(ls);
end;

IsomorphismRaduGraphsWithCover := function(radu_graph_classes_cover1, radu_graph_classes_cover2)
    local
    radu_graph1, classes1, cover1,
    radu_graph2, classes2, cover2,
    iso, aut2, graph_isos;
    ###
    radu_graph1 := radu_graph_classes_cover1[1];
    classes1 := radu_graph_classes_cover1[2];
    cover1 := SSortedList(radu_graph_classes_cover1[3]);
    ###
    radu_graph2 := radu_graph_classes_cover2[1];
    classes2 := radu_graph_classes_cover2[2];
    cover2 := SSortedList(radu_graph_classes_cover2[3]);
    ###
    iso := GraphIsomorphism(radu_graph1, radu_graph2);
    if iso = fail then
        return fail;
    else
        aut2 := AutomorphismGroup(radu_graph2);
        graph_isos := List(aut2, a->iso*a);
        iso := First(graph_isos, a ->
            ((classes2 = OnSetsSets(classes1, a)) and
            (cover2 = OnSetsSets(cover1, a))) );
        return iso;
    fi;
    return iso;
end;

IsomorphicRaduDatumsWithCovers := function(radu_datum_with_cover1, radu_datum_with_cover2)
    local radu_graph_classes_cover1, radu_graph_classes_cover2;
    radu_graph_classes_cover1 := RaduGraphClassesCoverRaduDatumWithCover(radu_datum_with_cover1);
    radu_graph_classes_cover2 := RaduGraphClassesCoverRaduDatumWithCover(radu_datum_with_cover2);
    return not IsomorphismRaduGraphsWithCover(radu_graph_classes_cover1, radu_graph_classes_cover2) = fail;
end;

AutomorphismGroupRaduGraphClassesCover := function(radu_graph_classes_cover)
    local aut, radu_graph, triangles, classes;
    radu_graph := radu_graph_classes_cover[1];
    classes := radu_graph_classes_cover[2];
    triangles := radu_graph_classes_cover[3];
    aut := AutomorphismGroup(radu_graph);
    aut := Stabilizer(aut, classes, OnSetsSets);
    aut := Stabilizer(aut, SSortedList(triangles), OnSetsSets);
    if Size(aut) > 2 then
        if IsSolvable(aut) then
            aut := Group(MinimalGeneratingSet(aut));
        else
            aut := Group(SmallGeneratingSet(aut));
        fi;
    fi;
    return aut;
end;

AutomorphismGroupRaduDatumWithCover := function(radu_datum_with_cover)
    local radu_graph_classes_cover, aut;
    radu_graph_classes_cover  := RaduGraphClassesCoverRaduDatumWithCover(radu_datum_with_cover);
    aut := AutomorphismGroupRaduGraphClassesCover(radu_graph_classes_cover);
    return aut;
end;

DescriptionAutomorphismGroupRaduDatumWithCover := function(rdwc)
    local aut, rgcc, ls, gens, g, i, vertextypes, vt, edgetypes, e, t, triangles;
    Print("We describe the action on the automorphism group\non the simplices of the Delta complex.\n\n");
    rgcc := RaduGraphClassesCoverRaduDatumWithCover(rdwc);
    ls := LocalStructuresRaduDatumWithCover(rdwc);
    vertextypes := ls[1];
    edgetypes := ls[2];
    triangles := ls[4];
    aut := AutomorphismGroupRaduGraphClassesCover(rgcc);
    gens := GeneratorsOfGroup(aut);
    Print("The automorphism group is ", StructureDescription(aut), ".\n");
    if Size(aut) > 1 then
        Print("We have ", Size(gens), " generators.\n");
        for i in [1..Size(gens)] do
            g := gens[i];
            Print("Generator ", i, " has order ", Order(g), ".\n");
        od;
        Print("\n");
        Print("We describe the action on vertices:\n");
        for i in [1..Size(gens)] do
            g := gens[i];
            Print("Action of generator ", i, " on vertices:\n");
            for vt in vertextypes do
                Print(LabelSimplex(ls, vt), " is mapped to ", LabelSimplex(ls, OnSets(vt, g)), "\n");
            od;
            Print("\n");
        od;
        Print("We describe the action on edges:\n");
        for i in [1..Size(gens)] do
            g := gens[i];
            Print("Action of generator ", i, " on edges:\n");
            for e in edgetypes do
                Print(LabelSimplex(ls, e), " is mapped to ", LabelSimplex(ls, e^g), "\n");
            od;
            Print("\n");
        od;
    fi;
end;

DescriptionSetOfAutomorphismsRaduDatumWithCover := function(rdwc, subset)
    local rgcc, ls, gens, g, i, vertextypes, vt, edgetypes, e, t, triangles, aut, sub;
    sub := List(subset);
    Print("We describe the action on the given automorphism group\non the simplices of the Delta complex.\n\n");
    rgcc := RaduGraphClassesCoverRaduDatumWithCover(rdwc);
    ls := LocalStructuresRaduDatumWithCover(rdwc);
    vertextypes := ls[1];
    edgetypes := ls[2];
    triangles := ls[4];
    aut := AutomorphismGroupRaduGraphClassesCover(rgcc);
    if ForAll(sub, s->s in aut) then
        sub := Filtered(sub, s->not s = One(aut));
        if Size(sub) > 1 then
            Print("We have ", Size(sub), " automorphisms.\n");
            for i in [1..Size(sub)] do
                g := sub[i];
                Print("Automorphism ", i, " has order ", Order(g), ".\n");
            od;
            Print("\n");
            Print("We describe the action on vertices:\n");
            for i in [1..Size(sub)] do
                g := sub[i];
                Print("Action of automorphism ", i, " on vertices:\n");
                for vt in vertextypes do
                    Print(LabelSimplex(ls, vt), " is mapped to ", LabelSimplex(ls, OnSets(vt, g)), "\n");
                od;
                Print("\n");
            od;
            Print("We describe the action on edges:\n");
            for i in [1..Size(sub)] do
                g := sub[i];
                Print("Action of automorphism ", i, " on edges:\n");
                for e in edgetypes do
                    Print(LabelSimplex(ls, e), " is mapped to ", LabelSimplex(ls, e^g), "\n");
                od;
                Print("\n");
            od;
        fi;
    else
        Print("The given group, does not act on the Radu datum with cover!\n\n");
    fi;
end;

DescriptionSetOfAutomorphismsRaduDatumWithCover := function(rdwc, subset)
    local rgcc, ls, gens, g, i, vertextypes, vt, edgetypes, e, t, triangles, aut, sub;
    sub := List(subset);
    Print("We describe the action on the given automorphism group\non the simplices of the Delta complex.\n\n");
    rgcc := RaduGraphClassesCoverRaduDatumWithCover(rdwc);
    ls := LocalStructuresRaduDatumWithCover(rdwc);
    vertextypes := ls[1];
    edgetypes := ls[2];
    triangles := ls[4];
    aut := AutomorphismGroupRaduGraphClassesCover(rgcc);
    if ForAll(sub, s->s in aut) then
        sub := Filtered(sub, s->not s = One(aut));
        if Size(sub) > 0 then
            Print("We have ", Size(sub), " automorphisms.\n");
            for i in [1..Size(sub)] do
                g := sub[i];
                Print("Automorphism ", i, " has order ", Order(g), ".\n");
            od;
            Print("\n");
            Print("We describe the action on vertices:\n");
            for i in [1..Size(sub)] do
                g := sub[i];
                Print("Action of automorphism ", i, " on vertices:\n");
                for vt in vertextypes do
                    Print(LabelSimplex(ls, vt), " is mapped to ", LabelSimplex(ls, OnSets(vt, g)), "\n");
                od;
                Print("\n");
            od;
            Print("We describe the action on edges:\n");
            for i in [1..Size(sub)] do
                g := sub[i];
                Print("Action of automorphism ", i, " on edges:\n");
                for e in edgetypes do
                    Print(LabelSimplex(ls, e), " is mapped to ", LabelSimplex(ls, e^g), "\n");
                od;
                Print("\n");
            od;
        fi;
    else
        Print("The given group, does not act on the Radu datum with cover!\n\n");
    fi;
end;


#######################################################################

TripleTrianglesRaduDatumWithCover := function(rdwc)
    local rd_triangles, triple_triangles, rdt;
    rd_triangles := rdwc[2];
    triple_triangles := [];
    for rdt in rd_triangles do
        Add(triple_triangles, [rdt[1][1], rdt[2][1], rdt[3][1]]);
    od;
    return triple_triangles;
end;

#uses triangles of the from [i,j,k]
RaduDatumWithCoverFromTriangles := function(triangles)
    local geo1, geo2, geo3, idx1, idx2, idx3, lines1, lines2, lines3, i, j,
    cover, t;
    idx1 := SSortedList(List(triangles, t->t[2]));
    idx2 := SSortedList(List(triangles, t->t[3]));
    idx3 := SSortedList(List(triangles, t->t[1]));
    ###
    lines1 := [];
    for i in idx1 do
        Add(lines1, []);
        for j in idx3 do
            if ForAny(triangles, t->t{[1,2]} = [j,i]) then
                Add(lines1[i], j);
            fi;
        od;
        lines1[i] := SSortedList(lines1[i]);
    od;
    ###
    lines2 := [];
    for i in idx2 do
        Add(lines2, []);
        for j in idx1 do
            if ForAny(triangles, t->t{[2,3]} = [j,i]) then
                Add(lines2[i], j);
            fi;
        od;
        lines2[i] := SSortedList(lines2[i]);
    od;
    ###
    lines3 := [];
    for i in idx3 do
        Add(lines3, []);
        for j in idx2 do
            if ForAny(triangles, t->t{[3,1]} = [j,i]) then
                Add(lines3[i], j);
            fi;
        od;
        lines3[i] := SSortedList(lines3[i]);
    od;
    geo1 := [Size(idx3), lines1];
    geo2 := [Size(idx1), lines2];
    geo3 := [Size(idx2), lines3];
    ###
    cover := [];
    for t in triangles do
        Add(cover, [[t[1], t[2], 1], [t[2], t[3], 2], [t[3],t[1],3]]);
    od;
    return [[geo1, geo2, geo3], cover];
end;

#####################################

IsValidTrianglePresentation := function(triangle_presentation)
    local closed, valid, gamma, delta;
    valid := true;
    if not IsDuplicateFree(triangle_presentation) then
        Print("The set of triangles is not duplicate-free...\n");
        valid := false;
        #we now check if the triangle_presentation is closed under cyclic permutation
    elif not ForAll(triangle_presentation, t->[t[2],t[3],t[1]] in triangle_presentation) then
        Print("The set of triangles is not closed under cyclic permutation...\n");
        valid := false;
        return valid;
    fi;
    return valid;
end;

#the link
GrapeGraphTrianglePresentation := function(triangle_presentation)
    local edges, points, n, gamma;
    if not IsValidTrianglePresentation(triangle_presentation) then
        Print("The triangle presentation is not valid...\n");
        gamma := fail;
    else
        points := List(triangle_presentation, t->t[1]);
        points := SSortedList(points);
        n := Size(points);
        edges := List(triangle_presentation, t-> [Position(points, t[1]), Position(points, t[2])]);
        edges := List(edges, a->[a[1], a[2]+n]);
        edges := Concatenation(edges, List(edges, a->[a[2],a[1]]));
        gamma := EdgeOrbitsGraph(Group(()), edges, 2*n);
    fi;
    return gamma;
end;

RevertedTrianglePresentation := function(tp)
    return SSortedList(List(tp), t-> [t[3],t[2],t[1]]);
end;

IsomorphicTrianglePresentationsTypePreserving := function(tp1, tp2)
    local gamma1, gamma2, aut1, iso, autos;
    gamma1 := GrapeGraphTrianglePresentation(tp1);
    gamma2 := GrapeGraphTrianglePresentation(tp2);
    iso := GraphIsomorphism(gamma1, gamma2);
    if iso = fail then
        return false;
    else
        aut1 := AutomorphismGroup(gamma1);
        autos := List(aut1, a->a*iso);
        return ForAny(autos, a -> OnSetsTuples(tp1, a) = tp2);
    fi;
end;

IsomorphicTrianglePresentations := function(tp1, tp2)
    return IsomorphicTrianglePresentationsTypePreserving(tp1, tp2) or IsomorphicTrianglePresentationsTypePreserving(tp1, RevertedTrianglePresentation(tp2));
end;

C3ActionsOnRaduGraph := function(rdwc)
    local aut, rgcc, c3s, classes;
    rgcc := RaduGraphClassesCoverRaduDatumWithCover(rdwc);
    classes := rgcc[2];
    aut := AutomorphismGroupRaduGraphClassesCover(rgcc);
    c3s := Filtered(AllSubgroups(aut), g->Size(g) = 3);
    c3s := Filtered(c3s, g-> Size(Orbit(g, classes[1], OnSets)) = 3);
    return c3s;
end;

TrianglePresentationRotatingRaduDatum := function(rdwc, c3)
    local rgcc, cover, rep, classes, class1;
    rgcc := RaduGraphClassesCoverRaduDatumWithCover(rdwc);
    classes := rgcc[2];
    class1 := classes[1];
    cover := rgcc[3];
    rep := function(v)
        return Intersection(class1, Orbit(c3, v))[1];
    end;
    return SSortedList(List(cover, c->List(c, c->rep(c))));
end;

TrianglePresentationsWithRotatorRaduDatum := function(rdwc)
    local tp, reps, actions, c3;
    actions := C3ActionsOnRaduGraph(rdwc);
    reps := [];
    for c3 in actions do
        tp := TrianglePresentationRotatingRaduDatum(rdwc, c3);
        if ForAll(reps, t-> IsomorphicTrianglePresentations(t[1], tp) = false ) then
            Add(reps, [tp, c3]);
        fi;
    od;
    return reps;
end;


############################


