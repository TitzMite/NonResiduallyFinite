# it may be that some of these functions are never used

LoadPackage("grape");

EquivariantActions := function(gamma1, gamma2)
    local phi, g1, g2, shifted, aut2;
    phi := GraphIsomorphism(gamma1, gamma2);
    if phi = fail then
        return false;
    else
        g1 := gamma1.group;
        g2 := gamma2.group;
        if not Size(g1) = Size(g2) then
            return false;
        else
            aut2 := AutomorphismGroup(gamma2);
            shifted := g1^phi;
            return g2 in shifted^aut2;
        fi;
    fi;
end;

DuplicateFreeActions := function(gammas)
    local gamma, no_duplis;
    no_duplis := [];
    for gamma in gammas do
        if ForAll(no_duplis, gamma2->EquivariantActions(gamma, gamma2) = false) then
            Add(no_duplis, gamma);
        fi;
    od;
    return no_duplis;
end;

#b and c should be contained in a common group
#example: b,c are permutation groups
CosetGraph := function(b,c)
    local gamma, d, vertices, x, y, action, permgroup;
    d := ClosureGroup(b,c);
    d := Group(SmallGeneratingSet(d));
    vertices := Concatenation(RightCosets(d,b), RightCosets(d,c));
    x := Position(vertices, RightCoset(b, Representative(TrivialSubgroup(d))));
    y := Position(vertices, RightCoset(c, Representative(TrivialSubgroup(d))));
    action := ActionHomomorphism(d, vertices, OnRight);
    permgroup := Image(action);
    gamma := EdgeOrbitsGraph(permgroup, [[x,y],[y,x]]);
    return gamma;
end;

#computes the automorphism group of type preserving automorphisms;
#gamma should be a bipartite graph
TypePreservingAutosBipartiteGraph := function(gamma)
    local aut, type1;
    aut := AutomorphismGroup(gamma);
    aut := Group(SmallGeneratingSet(aut));
    type1 := Bicomponents(gamma)[1];
    aut := Stabilizer(aut, type1, OnSets);
    aut := Group(SmallGeneratingSet(aut));
    Size(aut);
    return aut;
end;

IsSelfDualGraph := function(gamma)
    local aut, aut_plus, duality;
    aut := AutomorphismGroup(gamma);
    aut := Group(SmallGeneratingSet(aut));
    aut_plus := TypePreservingAutosBipartiteGraph(gamma);
    return Index(aut, aut_plus) = 2;
end;

DualityGraph := function(gamma)
    local aut, aut_plus, duality;
    aut := AutomorphismGroup(gamma);
    aut := Group(SmallGeneratingSet(aut));
    aut_plus := TypePreservingAutosBipartiteGraph(gamma);
    if Index(aut, aut_plus) = 1 then
        #Print("This graph is not self-dual.\n\n");
        duality := fail;
    else
        repeat
            duality := Random(aut);
        until not duality in aut_plus;
    fi;
    return duality;
end;

DualGraph := function(gamma)
    local bicomponents, dual_graph, dual_bicomponents, dual_rel;
    bicomponents := Bicomponents(gamma);
    dual_bicomponents := Concatenation(bicomponents[2],bicomponents[1]);
    dual_rel := function(x,y)
        return IsEdge(gamma, [x,y]);
    end;
    dual_graph := Graph(gamma.group, dual_bicomponents, OnPoints, dual_rel, true);
    return dual_graph;
end;

TypePreservingIsomorphism := function(gamma1, gamma2)
    local iso;
    iso := GraphIsomorphism(gamma1, gamma2);
    if not iso = fail then
        if not SortedList(List(Bicomponents(gamma1)[1], x->x^iso)) = Bicomponents(gamma2)[1] then
            if not DualityGraph(gamma1) = fail then
                iso := DualityGraph(gamma1)*iso;
            elif not DualityGraph(gamma2) = fail then
                iso := iso*DualityGraph(gamma2);
            else
                iso := fail;
            fi;
        fi;
    fi;
    return iso;
end;

IsCompleteBipartiteGraph := function(gamma)
    local bi, bi1, bi2;
    bi := Bicomponents(gamma);
    bi1 := bi[1];
    bi2 := bi[2];
    return ForAll(Cartesian(bi1, bi2), e->IsEdge(gamma,e) and IsEdge(gamma, e{[2,1]}) );
end;

IsFamilyOfCompleteBipartiteGraphs := function(gamma)
    local components;
    components := ConnectedComponents(gamma);
    return ForAll(components, c->IsCompleteBipartiteGraph(InducedSubgraph(gamma, c)));
end;


############################
############################

GeoBipartiteGraph := function(delta)
    local bi, points, bi1, bi2, lines, n, l;
    bi := Bicomponents(delta);
    bi1 := bi[1];
    bi2 := bi[2];
    n := Size(bi1);
    lines := [];
    for l in bi2 do
        Add(lines, Filtered([1..n], i-> IsEdge(delta, [bi1[i],l]) ));
    od;
    return [n, lines];
end;


#An arrow is an integer point [i,j], such that the point i
#is contained in the line j
ArrowsGeo := function(geo)
    local i, j, m, arrows;
    m := Size(geo[2]);
    arrows := [];
    for j in [1..m] do
        for i in geo[2][j] do
            Add(arrows, [i,j]);
        od;
    od;
    return arrows;
end;

ChamberNumber := function(geo)
    return Size(ArrowsGeo(geo));
end;

DualGeo := function(geo)
    local m, n, lines, dual;
    n := geo[1];
    lines := geo[2];
    m := Size(geo[2]);
    dual := [m, List([1..n], i -> Filtered([1..m], j-> i  in lines[j]))];
    return dual;
end;

SingleAction := function(geo, tau)
    local geocopy, newgeo, n, lines;
    n := geo[1];
    lines := StructuralCopy(geo[2]);
    newgeo := [geo[1], List([1..Size(lines)], i -> lines[i^(tau^(-1))])];
    return newgeo;
end;

SingleActionOnDual := function(geo, tau)
    return DualGeo(SingleAction(DualGeo(geo), tau^(-1)));
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

GirthGeo := function(geo)
    return Girth(GrapeGraphGeo(geo));
end;


IsomorphicGeos := function(geo1, geo2)
    local graph1, graph2;
    graph1 := GrapeGraphGeo(geo1);
    graph2 := GrapeGraphGeo(geo2);
    return not TypePreservingIsomorphism(graph1, graph2) = fail;
end;

IsomorphicGeosNonTypePreserving := function(geo1, geo2)
    local graph1, graph2;
    graph1 := GrapeGraphGeo(geo1);
    graph2 := GrapeGraphGeo(geo2);
    return not GraphIsomorphism(graph1, graph2) = fail;
end;

#if there exists a permutation tau such that SingleAction(geo1, tau) = geo2
#then this permutations is returned otherwise it returns fail
RepresentativeSingleAction := function(geo1, geo2)
    local distance, relative_positions, m;
    if not IsEqualSet(geo1[2], geo2[2]) then
        distance := fail;
    else
        m := Size(geo1[2]);
        relative_positions := List(geo1[2], l->Position(geo2[2], l));
    fi;
    return PermList(relative_positions);
end;

#this function is just for two geos, for which one can obtained from the other
#by SingleAction
DistanceGeos := function(geo1, geo2)
    local distance;
    distance := NrMovedPoints(RepresentativeSingleAction(geo1, geo2));
end;

GrapeGraphSubGeo := function(geo, points, lines)
    local vertices, rel, trivialaction;
    vertices := Concatenation(points, lines);
    rel := function(x,y)
        local incident;
        if (x in points and y in points) or (x in lines and y in lines) then
            incident := false;
        elif x in lines then
            incident := y in x;
        elif y in lines then
            incident := x in y;
        fi;
        return incident;
    end;
    trivialaction := function(x,g)
        return x;
    end;
    return Graph(Group(()), vertices, trivialaction, rel, true);
end;

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

RandomDualityGeo := function(geo)
    local duality, gamma, duality_of_graph, n;
    n := geo[1];
    gamma := GrapeGraphGeo(geo);
    duality_of_graph := DualityGraph(gamma);
    duality := List([1..n], i -> i^duality_of_graph - n);
    return duality;
end;

IsSelfDualGeo := function(geo)
    local gamma;
    gamma := GrapeGraphGeo(geo);
    return IsSelfDualGraph(gamma);
end;

#A duality of a geo with n lines and n points is an n-tuple d such that
#if for i the point i is mapped to the line d[i] then we obtain a duality
DualitiesGeo := function(geo)
    local gamma, aut, aut_plus, dualities, dualities_of_graph, n, duality;
    n := geo[1];
    dualities := [];
    dualities_of_graph := [];
    gamma := GrapeGraphGeo(geo);
    aut := AutomorphismGroup(gamma);
    aut_plus := TypePreservingAutosBipartiteGraph(gamma);
    if Index(aut, aut_plus) > 1 then
        duality := DualityGraph(gamma);
        dualities_of_graph := List(aut_plus, x->x*duality);
        dualities := List(dualities_of_graph, x->List([1..n], i -> i^x-n));
    fi;
    return dualities;
end;

#returns a function that takes a an element acting on the geo
#and an element in the group of the geo and returns an new element
#acting on the geo with the same score
ActionGeo := function(geo)
    local group, hom, action;
    group := GroupGeo(geo);
    hom := ActionHomomorphism(group, geo[2], OnSets);
    action := function(point, collineation)
        local permpoints, permlines;
        permpoints := collineation;
        permlines := (collineation)^hom;
        return permlines*point*permpoints^(-1);
    end;
    return action;
end;

#return a new point
GeoPointCollineation := function(geo, point, collineation)
    local action_on_lines;
    action_on_lines := Permutation(collineation, geo[2], OnSets);
    return action_on_lines*point*collineation^(-1);
end;

VariantGeoPoint := function(geo, point)
    local group;
    group := GroupGeo(geo);
    return GeoPointCollineation(geo, point, Random(group));
end;

#collination is assumed to be an element of the group of collineations of geo
#returns a new geo with same score
VariantGeo_Collineation := function(geo, collineation)
    return SingleAction(geo, GeoPointCollineation(geo, (), collineation) );
end;

VariantGeo := function(geo)
    local group;
    group := GroupGeo(geo);
    return VariantGeo_Collineation(geo, Random(group));
end;

###########

PruneGeometry := function(geo, specialpoints, speciallinepositions)
    local newgeo, n, m, pruneline, lines, linepositions, line;
    n := geo[1];
    lines := geo[2];
    m := Size(lines);
    pruneline := function(lineposition)
        line := lines[lineposition];
        if lineposition in speciallinepositions then
            return Filtered(line, p-> not p in specialpoints);
        else
            return StructuralCopy(line);
        fi;
    end;
    newgeo := [n, List([1..m], l->pruneline(l))];
    return newgeo;
end;

#This function takes a geometry and a specified subsets of points and lines
#it returns the sub geometry generated by these points and lines
#but in normal form, so the points of the results are 1..l
#where l is the number of points in the sub geometry
NormalFormSubGeo := function(geo, specialpoints, speciallinepositions)
    local
    n, lines, m,
    speciallines, l, k,
    shiftpoints,
    sublines,
    shiftedsubgeo;
    ###
    n := geo[1];
    lines := geo[2];
    m := Size(lines);
    ###
    speciallines := List(speciallinepositions, p->lines[p]);
    l := Size(specialpoints);
    k := Size(speciallines);
    ###
    shiftpoints := RepresentativeAction(SymmetricGroup(n), specialpoints, [1..l], OnTuples);
    ###
    sublines := List(speciallines, l -> Filtered(l, p -> p in specialpoints));
    shiftedsubgeo := [l, List(sublines, l->OnSets(l, shiftpoints) )];
    return shiftedsubgeo;
end;

#This function takes a geometry and a subset of points and some positions of lines
#and and another list of point- and linepositions
#and returns an isomorphic geometry with the given points and lines at the
#specified positions
#it ensures that protected subsets of points and lines is not manipulated
SpecialShift := function(geo, specialpoints, speciallineplaces, newpointplaces, newlineplaces, protectedpoints, protectedlineplaces)
    local
    sub, n, points, lines, lineplaces,
    flexiblepoints, flexiblelineplaces, pointperm, lineperm, newlines, newgeo, newsub;
    #
    #we just compute this for a check
    sub := NormalFormSubGeo(geo, specialpoints, speciallineplaces);
    #
    n := geo[1];
    lines := geo[2];
    points := [1..n];
    lineplaces := [1..Size(geo[2])];
    #
    flexiblepoints := Filtered(points, x -> not x in protectedpoints);
    flexiblelineplaces := Filtered(lineplaces, x-> not x in protectedlineplaces);
    pointperm := RepresentativeAction(SymmetricGroup(flexiblepoints), specialpoints, newpointplaces, OnTuples);
    lineperm := RepresentativeAction(SymmetricGroup(flexiblelineplaces), speciallineplaces, newlineplaces, OnTuples);
    if pointperm = fail or lineperm = fail then
        newgeo := fail;
    else
        newlines := List(lines, l-> OnSets(l, pointperm));
        newlines := List(List(lineplaces), i -> newlines[i^(lineperm^(-1))]);
        newgeo := [n, newlines];
        newsub := NormalFormSubGeo(newgeo, newpointplaces, newlineplaces);
        if not IsomorphicGeos(sub, newsub) then
            newgeo := fail;
        fi;
    fi;
    return newgeo;
end;

##############

#this function takes a GRAPE-graph and a set of vertices of the graph
#it returns a geometry corresponding to the the graph
#the returned geometry satisfies the following properties:
#the points corresponding to the specialvertices (specialvertices of type 1)
#can be found are the newpointplaces
#the lines corresponding to the specialvertices (specialvertices of type 2)
#can be found at the newlineplaces
#the points corresponding to the protectedpoints (pro)
#the GRAPE-graph is asummed to be nice
GeoGrapeGraphSpecial := function(grapegraph, specialvertices, newpointplaces, newlineplaces, protectedvertices)
    #Add some verification test that the input is valid
    #nice grapegraph
    #size specialvertices = size newpoint places = = size protectedvertices of type 1
    #same for lines
    local
    bi, geo, n, specialpoints, speciallinepositions,
    protectedpoints, protectedlinepositions, newgeo;
    #
    bi := Bicomponents(grapegraph);
    #
    geo := GeoBipartiteGraph(grapegraph);
    n := geo[1];
    #
    specialpoints := Intersection(bi[1], specialvertices);
    speciallinepositions := Intersection(bi[2], specialvertices);
    speciallinepositions := List(speciallinepositions, x->x-n);
    #
    specialpoints := Intersection(bi[1], specialvertices);
    speciallinepositions := Intersection(bi[2], specialvertices);
    speciallinepositions := List(speciallinepositions, x->x-n);
    #
    protectedpoints := Intersection(bi[1], protectedvertices);
    protectedlinepositions := Intersection(bi[2], protectedvertices);
    protectedlinepositions := List(protectedlinepositions, x->x-n);
    #
    newgeo:= SpecialShift(geo, specialpoints, speciallinepositions, newpointplaces, newlineplaces, protectedpoints, protectedlinepositions);
    return newgeo;
end;

########################

LoadPackage("digraphs");

#If you take a graph and a subset of vertices, the vertices of the induced
#subgraph are different from than the original vertices
#this function is supposed to return a subgraph and a function, that associates
#to a vertex in the induced subgraph the corresponding vertex in the initial graph
Subgraph_With_Embedding := function(graph, special_vertices)
    local subgraph, finder;
    subgraph := InducedSubgraph(graph, special_vertices);
    #finder takes a vertex of subgraph, and finds the corresponding vertex in graph
    #finder is not a permutation, it is a function
    finder := function(i)
        local position_in_big_graph;
        #vertex names stay the same in induced graphs
        position_in_big_graph := PositionProperty(Vertices(graph), x -> VertexName(graph, x) = VertexName(subgraph, i) );
        return position_in_big_graph;
    end;
    return [subgraph, finder];
end;

#input: a big GRAPE-graph, a small GRAPE-graph, a subset of vertices of the big graph (special vertices)
#it assumes that the the special vertices generate (in the big graph) a graph
#isomorphic to the small graph
#it checks if the isomorphism between small and its copy in big can be choosen to be type-preserving
#Remark: a bipartite GRAPE-graph has a canical order on its two types
IsTypePreservingEmbedding := function(big, small, specialvertices)
    local
    bicomponents_big, bicomponents_small, is_type_preserving_embedding,
    induced_small_embedding, induced_small, embedding, iso_between_smalls;
    ###
    bicomponents_big := Bicomponents(big);
    bicomponents_small := Bicomponents(small);
    ###
    is_type_preserving_embedding := false;
    ###
    if IsSelfDualGraph(small) then
        is_type_preserving_embedding := true;
    else
        induced_small_embedding := Subgraph_With_Embedding(big, specialvertices);
        induced_small := induced_small_embedding[1];
        embedding := induced_small_embedding[2];
        ###
        iso_between_smalls := GraphIsomorphism(small, induced_small);
        if IsSubset(bicomponents_big[1], List(bicomponents_small[1], x->embedding(x^iso_between_smalls))) then
            is_type_preserving_embedding := true;
        fi;
    fi;
    return is_type_preserving_embedding;
end;

#INPUT: a big GRAPE-graph and a small GRAPE-graph
#if there exist a type-preserving embedding of the small graph
#then it returns the vertices of the image, which then generate a copy
#of small in big
#otherwise it returns fail
#REMARK: An emdedding means that the image vertices generate a copy of the
#small graph
DetectSubgraphTypePreserving := function(big, small)
    local
    dibig, dismall, mono,vertices, is_good_embedding, duality, monos;
    ###
    dibig := Digraph(big);
    dismall := Digraph(small);
    mono := DigraphEmbedding(dismall, dibig);
    ###
    if mono = fail then
        vertices := fail;
    else
        vertices := List(Vertices(small), x->x^mono);
        Sort(vertices);
        ###
        is_good_embedding := IsTypePreservingEmbedding(big, small, vertices);
        if not is_good_embedding then
            duality := DualityGraph(big);
            if not duality = fail then
                vertices := List(vertices, x->x^duality);
                is_good_embedding := true;
            fi;
        fi;
        ###
        if not is_good_embedding then
            #if we are in this loop we already know that neiter big nor small
            #is self-dual
            monos := EmbeddingsDigraphsRepresentatives(dismall, dibig);
            for mono in monos do
                vertices := List(Vertices(small), x->x^mono);
                Sort(vertices);
                is_good_embedding := IsTypePreservingEmbedding(big, small, vertices);
                if is_good_embedding then
                    break;
                fi;
            od;
        fi;
        if is_good_embedding = false then
            vertices := fail;
        fi;
    fi;
    return vertices;
end;

DetectSubgraph := function(big, small)
    local
    dibig, dismall, mono, vertices;
    ###
    dibig := Digraph(big);
    dismall := Digraph(small);
    mono := DigraphEmbedding(dismall, dibig);
    if mono = fail then
        vertices := fail;
    else
        vertices := List(Vertices(small), x->x^mono);
        Sort(vertices);
    fi;
    return vertices;
end;

DetectSubgraphTypePreserving_Protected := function(big, small, protected)
    local flexible, flexible_subgraph, embedding, flexible_subgraph_embedding, small_in_flexible_subgraph, smallinbig, vertices;
    ###
    flexible := Filtered(Vertices(big), x-> not x in protected);
    ###
    flexible_subgraph_embedding := Subgraph_With_Embedding(big, flexible);
    flexible_subgraph := flexible_subgraph_embedding[1];
    embedding := flexible_subgraph_embedding[2];
    ###
    if IsTypePreservingEmbedding(big, flexible_subgraph, List(Vertices(flexible_subgraph), x->embedding(x))) then
        small_in_flexible_subgraph := DetectSubgraphTypePreserving(flexible_subgraph, small);
        if small_in_flexible_subgraph = fail then
            vertices := fail;
        else
            vertices := List(small_in_flexible_subgraph, x -> embedding(x));
            Sort(vertices);
        fi;
    else
        Print("This part of the function 'DetectSubgraphTypePreserving_Protected' is not written yet. Go to 'SubgraphSearcher.g', line 136 \n");
        Sleep(10);
        #we basicalley need to do the same as in the situation where the embedding of flexible is type preserving
        #but this time we have to add a swap on the flexible subgraph, so the whole chain of embeddings is again
        #type preserving
    fi;
    return vertices;
end;

DetectSubgraph_Protected := function(big, small, protected)
    local flexible, flexible_subgraph, f, flexible_subgraph_embedding, small_in_flexible_subgraph, smallinbig, vertices;
    ###
    flexible := Filtered(Vertices(big), x-> not x in protected);
    ###
    flexible_subgraph_embedding := Subgraph_With_Embedding(big, flexible);
    flexible_subgraph := flexible_subgraph_embedding[1];
    f := flexible_subgraph_embedding[2];
    small_in_flexible_subgraph := DetectSubgraph(flexible_subgraph, small);
    if small_in_flexible_subgraph = fail then
        vertices := fail;
    else
        vertices := List(small_in_flexible_subgraph, x->f(x));
        Sort(vertices);
    fi;
    return vertices;
end;


##############

#We introduce the notion of a protected geometry, it consits of
#a geometry
#a set of protected points
#a set of positions of protected lines
#a list of pairs
#each of the pairs contains a list of points and a list of lines
#for each pair the sub geometry generated by the points and the lines in the pair
#yields a nice subgeometry
#the set of points is the union of the point sets in the pairs
#the set of lines is the union of the line sets in the pairs

BareProtectedGeometry := function(geo)
    local progeo;
    progeo := [StructuralCopy(geo), [], [], []];
    return progeo;
end;

#takes two geometries
#if they are not type-preserving-isomorphic then it returns fail
#else it gives a permuations, which can be applied to the lines of geo2
#the resulting geometry has the same score as geo1, it actually has the same
#strucure as quotient of geos by the canonical gluing point[i] -> line[i]
PushLineOrderFromSecondGeo := function(geo1, geo2)
    local graph1, graph2, iso, tau, psi1, psi2, geo2_permuted, permuted_lines, n, i, j, m, newline, line, shift;
    graph1 := GrapeGraphGeo(geo1);
    graph2 := GrapeGraphGeo(geo2);
    ###
    iso := TypePreservingIsomorphism(graph1, graph2);
    if iso = fail then
        return fail;
    else
        n := geo1[1];
        m := Size(geo1[2]);
        psi1 := RestrictedPerm(iso, Bicomponents(graph1)[1]);
        psi2 := RestrictedPerm(iso, Bicomponents(graph1)[2]);
        shift := RepresentativeAction(SymmetricGroup(n+m), [n+1..n+m], [1..m], OnTuples);
        psi2 := psi2^shift;
        permuted_lines := [];
        for i in [1..m] do
            j := i^(psi2^(-1));
            newline := StructuralCopy(geo1[2][j]);
            newline := List(newline, x->x^psi1);
            Sort(newline);
            Add(permuted_lines, newline);
        od;
        geo2_permuted := [n, permuted_lines];
        if RepresentativeSingleAction(geo2, geo2_permuted) = () then
            return psi2;
        else
            Print("Error while pushing line order");
        fi;
    fi;
end;

#This function takes a protected geometry, a smaller geometry and a set of point
#positions and a set of line positions
#it tries to find a copy of the small geoemtry in the bigger geoemtry and shifts
#the points and lines of the copy to point and line positions that are given
#the protected geoemtries in the protected geometry are not affected
#newpointplaces and newlineplaces should be sorted
BigGeoSmallGeoProtected := function(protectedgeo, small, newpointplaces, newlineplaces)
    local
    big, n, biggraph, smallgraph,
    protectedpoints, protectedlineplaces, protectedvertices,
    smallgraph_in_biggraph, geo,
    newprotectedpoints, newprotectedlineplaces, newsubgeos,
    sigma, tau, rho, small_geo, k;
    ###
    big := protectedgeo[1];
    n := big[1];
    ###
    biggraph := GrapeGraphGeo(big);
    smallgraph := GrapeGraphGeo(small);
    ###
    protectedpoints  := protectedgeo[2];
    protectedlineplaces := protectedgeo[3];
    protectedvertices := Concatenation(protectedpoints, List(protectedlineplaces, l -> l+n));
    ###
    smallgraph_in_biggraph := DetectSubgraphTypePreserving_Protected(biggraph, smallgraph, protectedvertices);
    if smallgraph_in_biggraph = fail then
        return fail;
    # add here a plausibility check
    else
        geo := GeoGrapeGraphSpecial(biggraph, smallgraph_in_biggraph, newpointplaces, newlineplaces, protectedvertices);
        #
        k := Size(small[2]);
        small_geo := NormalFormSubGeo(geo, newpointplaces, newlineplaces);
        #let k be the number of points in small then k is in Sym(k)
        sigma := PushLineOrderFromSecondGeo(small, small_geo);
        tau := RepresentativeAction(SymmetricGroup(n), [1..k], newlineplaces, OnTuples);
        rho := tau^(-1)*sigma^(-1)*tau;
        geo := SingleAction(geo, rho);
        #
        newprotectedpoints := Concatenation(protectedpoints, newpointplaces);
        newprotectedlineplaces := Concatenation(protectedlineplaces, newlineplaces);
        #
        Sort(newprotectedpoints);
        Sort(newprotectedlineplaces);
        newsubgeos := Concatenation(protectedgeo[4], [[newpointplaces, newlineplaces]]);
        Sort(newsubgeos);
        return [geo, newprotectedpoints, newprotectedlineplaces, newsubgeos];
    fi;
end;

#embeds small geo in big geo
BigGeoSmallGeo := function(big, small)
    local
    progeo,
    n, m, k, l,
    pointplaces, lineplaces;
    ###
    progeo := BareProtectedGeometry(big);
    ###
    n := big[1];
    m := Size(big[2]);
    k := small[1];
    l := Size(small[2]);
    ###
    pointplaces := [1..k];
    lineplaces := [1..l];
    return BigGeoSmallGeoProtected(progeo, small, pointplaces, lineplaces);
end;

BigGeoSmallGeoClean := function(big, small)
    local protected, gamma_initial, gamma_embeded, sub, tau, clean;
    protected := BigGeoSmallGeo(big, small);
    if protected = fail then
        return fail;
    else
        big := protected[1];
        sub := NormalFormSubGeo(big, protected[2], protected[3]);
        gamma_initial := GrapeGraphGeo(small);
        gamma_embeded := GrapeGraphGeo(sub);
        tau := GraphIsomorphism(gamma_embeded, gamma_initial);
        tau := RestrictedPerm(tau, [1..small[1]]);
        clean := SingleActionOnDual(big, tau^-1);
        if ForAll([1..Size(small[2])], i -> IsSubset(clean[2][i], small[2][i])) then
            return clean;
        else
            return fail;
        fi;
    fi;
end;


########

IsFamilyOfA1A1Geos := function(geo)
    local gamma;
    gamma := GrapeGraphGeo(geo);
    return IsFamilyOfCompleteBipartiteGraphs(gamma);
end;

A1A1Partitions := function(geo)
    local gamma, bi, bi1, bi2, components, partitions, c, n;
    n := geo[1];
    if IsFamilyOfA1A1Geos(geo) then
        gamma := GrapeGraphGeo(geo);
        bi := Bicomponents(gamma);
        bi1 := bi[1];
        bi2 := bi[2];
        components := ConnectedComponents(gamma);
        partitions := [];
        for c in components do
            Add(partitions, [Intersection(c,bi1), List(Intersection(c, bi2), x-> x-n)]);
        od;
        return partitions;
    else
        return fail;
    fi;
end;

Transpositions := function(points)
    local transpositions;
    transpositions := List(Combinations(points,2), c->(c[1], c[2]));
    return transpositions;
end;


################


#the main function of this file is IsomorphicRaduDatumsWithCover, a
#function can determine if two Radu datums with cover are isomorphic, i.e.
#they yield equivariant actions

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

SimplexFromLabel := function(local_structure, label)
    local vertextypes, edgetypes, triangles, vertextypepositions, classes, firstletter, number;
    vertextypes := local_structure[1];
    edgetypes := local_structure[2];
    triangles := local_structure[4];
    vertextypepositions := local_structure[5];
    classes := local_structure[6];
    #
    firstletter := label[1];
    number := Int(label{[2..Size(label)]});
    if firstletter = 'u' then
        return vertextypes[number];
    elif firstletter = 'v' then
        return vertextypes[number+Size(vertextypepositions[1])];
    elif firstletter = 'w' then
        return vertextypes[number+Size(vertextypepositions[1])+Size(vertextypepositions[2])];
    elif firstletter = 'e' then
        return edgetypes[number];
    elif firstletter = 'f' then
        return edgetypes[number+Size(classes[1])];
    elif firstletter = 'g' then
        return edgetypes[number+Size(classes[1])+Size(classes[2])];
    elif firstletter = 't' then
        return triangles[number];
    fi;
end;

#need function that associates simplex-label to vertex-type (connected component) of Radu graph
#need function that associates simplex label to edge-type (vertex in graph) of Radu graph
#need function that associated simplex label to triangle of Radu graph with cover

#need function that takes admissible simplex label and returns the corresponding structure in
#a Radu graph with cover

#there should be a function that computes decorated balls
#there should be a variant of the ball computation that reads in the label

#need a function that takes a decorated ball and returns simplex labels of
#vertices, edges, paths, triangles
#for the paths we need to set up some kind of path structure in graphs

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


IsomorphicRaduDatums := function(radu_datum1, radu_datum2)
    local rgc1, rgc2, aut2, iso, isos, rg1, rg2, c1, c2;
    rgc1 := RaduGraphClasses(radu_datum1);
    rgc2 := RaduGraphClasses(radu_datum2);
    rg1 := rgc1[1];
    c1 := rgc1[2];
    rg2 := rgc2[1];
    c2 := rgc2[2];
    iso := GraphIsomorphism(rg1, rg2);
    if iso = fail then
        return false;
    else
        aut2 := AutomorphismGroup(rg2);
        isos := List(aut2, a->iso*a);
        return ForAny(isos, x -> c2 = OnSetsSets(c1, x));
    fi;
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

ActionOnTypes := function(radu_datum_with_cover)
    local radu_graph_classes_cover, radu_graph, classes, cover, aut;
    ###
    radu_graph_classes_cover  := RaduGraphClassesCoverRaduDatumWithCover(radu_datum_with_cover);
    radu_graph := radu_graph_classes_cover[1];
    classes := radu_graph_classes_cover[2];
    cover := radu_graph_classes_cover[3];
    ###
    aut := AutomorphismGroupRaduGraphClassesCover(radu_graph_classes_cover);
    return StructureDescription(Action(aut,classes,OnSets));
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

#want output of automorphism group of delta complex for Radu datum with cover
#want output of automorphism group of subgroup of ball of Radu datum with cover

#assume the automorphism group of the radu graph is generated by n elements
#then this function returns 3 groups with n generators each
#generator i of the first group is the permuation of the vertices, that is
#induced by generator i of the automorphism group
#group 2 <-> edges
#group 3 <-> triangles

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
        # Print("We describe the action on triangles:\n");
        # for i in [1..Size(gens)] do
        #     g := gens[i];
        #     Print("Action of generator ", i, " on triangles:\n");
        #     for t in triangles do
        #         Print(LabelSimplex(ls, t), " is mapped to ", LabelSimplex(ls, OnSets(t, g)), "\n");
        #     od;
        #     Print("\n");
        # od;
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
            # Print("We describe the action on triangles:\n");
            # for i in [1..Size(sub)] do
            #     g := sub[i];
            #     Print("Action of generator ", i, " on triangles:\n");
            #     for t in triangles do
            #         Print(LabelSimplex(ls, t), " is mapped to ", LabelSimplex(ls, OnSets(t, g)), "\n");
            #     od;
            #     Print("\n");
            # od;
        fi;
    else
        Print("The given group, does not act on the Radu datum with cover!\n\n");
    fi;
end;
