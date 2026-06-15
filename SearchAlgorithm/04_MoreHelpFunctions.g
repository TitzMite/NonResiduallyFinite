StableScoreFunctionAction := function(geo_datum, score_function, action, point, k)
    local new_geo_datum, scores;
    new_geo_datum := action(geo_datum, point);
    scores := List([1..k], i -> score_function(new_geo_datum));
    return Maximum(scores);
end;

SuperGreedySearcher := function
    (
        geo_datum,
        action,
        multiplication,
        score_function,
        metric_on_points,
        perfect_score,
        aim,
        permutation_generator,
        random_starter,
        levelup,
        limit,
        number_kernels
    )
    local persistence_function;
    persistence_function := function(score, very_best_score, entry)
        return score >= very_best_score - 4;
    end;
    return Searcher(
        geo_datum,
        action,
        multiplication,
        score_function,
        metric_on_points,
        perfect_score,
        aim,
        permutation_generator,
        persistence_function,
        perfect_score, #entry
        random_starter,
        levelup,
        limit,
        number_kernels
        );
end;

Searcher_AutoEntry := function(
        geo_datum,
        action,
        multiplication,
        score_function,
        metric_on_points,
        perfect_score,
        aim,
        permutation_generator,
        persistence_function,
        random_starter,
        levelup,
        limit,
        number_kernels
    )
    local starting_data;
    starting_data := SuperGreedySearcher
    (
        geo_datum,
        action,
        multiplication,
        score_function,
        metric_on_points,
        perfect_score,
        aim,
        permutation_generator,
        random_starter,
        levelup,
        limit,
        number_kernels
    );
    return
    Searcher
    (
    geo_datum,
    action,
    multiplication,
    score_function,
    metric_on_points,
    perfect_score,
    aim,
    permutation_generator,
    persistence_function,
    StableScoreFunctionAction(geo_datum, score_function, action, starting_data[2], 10),
    starting_data[2],
    levelup,
    limit,
    number_kernels
    );
end;

#We introduce the notion of a Radu datum
#this is just a triple of geos

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

#the next part consists of function for RaduGraphs

PerfectScoreRaduDatum := function(radu_datum)
    return Size(EdgesOfRaduDatum(radu_datum));
end;

IsPerfectRaduDatum := function(radu_datum)
    return PerfectScoreRaduDatum(radu_datum) = ScoreOfRaduDatum(radu_datum);
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

#####

#this function takes two triples of perms and mulplies them pointwise
TripleProduct := function(triple1, triple2)
    return [triple1[1]*triple2[1],triple1[2]*triple2[2],triple1[3]*triple2[3]];
end;

#this is not a GAP-action
TripleAction := function(radu_datum, tau)
    local geo1, geo2, geo3;
    geo1 := SingleAction(radu_datum[1], tau[1]);
    geo2 := SingleAction(radu_datum[2], tau[2]);
    geo3 := SingleAction(radu_datum[3], tau[3]);
    return [geo1, geo2, geo3];
end;

###

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

CyclicPermutedRaduDatumWithCover := function(rdwc, cyc)
    local rd, geo1, geo2, geo3, old_cover, new_cover, new_rd, t, i, j,k, new_rdwc;
    rd := rdwc[1];
    geo1 := rd[1];
    geo2 := rd[2];
    geo3 := rd[3];
    old_cover := rdwc[2];
    if cyc = (1,2,3) then
        new_rd := [geo3, geo1, geo2];
        new_cover := [];
        for t in old_cover do
            i := t[1][1];
            j := t[2][1];
            k := t[3][1];
            Add(new_cover, [[k,i,1], [i,j,2], [j,k,3]]);
        od;
        new_rdwc := [new_rd, new_cover];
        return new_rdwc;
    elif cyc = (1,3,2) then
        new_rd := [geo2, geo3, geo1];
        new_cover := [];
        for t in old_cover do
            i := t[1][1];
            j := t[2][1];
            k := t[3][1];
            Add(new_cover, [[j,k,1], [k,i,2], [i,j,3]]);
        od;
        new_rdwc := [new_rd, new_cover];
        return new_rdwc;
    else
        return fail;
    fi;
end;


############################


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

#computes score of the radugraph obtained by acting with triple on delta
RaduScoreRaduDatumAction := function(delta, triple)
    local newdelta;
    newdelta := TripleAction(delta, triple);
    return RaduScoreRaduDatum(newdelta);
end;

#########################


#use if linepositions in partitions are parts of a A1A1 geo
TranspositionsForA1A1Geos := function(points, partitions)
    local transpositions;
    transpositions := Combinations(points,2);
    transpositions := Filtered(transpositions, c-> ForAll(partitions, p -> not IsSubset(p,c)));
    transpositions := List(transpositions, c->(c[1], c[2]));
    return transpositions;
end;

#need permutation generator should be able to detect families of bipartite
#graphs
OrdinaryTripleGenerator := function(radu_datum, triple)
    local permutation_generator, perms, n, m, point_components, line_components,
    i, a1a1_partitions, triples, newdatum;
    n := [radu_datum[1][1], radu_datum[2][1], radu_datum[3][1]];
    m :=  [Size(radu_datum[1][2]),Size(radu_datum[2][2]),Size(radu_datum[3][2])];
    i := PositionProperty(radu_datum, geo -> IsFamilyOfA1A1Geos(geo));
    perms := [[],[],[]];
    ###
    newdatum := TripleAction(radu_datum, triple);
    ###
    if not i = fail then
        a1a1_partitions := A1A1Partitions(newdatum[i]);
        point_components := List(a1a1_partitions, p->p[1]);
        line_components := List(a1a1_partitions, p->p[2]);
        ###
        ###
        perms[i] := TranspositionsForA1A1Geos([1..m[i]], line_components);
        ###
        perms[Mod3(i+1)] := Transpositions([1..m[Mod3(i+1)]]);
        ###
        perms[Mod3(i+2)] := TranspositionsForA1A1Geos([1..m[Mod3(i+2)]], point_components);
        ###
    else
        for i in [1..3] do
            perms[i] := Transpositions([1..m[i]]);
        od;
    fi;
    triples := List(perms[1], tau->[tau, (), ()]);
    Append(triples, List(perms[2], tau->[(), tau, ()]));
    Append(triples, List(perms[3], tau->[(), (), tau]));
    return triples;
end;

TorsionFreePersistenceFunction := function()
    local persistence_function;
    persistence_function := function(score, very_best_score, entry)
        return score >= very_best_score - 6 or score >= entry - 12;
    end;
    return persistence_function;
end;

TorsionFreeMetric := function(triple1, triple2)
    return [NrMovedPoints(triple1[1]*triple2[1]^(-1)), NrMovedPoints(triple1[2]*triple2[2]^(-1)), NrMovedPoints(triple1[3]*triple2[3]^(-1))];
end;

TorsionFreeSearcher := function(radu_datum, number_kernels)
    local x, start_time;
    start_time := CurrentDateTimeString();
    repeat
        x := Searcher_AutoEntry
        (
            radu_datum,
            TripleAction,
            TripleProduct,
            RaduScoreRaduDatum,
            TorsionFreeMetric,
            PerfectScoreRaduDatum(radu_datum),
            PerfectScoreRaduDatum(radu_datum),
            OrdinaryTripleGenerator,
            TorsionFreePersistenceFunction(),
            [Random(SymmetricGroup(Size(radu_datum[1][2]))), Random(SymmetricGroup(Size(radu_datum[2][2]))), Random(SymmetricGroup(Size(radu_datum[3][2])))],
            1000,
            2000,
            number_kernels
        );
    until x[3] =4;
    Print("Start time: ", start_time, ".\n\n");
    Print("End time: ", CurrentDateTimeString(), ".\n\n");
    return [x[1], x[2]];
end;

########
#convinient functions

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

GetRaduDatumWithCoverPerfectRaduDatum := function(perfect_radu_datum)
    return Random(RaduDatumsWithCoversPerfectRaduDatum(perfect_radu_datum));
end;

GetRaduDatumWithCoverRaduDatum := function(radu_datum)
    local perfect_radu_datum, x;
    x := TorsionFreeSearcher(radu_datum, 6);
    perfect_radu_datum := TripleAction(x[1], x[2]);
    return GetRaduDatumWithCoverPerfectRaduDatum(perfect_radu_datum);
end;


#####


DescriptionTriangleComplex := function(complex)
    local rdwc;
    rdwc := RaduDatumWithCoverFromTriangles(complex);
    DescriptionRaduDatumWithCover(rdwc);
end;

DescriptionAutomorphismGroupTriangleComplex := function(complex)
    local rdwc;
    rdwc := RaduDatumWithCoverFromTriangles(complex);
    DescriptionAutomorphismGroupRaduDatumWithCover(rdwc);
end;