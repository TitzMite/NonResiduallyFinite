
LoadPackage("KBMAG");

#######################################

A1A1BoundariesLocal := function(triangles, invo, vertices1, vertices2)
    local cycles, type1, type2, e,f, boundaries, helper1, helper2;
    cycles := [];
    type1 := Arrangements(vertices1, 2);
    type2 := Arrangements(vertices2, 2);
    for e in type1 do
        for f in type2 do
            Add(cycles, [e[1],f[1],e[2],f[2]]);
        od;
    od;
    ###
    helper1 := function(pair)
        local t;
        #there is a unique such triangle
        t := First(triangles,t-> t{[1,2]} = pair);
        return t[3];
    end;
    ###
    helper2 := function(cyc)
        return
        [
            helper1(cyc{[1,2]})^invo,
            helper1(cyc{[3,2]}),
            helper1(cyc{[3,4]})^invo,
            helper1(cyc{[1,4]})
        ];
    end;
    boundaries := List(cycles, cyc->helper2(cyc));
    return DuplicateFreeList(boundaries);
end;

#if this exists, then it is unique
NiceInvolution := function(triangles)
    local radu_graph_data, coloring, radu_graph;
    radu_graph_data := RaduGraphTriangles(triangles);
    radu_graph := radu_graph_data[1];
    coloring := radu_graph_data[2];
    return First(radu_graph.group, x->OnTuples(coloring[1], x) = coloring[2]);
end;

#this should return all the A1A1boundaries
#the returned set is closed under the action of D8
A1A1Boundaries := function(triangles)
    local rg_coloring_cover, rg, coloring, shifted_triangles, localgeo12,
    a1a1_links, a1a1_boundaries, link, es, fs, invo;
    rg_coloring_cover := RaduGraphTriangles(triangles);
    rg := rg_coloring_cover[1];
    coloring := rg_coloring_cover[2];
    shifted_triangles := rg_coloring_cover[3];
    invo := NiceInvolution(triangles);
    if not invo = fail then
        localgeo12 := InducedSubgraph(rg, Concatenation(coloring[1], coloring[2]));
        a1a1_links := ConnectedComponents(localgeo12);
        a1a1_boundaries := [];
        for link in a1a1_links do
            es := Intersection(link, coloring[1]);
            fs := Intersection(link, coloring[2]);
            Append(a1a1_boundaries, A1A1BoundariesLocal(shifted_triangles, invo, es,fs));
        od;
        a1a1_boundaries := List(a1a1_boundaries, b-> List(b, x-> x- Last(coloring[2])));
        a1a1_boundaries := SSortedList(a1a1_boundaries);
        return a1a1_boundaries;
    else
        return fail;
    fi;
end;

#######################

ShiftedNiceInvolution := function(triangles)
    local invo, k, l;
    k := Maximum(List(triangles, t->t[1]))+ Maximum(List(triangles, t->t[2]));
    l := Size(DuplicateFreeList(List(triangles, t->t[3])));
    invo := NiceInvolution(triangles);
    return PermList(List([1..l], i-> (i+k)^invo-k));
end;

Alphabet40 :=
[
    "g1", "g2", "g3", "g4", "g5", "g6", "g7", "g8", "g9", "g10",
    "g11", "g12", "g13", "g14", "g15", "g16", "g17", "g18", "g19", "g20",
    "g21", "g22", "g23", "g24", "g25", "g26", "g27", "g28", "g29", "g30",
    "g31", "g32", "g33", "g34", "g35", "g36", "g37", "g38", "g39", "g40"
];

Free40 :=  FreeGroup(Alphabet40);

RemoveRedundantRels := function(input_grp, invo, invo_tietzes, num_gens)
    local free, free_gens, pres, grp, rels, boundary_rels, boundary_rels_copy, r, s,
    four_tuple, other_four_tuple, eight_tuple, i;
    ###
    if num_gens = 40 then
        free := Free40;
        free_gens := GeneratorsOfGroup(free);
    else
        free := FreeGroup(num_gens);
        free_gens := GeneratorsOfGroup(free);
    fi;
    pres := PresentationFpGroup(input_grp);
    TzOptions(pres).protected := num_gens;
    #TzOptions(pres).printLevel := 3;
    for i in [1..25] do
        TzGoGo(pres);
    od;
    grp := FpGroupPresentation(pres);
    if Size(GeneratorsOfGroup(grp)) > num_gens then
        return fail;
    else
        rels := List(RelatorsOfFpGroup(grp), r-> TietzeWordAbstractWord(r, FreeGeneratorsOfFpGroup(grp)));
        if ForAny(rels, r-> not Size(r) in [2,4]) then
            return fail;
        else
            #making the relators nice again
            boundary_rels := Filtered(rels, r->Length(r) = 4);
            boundary_rels_copy := StructuralCopy(boundary_rels);
            boundary_rels := [];
            for r in boundary_rels_copy do
                s := [];
                for i in r do
                    if i > 0 then
                        Add(s, i);
                    else
                        Add(s, (-i)^invo);
                    fi;
                od;
                four_tuple := List(Group((1,2,3,4)), pi-> Permuted(s, pi));
                other_four_tuple := List(four_tuple, t -> [t[4]^invo, t[3]^invo, t[2]^invo, t[1]^invo]);
                eight_tuple := Concatenation(four_tuple, other_four_tuple);
                Sort(eight_tuple);
                Add(boundary_rels, eight_tuple[1]);
            od;
            Sort(boundary_rels);
            rels := Concatenation(invo_tietzes, boundary_rels);
            return free/List(rels, r->AbstractWordTietzeWord(r, free_gens));
        fi;
    fi;
end;

#return fp group
PresentationExtension := function(triangles)
    local invo, invo_tietzes, invo_rels, boundaries,
    boundary_rels, rels, grp, k, l, i, num_gens, free, free_gens;
    ###
    num_gens := Maximum(List(triangles, t-> t[3]));
    if num_gens = 40 then
        free := Free40;
        free_gens := GeneratorsOfGroup(free);
    else
        free := FreeGroup(num_gens);
        free_gens := GeneratorsOfGroup(free);
    fi;
    invo:= ShiftedNiceInvolution(triangles);
    invo_tietzes := [];
    for i in [1..num_gens] do
        if i^invo >= i then
            Add(invo_tietzes, [i,i^invo]);
        fi;
    od;
    invo_rels := List(invo_tietzes, t->AbstractWordTietzeWord(t, free_gens));
    boundaries := A1A1Boundaries(triangles);
    boundary_rels := List(boundaries, b->AbstractWordTietzeWord(b, free_gens));
    rels := Concatenation(invo_rels, boundary_rels);
    grp := free/rels;
    repeat
        k := Size(RelatorsOfFpGroup(grp));
        grp := RemoveRedundantRels(grp, invo, invo_tietzes, num_gens);
        if grp = fail then
            return fail;
        else
            l := Size(RelatorsOfFpGroup(grp));
        fi;
    until k = l;
    return grp;
end;

SetInfoLevel( InfoRWS, 0 );
#help function
IsRedundantRel := function(tietzes, rel)
    local n, free, rels, other_tietzes, gens, grp, rws, abs_rel, oprec;
    n := Maximum(List(tietzes, t -> Maximum(List(t, i->AbsInt(i)))));
    free := FreeGroup(n);
    gens := GeneratorsOfGroup(free);
    other_tietzes := Filtered(tietzes, t-> not t = rel);
    rels := List(other_tietzes, t->AbstractWordTietzeWord(t,gens));
    grp := free/rels;
    rws := KBMAGRewritingSystem(grp);
    oprec := OptionsRecordOfKBMAGRewritingSystem( rws );
    oprec.maxeqns := 2 ^ 15 - 1;
    oprec.confnum := 5000;
    oprec.tidyint := 2000;
    KnuthBendix(rws);
    abs_rel := AbstractWordTietzeWord(rel, gens);
    return Length(ReducedForm(rws, abs_rel))=0;
end;

#can be used but is expensive
ImproveC2TildePresentation := function(grp)
    local tietzes, new_tietzes, t, k, i;
    tietzes := List(RelatorsOfFpGroup(grp), r->TietzeWordAbstractWord(r, FreeGeneratorsOfFpGroup(grp)));
    new_tietzes := StructuralCopy(tietzes);
    i := 1;
    while i <= Size(new_tietzes) do
        k := Size(new_tietzes);
        Print("checking with ", k, " defining relations\n");
        t := new_tietzes[i];
        if Length(t) = 4 then
            if IsRedundantRel(new_tietzes, t) then
                Print("We removed the relation ", t, ".\n\n");
                new_tietzes := Filtered(new_tietzes, s-> not s=t);
            else
                i := i+1;
            fi;
        else
            i := i+1;
        fi;
    od;
    new_tietzes := SSortedList(new_tietzes);
    StableSortBy(new_tietzes, Length);
    return FreeGroupOfFpGroup(grp)/List(new_tietzes, t->AbstractWordTietzeWord(t, FreeGeneratorsOfFpGroup(grp)));
end;