
LoadPackage("kbmag");

#with the functions in this script, we can verify that the presentations are correct
#we also give a function that is capable of compute A1A1-boundaries

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

InvolutionOnLongEdges := function(triangles)
    local invo, k, l;
    k := Maximum(List(triangles, t->t[1]))+ Maximum(List(triangles, t->t[2]));
    l := Size(DuplicateFreeList(List(triangles, t->t[2])));
    invo := NiceInvolution(triangles);
    return PermList(List([1..l], i-> (i+k)^invo-k));
end;

TietzeRelationsOfPresentation := function(triangles)
    local r1, r2, invo, l;
    l := Size(DuplicateFreeList(List(triangles, t->t[2])));
    invo := InvolutionOnLongEdges(triangles);
    r1 := List([1..l], i-> [i, i^invo]);
    r2 := A1A1Boundaries(triangles);
    return Concatenation(r1, r2);
end;

CorrectPresentation := function(triangles, fp_grp)
    local tietzes, gens, all_tietzes, rws;
    gens := FreeGeneratorsOfFpGroup(fp_grp);
    tietzes := List(RelatorsOfFpGroup(fp_grp), w->TietzeWordAbstractWord(w, gens));
    all_tietzes := TietzeRelationsOfPresentation(triangles);
    if ForAll(tietzes, t-> t in all_tietzes) then
        rws := KBMAGRewritingSystem(fp_grp);
        KnuthBendix(rws);
        if ForAll(all_tietzes, t-> Length(ReducedForm(rws, AbstractWordTietzeWord(t, gens))) = 0) then
            Print("The presentation is correct.\n");
            return true;
        else
            Print("The presentation is incorrect.\n");
            return fail;
        fi;
    else
        Print("The presentation is incorrect.\n");
        return fail;
    fi;
end;