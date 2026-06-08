#only use for q=3 case

#non-special links are pairs, each entry contains four words
#the first entry contains words of even length
#the second entry contains words of odd length
#the words correspond to the special vertices adjacent contained in the non-special link
RepresentativeSystemNonSpecialAtIdentityModPi1T := function(triangles, reductions, turns, alternative_turns)
    local rg_coloring_cover, rg, coloring, shifted_triangles, localgeo12,
    a1a1_links, local_a1a1_boundaries, link, es, fs, invo,
    non_decomposed_links, decomposition_link, decomposed_links, local_boundaries,
    same_apartment, cycle_graph;
    ###
    rg_coloring_cover := RaduGraphTriangles(triangles);
    rg := rg_coloring_cover[1];
    coloring := rg_coloring_cover[2];
    shifted_triangles := rg_coloring_cover[3];
    invo := NiceInvolution(triangles);
    if not invo = fail then
        localgeo12 := InducedSubgraph(rg, Concatenation(coloring[1], coloring[2]));
        a1a1_links := ConnectedComponents(localgeo12);
        local_a1a1_boundaries := [];
        same_apartment := function(x,y)
            return (not x = y) and (x{[1,2]} = y{[1,2]} or x{[3,4]} = y{[3,4]} or x{[4,1]} = y{[4,1]});
        end;
        for link in a1a1_links do
            es := Intersection(link, coloring[1]);
            fs := Intersection(link, coloring[2]);
            local_boundaries := A1A1BoundariesLocal(shifted_triangles, invo, es,fs);
            local_boundaries := List(local_boundaries, lb -> lb - Last(coloring[2]) );
            cycle_graph := Graph(Group(()), local_boundaries, OnTuples, same_apartment, true);
            #the next link is a list of all non-special links encoded as list of words 
            local_boundaries := List(ConnectedComponents(cycle_graph), link-> List(link, x->VertexName(cycle_graph, x)))[1];
            Add(local_a1a1_boundaries, local_boundaries);
        od;
        #next function takes a link a decomposed it into the words of even length (type 1) and the odd length (type 2)
        decomposition_link := function(link)
            local vertices1, vertices2, c;
            vertices1 := [[]];
            vertices2 :=[];
            for c in link do
                Add(vertices2, [c[1]]);
            od;
            vertices2 := SSortedList(vertices2);
            for c in link do
                if c[1] = vertices2[1][1] then
                    Add(vertices1, NormalFormDataProvided(reductions, turns, alternative_turns, c{[1,2]}));
                fi;
            od;
            vertices1 := SSortedList(vertices1);
            return [vertices1, vertices2];
        end;
        decomposed_links := List(local_a1a1_boundaries, link -> decomposition_link(link));
        decomposed_links := List(decomposed_links, c->[SortedList(c[1]), SortedList(c[2])]);
        return decomposed_links;
    else
        return fail;
    fi;
end;

#translating a non-special link
ActionOnLink := function(reductions, turns, alternative_turns, tietze, link)
    local new;
    new := [List(link[1], w->Concatenation(tietze,w)), List(link[2], w->Concatenation(tietze,w))];
    new := [List(new[1], w->NormalFormDataProvided(reductions, turns, alternative_turns, w)), List(new[2], w->NormalFormDataProvided(reductions, turns, alternative_turns, w))];
    new := [SortedList(new[1]), SortedList(new[2])];
    if Size(tietze) mod 2 = 1 then
        new := [new[2], new[1]];
    fi;
    return new;
end;

#compute a representative system modulo the kernel K
#elements_quotient should be a set of underyling elements in f40 representating the elements of the quotients
RepresentativeSystemNonSpecialAtIdentityModK := function(triangles, reductions, turns, alternative_turns, a1a1_boundaries, rws_quotient, elements_quotient)
    local reps_mod_pi1T, shifts, free_gens, invo, reps, w, r;
    ###
    reps_mod_pi1T := RepresentativeSystemNonSpecialAtIdentityModPi1T(triangles, reductions, turns, alternative_turns);
    if not reps_mod_pi1T = fail then
        free_gens := GeneratorsOfGroup(f40);
        shifts := Filtered(elements_quotient, w->Length(w) = 2);
        shifts := List(shifts, w -> TietzeWordAbstractWord(w, free_gens));
        #at this point a Tietze word in words might contain inverses
        invo := InvolutionOnLongEdges(triangles);
        shifts := List(shifts, w -> List(w, function(x) if x>0 then return x; else return (-x)^invo; fi; end  ));
        reps := StructuralCopy(reps_mod_pi1T);
        for w in shifts do
            for r in reps_mod_pi1T do
                Add(reps, ActionOnLink(reductions, turns, alternative_turns, w, r));
            od;
        od;
        return reps;
    else
        return fail;
    fi;
end;

# dont forget that extra_rels must be a set of tietze relations
ConstructCover := function(triangles, extra_rels)
    local a1a1_boundaries, wp_data, reductions, turns, alternative_turns, invo,
    inv_tietzes, free_gens, rels, quotient, rws, oprec, confluent, size_quotient,
    k, elements_quotient, non_special_links, 
    counter_vertices, abstract_vertices, counter_edges, abstract_edges, counter_triangles, abstract_triangles,
    v, g, link, non_special, positions_short_edges_in_this_link, tietzes_in_link, t, w,
    edges_in_this_link, tietze_long_edge, i,j, short_edge1, short_edge2, v_tietze_inv, v_in_quotient, long_edge;
    ###
    invo := InvolutionOnLongEdges(triangles);
    a1a1_boundaries := A1A1Boundaries(triangles);
    wp_data := ComputeDataWordProblem(triangles);
    reductions := wp_data[1];
    turns := wp_data[2];
    alternative_turns := wp_data[3];
    inv_tietzes := List([1..HighestGenerator(turns)], i->[i,i^invo]);
    free_gens := GeneratorsOfGroup(f40);
    rels := List(Concatenation(inv_tietzes, a1a1_boundaries, extra_rels), t->AbstractWordTietzeWord(t, free_gens));
    quotient := f40/rels;
    rws := KBMAGRewritingSystem(quotient);
    oprec := OptionsRecordOfKBMAGRewritingSystem( rws);
    oprec.maxeqns := 2 ^ 22 - 1;
    oprec.confnum := 5000;
    oprec.tidyint := 2000;
    confluent := KnuthBendix(rws);
    if confluent = false then
        return fail;
    else
        size_quotient := Size(rws);
        if size_quotient = infinity then
            return fail;
        else
            k := 0;
            repeat
                k := k+1;
                elements_quotient := EnumerateReducedWords(rws, 0, k);
            until Size(elements_quotient) = Size(rws);
            non_special_links := RepresentativeSystemNonSpecialAtIdentityModK(triangles, reductions, turns, alternative_turns, a1a1_boundaries, rws, elements_quotient);
            #we start building the cover
            #we store the vertices in the list abstract_vertices
            #special vertices are pairs, the first entry is a counter variable the second is in elements quotient
            abstract_vertices := List([1..Size(elements_quotient)], i-> [i, elements_quotient[i]]);
            counter_vertices := Size(abstract_vertices);
            #we now add the first edges
            counter_edges := 0;
            abstract_edges := [];
            #we add a long edge starting at every special vertex corresponding to a word of even type
            for v in abstract_vertices do
                if Length(v[2]) mod 2 = 0 then
                    for g in free_gens do
                        counter_edges := counter_edges + 1;
                        #looking for the vertex v*g
                        w := First(abstract_vertices, x -> x[2] = ReducedForm(rws, v[2]*g));
                        Add(abstract_edges, [counter_edges,v,w,g]);
                    od;
                fi;
            od;
            #okay now we have all the special vertices and long edges
            #lets start with the simplices involving non-special vertices
            abstract_triangles := [];
            counter_triangles := 0;
            for link in non_special_links do
                #starting with non-special vertices
                #we encode them as pairs, first entry is the counter variable, the second one is just the link
                #which is a pair consisting of lists of tietze words
                counter_vertices := counter_vertices+1;
                non_special := [counter_vertices, link];
                Add(abstract_vertices, non_special);
                #now we add short edges
                positions_short_edges_in_this_link := [counter_edges+1..counter_edges+8];
                tietzes_in_link := Concatenation(link);
                for t in tietzes_in_link do
                    counter_edges := counter_edges+1;
                    w := First(abstract_vertices, x->x[2] = ReducedForm(rws, AbstractWordTietzeWord(t,free_gens)));
                    Add(abstract_edges, [counter_edges, non_special, w]);
                od;
                #we now add triangles
                edges_in_this_link := [];
                for tietze_long_edge in Cartesian(link[1], link[2]) do
                    counter_triangles := counter_triangles + 1;
                    i := Position(tietzes_in_link, tietze_long_edge[1]);
                    j := Position(tietzes_in_link, tietze_long_edge[2]);
                    short_edge1 := abstract_edges[positions_short_edges_in_this_link[i]];
                    short_edge2 := abstract_edges[positions_short_edges_in_this_link[j]];
                    v_tietze_inv := NormalFormInverseDataProvided(invo, reductions, turns, alternative_turns, tietze_long_edge[1]);
                    g := free_gens[NormalFormDataProvided(reductions, turns, alternative_turns, Concatenation(v_tietze_inv, tietze_long_edge[2]))[1]];
                    v_in_quotient := ReducedForm(rws, AbstractWordTietzeWord(tietze_long_edge[1], free_gens));
                    long_edge := First(abstract_edges, ae -> ae[2][2] = v_in_quotient and ae[4] = g);
                    Add(abstract_triangles, [counter_triangles, long_edge, short_edge1, short_edge2]);
                od;
            od;
            return [abstract_vertices, abstract_edges, abstract_triangles];
        fi; 
    fi;
end;

ConstructRaduGraphCover := function(complex, extra_rels)
    local simplices, vertices, edges, triangles, type_function_edges,
    vertices_radu_graph, radu_graph, triangles_radu_graph, classes, adjacency, action;
    #
    simplices := ConstructCover(complex, extra_rels);
    vertices := simplices[1];
    edges := simplices[2];
    triangles := simplices[3];
    #
    type_function_edges := function(e)
        if e[2][2] in f40 and e[3][2] in f40 then
            return 1;
        elif Length(e[3][2]) mod 2 = 0 then
            return 2;
        elif Length(e[3][2]) mod 2 = 1 then
            return 3;
        fi;
    end;
    vertices_radu_graph := StructuralCopy(edges);
    SortBy(vertices_radu_graph, vrg->type_function_edges(vrg));
    adjacency := function(e1, e2)
        return (not e1 = e2) and ForAny(triangles, t-> e1 in t and e2 in t);
    end;
    action := function(x,g)
        return x;
    end;
    radu_graph :=  Graph(Group(()), vertices_radu_graph, action, adjacency, true);
    triangles_radu_graph := List(triangles, t-> [Position(vertices_radu_graph, t[2]), Position(vertices_radu_graph, t[3]), Position(vertices_radu_graph, t[4])]);
    classes := List([1..3], i-> Filtered(vertices_radu_graph, e-> type_function_edges(e) = i ));
    classes := List(classes, c-> List(c, e->Position(vertices_radu_graph, e)));
    Perform(classes, IsRange);
    return [radu_graph, classes, triangles_radu_graph];
end;

#would be better to use CheckLinks from 03_locally_C2tilde.g

#plugin the result from ConstructRaduGraphCover
CheckLinksCover := function(rgcc)
    local rg, coloring, localgeo12, localgeo23, localgeo31, i, c, cons, sub;
    rg := rgcc[1];
    coloring := rgcc[2];
    localgeo12 := InducedSubgraph(rg, Concatenation(coloring[1], coloring[2]));
    localgeo23 := InducedSubgraph(rg, Concatenation(coloring[2], coloring[3]));
    localgeo31 := InducedSubgraph(rg, Concatenation(coloring[3], coloring[1]));
    cons := ConnectedComponents(localgeo12);
    for i in [1..Size(cons)] do
        c := cons[i];
        sub := InducedSubgraph(localgeo12, c);
        Print("Link number ", i, " in the local geometry (1,2) has\n");
        Print("order ", OrderGraph(sub), ", girth ", Girth(sub), " and diameter ", Diameter(sub), ".\n\n");
    od;
    cons := ConnectedComponents(localgeo23);
    for i in [1..Size(cons)] do
        c := cons[i];
        sub := InducedSubgraph(localgeo23, c);
        Print("Link number ", i, " in the local geometry (2,3) has\n");
        Print("order ", OrderGraph(sub), ", girth ", Girth(sub), " and diameter ", Diameter(sub), ".\n\n");
    od;
    cons := ConnectedComponents(localgeo31);
    for i in [1..Size(cons)] do
        c := cons[i];
        sub := InducedSubgraph(localgeo31, c);
        Print("Link number ", i, " in the local geometry (3,1) has\n");
        Print("order ", OrderGraph(sub), ", girth ", Girth(sub), " and diameter ", Diameter(sub), ".\n\n");
    od;

end;