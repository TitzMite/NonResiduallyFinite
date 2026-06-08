

#compute the words of length at most radius and a list of
#pairs of such words if one differs from the other by a generator
DataCayleyBall := function(reductions, turns, alternative_turns, radius)
    local smaller, words, edges, sphere, w, n, a, b, i, new;
    if radius = 0 then
        return [[[]], []];
    else
        smaller := DataCayleyBall(reductions, turns, alternative_turns, radius-1);
        words := StructuralCopy(smaller[1]);
        edges := StructuralCopy(smaller[2]);
        sphere := Filtered(words, w->Length(w) = radius-1);
        new := [];
        for i in [1..HighestGenerator(turns)] do
            for w in sphere do
                a := Position(words, w);
                n := NormalFormDataProvided(reductions, turns, alternative_turns, Concatenation(w, [i]));
                b := Position(words, n);
                if b = fail then
                    Add(words, n);
                    Add(new, n);
                elif not [a,b] in edges then
                    Add(edges, [a,b]);
                    Add(edges, [b,a]);
                fi;
            od;
        od;
        # for w in new do
        #     a := Position(words, w);
        #     for i in [1..HighestGenerator(turns)] do
        #         n := NormalFormDataProvided(reductions, turns, alternative_turns, Concatenation(w, [i]));
        #         b := Position(words, n);
        #         if not b = fail and not [a,b] in edges then
        #             Add(edges, [a,b]);
        #             Add(edges, [b,a]);
        #         fi;
        #     od;
        # od;
        Sort(edges);
        return [words, edges];
    fi;
end;

#returns the ball in the Cayley graph as GRAPE graph and 
#a the list with the words corresponding to the vertices
CayleyBall := function(triangles, radius)
    local wp_data, reductions, turns, alternative_turns, ball, words, edges;
    ###
    wp_data := ComputeDataWordProblem(triangles);
    reductions := wp_data[1];
    turns := wp_data[2];
    alternative_turns := wp_data[3];
    ball := DataCayleyBall(reductions, turns, alternative_turns, radius);
    words := ball[1];
    edges := ball[2];
    return [EdgeOrbitsGraph(Group(()), edges, Size(words)), words];
end;

#ball in Cayley graph with leafs removed
#second entry encodes to which word a vertex corresponds
#third entry the partition of the vertices into spheres of different radii
PrunedCayleyBall := function(triangles, radius)
    local inner_vertices, pruned_cayley, cayley_ball_data, pcb, i, k, new_labels, layers;
    cayley_ball_data := CayleyBall(triangles, radius);
    inner_vertices :=  Filtered(Vertices(cayley_ball_data[1]), v->Size(Adjacency(cayley_ball_data[1], v)) > 1);
    pcb := InducedSubgraph(cayley_ball_data[1], inner_vertices);
    new_labels := cayley_ball_data[2]{inner_vertices};
    layers := [];
    for i in [1..radius + 1] do
        Add(layers, []);
    od;
    for i in [1..Size(inner_vertices)] do
        k := Size(new_labels[i]);
        Add(layers[k+1], i);
    od;
    Perform(layers, IsRange);
    return [pcb, new_labels, layers];
end;

PrunedCayleyBallWithAutomorphisms := function(triangles, radius)
    local pcb_data, aut, pcb, pcb_labels,
    rg_coloring_cover, rg, coloring, cover, aut_rg, aut_long_edges, l,
    wp_data, reductions,turns, alternative_turns;
    pcb_data := PrunedCayleyBall(triangles, radius);
    pcb := pcb_data[1];
    pcb_labels := pcb_data[2];
    rg_coloring_cover := RaduGraphTriangles(triangles);
    rg := rg_coloring_cover[1];
    coloring := rg_coloring_cover[2];
    l := Size(coloring[1])+Size(coloring[2]);
    aut_rg := rg.group;
    aut_rg := Group(Filtered(aut_rg, x->OnSets(coloring[1], x) = coloring[1] ));
    if Size(aut_rg) > 1 then
        aut_rg := Group(SmallGeneratingSet(aut_rg));
        aut_long_edges := Group(List(GeneratorsOfGroup(aut_rg), x-> PermList(List([1..Size(coloring[3])], i-> (i+l)^x-l))));
        wp_data := ComputeDataWordProblem(triangles);
        reductions := wp_data[1];
        turns := wp_data[2];
        alternative_turns := wp_data[3];
        aut := 
            Group(
                List(
                    GeneratorsOfGroup(aut_long_edges),
                    x-> PermList(
                        List(Vertices(pcb),
                            i ->
                            Position(
                                pcb_labels,
                                NormalFormDataProvided(reductions, turns, alternative_turns, List(pcb_labels[i], j->j^x))
                            )
                        )
                    )
                )
            );
        pcb := NewGroupGraph(aut, pcb);
        aut := AutomorphismGroup(pcb);
        pcb := NewGroupGraph(aut, pcb);
        return [pcb, pcb_data[2], pcb_data[3]];
    else
        aut := AutomorphismGroup(pcb);
        pcb := NewGroupGraph(aut, pcb);
        return [pcb, pcb_data[2], pcb_data[3]];
    fi;
end;

DiscretenessCheckThickness3 := function(triangles)
    local pcb_data, pcb, aut,
    labels, layers, k1, k2, pro1, pro2;
    ###
    pcb_data := PrunedCayleyBallWithAutomorphisms(triangles, 4);
    pcb := pcb_data[1];
    aut := pcb.group;
    labels := pcb_data[2];
    layers := pcb_data[3];
    k1 := Maximum(layers[2]);
    k2 := Maximum(layers[3]);
    pro1 := Group(List(GeneratorsOfGroup(aut), g->RestrictedPerm(g, [1..k1])));
    pro2 := Group(List(GeneratorsOfGroup(aut), g->RestrictedPerm(g, [1..k2])));
    if Size(pro2) = 1 then
        Print("Every automorphism of the 4-ball fixes the 2-ball pointwise.\n");
        Print("The stabilizer of a special vertex is trivial.\n");
        return true;
    else
        Print("The discretness criterion failed. :(\n");
        return fail;
    fi;
end;

DiscretenessCheckThickness4 := function(triangles)
    local wp_data, reductions, turns, alternative_turns,
    pcb_data, pcb, aut, labels, layers, k1, k2, pro1, pro2,
    rigids, rigids_inverses, fixed_labels, r,s, gens, fixed, fix2,
    n, m, invo;
    ###
    pcb_data := PrunedCayleyBallWithAutomorphisms(triangles, 3);
    pcb := pcb_data[1];
    aut := pcb.group;
    labels := pcb_data[2];
    layers := pcb_data[3];
    k1 := Maximum(layers[2]);
    k2 := Maximum(layers[3]);
    pro1 := Group(List(GeneratorsOfGroup(aut), g->RestrictedPerm(g, [1..k1])));
    pro2 := Group(List(GeneratorsOfGroup(aut), g->RestrictedPerm(g, [1..k2])));
    #
    #the vertices in rigids are the vertices in the 1-ball around 1 with the
    #following property
    #if an automorphism fixes the vertex 1 and one of the vertices in rigids then
    #the 1-ball around 1 is fixed.
    #in particular if r is in rigid and an automoprphism fixes the vertices
    #s and sr then the 1-ball around s is fixed
    rigids := Filtered([2..k1], x-> Stabilizer(pro1,x) = Group(()));
    #now lets assume we fix the 1-ball around 1
    #clearly we fix both r^-1 and 1 = r^-1 r
    #there for we fix the 1-ball around r^-1
    wp_data := ComputeDataWordProblem(triangles);
    reductions := wp_data[1];
    turns := wp_data[2];
    alternative_turns := wp_data[3];
    invo := InvolutionOnLongEdges(triangles);
    #
    rigids_inverses := List(rigids, r->NormalFormInverseDataProvided(invo,reductions, turns, alternative_turns, labels[r]));
    fixed_labels := labels{[1..k1]}; #<- one ball is fixed
    gens := labels{[2..k1]};
    for r in rigids_inverses do
        for s in gens do
            Add(fixed_labels, NormalFormDataProvided(reductions, turns, alternative_turns, Concatenation(r,s)));
        od;
    od;
    fixed_labels := SSortedList(fixed_labels);
    fixed := List(fixed_labels, fl -> Position(labels, fl));
    fix2 := Stabilizer(pro2, fixed, OnTuples);
    if Size(fix2) = 1 then
        n := Size(RaduGraphTriangles(triangles)[1].group);
        m := Size(pro1);
        Print("Let pi be the fundamental group of the triangle complex T, you provided.\n");
        Print("We calculated that the index of pi in the full automorphism group\n");
        Print("of the building is at most ", 2*m, ".\n");
        Print("In particular the full automomorphism group is discrete.\n\n");
        Print("If lambda is the extension of pi consisting of deck transformations \n");
        Print("covering the automorphism group of T, then pi is of index ", n, " in lambda.\n\n");
        return true;
    else
        Print("The discretness criterion failed. :(\n");
        return fail;
    fi;
end;