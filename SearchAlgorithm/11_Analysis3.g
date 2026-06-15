
HighestGeneratorFromTriangles := function(triangles)
    return Maximum(List(triangles, t->t[3]));
end;

HighestGenerator := function(turns)
    return Maximum(List(turns, t->Maximum(t)));
end;

ComputeDataWordProblem := function(triangles)
    local a1a1_boundaries, invo, inv_rels, cancelations, shortenings, turns, b, i,
    alternative_turns, reductions;
    invo := ShiftedNiceInvolution(triangles);
    a1a1_boundaries := A1A1Boundaries(triangles);
    inv_rels := List([1..HighestGeneratorFromTriangles(triangles)], i->[i,i^invo]);
    cancelations := List(inv_rels, ir->[[], ir]);
    shortenings := List(a1a1_boundaries, b->[[b[4]^invo], b{[1,2,3]}]);
    reductions := Concatenation(cancelations, shortenings);
    turns := List(a1a1_boundaries, b->b{[1,2]});
    turns := SSortedList(turns);
    alternative_turns := List(turns, t-> []);
    for b in a1a1_boundaries  do
        i := Position(turns, b{[1,2]});
        Add(alternative_turns[i], [b[4]^invo, b[3]^invo]);
    od;
    return [reductions, turns, alternative_turns];
end;

ObviousReduction := function(reductions, w)
    local r, critical, better, replacement, even_better;
    #
    better := StructuralCopy(w);
    repeat
        for r in reductions do
            critical := PositionSublist(better, r[2]);
            if not critical = fail then
                break;
            fi;
        od;
        if not critical = fail then
            #Print("we performed a shorteining or cancellation.\n");
            replacement := r[1];
            better := Concatenation(better{[1..critical-1]}, replacement, better{[critical+Size(r[2])..Size(better)]});
        fi;
    until critical = fail;
    return better;
end;

#word is at least of length 3
CriticalPosition := function(turns, w)
    local l, i, k ;
    l := Length(w);
    i := First([2..l], i-> not w{[i-1,i]} in turns);
    if i = fail then
        return 0;
    else
        k := First([i+1..l], k-> w{[k-1,k]} in turns);
        if k = fail then
            return 0;
        else
            return k;
        fi;
    fi;
end;    

AdjustThreeEdgePath := function(turns, alternative_turns, w)
    local i, alternative;
    i := PositionProperty(turns, t->t = w{[2,3]});
    alternative := First(alternative_turns[i], t-> [w[1],t[1]] in turns);
    if alternative = fail then
        return fail;
    else
        return [w[1],alternative[1],alternative[2]];
    fi;
end;

SemiNormalForm := function(reductions, turns, alternative_turns, w)
    local better_word, k, adjusted;
    better_word := StructuralCopy(w);
    repeat
        better_word := ObviousReduction(reductions, better_word);
        k := CriticalPosition(turns, better_word);
        if k>0 then
            adjusted := AdjustThreeEdgePath(turns, alternative_turns, better_word{[k-2, k-1, k]});
            better_word := Concatenation(better_word{[1..k-3]}, adjusted, better_word{[k+1..Size(better_word)]});
            #Print("we replaced something.\n");
        fi;
    until k=0;
    return better_word;
end;

#input should be zigzag path of even length
CheapestStartingPath := function(turns, alternative_turns, w)
    local first_zigzag, cheaper_word, l, i, j, next_zigzag;
    i := PositionProperty(turns, t->t=w{[1,2]});
    first_zigzag := Minimum(Concatenation([turns[i]], alternative_turns[i]));
    if first_zigzag = w{[1,2]} then
        return w;
    else
        cheaper_word := StructuralCopy(first_zigzag);
        l := Length(w)/2;
        for j in [2..l] do
            i := PositionProperty(turns, t->t=w{[2*j-1,2*j]});
            next_zigzag := First(alternative_turns[i], t->[Last(cheaper_word), t[1]] in turns);
            #Print("we replaced something.\n");
            Append(cheaper_word, next_zigzag);
        od;
        return cheaper_word;
    fi;
end;

NormalFormDataProvided := function(reductions, turns, alternative_turns, w)
    local semi_normal, zigzag, i, l, k;
    semi_normal := SemiNormalForm(reductions, turns, alternative_turns, w);
    l := Size(semi_normal);
    k := Int(l/2);
    i := Last([1..k], i-> semi_normal{[2*i-1,2*i]} in turns);
    if i = fail then
        return semi_normal;
    else
        zigzag := CheapestStartingPath(turns, alternative_turns, semi_normal{[1..2*i]});
        return Concatenation(zigzag, semi_normal{[2*i+1.. Size(semi_normal)]});
    fi;
end;

NormalForm := function(triangles, w)
    local wp_data, reductions, turns, alternative_turns,
    semi_normal, zigzag, i, l, k;
    wp_data := ComputeDataWordProblem(triangles);
    reductions := wp_data[1];
    turns := wp_data[2];
    alternative_turns := wp_data[3];
    return NormalFormDataProvided(reductions, turns, alternative_turns, w);
end;

NormalFormInverseDataProvided := function(invo, reductions, turns, alternative_turns, w)
    local inverse;
    inverse := List(Reversed(w), x->x^invo);
    return NormalFormDataProvided(reductions, turns, alternative_turns, inverse);
end;

NormalFormInverse := function(triangles, w)
    local wp_data, reductions, turns, alternative_turns, semi_normal,
    zigzag, i, l, k, invo;
    wp_data := ComputeDataWordProblem(triangles);
    reductions := wp_data[1];
    turns := wp_data[2];
    alternative_turns := wp_data[3];
    invo := ShiftedNiceInvolution(triangles);
    return NormalFormInverseDataProvided(invo, reductions, turns, alternative_turns, w);
end;


###
#from here on we develop a discreteness criterion

SortSizeLex := function(tietze1, tietze2)
    if Size(tietze1) < Size(tietze2) then
        return true;
    elif Size(tietze2) < Size(tietze1) then
        return false;
    else
        return tietze1 < tietze2;
    fi;
end;


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
    invo := ShiftedNiceInvolution(triangles);
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