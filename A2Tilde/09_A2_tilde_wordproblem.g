#######

#so triangles are triples [i,j,k] with
#i in classes[1], j in classes[2], k in classes[3]
#positive edges are just numbers in Concatenation(classes)
#negative edges are just numbers in -1*Concatenation(classes)

rho := (1,2,3);

OriginTerminusEdge := function(classes, e)
    if e in classes[1] then
        return [1,2];
    elif e in classes[2] then
        return [2,3];
    elif e in classes[3] then
        return [3,1];
    elif -e in classes[1] then
        return [2,1];
    elif -e in classes[2] then
        return [3,2];
    elif -e in classes[3] then
        return [1,3];
    fi;
end;

OriginEdge := function(classes, e)
    return OriginTerminusEdge(classes,e)[1];
end;

TerminusEdge := function(classes, e)
    return OriginTerminusEdge(classes,e)[2];
end;

AdmissibleEdgePath := function(classes,gamma)
    local k;
    k := Size(gamma);
    return ForAll([2..k], i-> TerminusEdge(classes, gamma[i-1]) = OriginEdge(classes, gamma[i]) );
end;

InverseReductions := function(shifted_trianlges)
    local edges, reductions, e;
    edges := Concatenation(List(shifted_trianlges));
    edges := Flat(edges);
    reductions := [];
    for e in edges do
        Add(reductions, [[], [e, -e]]);
        Add(reductions, [[], [-e, e]]);
    od;
    return reductions;
end;

ComputeReductions := function(shifted_trianlges, classes)
    local reductions, t, class, g;
    reductions := [];
    for class in classes do
        for g in class do
            Add(reductions, [[], [g, -g]]);
            Add(reductions, [[], [-g, g]]);
        od;
    od;
    for t in shifted_trianlges do
        Add(reductions, [[-t[3]], t{[1,2]}]);
        Add(reductions, [[-t[2]], t{[3,1]}]);
        Add(reductions, [[-t[1]], t{[2,3]}]);
        #
        Add(reductions, [[t[3]], -t{[2,1]}]);
        Add(reductions, [[t[2]], -t{[1,3]}]);
        Add(reductions, [[t[1]], -t{[3,2]}]);
    od;
    return reductions;
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
            replacement := r[1];
            better := Concatenation(better{[1..critical-1]}, replacement, better{[critical+Size(r[2])..Size(better)]});
        fi;
    until critical = fail;
    return better;
end;

PlusMinusTurns := function(shifted_trianlges, classes)
    local type11, type22, type33, e, f;
    type11 := [];
    for e in classes[1] do
        for f in classes[1] do
            if not e = f then
                Add(type11, [e,-f]);
            fi;
        od;
    od;
    type22 := [];
    for e in classes[2] do
        for f in classes[2] do
            if not e = f then
                Add(type22, [e,-f]);
            fi;
        od;
    od;
    type33 := [];
    for e in classes[3] do
        for f in classes[3] do
            if not e = f then
                Add(type33, [e,-f]);
            fi;
        od;
    od;
    return Concatenation(type11, type22, type33);
end;

CounterTerm := function(shifted_trianlges, plusminus_turn)
    local first_triangles, second_triangles, type, match;
    first_triangles := Filtered(shifted_trianlges, t->plusminus_turn[1] in t);
    second_triangles := Filtered(shifted_trianlges, t->-plusminus_turn[2] in t);
    type := Position(first_triangles[1], plusminus_turn[1]);
    match := First(Cartesian(first_triangles, second_triangles), pair->pair[1][type^rho] = pair[2][type^rho]);
    return [-match[1][type^(rho^2)], match[2][type^(rho^2)]];
end;

MinusPlusTerms := function(shifted_trianlges, plusminus_turns)
    return List(plusminus_turns, t->CounterTerm(shifted_trianlges, t));
end;

#word cannot be obviuosly reduced, so it as least of length 2
ReplaceCriticalPosition := function(w, turns, alternative_turns)
    local critical, better, turn_index;
    better := StructuralCopy(w);
    repeat
        critical := First([2..Length(better)], k-> better[k-1]<0 and better[k]>0);
        if not critical = fail then
            if better[critical-1]*-1 = better[critical] then
                better := Concatenation(
                    better{[1..critical-2]},
                    better{[critical+1..Size(better)]}
                );
            else
                turn_index := PositionProperty(turns, t -> t=better{[critical-1, critical]});
                better := Concatenation(
                    better{[1..critical-2]},
                    alternative_turns[turn_index],
                    better{[critical+1..Size(better)]}
                );
            fi;
        fi;
    until critical = fail;
    return better;
end;

NormalFormDataProvided := function(reductions, plusminus_turns, minusplus_turns, w)
    local better, even_better;
    even_better := ObviousReduction(reductions, w);
    repeat
        better := StructuralCopy(even_better);
        even_better := ReplaceCriticalPosition(better, minusplus_turns, plusminus_turns);
        even_better := ObviousReduction(reductions, even_better);
    until better = even_better;
    return better;
end;

NormalForm := function(triangles, tietze)
    local rgcc, classes, shifted_triangles, reductions, pm_turns, mp_turns;
    rgcc := RaduGraphTriangles(triangles);
    classes := rgcc[2];
    shifted_triangles := rgcc[3];
    reductions := ComputeReductions(shifted_triangles, classes);
    pm_turns := PlusMinusTurns(shifted_triangles, classes);
    mp_turns := MinusPlusTerms(shifted_triangles, pm_turns);
    if AdmissibleEdgePath(classes, tietze) then
        return NormalFormDataProvided(reductions, pm_turns, mp_turns, tietze);
    else
        return fail;
    fi;
end;

NormalFormInverseDataProvided := function(reductions, plusminus_turns, minusplus_turns, w)
    local inverse;
    inverse := List(Reversed(w), x->-x);
    return NormalFormDataProvided(reductions, plusminus_turns, minusplus_turns, inverse);
end;

NormalFormInverse := function(triangles, tietze)
    local rgcc, classes, shifted_triangles, reductions, pm_turns, mp_turns;
    rgcc := RaduGraphTriangles(triangles);
    classes := rgcc[2];
    shifted_triangles := rgcc[3];
    reductions := ComputeReductions(shifted_triangles, classes);
    pm_turns := PlusMinusTurns(shifted_triangles, classes);
    mp_turns := MinusPlusTerms(shifted_triangles, pm_turns);
    if AdmissibleEdgePath(classes, tietze) then
        return NormalFormInverseDataProvided(reductions, pm_turns, mp_turns, tietze);
    else
        return fail;
    fi;
end;