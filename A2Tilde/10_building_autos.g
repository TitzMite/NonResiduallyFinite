
OutgoingEdges := function(vertex, classes)
    if vertex = 2 then
        return Concatenation(classes[2], -1*classes[1]);
    elif vertex = 3 then
        return Concatenation(classes[3], -1*classes[2]);
    elif vertex = 1 then
        return Concatenation(classes[1], -1*classes[3]);
    fi;
end;

SuccessorsPath := function(origin, path, classes)
    if Length(path) = 0 then
        return OutgoingEdges(origin, classes);
    else
        return OutgoingEdges(TerminusEdge(classes, Last(path)), classes);
    fi;
end;

#compute the words of length at most radius and a list of
#pairs of such words if one differs from the other by an edge

DataA2TildeBall := function(classes, reductions, plusminus_turns, minusplus_turns, origin, radius)
    local smaller, words, edges, sphere, s, w, n, a, b, new;
    if radius = 0 then
        return [[[]], []];
    else
        smaller :=  DataA2TildeBall(classes, reductions, plusminus_turns, minusplus_turns, origin, radius-1);
        words := StructuralCopy(smaller[1]);
        edges := StructuralCopy(smaller[2]);
        sphere := Filtered(words, w->Length(w) = radius-1);
        new := [];
        #
        for w in sphere do  
            a := Position(words, w);
            for s in SuccessorsPath(origin, w, classes) do
                n := NormalFormDataProvided(reductions, plusminus_turns, minusplus_turns, Concatenation(w, [s]));
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
        for w in new do
            a := Position(words, w);
            for s in SuccessorsPath(origin, w, classes) do
                n := NormalFormDataProvided(reductions, plusminus_turns, minusplus_turns, Concatenation(w, [s]));
                b := Position(words, n);
                if not b = fail and not [a,b] in edges then
                    Add(edges, [a,b]);
                    Add(edges, [b,a]);
                fi;
            od;
        od;
        edges := SSortedList(edges);
        return [words, edges];
    fi;
end;

#returns the ball in the Cayley graph as GRAPE graph and 
#a the list with the words corresponding to the vertices
A2TildeBall := function(triangles, origin, radius)
    local rgcc, classes, shifted_triangles, reductions, pm_turns, mp_turns, ball,
    words, edges;
    ###
    rgcc := RaduGraphTriangles(triangles);
    classes := rgcc[2];
    shifted_triangles := rgcc[3];
    reductions := ComputeReductions(shifted_triangles, classes);
    pm_turns := PlusMinusTurns(shifted_triangles, classes);
    mp_turns := MinusPlusTerms(shifted_triangles, pm_turns);
    ###
    ball := DataA2TildeBall(classes, reductions, pm_turns, mp_turns, origin, radius);
    words := ball[1];
    edges := ball[2];
    return [EdgeOrbitsGraph(Group(()), edges, Size(words)), words];
end;

#ball around vertex v
BallInBigGraph := function(gamma, v, k)
    local ball, ball_vertices, add_layer, i;
    add_layer := function(vertices)
        local x, more_vertices;
        more_vertices := StructuralCopy(vertices);
        for x in vertices do
            Append(more_vertices, Adjacency(gamma, x));
            more_vertices := SSortedList(more_vertices);
        od;
        return more_vertices;
    end;
    ball_vertices := [v];
    for i in [1..k] do
        ball_vertices := add_layer(ball_vertices);
    od;
    return ball_vertices;
end;

RestrictedPermGroup := function(permgroup, points)
    if permgroup = Group(()) then
        return Group(());
    else
        return Group(List(GeneratorsOfGroup(permgroup), gen->RestrictedPerm(gen, points)));
    fi;
end;

#input is a 4-ball
#first we compute the automorphism group Aut4=F0
#
#the fixator of the 1-ball is F1
#the fixator of the 2-ball is F2
#the fixator of the 3-ball is F3
#
#we have projections
#to the automorphism group of the 1-ball Aut1
#to the automorphism group of the 2-ball Aut2
#to the automorphism group of the 3-ball Aut3
#
#we have the following subquotients
#
# F03 <- F0 in Aut3
# F13 <- F1 in Aut3
# F23 <- F2 in Aut3
#
# F02 <- F0 in Aut2
# F12 <- F1 in Aut2
#
# F01 <- F0 in Aut1
#
SubquotientsFourBall := function(ball)
    local aut, one_ball, two_ball, three_ball,
    f1, f2, f3,
    f03, f13, f23, f02, f12, f01;
    #
    aut := AutomorphismGroup(ball);
    #
    one_ball := BallInBigGraph(ball, 1, 1);
    two_ball := BallInBigGraph(ball, 1, 2);
    three_ball := BallInBigGraph(ball, 1, 3);
    #
    f1 := Stabilizer(aut, one_ball, OnTuples);
    f2 := Stabilizer(aut, two_ball, OnTuples);
    f3 := Stabilizer(aut, three_ball, OnTuples);
    #
    f03 := RestrictedPermGroup(aut, three_ball);
    f13 := RestrictedPermGroup(f1, three_ball);
    f23 := RestrictedPermGroup(f2, three_ball);
    #
    f02 := RestrictedPermGroup(aut, two_ball);
    f12 := RestrictedPermGroup(f1, two_ball);
    #
    f01 := RestrictedPermGroup(aut, one_ball);
    #
    return [aut, f1, f2, f3, f03, f13, f23, f02, f12, f01];
end;

Compute4BallData := function(triangles)
    local fourball, subquotients;
    #origin 2 is u
    fourball:= A2TildeBall(triangles, 2, 4)[1];
    subquotients := SubquotientsFourBall(fourball);
    Print("4-ball around u1:\n");
    Print("The automorphism group of the 4-ball around has size ", Size(subquotients[1]), ".\n");
    Print("The number of automorphisms of the 1-ball induced by automorphisms of the 4-ball is ", Size(subquotients[10]), ".\n");
    Print("The number of automorphisms of the 3-ball that are induced by automorphisms that fix the 1-ball ", Size(subquotients[6]), ".\n");
    return [Size(subquotients[1]), Size(subquotients[10]),Size(subquotients[6])];
end;