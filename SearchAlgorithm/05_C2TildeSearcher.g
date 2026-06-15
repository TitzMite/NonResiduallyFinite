

GeneratorSort := function(i,j)
    if AbsInt(i) = AbsInt(j) then
        return -i<-j;
    else
        return AbsInt(i) < AbsInt(j);
    fi;
end;

SquaresBMW := function(bmw_group)
    local fgens, abstract_rels, tietze_rels, square_rels, squares, As, Xs, invo;
    ###
    fgens := FreeGeneratorsOfFpGroup(bmw_group);
    abstract_rels := RelatorsOfFpGroup(bmw_group);
    tietze_rels := List(abstract_rels, arel -> TietzeWordAbstractWord(arel, fgens));
    square_rels := Filtered(tietze_rels, rel->Size(rel) = 4);
    As := DuplicateFreeList(List(square_rels, r->r[1]));
    Sort(As, GeneratorSort);
    Xs := DuplicateFreeList(List(square_rels, r->r[2]));
    Sort(Xs, GeneratorSort);
    squares := List(square_rels, r-> [Position(As, r[1])+4,Position(Xs, r[2]),Position(As, r[3])+4, Position(Xs, r[4])]);
    invo := PermList(List([1..16], i->Position(squares, squares[i]{[3,4,1,2]})));
    return [squares, invo];
end;

#the generator As[i] will become f{i} and e_{i}
#the generator Xs[i] will become f{i+4} and e_{i+4}
#where generators in square relations are mapped to
#1 -> f5..f8
#2 -> f1..f4
#3 -> e5..e8
#4 -> e1..e4

SubdividingSquareComplex := function(squares)
    local triangles, s, i;
    triangles := [];
    for i in [1..Size(squares)] do
        s := squares[i];
        Add(triangles, [s[4], s[1], i]);
        Add(triangles, [s[3], s[2], i]);
    od;
    return triangles;
end;

RaduDatumWithCoverBMW := function(bmw_group)
    local squares, subdiv, rdwc;
    squares := SquaresBMW(bmw_group)[1];
    subdiv := SubdividingSquareComplex(squares);
    rdwc := RaduDatumWithCoverFromTriangles(subdiv);
    rdwc := CyclicPermutedRaduDatumWithCover(rdwc, (1,2,3));
    return rdwc;
end;

#compute the involution by looking at the squares

ReadyForSearchBMW44 := function(bmw_group)
    local small_rdwc, small_geo1, big_geo1, small_geo2, small_geo3, big_geo2,
    involution, cover;
    ###
    small_rdwc := RaduDatumWithCoverBMW(bmw_group);
    cover := small_rdwc[2];
    ###
    small_geo1 := small_rdwc[1][1];
    small_geo2 := small_rdwc[1][2];
    small_geo3 := small_rdwc[1][3];
    ###
    big_geo1 := BigGeoSmallGeoClean(DualGeo(W3_geo), small_geo1);
    big_geo2 := [40, Concatenation(small_geo2[2], rest_A1A1)];
    involution := SquaresBMW(bmw_group)[2];
    return [big_geo1, big_geo2, small_rdwc, involution];
end;

######

DoubledWithFixedInvolution:= function(involution)
    local Doubled;
    Doubled := function(geopair, triple)
        local geo1, geo2, lambda, pol, inv;
        geo1 := geopair[1];
        geo2 := geopair[2];
        lambda := triple[1];
        pol := triple[2];
        inv := triple[3];
        return
        [
            SingleAction(geo1, lambda),
            SingleAction(geo2, pol),
            SingleAction(DualGeo(SingleAction(geo1, lambda*pol)), inv*involution)
        ];
    end;
    return Doubled;
end;

TranspositionsForInvo := function(invo, flexible)
    local fixed, pairs, i, more_moved_points, less_moved_points;
    fixed := [];
    pairs := [];
    for i in flexible do
        if i^invo = i then
            Add(fixed, i);
        else
            if not [i^invo, i] in pairs then
                Add(pairs, [i, i^invo]);
            fi; 
        fi;
    od;
    more_moved_points := Transpositions(fixed);
    less_moved_points := List(pairs, p-> (p[1], p[2]));
    return Concatenation(less_moved_points, more_moved_points);
end;

TranspositionsForInvoPushingDown := function(invo, flexible)
    local fixed, pairs, i, more_moved_points, less_moved_points;
    fixed := [];
    pairs := [];
    for i in flexible do
        if i^invo = i then
            Add(fixed, i);
        else
            if not [i^invo, i] in pairs then
                Add(pairs, [i, i^invo]);
            fi; 
        fi;
    od;
    more_moved_points := Transpositions(fixed);
    less_moved_points := List(pairs, p-> (p[1], p[2]));
    Append(less_moved_points, List(Combinations(pairs, 2), c-> (c[1][1], c[1][2])(c[2][1],c[2][2]) ));
    return Concatenation(less_moved_points, more_moved_points);
end;

PolarityOfInvo := function(invo)
    local list;
    list := List([1..40], i-> ((Int((i-1)/4)+1)^invo-1)*4 + (i-1) mod 4 + 1);
    return PermList(list);
end;

PolaritiesForPolarity := function(pol)
    local pi, invos, pols;
    pi := Permutation(pol, [1,5,9,13,17,21,25,29,33,37]);
    invos := TranspositionsForInvo(pi, [3..10]);
    return List(invos, invo->PolarityOfInvo(invo));
end;

DoublePolaritiesForPolarity := function(pol)
    local pols, pols1, pols2, p1, p2, p;
    pols :=[];
    pols1 := PolaritiesForPolarity(pol);
    for p1 in pols1 do
        Add(pols, p1);
        pols2 := PolaritiesForPolarity(p1);
        for p2 in pols2 do
            p := p1*p2;
            if (not p = ()) and (not p in pols) then
                Add(pols, p);
            fi;
        od;
    od;
    return pols;
end;

PermGeneratorBMW44 := function(geopair, triple)
    local pol, inv, p, t, perms1, perms2, perms3, triples;
    pol := triple[2];
    inv := triple[3];
    perms1 := transpositions_for_geo1;
    if Random([1..10]) mod 10 = 0 then
        perms2 := PolaritiesForPolarity(pol);
    else
        perms2 := [];
    fi;
    perms3 := TranspositionsForInvoPushingDown(inv, [17..40]);
    triples := List(perms1, x->[x, (), ()]);
    Append(triples, List(perms2, x->[(), x, ()]));
    Append(triples, List(perms3, x->[(), (), x]));
    return triples;
end;

# Function to compute the number of involutions of size n recursively
InvolutionCount := function(n)
  if n = 0 then
    return 1;
  elif n = 1 then
    return 1;
  else
    return InvolutionCount(n - 1) + (n - 1) * InvolutionCount(n - 2);
  fi;
end;

# Function to generate a random involution of range
RandomInvolution := function(range)
    local images, unseen, number_unseen, i,j,s,t,r, list;
    ###
    # Initialize: fixed points by default
    images := StructuralCopy(range);
    # List of undecided elements
    unseen := StructuralCopy(range);
    number_unseen := Size(unseen);
    while number_unseen > 1 do
        i := Random([1..number_unseen]);
        s := InvolutionCount(number_unseen);
        t := InvolutionCount(number_unseen - 1);
        r := Random([1..s]);
        if r <= t then
            # Fix current element
            Remove(unseen, i);
            number_unseen := number_unseen -1;
        else
        # Swap current element with another unseen one
            j := Random(Filtered([1..number_unseen], k->not k = i));
            images[Position(images, unseen[i])] := unseen[j];
            images[Position(images, unseen[j])] := unseen[i];
            if i < j then
                Remove(unseen, j);
                Remove(unseen, i);
            else
                Remove(unseen, i);
                Remove(unseen, j);
            fi;
            number_unseen := number_unseen-2;
        fi;
    od;
    list := [];
    for i in [1..Maximum(range)] do
        if not i in range then
            Add(list, i);
        else
            j := Position(range, i);
            Add(list, images[j]);
        fi;
    od;
    return PermList(list);
end;

PrunedResultBMW44 := function(geo_pair, action, number_kernels)
    local x, result, starter;
    repeat
        starter := [Random(SymmetricGroup([9..40])), PolarityOfInvo(RandomInvolution([3..10])), RandomInvolution([17..40])];
        x := Searcher
        (
            geo_pair,
            action,
            TripleProduct,
            RaduScoreRaduDatum,
            TorsionFreeMetric,
            480 - 96,
            480 - 96,
            PermGeneratorBMW44,
            TorsionFreePersistenceFunction(),
            438 - 96,
            starter,
            500,
            500,
            number_kernels
        );
    until x[3] = 4;
    result := action(geo_pair, x[2]);
    return result;
end;

#######################


Refill := function(result, small_rd)
    local lines1, lines2, lines3, i;
    lines1 := StructuralCopy(result[1][2]);
    lines2 := StructuralCopy(result[2][2]);
    lines3 := StructuralCopy(result[3][2]);
    lines1 := Concatenation(small_rd[1][1][2], lines1{[9..40]});
    lines2 := Concatenation(small_rd[1][2][2], lines2{[9..40]});
    for i in [1..16] do
        Append(lines3[i], small_rd[1][3][2][i]);
        Sort(lines3[i]);
    od;
    return [[40, lines1], [40, lines2], [40, lines3]];
end;

FindEnvelopingC2Tilde := function(bmw_group, number_kernels)
    local ready, geo_pair, involution, action, pruned, pruned_geo1, pruned_geo2,
    pruned_result, partial_cover, small, refilled, found;
    ###
    ready := ReadyForSearchBMW44(bmw_group);
    geo_pair := ready{[1,2]};
    involution := ready[4];
    action := DoubledWithFixedInvolution(involution);
    pruned_geo1 := [40, Concatenation([[],[],[],[],[],[],[],[]], geo_pair[1][2]{[9..40]})];
    pruned_geo2 := [40, Concatenation([[],[],[],[],[],[],[],[]], geo_pair[2][2]{[9..40]})];
    pruned := [pruned_geo1, pruned_geo2];
    AppendTo("searcher.log", "------------------------------------\n");
    AppendTo("searcher.log", "------------------------------------\n\n");
    AppendTo("searcher.log", CurrentDateTimeString(), "\nWe start a new search\n\n");
    AppendTo("searcher.log", "------------------------------------\n\n");
    ###
    pruned_result := PrunedResultBMW44(pruned, action, number_kernels);
    ###
    AppendTo("searcher.log", CurrentDateTimeString(), "\n\nsearch successful\n\n\n ");
    partial_cover := GetRaduDatumWithCoverPerfectRaduDatum(pruned_result)[2];
    small := ready[3];
    refilled := Refill(pruned_result, small);
    found := [refilled, Concatenation(ready[3][2], partial_cover)];
    return found;
end;

###
#alternative search approach
#may return non-symmetric C2-Tilde lattice, but this seems to be unlikely

Starter360 := function(geo_pair, action, number_kernels)
    local x, result, starter;
    repeat
        starter := [Random(SymmetricGroup([9..40])), PolarityOfInvo(RandomInvolution([3..10])), RandomInvolution([17..40])];
        x := Searcher
        (
            geo_pair,
            action,
            TripleProduct,
            RaduScoreRaduDatum,
            TorsionFreeMetric,
            480 - 96,
            453 - 96,
            PermGeneratorBMW44,
            TorsionFreePersistenceFunction(),
            438 - 96,
            starter,
            500,
            500,
            number_kernels
        );
    until x[3] in [3,4];
    result := action(geo_pair, x[2]);
    return result;
end;

StandardGenerator := function(radu_datum, triple)
    local perms1, perms2, perms3, triples, newdatum, lines_components;
    newdatum := TripleAction(radu_datum, triple);
    #
    perms1 := transpositions_for_geo1;
    #
    lines_components := List(A1A1Partitions(newdatum[2]), p->p[2]);
    perms2 := Combinations([9..40], 2);
    perms2 := Filtered(perms2, c-> ForAll(lines_components, l -> not IsSubsetSet(l,c)));
    perms2 := List(perms2, c->(c[1],c[2]));
    #
    perms3 := Transpositions_17_40;
    triples := List(perms1, x->[x, (), ()]);
    Append(triples, List(perms2, x->[(), x, ()]));
    Append(triples, List(perms3, x->[(), (), x]));
    return triples;
end;

PrunedResultBMW44Alternative := function(geopair, action, number_kernels)
    local starter, x, result;
    repeat
        starter := Starter360(geopair, action, number_kernels);
        x := Searcher
        (
            starter,
            TripleAction,
            TripleProduct,
            RaduScoreRaduDatum,
            TorsionFreeMetric,
            480 - 96,
            480 - 96,
            StandardGenerator,
            TorsionFreePersistenceFunction(),
            445 - 96,
            [(),(),()],
            500,
            5000,
            number_kernels
        );
    until x[3] = 4;
    result := TripleAction(starter, x[2]);
    return result;
end;

FindEnvelopingC2TildeAlternative := function(bmw_group, number_kernels)
    local ready, geo_pair, involution, action, pruned, pruned_geo1, pruned_geo2,
    pruned_result, partial_cover, small, refilled, found;
    ###
    ready := ReadyForSearchBMW44(bmw_group);
    geo_pair := ready{[1,2]};
    involution := ready[4];
    action := DoubledWithFixedInvolution(involution);
    pruned_geo1 := [40, Concatenation([[],[],[],[],[],[],[],[]], geo_pair[1][2]{[9..40]})];
    pruned_geo2 := [40, Concatenation([[],[],[],[],[],[],[],[]], geo_pair[2][2]{[9..40]})];
    pruned := [pruned_geo1, pruned_geo2];
    AppendTo("alternative_searcher.log", "------------------------------------\n");
    AppendTo("alternative_searcher.log", "------------------------------------\n\n");
    AppendTo("alternative_searcher.log", CurrentDateTimeString(), "\nWe start a new alternative search\n\n");
    AppendTo("alternative_searcher.log", "------------------------------------\n\n");
    ###
    pruned_result := PrunedResultBMW44Alternative(pruned, action, number_kernels);
    ###
    AppendTo("alternative_searcher.log", CurrentDateTimeString(), "\n\nalternative search successful\n\n\n ");
    partial_cover := GetRaduDatumWithCoverPerfectRaduDatum(pruned_result)[2];
    small := ready[3];
    refilled := Refill(pruned_result, small);
    found := [refilled, Concatenation(ready[3][2], partial_cover)];
    return found;
end;