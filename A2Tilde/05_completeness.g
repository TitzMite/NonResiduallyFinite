#IN GAP WE ARE ACTING FROM THE RIGHT, HENCE WE NEED A REPRESENTATIVE SYSTEM OF
#(L1 lambda1 P2, L2 lambda2 P3, L3 lambda3 P1)

HeawoodGeo := [
    7,
    [
    [ 1, 2, 3 ], [ 1, 4, 5 ], [ 1, 6, 7 ], [ 2, 4, 6 ], [ 2, 5, 7 ], [ 3, 4, 7 ], [ 3, 5, 6 ]
    ]
];

HeawoodRaduDatum := [StructuralCopy(HeawoodGeo), StructuralCopy(HeawoodGeo), StructuralCopy(HeawoodGeo)];

Sym7 := SymmetricGroup(7);

SymPoints := GroupGeo(HeawoodGeo);

SymLines := Group(List(SmallGeneratingSet(SymPoints), g-> Permutation(g, HeawoodGeo[2], OnSets)));

DoubleReps := List(DoubleCosetRepsAndSizes(Sym7, SymLines, SymPoints), rs -> rs[1]);

TransversalLines :=  RightTransversal(Sym7, SymLines);

ConfirmAllLattices := function()
    local triple, radu_datum, radu_datums_with_covers, x, count, i;
    count := ListWithIdenticalEntries(14,0);
    for triple in Cartesian(DoubleReps, Sym7, TransversalLines) do
        radu_datum := TripleAction(HeawoodRaduDatum, triple);
        if RaduScoreRaduDatum(radu_datum) = 63 then
            radu_datums_with_covers := RaduDatumsWithCoversPerfectRaduDatum(radu_datum);
            for x in radu_datums_with_covers do
                i := PositionProperty(A2TildeRaduDatumsWithCovers, y -> IsomorphicRaduDatumsWithCovers(x,y));
                if i = fail then
                    count[14] := count[14] +1;
                else
                    count[i] := count[i] +1;
                fi;
            od;
        fi;
    od;
    if count[14] = 0 then
        Print("Every type-preserving vertex-regular action arises from one of the 13 GABs.\n\n");
    fi;
    return count;
end;