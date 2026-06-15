

TorsionFreeInvos := function(rdwc)
    local vertex_types, auts;
    vertex_types := LocalStructuresRaduDatumWithCover(rdwc);
    auts := AutomorphismGroupRaduDatumWithCover(rdwc);
    auts := Filtered(auts, a-> Order(a) = 2);
    auts := Filtered(auts, a-> NrMovedPoints(a) = 120);
    auts :=  Filtered(auts, a->NrMovedPoints(Permutation(a, vertex_types, OnSets)) = 12);
    return auts;
end;

ExtendedInvos := function(rdwc, small_invo)
    local auts, better_auts;
    auts := AutomorphismGroupRaduDatumWithCover(rdwc);
    auts := Filtered(auts, a-> Order(a) = 2);
    auts := Filtered(auts, a-> OnSets([1..16], a) = [1..16]);
    auts := Filtered(auts, a-> RestrictedPerm(a, [1..16]) = small_invo);
    if auts = [] then
        return fail;
    else    
        return auts;
    fi;
end;

ChooseInvolution := function(rdwc, prefered)
    local aut, invos, extendeds, vertex_types, torsionfree;
    aut := AutomorphismGroupRaduDatumWithCover(rdwc);
    invos := Filtered(aut, a->Order(a) = 2);
    invos := Filtered(invos, a->OnSets([41..80], a) = [81..120] );
    if invos = [] then
        return fail;
    else
        extendeds := Filtered(invos, a-> OnSets([1..16], a) = [1..16]);
        extendeds := Filtered(extendeds, a-> RestrictedPerm(a, [1..16]) = prefered);
        if extendeds = [] then
            return fail;
        else
            vertex_types := LocalStructuresRaduDatumWithCover(rdwc)[1];
            SortBy(extendeds, tau -> -NrMovedPoints(Permutation(tau, vertex_types, OnSets)));
            torsionfree := Filtered(extendeds, a->NrMovedPoints(a) = 120);
            torsionfree := Filtered(torsionfree, a->NrMovedPoints(Permutation(a, vertex_types, OnSets)) = 12);
            if torsionfree = [] then
                return [extendeds[1], 0];
            elif Size(torsionfree) = 1 then
                return [torsionfree[1], 1];
            else
                return [torsionfree[1], 2];
            fi;
        fi;
    fi;
end;

ShiftInvo := function(invo)
    local images;
    images := List([1..40], i-> (i+40)^invo-80);
    return PermList(images);
end;

RelabelC2TildeRDWC1 := function(rdwc, prefered)
    local triangles, new_triangles, new_rdwc, shifted_invo, extended_invo;
    extended_invo := ChooseInvolution(rdwc, prefered);
    if extended_invo = fail then
        return fail;
    else
        triangles := rdwc[2];
        shifted_invo := ShiftInvo(extended_invo[1]);
        triangles := TripleTrianglesRaduDatumWithCover(rdwc);
        new_triangles := List(triangles, t->[t[1], t[2]^shifted_invo, t[3]]);
        return [RaduDatumWithCoverFromTriangles(new_triangles), extended_invo[2]];
    fi;
end;

RelabelC2TildeRDWC2 := function(rdwc)
    local f, lines, blocks, l, triangles, new_triangles, tau;
    lines := rdwc[1][2][2];
    blocks := [];
    for l in lines do
        if not l in blocks then
            Add(blocks, l);
        fi;
    od;
    f := List([1..40], i->Position(blocks, lines[i]));
    tau := Sortex(f);
    triangles := TripleTrianglesRaduDatumWithCover(rdwc);
    new_triangles := List(triangles, t->[t[1], t[2]^tau, t[3]^tau]);
    return RaduDatumWithCoverFromTriangles(new_triangles);
end;

RelabelC2TildeRDWC3 := function(rdwc)
    local g, lines, blocks, l, triangles, new_triangles, moved, k,
    little_shift, big_shift, shift_helper, g_perm, i, aim;
    ###
    lines := rdwc[1][2][2];
    blocks := [];
    for l in lines do
        if not l in blocks then
            Add(blocks, l);
        fi;
    od;
    g := List([0..9], i -> PositionProperty(blocks, b-> i*4+1 in b));
    g_perm := PermList(g);
    moved := MovedPoints(g_perm);
    k := Size(moved)/2;
    aim := [];
    for i in moved do
        if not i in aim then
            Add(aim, i);
            Add(aim, i^g_perm);
        fi;
    od;
    Append(aim, Filtered([1..10], i-> not i in moved ));
    little_shift := PermList(aim);
    shift_helper := function(i)
        local j;
        j := First([1..10], k-> i in [k*4-3..k*4]);
        return (j^little_shift)*4 - j*4 + i; 
    end;
    big_shift := PermList(List([1..40], shift_helper))^-1;
    triangles := TripleTrianglesRaduDatumWithCover(rdwc);
    new_triangles := List(triangles, t->[t[1], t[2]^big_shift, t[3]^big_shift]);
    return RaduDatumWithCoverFromTriangles(new_triangles);
end;

TriSort := function(t1,t2)
    if t1[2][1] = t2[2][1] then
        return t1[3][1] < t2[3][1];
    else
        return t1[2][1] < t2[2][1];
    fi;
end;

SortTriangles := function(rdwc, bmw_group)
    local old_cover, new_cover, small_cover;
    old_cover := StructuralCopy(rdwc[2]);
    small_cover := RaduDatumWithCoverBMW(bmw_group)[2];
    Sort(old_cover, TriSort);
    if not IsSubsetSet(old_cover, small_cover) then
        return fail;
    else
        new_cover := Concatenation(StructuralCopy(small_cover), Filtered(old_cover, t-> not t in small_cover));
        return [StructuralCopy(rdwc[1]), new_cover];
    fi;
end;

#only use for rdwc that come as result of search
#tries to relabel the result nicely
#if relabeling is possible it returns the relabbeled
#rdwc together with a code 1,2,3
#if relabeling fails it returns the input rdwc with 
#the code 0
RelabelC2Tilde := function(rdwc, bmw_group)
    local small_invo, new, newer, sorted, final, code;
    small_invo := SquaresBMW(bmw_group)[2];
    new := RelabelC2TildeRDWC1(rdwc, small_invo);
    if new = fail then
        final := StructuralCopy(rdwc);
        code := 0;
    else
        newer := RelabelC2TildeRDWC3(RelabelC2TildeRDWC2(new[1]));
        sorted := SortTriangles(newer, bmw_group);
        if new[2] = 0 then
            if sorted = fail then
                final := newer;
                code := 0;
            else
                final := sorted;
                code := 1;
            fi;
        elif new[2] = 1 then
            if sorted = fail then
                final := newer;
                code := 0;
            else
                final := newer;
                code := 2;
            fi;
        elif new[2] = 2 then
            if sorted = fail then
                final := newer;
                code := 0;
            else
                final := newer;
                code := 3;
            fi;
        fi;
    fi;
    return [CyclicPermutedRaduDatumWithCover(final, (1,3,2)), code];
end;