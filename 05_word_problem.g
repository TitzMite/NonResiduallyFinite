
#main functions:
#NormalFormWithDataProvided(descendings, congruents, turns, w)
#NormalFormInverseWithDataProvided(descendings, congruents, turns, w)
#NormalFormTrianglesTietze(triangles, tietze)
#NormalFormInverseTrianglesTietze(triangles, tietze)

HighestGeneratorFromTriangles := function(triangles)
    return Maximum(List(triangles, t->t[3]));
end;

HighestGenerator := function(turns)
    return Maximum(List(turns, t->Maximum(t)));
end;

ComputeDataWordProblem := function(triangles)
    local a1a1_boundaries, invo, inv_rels, cancelations, shortenings, turns, b, i,
    alternative_turns, reductions;
    invo := InvolutionOnLongEdges(triangles);
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
    invo := InvolutionOnLongEdges(triangles);
    return NormalFormInverseDataProvided(invo, reductions, turns, alternative_turns, w);
end;

####
#the following functions count the performed operations

ObviousReduction_WithCounting := function(reductions, w)
    local r, critical, better, replacement, even_better, counter_cancelling, counter_shortening;
    #
    counter_cancelling := 0;
    counter_shortening := 0;
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
            if Length(replacement) = 0 then
                counter_cancelling := counter_cancelling + 1;
            else
                counter_shortening := counter_shortening + 1;
            fi;
            better := Concatenation(better{[1..critical-1]}, replacement, better{[critical+Size(r[2])..Size(better)]});
        fi;
    until critical = fail;
    return [better, counter_cancelling, counter_shortening];
end;

SemiNormalForm_WithCounting_DataProvided := function(reductions, turns, alternative_turns, w)
    local better_word, k, adjusted, counter_exchanging, counter_cancelling, better_word_data, counter_shortening;
    better_word := StructuralCopy(w);
    counter_cancelling := 0;
    counter_shortening := 0;
    counter_exchanging := 0;
    repeat
        better_word_data := ObviousReduction_WithCounting(reductions, better_word);
        better_word := better_word_data[1];
        counter_cancelling := counter_cancelling + better_word_data[2];
        counter_shortening := counter_shortening + better_word_data[3];
        k := CriticalPosition(turns, better_word);
        if k>0 then
            adjusted := AdjustThreeEdgePath(turns, alternative_turns, better_word{[k-2, k-1, k]});
            better_word := Concatenation(better_word{[1..k-3]}, adjusted, better_word{[k+1..Size(better_word)]});
            counter_exchanging := counter_exchanging + 1;
            #Print("we replaced something.\n");
        fi;
    until k=0;
    return [better_word, counter_cancelling, counter_shortening, counter_exchanging];
end;

SemiNormalForm_WithCounting := function(triangles, w)
    local wp_data, reductions, turns, alternative_turns,
    semi_normal, zigzag, i, l, k;
    wp_data := ComputeDataWordProblem(triangles);
    reductions := wp_data[1];
    turns := wp_data[2];
    alternative_turns := wp_data[3];
    return SemiNormalForm_WithCounting_DataProvided(reductions, turns, alternative_turns, w);
end;

#input should be zigzag path of even length
CheapestStartingPath_WithCounting := function(turns, alternative_turns, w)
    local first_zigzag, cheaper_word, l, i, j, next_zigzag, counter_exchanging;
    counter_exchanging := 0;
    i := PositionProperty(turns, t->t=w{[1,2]});
    first_zigzag := Minimum(Concatenation([turns[i]], alternative_turns[i]));
    if first_zigzag = w{[1,2]} then
        return [w, 0];
    else
        cheaper_word := StructuralCopy(first_zigzag);
        l := Length(w)/2;
        for j in [2..l] do
            i := PositionProperty(turns, t->t=w{[2*j-1,2*j]});
            next_zigzag := First(alternative_turns[i], t->[Last(cheaper_word), t[1]] in turns);
            counter_exchanging := counter_exchanging + 1;
            #Print("we replaced something.\n");
            Append(cheaper_word, next_zigzag);
        od;
        return [cheaper_word, counter_exchanging];
    fi;
end;

NormalForm_WithCounting_DataProvided := function(reductions, turns, alternative_turns, w)
    local semi_normal, zigzag, i, l, k, semi_normal_data, zigzag_data;
    semi_normal_data := SemiNormalForm_WithCounting_DataProvided(reductions, turns, alternative_turns, w);
    semi_normal := semi_normal_data [1];
    l := Size(semi_normal);
    k := Int(l/2);
    i := Last([1..k], i-> semi_normal{[2*i-1,2*i]} in turns);
    if i = fail then
        return Concatenation([semi_normal], semi_normal_data{[2,3,4]});
    else
        zigzag_data := CheapestStartingPath_WithCounting(turns, alternative_turns, semi_normal{[1..2*i]});
        zigzag := zigzag_data[1];
        return Concatenation([Concatenation(zigzag, semi_normal{[2*i+1.. Size(semi_normal)]})], semi_normal_data{[2,3,4]} + [0,0, zigzag_data[2]]);
    fi;
end;

NormalForm_WithCounting := function(triangles, w)
    local wp_data, reductions, turns, alternative_turns,
    semi_normal, zigzag, i, l, k;
    wp_data := ComputeDataWordProblem(triangles);
    reductions := wp_data[1];
    turns := wp_data[2];
    alternative_turns := wp_data[3];
    return NormalForm_WithCounting_DataProvided(reductions, turns, alternative_turns, w);
end;
