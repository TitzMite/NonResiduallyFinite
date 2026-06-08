#for q=2 case

ComputeMultiplicationTable := function(left_factors, right_factors, reductions, turns, alternative_turns)
    local products, a, b, ab, i,j,k,table;
    table := NullMat(Size(left_factors), Size(right_factors), Integers);
    products := [];
    for i in [1..Size(left_factors)] do
        a := left_factors[i];
        for j in [1..Size(right_factors)] do
            b := right_factors[j];
            ab := NormalFormDataProvided(reductions, turns, alternative_turns, Concatenation(a,b));
            k := Position(products, ab);
            if not k = fail then
                table[i,j] := k;
            else
                Add(products, ab);
                table[i,j] := Size(products);
            fi;
        od;
    od;
    # Print(table, "\n");
    return [table, products];
end;

#elm should be an list of numbers and the list should have the same size as B2
#the table should be the multiplication tabel for B2 and B2_inv
#the result will be a list of numbers it will have the same size as B4
#the result encondes an element with support in B4
SquareElement := function(elm, table)
    local i,j,x,y,result, max,k,square;
    max := Maximum(List(table, row -> Maximum(row)));
    square := List([1..max], i->0);
    for i in [1..Size(elm)] do
        x := elm[i];
        for j in [1..Size(elm)] do
            y := elm[j];
            k := table[i][j];
            square[k] := square[k] + x*y;
        od;
    od;
    return square;
end;

SquareSomeElements := function(elms, table)
    local sum_of_squares, i;
    sum_of_squares := SquareElement(elms[1], table);
    for i in [2..Size(elms)] do
        sum_of_squares := sum_of_squares + SquareElement(elms[i], table);
    od;
    return sum_of_squares;
end;

compute_norm_of_error := function()
    local table, triangles, ball2, ball2_inv, ball4, table_data, approximation, difference,
    x, i, w, norm_diff, c, wp_data, reductions, turns, alternative_turns, invo, delta, delta_squared;
    ###
    triangles := y21;
    invo := InvolutionOnLongEdges(triangles);
    wp_data := ComputeDataWordProblem(triangles);
    reductions := wp_data[1];
    turns := wp_data[2];
    alternative_turns := wp_data[3];
    ball2 := CayleyBall(triangles, 2)[2];
    Sort(ball2);
    StableSortBy(ball2, Length);
    ball2_inv := List(ball2, t->NormalFormInverseDataProvided(invo, reductions, turns, alternative_turns, t));
    table_data := ComputeMultiplicationTable(ball2_inv, ball2, reductions, turns, alternative_turns);
    table := table_data[1];
    ball4 := table_data[2];
    #this is the approximation to x = (Delta^2 - 1.29 Delta)*10^24
    approximation := SquareSomeElements(roots, table);
    #we now compute the difference
    #delta lives in <ball2>
    delta := List([1..Size(ball2)], i->0);
    i := Position(ball2, []);
    delta[i] := 15;
    for i in [1..Size(ball2)] do
        w := ball2[i];
        if Size(w) = 1 then
            delta[i] := -1;
        fi;
    od;
    #delta_squared lives in <ball4>
    delta_squared := SquareElement(delta, table);
    x := StructuralCopy(delta_squared);
    i := Position(ball4, []);
    x[i] := x[i] - 15*(129/100);
    for i in [1..Size(ball4)] do
        w := ball4[i];
        if Size(w) = 1 then
            x[i] := x[i] + (129/100);
        fi;
    od;
    x := x*(10^24);
    #now x is (Delta^2 - 1.29 Delta)*10^24
    difference := approximation - x;
    norm_diff := 0;
    for c in difference do
        if c>=0 then
           norm_diff := norm_diff + c;
        else
            norm_diff := norm_diff - c;
        fi;
    od;
    return norm_diff;
end;