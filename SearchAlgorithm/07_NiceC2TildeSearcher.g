


SortRelators := function(r1, r2)
    if r1[1] = r2[1] then
        return GeneratorSort(r1[2], r2[2]);
    else
        return GeneratorSort(r1[1], r2[1]);
    fi;
end;

#only prints something if the presentation is not admissible
AdmissiblePresentation := function(G)
    local rels, square_rels, inv_rels, looks_admissible, As, Xs, free, free_gens,
    replace_invs, involutions;
    rels := RelatorsOfFpGroup(G);
    free := FreeGroupOfFpGroup(G);
    free_gens := FreeGeneratorsOfFpGroup(G);
    looks_admissible := true;
    if ForAll(rels, r->Length(r) in [2,4]) then
        inv_rels := Filtered(rels, r->Length(r) = 2);
        inv_rels := List(inv_rels, r->TietzeWordAbstractWord(r, free_gens));
        if ForAll(inv_rels, r-> r[1]=r[2]) then
            inv_rels := List(inv_rels, r->[SignInt(r[1])*r[1], SignInt(r[1])*r[1]]);
            inv_rels := SSortedList(inv_rels);
            involutions := List(inv_rels, r->r[1]);
            square_rels := Filtered(rels, r->Length(r) = 4);
            square_rels := List(square_rels, r->TietzeWordAbstractWord(r, FreeGeneratorsOfFpGroup(G)));
            square_rels := Concatenation(square_rels, List(square_rels, r-> r{[3,4,1,2]}));
            square_rels := Concatenation(square_rels, List(square_rels, r-> -1*r{[1,4,3,2]}));
            replace_invs := function(r)
                local new, s;
                new := [];
                for s in r do
                    if -s in involutions then
                        Add(new, -s);
                    else
                        Add(new, s);
                    fi;
                od;
                return new;
            end;
            square_rels := List(square_rels, r->replace_invs(r));
            square_rels := DuplicateFreeList(square_rels);
            Sort(square_rels, SortRelators);
            As := Concatenation(List(square_rels, s->s{[1,3]}));
            Xs := Concatenation(List(square_rels, s->s{[2,4]}));
            if not Intersection(As, Xs) = [] then
                Print("We only allow relations of length four of the form a1x1a2x2.\n\n");
                looks_admissible := false;
            fi;
        else
            Print("We only allow relations of length two of the form a^2.\n\n");
            Print("Please adjust the presentation.\n");
            looks_admissible := false;
        fi;
    else
        looks_admissible := false;
    fi;
    if looks_admissible then
        inv_rels := List(inv_rels, r->AbstractWordTietzeWord(r, free_gens));
        square_rels := List(square_rels, r->AbstractWordTietzeWord(r, free_gens));
        return FreeGroupOfFpGroup(G)/Concatenation(inv_rels, square_rels);
    else
        Print("This presentation is not admissible.\n\n");
        return fail;
    fi;
end;

#only use output of AdmissiblePresentation
DescriptionBMWPresentation:=function(G)
    local rels, free_gens, inv_rels, square_rels, i;
    rels := RelatorsOfFpGroup(G);
    free_gens := FreeGeneratorsOfFpGroup(G);
    Print("You provided a BMW-group that is compatible with our methods.\n");
    Print("We might have added some redundant relations of length 4\n");
    Print("and we might have changed the order of the relations.\n\n");
    Print("We work with the presentation with the following relations.\n");
    inv_rels := Filtered(rels, r->Length(r) = 2);
    square_rels := Filtered(rels, r->Length(r) = 4);
    if not inv_rels = [] then
        for i in [1..Size(inv_rels)] do
            Print(inv_rels[i], ", ");
        od;
        Print("\n");
    fi;
    for i in [1..Size(square_rels)] do
        if i < 16 then
            Print(square_rels[i], ", ");
        elif i = 16 then
            Print(square_rels[i], ".");
        fi;
        if i mod 4 = 0 then
            Print("\n");
        fi;
    od;
    Print("\n\n");
end;

PrintFourLabeledSquares := function(list_of_squares, positions)
    local allSquaresLines, i, s, topLabel, bottomLabel, rightLabel, leftLabel,
    line1, line2, line3, line4, line5, line6, BuildSquareLines, combinedLine, k,
    padBetween, two_char_string;
    ###
    padBetween := "    ";
    two_char_string := function(i)
        if i < 10 then
            return Concatenation(" ", String(i));
        else
            return String(i);
        fi;
    end;
    BuildSquareLines := function(s, i)
        local tLabel, bLabel, rLabel, lLabel, lns, labelLine;
        tLabel := Concatenation("e", String(s[3]));
        bLabel := Concatenation("f", String(s[1]));
        rLabel := Concatenation("f", String(s[2]));
        lLabel := Concatenation("e", String(s[4]));
        # Center labels
        line1 := Concatenation("       ", tLabel, "      ");                # centered top label
        line2 := "   4-------3   ";                                         # top edge
        line3 := Concatenation(lLabel, " |       | ", rLabel);              # side labels in own line
        line4 := Concatenation("   |   ", two_char_string(i) ,"  |   ");  # middle
        line5 := "   1-------2   ";                                         # bottom edge
        line6 := Concatenation("       ", bLabel, "      ");                # centered bottom label
        return [line1, line2, line3, line4, line5, line6];
    end;
    # Build all squares
    allSquaresLines := List([1..4], i-> BuildSquareLines(list_of_squares[i], positions[i]));
    # Print each row
    for i in [1..6] do
        combinedLine := "";
        for k in [1..4] do
            combinedLine := Concatenation(combinedLine, allSquaresLines[k][i]);
            if k < 4 then
                combinedLine := Concatenation(combinedLine, padBetween);
            fi;
        od;
        Print(combinedLine, "\n");
    od;
    Print("\n");
end;


DescriptionSquareComplex := function(bmw_group)
    local fgens, abstract_rels, tietze_rels, square_rels, squares, As, Xs, s, i;
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
    ###
    Print("The fundamental group of the complex S with the following squares\n");
    Print("is index 4 in the considered BMW group.\n\n");
    for i in [0..3] do
        PrintFourLabeledSquares(squares{[4*i+1..4*i+4]}, [4*i+1..4*i+4]);
    od;
    Print("\n");
    Print("This square complex admits an involutory automorphism defined by ei <-> fi:\n");
    Print("It acts on the sqaures as follows:\n");
    Print(PermList(List([1..16], i->Position(squares, squares[i]{[3,4,1,2]}))), "\n\n");
end;

DescriptionRelabeled := function(rdwc)
    local psi, lines, triangles, i;
    Print("We found a C2Tilde-GAB T.\n\n");
    Print("We have 12 vertices, u1,.., u10, v, w.\n");
    Print("We have 120 edges, e1,.., e40, f1,.., f40, g1,..,g40.\n");
    Print("The vertex gi has boundary [v,w].\n");
    Print("Let chi: [1..40] -> [1,10]  be the function that maps i to smallest integer bigger than i/4.\n");
    Print("The vertex ei has boundary [uj,w], with j = chi(i).\n");
    lines :=  rdwc[1][1][2];
    psi := PermList(List([1..10], i-> (lines[i*4][1]-1)/4 + 1 ));
    Print("Let psi be the following permutation: ", psi, "\n");
    Print("The vertex fi has boundary [uj,v], with j = psi(chi(i)).\n");
    Print("We have 160 triangles and we indicate them by their boundary.\n");
    triangles := List(rdwc[2], t-> Concatenation("[e", String(t[1][1]), ", f", String(t[2][1]), ", g", String(t[3][1]), "]" ));
    for i in [1..160] do
        Print(triangles[i]);
        if i mod 4 = 0 then
            if i = 32 then
                Print(",\n\n");
            elif not i = 160 then
                Print(",\n");
            else
                Print(".\n");
            fi;
        else
            Print(", ");
        fi;
    od;
    Print("\n");
    Print("This GAB has an involutory automorphism defined by ei <-> fi\n");
    Print("If we subdive S along the diagonals from 2 to 4 and label the diagonals by si,\n");
    Print("then the map ei->ei, fi->fi, si->gi defines an embedding of S into T.\n");
end;

CheckTorsionFreenessRDWC := function(rdwc)
    local aut, invo, vertex_types, torsionfree;
    aut := AutomorphismGroupRaduDatumWithCover(rdwc);
    invo := Filtered(aut, a->OnTuples([1..40], a) = [41..80]);
    if invo = [] then
        return fail;
    else
        invo := invo[1];
        vertex_types := LocalStructuresRaduDatumWithCover(rdwc);
        torsionfree := NrMovedPoints(invo) = 120 and NrMovedPoints(Permutation(invo, vertex_types, OnSets)) = 12;
        return torsionfree;
    fi;
end;

#only allow groups in right format
#   BMW groups of degree (4,4)
#   just relations of the form a^2 or square relations allowed
#   exactly 16 square relations
#   only square relations of the form a1*x1*a2*x2
C2TildeBMW := function(G, number_kernels)
    local raw, relabeled, new_G;
    new_G := AdmissiblePresentation(G);
    if not new_G = fail then
        raw := FindEnvelopingC2Tilde(new_G, number_kernels);
        Exec("clear");
        relabeled := RelabelC2Tilde(raw, new_G);
        if relabeled[2] = 0 then 
            Print("Somethin went wrong here, sorry...\n\n");
            return fail;
        else
            DescriptionBMWPresentation(new_G);
            DescriptionSquareComplex(new_G);
            if relabeled[2] = 1 then
                DescriptionRelabeled(relabeled[1]);
                # we have extensions but no free ones
                Print("This autmorphisms does not act freely, there exists no involutory automorphism\n");
                Print("acting freely that extends the one from the BMW group.\n\n");
            elif relabeled[2] = 2 then
                DescriptionRelabeled(relabeled[1]);
                # we have a unique free extensions
                Print("This autmorphisms acts freely, and it the only involutory automorphism\n");
                Print("acting freely that extends the one from the BMW group.\n\n");
            elif relabeled[2] = 3 then
                DescriptionRelabeled(relabeled[1]);
                # we have a unique free extensions
                Print("This autmorphisms acts freely, and there are multiple involutory automorphism\n");
                Print("acting freely that extend the one from the BMW group.\n\n");
            fi;
            return TripleTrianglesRaduDatumWithCover(relabeled[1]);
        fi;
    else
        return fail;
    fi;
end;


#only allow groups in right format
#   BMW groups of degree (4,4)
#   just relations of the form a^2 or square relations allowed
#   exactly 16 square relations
#   only square relations of the form a1*x1*a2*x2
C2TildeBMWAlternative := function(G, number_kernels)
    local raw, relabeled, new_G;
    new_G := AdmissiblePresentation(G);
    if not new_G = fail then
        raw := FindEnvelopingC2TildeAlternative(new_G, number_kernels);
        Exec("clear");
        relabeled := RelabelC2Tilde(raw, new_G);
        if relabeled[2] = 0 then 
            Print("Somethin went wrong here, sorry...\n\n");
            return fail;
        else
            DescriptionBMWPresentation(new_G);
            DescriptionSquareComplex(new_G);
            if relabeled[2] = 1 then
                DescriptionRelabeled(relabeled[1]);
                # we have extensions but no free ones
                Print("This autmorphisms does not act freely, there exists no involutory automorphism\n");
                Print("acting freely that extends the one from the BMW group.\n\n");
            elif relabeled[2] = 2 then
                DescriptionRelabeled(relabeled[1]);
                # we have a unique free extensions
                Print("This autmorphisms acts freely, and it the only involutory automorphism\n");
                Print("acting freely that extends the one from the BMW group.\n\n");
            elif relabeled[2] = 3 then
                DescriptionRelabeled(relabeled[1]);
                # we have a unique free extensions
                Print("This autmorphisms acts freely, and there are multiple involutory automorphism\n");
                Print("acting freely that extend the one from the BMW group.\n\n");
            fi;
            return TripleTrianglesRaduDatumWithCover(relabeled[1]);
        fi;
    else
        return fail;
    fi;
end;


###########

#this function assumes that the result is labeled
#in the right way
#it does not check if the bmw-group is compatible with
#the C2-tilde GAB
DescriptionFinalResult := function(raw_triangles, bmw)
    local new_bmw, rdwc, torsionfree;
    new_bmw := AdmissiblePresentation(bmw);
    if new_bmw = fail then
        Print("fail.\n\n");
    else
        rdwc := RaduDatumWithCoverFromTriangles(raw_triangles);
        torsionfree := CheckTorsionFreenessRDWC(rdwc);
        if torsionfree = fail then
            Print("fail.\n\n");
        else 
            DescriptionBMWPresentation(new_bmw);
            DescriptionSquareComplex(new_bmw);
            DescriptionRelabeled(rdwc);
            if torsionfree then
                Print("\nThe involutory automorphism on the GAB acts freely.\n\n"); 
            else
                Print("\nThe involutory automorphism on the GAB does not act freely.\n\n"); 
            fi;
        fi;
    fi;
end;
