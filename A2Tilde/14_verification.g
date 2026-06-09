
VerifyClaims := function()
    local i, char0, char2, ball_u, ball_v, ball_w, gammas;
    #
    Print("starting verification at ", CurrentDateTimeString(), "\n");
    # 
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (1):\n\n");
    for i in [1..13] do
        Print("Delta ", i, ":\n");
        CheckLinks(A2TildeTriangleComplexes[i]);
    od;
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (2):\n\n");
    ConfirmAllLattices();
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (3):\n\n");
    for i in [1..13] do
        Print("Delta ", i, ":\n");
        DescriptionAutomorphismGroupRaduDatumWithCover(A2TildeRaduDatumsWithCovers[i]);
    od;
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (4):\n\n");
    CheckForExtensions();
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (5):\n\n");
    gammas := List(A2TildeRaduDatumsWithCovers, rdwc ->  ConvinientFundamentalGroupRaduDatumWithCover(rdwc));
    for i in [1..6] do
        Print("i=", i, ":\n");
        Print("The index of the second derived subgroup is ", Index(gammas[i], DerivedSubgroup(DerivedSubgroup(gammas[i]))), "\n\n");
    od;
    Print("i=7:\n");
    Print("The maximal solvable quotient is: ", StructureDescription(FactorGroup(gammas[7],PerfectResiduum(gammas[7]))), "\n\n");
    # 
    Print("i=8:\n");
    FiniteSimpleQuotients(gammas[8], 10^6, true);
    Print("i=9:\n");
    FiniteSimpleQuotients(gammas[9], 10^6, true);
    Print("i=10:\n");
    FiniteSimpleQuotients(gammas[10], 10^6, true);
    #
    Print("i=11\n");
    Print("The maximal solvable quotient is: ", StructureDescription(FactorGroup(gammas[11],PerfectResiduum(gammas[11]))), "\n\n");
    Print("i=12\n");
    Print("The maximal solvable quotient is: ", StructureDescription(FactorGroup(gammas[12],PerfectResiduum(gammas[12]))), "\n\n");
    # 
    Print("i=13:\n");
    FiniteSimpleQuotients(gammas[13], 10^6, true);
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (6):\n\n");
    if Filtered([1..13], i-> not GraphIsomorphism(RaduGraphTriangles(A2TildeTriangleComplexes[i])[1], radu_graph_induced_by_Reg ) = fail ) = [7] then
        Print("Omega2 contains Gamma7 as index 21 subgroup.\n\n");
    fi;
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (7):\n\n");
    char0 := A2TildeBall(A2TildeTriangleComplexes[4], 1, 2)[1];
    char2 := A2TildeBall(A2TildeTriangleComplexes[1], 1, 2)[1];
    for i in [7..13] do
        ball_w := A2TildeBall(A2TildeTriangleComplexes[i], 1, 2)[1];
        if not GraphIsomorphism(char0, ball_w) = fail then
            Print("The 2-ball around w is the char 0 ball.\n");
        elif not GraphIsomorphism(char2, ball_w) = fail then
            Print("The 2-ball around w is the char 2 ball.\n");
        fi;
        ball_u := A2TildeBall(A2TildeTriangleComplexes[i], 2, 2)[1];
        if not GraphIsomorphism(char0, ball_u) = fail then
            Print("The 2-ball around u is the char 0 ball.\n");
        elif not GraphIsomorphism(char2, ball_u) = fail then
            Print("The 2-ball around u is the char 2 ball.\n");
        fi;
        ball_v := A2TildeBall(A2TildeTriangleComplexes[i], 3, 2)[1];
        if not GraphIsomorphism(char0, ball_v) = fail then
            Print("The 2-ball around v is the char 0 ball.\n");
        elif not GraphIsomorphism(char2, ball_v) = fail then
            Print("The 2-ball around v is the char 2 ball.\n");
        fi;
        Print("\n");
    od;
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (9):\n\n");
    if 
        not unitary_rep = fail
        and
        IsScalar3x3(TransposedMat(A)*Q*GaloisConjugateMatrix(A)*Q^-1)
        and
        IsScalar3x3(TransposedMat(A)*Q*GaloisConjugateMatrix(A)*Q^-1)
        and
        IsScalar3x3(TransposedMat(A)*Q*GaloisConjugateMatrix(A)*Q^-1)
        then
            Print("The representation of Gamma6 to the projective unitary group is well-defined.\n");
    fi;
    Print("\n\n----------------------------------------\n\n");
    Print("verification finished at ", CurrentDateTimeString(), "\n");
end;

