
LoadPackage("grape");

#with the functions in this script we can verify
#that a set of triangles (as edge paths) defines a C2-tilde GAB
#and that this GAB admits an involution induced by the labelling

#returns Radu graph equipped with automorphism group
#that maps triangles to triangles
#this group corresponds to the automorphism group of the triangle complex
RaduGraphTriangles := function(triangles)
    local shifted_triangles, rel, aut, gamma, gens, l,m,n, coloring;
    l := Maximum(List(triangles, t->t[1]));
    m := Maximum(List(triangles, t->t[2]));
    n := Maximum(List(triangles, t->t[3]));
    shifted_triangles := List(triangles, t->[t[1],t[2]+l,t[3]+l+m]);
    Sort(shifted_triangles);
    coloring := [[1..l], [l+1..n+l], [n+l+1..n+l+m]];
    rel := function(x,y)
        return (not x=y) and ForAny(shifted_triangles, t->IsSubset(t, [x,y]));
    end;
    gamma := Graph(Group(()), [1..Last(coloring[3])], OnPoints, rel, true);
    aut := AutomorphismGroup(gamma);
    gens := Filtered(aut, a-> OnSetsSets(shifted_triangles, a) = shifted_triangles );
    aut := Group(gens);
    aut := Group(SmallGeneratingSet(aut));
    gamma := NewGroupGraph(aut, gamma);
    return [gamma, coloring, shifted_triangles];
end;

CheckLinks := function(triangles)
    local rg_coloring_cover, rg, coloring, localgeo12, localgeo23, localgeo31, i, c, cons, sub;
    rg_coloring_cover := RaduGraphTriangles(triangles);
    rg := rg_coloring_cover[1];
    coloring := rg_coloring_cover[2];
    localgeo12 := InducedSubgraph(rg, Concatenation(coloring[1], coloring[2]));
    localgeo23 := InducedSubgraph(rg, Concatenation(coloring[2], coloring[3]));
    localgeo31 := InducedSubgraph(rg, Concatenation(coloring[3], coloring[1]));
    cons := ConnectedComponents(localgeo12);
    for i in [1..Size(cons)] do
        c := cons[i];
        sub := InducedSubgraph(localgeo12, c);
        Print("Link number ", i, " in the local geometry (1,2) has\n");
        Print("order ", OrderGraph(sub), ", girth ", Girth(sub), " and diameter ", Diameter(sub), ".\n\n");
    od;
    cons := ConnectedComponents(localgeo23);
    for i in [1..Size(cons)] do
        c := cons[i];
        sub := InducedSubgraph(localgeo23, c);
        Print("Link number ", i, " in the local geometry (2,3) has\n");
        Print("order ", OrderGraph(sub), ", girth ", Girth(sub), " and diameter ", Diameter(sub), ".\n\n");
    od;
    cons := ConnectedComponents(localgeo31);
    for i in [1..Size(cons)] do
        c := cons[i];
        sub := InducedSubgraph(localgeo31, c);
        Print("Link number ", i, " in the local geometry (3,1) has\n");
        Print("order ", OrderGraph(sub), ", girth ", Girth(sub), " and diameter ", Diameter(sub), ".\n\n");
    od;
end;

NiceInvolution := function(triangles)
    local radu_graph_data, coloring, radu_graph;
    radu_graph_data := RaduGraphTriangles(triangles);
    radu_graph := radu_graph_data[1];
    coloring := radu_graph_data[2];
    return First(radu_graph.group, x->OnTuples(coloring[1], x) = coloring[2]);
end;