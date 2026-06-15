
We provide a search algorithm to find C2-lattices containing the type-preserving
subgroup of BMW-group of degree (4,4).

Let G be a BMW-presentation in the right format, i.e. the presentation only contains
relations of the form a^2 and square relations (a1*x1*a2*x2). Then the function 
C2TildeBMW( ... ) reads in G and the number of kernel that should be used, and
searches for a complex, such that the fundamental group is an eveloping C2-tilde
lattice.

C2TildeBMWAlternative( ... ) reads in the same and returns the same, but uses a
slightly different approach in the search.

Examples of BMW-groups can be found in BMW-examples.

An example usage of C2TildeBMW( ... ) with output is provided in the
file "output_search.txt".

In the analysis files we provide methods to study the complexes and the C2-tilde
lattices.

One may verify that the fundamental group is indeed a C2-tilde lattice with the
function CheckLinks( ... ).

One may print description of the complex with DescriptionTriangleComplex( ... ).

One may print description of the automorphism group of the complex with
DescriptionAutomorphismGroupTriangleComplex( ... ).

One may compute a presentation of the index 2 supergroup (as in the article) with
PresentationExtension( ... ).

One may compute words of the presentation in normal form with
NormalForm( ... ). The functions only works for Tietze relations
with entries in [1..40]. Negative entries may cause wrong results.
Moreover the function reads in the complex rather than the presentation. 

One may test for a sufficient condition for discreteness of the C2-tilde building with
DiscretenessCheckThickness4( ... ).

A finite index subgroup of the fundamental group corresponds to a cover of the complex.
One may construct normal covers with the function ConstructRaduGraphCover ( ... ).
The function reads in the complex and a list of tietze words. The list of tietze words
describe words in the presentation constructed with PresentationExtension( ... ).
These words normally generate a finite index subgroup and the function construct the
associated normal cover.

An example usage of the methods to study the C2-tilde complex, the associated lattice
and building is provided in "study_example_complex.txt".