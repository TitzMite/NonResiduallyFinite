
The GAP code provided in this folder can verify the following results:

(1) The links of the complexes $Y_i^q$ are complete bipartite graphs and generalized quadrangles.
In particular, the universal covers are C2-tilde-buildings. Note that this could be easily checked by hand.

(2) The presentations we provide for the $\bar \Gamma_i^q$ are indeed presentations for these groups.
This is not clear, since the presentations in the article do not contain all A1A1-boundaries.
Note that for $\bar \Gamma_1^2$, we do provide a proof in the article. 

(3) The normal closure of $\bar delta^4$ contains g7g4 as described in the proof of Theorem 58 Part 2.
In particular $\Gamma_1^2$ contains no finite index subgroup.

(4) If B4 is the 4-ball in the Cayley graph of $\bar \Gamma_1^2$, then every automorphism of B4 fixes
the centered 2-ball pointwise. Therefore, the group $\bar \Gamma_1^2$ is the full automorphism
group of $X_1^2$.

(5) The automorphism group of $X_i^3$ is as described in the article. In particular it is discrete.

(6) The finite residuals $\check \Gamma_i^3$ have indices in $\bar \Gamma_i^3$ as claimed in the article.

(7) The buildings $X_i^3$ are pairwise not isomorphic.

(8) There exists a sum of squares in the real group algebra $R \bar \Gamma_1^2$ that approximates
$\Delta^2 - 1.29 \Delta$ as claimed in the article.

-------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------

We show these claims as follows.

The files "01_data_q2.g" and "02_data_q3.g" contain data encoding the triangle complexes $Y_i^q$ and the 
presentations for $\bar \Gamma_i^q$ we provide in the article.

The file "03_locally_C2tilde.g" contains the function CheckLinks(...) which computes the links of a given
triangle complex. With this function one can verify (1).

The file "04_presentations.g" contains the function CorrectPresentation(...) which verifies correctness of
the presentations for $\bar \Gamma_i^q$ indicated in article. Let R be the set of relators of a presentation
indicated in article. Let R' be the set of relators in the presentation that one obtains by applying
Lemma 60. Then CorrectPresentation(...) checks if R' is a subset of R', and it checks if every relator
in R' is trivial in the group defined by the presentation in the article. In particular, we can verify (2).

Having verified the presentations, we compute the indices of the normal closures of certain elements known
to lie in the finite residual. These indices are finite and as claimed in the article. This shows (6).

The file "05_word_problem.g" is an implementation of our algorithm to compute normal forms in
$\tilde C_2$-lattices. With these methods we can verify (3).

The file "06_building_autos.g" contains functions that compute balls in the Cayley graphs of
$\bar \Gamma_i^q$. With these methods we can verify (4) and (5) with the methods described in the article.
We actually work with the subgraphs of the Cayley graphs which we obtain by removing all leaves but this
does not affect our argumentation.

The file "07_characteristic_covers.g" contains functions that are capable of computing finite 07_characteristic_covers
of Y_i^3 corresponding to type-preserving subgroups of $\bar \Gamma_i^3$. In particular we can compute
the covers corresponding to the finite residuals, which are invariants of the buildings. Thus we can prove (7).

The file "08_data_for_Ozawas_method.g" contains the data encoding our approximation to
$\Delta^2 - 1.29 \Delta$. In "09_Ozawas_method.g" we a provide function to compute the 1-norm of the
difference between $\Delta^2 - 1.29 \Delta$ and our approximation. In particular with these methods one
can verify (8).

-------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------

The file "10_verification.g" contains the function VerifyClaims(), which verifies all claims by proceeding as 
suggested above. It also prints what has been calculated. Executing VerifyClaims() takes around 7 minutes on 
the author's computer.

The function "00_main.g" reads in all files needed to execute VerifyClaims().


