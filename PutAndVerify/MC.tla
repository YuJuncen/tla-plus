---- MODULE MC ----
EXTENDS WriteAndVerify, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
Alice, Bob
----

\* MV CONSTANT definitions CLIENTS
const_171964209906974000 == 
{Alice, Bob}
----

\* SYMMETRY definition
symm_171964209906975000 == 
Permutations(const_171964209906974000)
----

=============================================================================
\* Modification History
\* Created Sat Jun 29 14:21:39 CST 2024 by Hillium
